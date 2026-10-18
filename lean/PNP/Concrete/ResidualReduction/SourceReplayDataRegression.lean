import PNP.Concrete.ResidualReduction.SourceReplayDataMachine
import Lean

/-! Complete-data integration regressions. The strict codec is the independent
acceptance oracle. Tests check every register, both history orders and EOF;
they do not rerun the preceding component suites or treat syntactically valid
but unlinked histories as semantically valid reductions. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayDataRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

example (input : BitString) :
    SourceReplayDataFields.valid input = true ↔
      ∃ d : SourceEncoding.ReductionData, SourceEncoding.dataCodec.decode input = some d :=
  SourceReplayDataFields.valid_iff input
example (input : BitString) :
    Exec SourceReplayDataMachine.block (SourceReplayDataMachine.initial input)
      (SourceReplayDataMachine.fuel input) (SourceReplayDataMachine.result input) :=
  SourceReplayDataMachine.block_exec input
example (input : BitString) :
    SourceReplayDataMachine.fuel input ≤ input.length * SourceReplayHistoryStack.allowance input.length +
      (16 * input.length + 36) * input.length + 11 * input.length + 150 :=
  SourceReplayDataMachine.fuel_bound input
example (input : BitString) (bad : SourceEncoding.dataCodec.decode input = none) :
    (SourceReplayDataMachine.result input).get 34 = [] := SourceReplayDataMachine.rejected input bad
example (d : SourceEncoding.ReductionData) :
    SourceReplayDataFields.capture (SourceEncoding.dataCodec.encode d) = SourceReplayDataFields.dataFields d :=
  SourceReplayDataFields.canonical d
example : SourceReplayDataFields.valid [false,false,false] = true := by decide
example : SourceReplayDataFields.valid [false,false,false,true] = false := by decide

run_cmd do
  let names := [
    ``SourceReplayDataFields.encode_bytes,
    ``SourceReplayDataFields.canonical,
    ``SourceReplayDataFields.valid_decode,
    ``SourceReplayDataFields.decoded_fields,
    ``SourceReplayDataFields.decode_contract,
    ``SourceReplayDataFields.valid_iff,
    ``SourceReplayDataFields.bounds,
    ``SourceReplayDataMachine.lift30_exec,
    ``SourceReplayDataMachine.guard_exec,
    ``SourceReplayDataMachine.endCheck_exec,
    ``SourceReplayDataMachine.header_exec,
    ``SourceReplayDataMachine.family_exec,
    ``SourceReplayDataMachine.history_exec,
    ``SourceReplayDataMachine.block_exec,
    ``SourceReplayDataMachine.fuel_bound,
    ``SourceReplayDataMachine.parsed_fields,
    ``SourceReplayDataMachine.rejected]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_DATA_AXIOMS_GREEN: {names.length} declarations"

private def sample0 : StepRecord := ⟨0,[],⟨(),0,(),[]⟩⟩
private def sample1 : StepRecord :=
  let F : Family 2 := [⟨false,aConst 2 true,aConst 2 false⟩]
  ⟨1,F,⟨(true,()),1,(true,()),[⟨true,aConst 1 false,aConst 1 true⟩]⟩⟩
private def sample2 : StepRecord :=
  let F : Family 3 := [⟨true,aConst 3 false,aConst 3 true⟩,⟨false,aConst 3 true,aConst 3 true⟩]
  ⟨2,F,⟨(true,(false,())),2,(true,(false,())),[]⟩⟩
private def historyCases : List (List StepRecord) :=
  [[],[sample0],[sample1],[sample1,sample0],[sample2,sample1,sample0],[sample0,sample2]]
private def words : Nat → List BitString
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [false :: w,true :: w])
private def compareStore (actual expected : Store 35) : IO Unit := do
  for i in List.finRange 35 do
    if actual.get i != expected.get i then
      throw (IO.userError s!"Complete-data register {i.val} differs from its contract")
private def check (p : Program 35) (counter : IO.Ref Nat) (input : BitString) : IO Bool := do
  let ticks := SourceReplayDataMachine.fuel input
  if ticks > input.length * SourceReplayHistoryStack.allowance input.length +
      (16 * input.length + 36) * input.length + 11 * input.length + 150 then
    throw (IO.userError "Complete-data instruction bound failed")
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,SourceReplayDataMachine.initial input⟩
  if actual.control != .accepted then throw (IO.userError "Complete-data reader failed to halt")
  compareStore actual.store (SourceReplayDataMachine.result input)
  for i in ([0,26,30,31,32,33] : List (Fin 35)) do
    if (actual.store.get i).length > input.length then
      throw (IO.userError "Complete-data saved field exceeded input bytes")
  if (actual.store.get 0).length + (actual.store.get 26).length > input.length then
    throw (IO.userError "Complete-data reverse stream duplicated consumed input")
  counter.modify (· + 1)
  match SourceEncoding.dataCodec.decode input with
  | none =>
    if actual.store.get 34 != [] || SourceReplayDataFields.valid input then
      throw (IO.userError "Strict codec rejected data accepted by the literal reader")
    return false
  | some d =>
    let expected := SourceReplayDataMachine.full
      (SourceReplayHistoryStack.work 0 [] (encodeSeq SourceEncoding.recordCodec.encode d.history.reverse) true)
      ⟨List.replicate d.dimension true,List.replicate d.core.length true,
        SourceMatrixEncoding.familyBits d.core,(listCodec SourceEncoding.recordCodec).encode d.history,[true]⟩
    compareStore actual.store expected
    if !SourceReplayDataFields.valid input then
      throw (IO.userError "Canonical complete data was rejected")
    return true

#eval (show IO Unit from do
  let counter ← IO.mkRef 0
  let p := SourceReplayDataMachine.block.program 0 34
  for width in List.range 8 do
    for input in words width do
      discard (check p counter input)
  for n in [0,1,3] do
    let a : Row n := ⟨true,aConst n true,aConst n false⟩
    let b : Row n := ⟨false,aConst n false,aConst n true⟩
    for F in ([[],[a],[b,a]] : List (Family n)) do
      for records in historyCases do
        let d : SourceEncoding.ReductionData := ⟨n,F,records⟩
        let encoded := SourceEncoding.dataCodec.encode d
        if !(← check p counter encoded) then throw (IO.userError "Complete canonical data rejected")
        for suffix in [[false],[true,false,true]] do
          if (← check p counter (encoded ++ suffix)) then throw (IO.userError "Trailing bytes accepted as complete data")
        let front := natural n ++ (SourceEncoding.familyCodec n).encode F
        let raw := encodeSeq SourceEncoding.recordCodec.encode records
        if (← check p counter (front ++ (natural (records.length + 1) ++ raw))) then
          throw (IO.userError "Overstated history count accepted")
        if !records.isEmpty then
          if (← check p counter (front ++ (natural (records.length - 1) ++ raw))) then
            throw (IO.userError "Understated history count bypassed EOF")
  let complete : SourceEncoding.ReductionData :=
    ⟨2,[⟨true,aConst 2 false,aConst 2 true⟩],[sample2,sample1,sample0]⟩
  let encoded := SourceEncoding.dataCodec.encode complete
  for cut in List.range encoded.length do
    if (← check p counter (encoded.take cut)) then throw (IO.userError "Truncated data accepted")
  for n in List.range 17 do
    if (← check p counter (List.replicate n true)) then throw (IO.userError "Missing dimension terminator accepted")
  for n in [0,1,4] do
    for rows in [1,8,32] do
      if (← check p counter (natural n ++ (natural rows ++ [false]))) then
        throw (IO.userError "Missing core payload accepted")
  let badRecord : BitString := [false,false,true,false,false]
  let broken := natural 0 ++ (natural 0 ++ (natural 3 ++
    (SourceEncoding.recordCodec.encode sample1 ++ (badRecord ++ SourceEncoding.recordCodec.encode sample2))))
  if (← check p counter broken) then throw (IO.userError "Malformed middle history record accepted")
  IO.println s!"REPLAY_DATA_REGRESSIONS_GREEN: {← counter.get} complete-data executions")

#print axioms PNP.Concrete.ResidualReduction.SourceReplayDataFields.valid_iff
#print axioms PNP.Concrete.ResidualReduction.SourceReplayDataFields.bounds
#print axioms PNP.Concrete.ResidualReduction.SourceReplayDataMachine.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayDataMachine.fuel_bound
#print axioms PNP.Concrete.ResidualReduction.SourceReplayDataMachine.parsed_fields

end PNP.Concrete.ResidualReduction.SourceReplayDataRegression
