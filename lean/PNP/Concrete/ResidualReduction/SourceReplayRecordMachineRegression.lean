import PNP.Concrete.ResidualReduction.SourceReplayRecordMachine
import Lean

/-! Combined literal record-machine regressions, independent canonical codec
comparisons and assumption guards. Prefix parsing preserves a following suffix;
the later history traversal must enforce its record count and terminal boundary.
These cases are tests of general theorems, not additional proof milestones. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayRecordMachineRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

example (input : BitString) :
    Exec SourceReplayRecordMachine.block (SourceReplayRecordState.initial input)
      (SourceReplayRecordMachine.fuel input) (SourceReplayRecordState.result input) :=
  SourceReplayRecordMachine.block_exec input
example (input : BitString) :
    SourceReplayRecordMachine.fuel input ≤ 32 * input.length * input.length + 145 * input.length + 292 :=
  SourceReplayRecordMachine.fuel_bound input
example (input : BitString) :
    match SourceEncoding.recordCodec.parse input with
    | none => (SourceReplayRecordState.result input).get 24 = []
    | some (q,suffix) => SourceReplayRecordState.result input =
        SourceReplayRecordState.work suffix (SourceReplayRecordState.fromFields (SourceReplayRecordFields.recordFields q) true) :=
  SourceReplayRecordMachine.parse_result input
example (input : BitString) (q : StepRecord) (suffix : BitString)
    (parsed : SourceEncoding.recordCodec.parse input = some (q,suffix)) :
    Exec SourceReplayRecordMachine.block (SourceReplayRecordState.initial input)
      (SourceReplayRecordMachine.fuel input)
      (SourceReplayRecordState.work suffix (SourceReplayRecordState.fromFields (SourceReplayRecordFields.recordFields q) true)) :=
  SourceReplayRecordMachine.parsed_exec input q suffix parsed
example (q : StepRecord) (suffix : BitString) :
    Exec SourceReplayRecordMachine.block
      (SourceReplayRecordState.initial (SourceEncoding.recordCodec.encode q ++ suffix))
      (SourceReplayRecordMachine.fuel (SourceEncoding.recordCodec.encode q ++ suffix))
      (SourceReplayRecordState.work suffix (SourceReplayRecordState.fromFields (SourceReplayRecordFields.recordFields q) true)) :=
  SourceReplayRecordMachine.parsed_exec _ q suffix (SourceEncoding.recordCodec.roundtrip q suffix)

private def words : Nat → List BitString
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [false :: w,true :: w])
private def points : (n : Nat) → List (Point n)
  | 0 => [()]
  | n + 1 => (points n).flatMap (fun p => [(false,p),(true,p)])
private def zeroPoint : (n : Nat) → Point n
  | 0 => ()
  | n + 1 => (false,zeroPoint n)
private def families (n : Nat) : List (Family n) :=
  let zero := aConst n false
  let one := aConst n true
  [[],[⟨false,one,one⟩],[⟨true,zero,one⟩],[⟨true,one,zero⟩,⟨false,one,one⟩]]
private def compareStore (a b : Store 26) (label : String) : IO Unit := do
  for i in List.finRange 26 do
    if a.get i != b.get i then throw (IO.userError (label ++ ": register state differs"))
private def check (p : Program 26) (counter : IO.Ref Nat) (input : BitString) : IO Bool := do
  let ticks := SourceReplayRecordMachine.fuel input
  if ticks > 32 * input.length * input.length + 145 * input.length + 292 then
    throw (IO.userError "Combined record parser exceeded its proved encoded-size instruction bound")
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,SourceReplayRecordState.initial input⟩
  if actual.control != .accepted then throw (IO.userError "Combined record parser did not halt within its proved count")
  compareStore actual.store (SourceReplayRecordState.result input) "Combined record parser"
  counter.modify (· + 1)
  match SourceEncoding.recordCodec.parse input with
  | none =>
    if actual.store.get 24 != [] then throw (IO.userError "Combined record parser accepted malformed input")
    return false
  | some (q,suffix) =>
    let expected := SourceReplayRecordState.work suffix
      (SourceReplayRecordState.fromFields (SourceReplayRecordFields.recordFields q) true)
    compareStore actual.store expected "Independent record codec"
    return true

#eval (show IO Unit from do
  let counter ← IO.mkRef 0
  let program := SourceReplayRecordMachine.block.program 0 24
  for width in List.range 11 do
    for input in words width do
      let _ ← check program counter input
  IO.println "REPLAY_RECORD_MACHINE_PHASE: all short inputs checked against the independent codec"
  let changedRows ← IO.mkRef false
  for n in [0,1,2] do
    for F in families (n + 1) do
      for w in points F.length do
        for k in List.finRange (n + 1) do
          for v in points n do
            for G in families n do
              let q : StepRecord := ⟨n,F,⟨w,k,v,G⟩⟩
              if G.length != F.length then changedRows.set true
              for suffix in [[],[false],[true,false,true]] do
                if !(← check program counter (SourceEncoding.recordCodec.encode q ++ suffix)) then
                  throw (IO.userError "Combined record parser rejected a canonical record or suffix")
              let badPivot := natural n ++ ((SourceEncoding.familyCodec (n + 1)).encode F ++
                ((SourceEncoding.pointCodec F.length).encode w ++
                  (natural (n + 1) ++ ((SourceEncoding.pointCodec n).encode v ++ (SourceEncoding.familyCodec n).encode G))))
              if (← check program counter badPivot) then throw (IO.userError "Combined record parser accepted an out-of-range pivot")
    let q : StepRecord := ⟨n,[],⟨(),0,zeroPoint n,[]⟩⟩
    let input := SourceEncoding.recordCodec.encode q
    for cut in List.range input.length do
      if (← check program counter (input.take cut)) then throw (IO.userError "Incomplete empty-family record was accepted")
    for F in (families (n + 1)).drop 1 do
      let q : StepRecord := ⟨n,F,⟨zeroPoint F.length,0,zeroPoint n,F.map (fun _ => ⟨true,aConst n true,aConst n false⟩)⟩⟩
      let input := SourceEncoding.recordCodec.encode q
      for cut in List.range input.length do
        if (← check program counter (input.take cut)) then throw (IO.userError "Incomplete populated record was accepted")
  for n in [3,8,32] do
    let q : StepRecord := ⟨n,[],⟨(),0,zeroPoint n,[]⟩⟩
    if !(← check program counter (SourceEncoding.recordCodec.encode q ++ [true,false])) then
      throw (IO.userError "Higher-dimensional record was rejected")
    for rows in [1,8,32] do
      if (← check program counter (natural n ++ natural rows)) then
        throw (IO.userError "Truncated large source payload was accepted")
  if !(← changedRows.get) then throw (IO.userError "Combined parser tests assumed equal source and output row counts")
  IO.println s!"REPLAY_RECORD_MACHINE_REGRESSIONS_GREEN: {← counter.get} executions")

run_cmd do
  let names := [
    ``SourceReplayRecordState.wide_exec,
    ``SourceReplayRecordState.core_exec,
    ``SourceReplayRecordState.clearWork_exec,
    ``SourceReplayRecordState.reset_exec,
    ``SourceReplayRecordState.guard_exec,
    ``SourceReplayRecordState.restrict_flag,
    ``SourceReplayRecordState.seed_exec,
    ``SourceReplayRecordMachine.dimension_exec,
    ``SourceReplayRecordMachine.source_exec,
    ``SourceReplayRecordMachine.fixed_exec,
    ``SourceReplayRecordMachine.weights_exec,
    ``SourceReplayRecordMachine.pivot_exec,
    ``SourceReplayRecordMachine.tail_exec,
    ``SourceReplayRecordMachine.output_exec,
    ``SourceReplayRecordMachine.range_exec,
    ``SourceReplayRecordMachine.savedOutput_capture,
    ``SourceReplayRecordMachine.block_exec,
    ``SourceReplayRecordMachine.fuel_bound,
    ``SourceReplayRecordMachine.parse_result,
    ``SourceReplayRecordMachine.parsed_exec]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_RECORD_MACHINE_AXIOMS_GREEN: {names.length} declarations"

#print axioms PNP.Concrete.ResidualReduction.SourceReplayRecordMachine.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayRecordMachine.fuel_bound
#print axioms PNP.Concrete.ResidualReduction.SourceReplayRecordMachine.parse_result

end PNP.Concrete.ResidualReduction.SourceReplayRecordMachineRegression
