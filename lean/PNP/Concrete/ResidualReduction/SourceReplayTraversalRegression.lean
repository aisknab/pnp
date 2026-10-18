import PNP.Concrete.ResidualReduction.SourceReplayTraversal
import Lean

/-! Focused witness and whole-traversal integration tests. The original
dependent-typed byte functions are the independent oracle, including rejected
dimension links. This does not rerun the previously verified data parser or
single-step machine suites, and no arbitrary syntactic history is called a
semantically valid reduction. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayTraversalRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence (Registers)
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

example (n : Nat) (input : BitString) :
    SourceReplayWitness.valid n input = true ↔ input.length = n :=
  SourceReplayWitness.valid_iff_width n input
example (r : Registers) (n : Nat) (input : BitString) :
    Exec SourceReplayWitness.block ({r with input := input,remaining := List.replicate n true}).store
      (SourceReplayWitness.fuel n input) (SourceReplayWitness.result r n input).store :=
  SourceReplayWitness.block_exec r n input
example (n : Nat) (input : BitString) :
    SourceReplayWitness.fuel n input ≤ 5 * n + 4 * input.length + 8 := SourceReplayWitness.fuel_bound n input
example (history : List StepRecord) (n d : Nat) (z : Point d) :
    (SourceReplayTraversal.walk SourceReplayTraversal.recoverOne history.reverse
      ((SourceEncoding.pointCodec d).encode z)).bind (SourceEncoding.pointCodec n).decode =
        SourceEncoding.liftHistory n d history z := SourceReplayTraversal.recovery_contract history n d z
example (history : List StepRecord) (n d : Nat) (x : Point n) :
    (SourceReplayTraversal.walk SourceReplayTraversal.projectOne history
      ((SourceEncoding.pointCodec n).encode x)).bind (SourceEncoding.pointCodec d).decode =
        SourceEncoding.projectHistory n d history x := SourceReplayTraversal.projection_contract history n d x
example (n : Nat) (data witness : BitString) :
    SourceReplayTraversal.recover n data witness = SourceEncoding.recoverBytes n data witness :=
  SourceReplayTraversal.recover_eq n data witness
example (n : Nat) (data witness : BitString) :
    SourceReplayTraversal.project n data witness = SourceEncoding.projectBytes n data witness :=
  SourceReplayTraversal.project_eq n data witness
example (input : BitString) : SourceReplayTraversal.answer input = SourceReplayRequest.answer input :=
  SourceReplayTraversal.answer_eq input
example (history : List StepRecord) (input output : BitString)
    (success : SourceReplayTraversal.walk SourceReplayTraversal.recoverOne history input = some output) :
    output.length = input.length + history.length := SourceReplayTraversal.recovery_length history input output success
example (history : List StepRecord) (input output : BitString)
    (success : SourceReplayTraversal.walk SourceReplayTraversal.projectOne history input = some output) :
    output.length + history.length = input.length := SourceReplayTraversal.projection_length history input output success
example (n : Nat) (F : Family n) (z : Point (reduce n F).dimension)
    (model : models (reduce n F).core z = true) :
    ∃ x : Point n, SourceReplayTraversal.recover n (SourceEncoding.dataCodec.encode (SourceEncoding.toData (reduce n F)))
      ((SourceEncoding.pointCodec (reduce n F).dimension).encode z) = some (NativeSource.pointBytes x) ∧ models F x = true := by
  rw [SourceReplayTraversal.recover_eq]
  exact SourceEncoding.recover_reduced_model n F z model
example (n : Nat) (F : Family n) (x : Point n) (model : models F x = true) :
    (SourceReplayTraversal.project n (SourceEncoding.dataCodec.encode (SourceEncoding.toData (reduce n F)))
      ((SourceEncoding.pointCodec n).encode x)).bind
        (SourceReplayTraversal.recover n (SourceEncoding.dataCodec.encode (SourceEncoding.toData (reduce n F)))) =
          some (NativeSource.pointBytes x) := by
  have decoder : SourceReplayTraversal.recover n (SourceEncoding.dataCodec.encode (SourceEncoding.toData (reduce n F))) =
      SourceEncoding.recoverBytes n (SourceEncoding.dataCodec.encode (SourceEncoding.toData (reduce n F))) :=
    funext (fun witness => SourceReplayTraversal.recover_eq n _ witness)
  rw [SourceReplayTraversal.project_eq,decoder]
  exact SourceEncoding.recover_project_model n F x model

run_cmd do
  let names := [
    ``SourceReplayWitness.decode_width,
    ``SourceReplayWitness.decode_complete,
    ``SourceReplayWitness.decode_iff_width,
    ``SourceReplayWitness.decode_encoded,
    ``SourceReplayWitness.valid_iff_width,
    ``SourceReplayWitness.endCheck_exec,
    ``SourceReplayWitness.block_exec,
    ``SourceReplayWitness.fuel_bound,
    ``SourceReplayWitness.parsed_fields,
    ``SourceReplayWitness.rejected,
    ``SourceReplayTraversal.walk_append,
    ``SourceReplayTraversal.recover_finish,
    ``SourceReplayTraversal.project_start,
    ``SourceReplayTraversal.recovery_contract,
    ``SourceReplayTraversal.projection_contract,
    ``SourceReplayTraversal.finish_eq,
    ``SourceReplayTraversal.recover_core,
    ``SourceReplayTraversal.project_core,
    ``SourceReplayTraversal.recover_eq,
    ``SourceReplayTraversal.project_eq,
    ``SourceReplayTraversal.answer_eq,
    ``SourceReplayTraversal.recoverOne_length,
    ``SourceReplayTraversal.projectOne_length,
    ``SourceReplayTraversal.recovery_length,
    ``SourceReplayTraversal.projection_length]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_TRAVERSAL_AXIOMS_GREEN: {names.length} declarations"

private def words : Nat → List BitString
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [false :: w,true :: w])
private def registersA : Registers := ⟨[],[],[],[],[],[],[],[],[]⟩
private def registersB : Registers :=
  ⟨[true],[false,true],[true,false],[true,true],[false],[false,true],[true],[false,true,false],[true,false]⟩
private def witnessCheck (p : Program 9) (counter : IO.Ref Nat) (r : Registers) (n : Nat) (input : BitString) : IO Unit := do
  let ticks := SourceReplayWitness.fuel n input
  if ticks > 5 * n + 4 * input.length + 8 then throw (IO.userError "Strict witness instruction bound failed")
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,({r with input := input,remaining := List.replicate n true} : Registers).store⟩
  if actual.control != .accepted then throw (IO.userError "Strict witness reader failed to halt")
  let expected := (SourceReplayWitness.result r n input).store
  for i in List.finRange 9 do
    if actual.store.get i != expected.get i then throw (IO.userError "Strict witness full state differs")
  match (SourceEncoding.pointCodec n).decode input with
  | none =>
    if actual.store.get 5 != [] || SourceReplayWitness.valid n input then
      throw (IO.userError "Wrong-width witness was accepted")
  | some x =>
    if actual.store.get 5 != [true] || actual.store.get 0 != [] ||
        actual.store.get 8 != (SourceEncoding.pointCodec n).encode x then
      throw (IO.userError "Exact-width witness result differs from independent codec")
  counter.modify (· + 1)

private def q0 : StepRecord := ⟨0,[],⟨(),0,(),[]⟩⟩
private def q1 : StepRecord :=
  let F : Family 2 := [⟨false,aConst 2 true,aConst 2 false⟩]
  ⟨1,F,⟨(true,()),1,(true,()),[⟨true,aConst 1 false,aConst 1 true⟩]⟩⟩
private def q2 : StepRecord :=
  let F : Family 3 := [⟨true,aConst 3 false,aConst 3 true⟩,⟨false,aConst 3 true,aConst 3 true⟩]
  ⟨2,F,⟨(true,(false,())),2,(true,(false,())),[]⟩⟩
private def histories : List (List StepRecord) :=
  [[],[q0],[q1],[q2],[q1,q0],[q2,q1],[q2,q1,q0],[q0,q2],[q1,q1]]

private def byteCheck (counter : IO.Ref Nat) (n : Nat) (data witness : BitString) : IO Unit := do
  let a := SourceReplayTraversal.recover n data witness
  let b := SourceEncoding.recoverBytes n data witness
  let c := SourceReplayTraversal.project n data witness
  let d := SourceEncoding.projectBytes n data witness
  if a != b || c != d then throw (IO.userError "Whole traversal differs from the original byte functions")
  counter.modify (· + 2)
private def requestCheck (counter : IO.Ref Nat) (input : BitString) : IO Unit := do
  if SourceReplayTraversal.answer input != SourceReplayRequest.answer input then
    throw (IO.userError "Replay request changed its exact answer or failure semantics")
  counter.modify (· + 1)

#eval (show IO Unit from do
  let witnesses ← IO.mkRef 0
  let bytes ← IO.mkRef 0
  let requests ← IO.mkRef 0
  let p := SourceReplayWitness.block.program 0 8
  for n in [0,1,2,3,5,8,16] do
    for width in List.range 7 do
      for input in words width do
        for r in [registersA,registersB] do
          witnessCheck p witnesses r n input
  for n in [0,1,8,32,64] do
    witnessCheck p witnesses registersB n [true,false,true]
  for history in histories do
    for terminal in List.range 4 do
      let data := SourceEncoding.dataCodec.encode (⟨terminal,[],history⟩ : SourceEncoding.ReductionData)
      for original in List.range 5 do
        for width in List.range 5 do
          for witness in words width do
            byteCheck bytes original data witness
  let linked := SourceEncoding.dataCodec.encode (⟨0,[],[q2,q1,q0]⟩ : SourceEncoding.ReductionData)
  if (SourceReplayTraversal.recover 3 linked []).isNone then
    throw (IO.userError "Valid descending history failed reverse reconstruction")
  for x in words 3 do
    if SourceReplayTraversal.project 3 linked x != some [] then
      throw (IO.userError "Valid descending history failed forward projection")
  for badHistory in [[q0,q2],[q1,q1],[q2,q0],[q0,q1,q2]] do
    let data := SourceEncoding.dataCodec.encode (⟨0,[],badHistory⟩ : SourceEncoding.ReductionData)
    if (SourceReplayTraversal.recover 3 data []).isSome ||
        (SourceReplayTraversal.project 3 data [true,false,true]).isSome then
      throw (IO.userError "Mismatched dimension link was accepted")
    byteCheck bytes 3 data []
    byteCheck bytes 3 data [true,false,true]
  for data in [[],[false],linked.take (linked.length - 1),linked ++ [true]] do
    byteCheck bytes 3 data []
    if (SourceReplayTraversal.recover 3 data []).isSome then
      throw (IO.userError "Malformed data reached reconstruction")
  for original in [0,2,3,4] do
    for witness in [[],[true],[true,false,true],[false,true,false,true]] do
      for direction in [false,true] do
        let request := SourceReplayRequest.codec.encode ⟨direction,original,linked,witness⟩
        requestCheck requests request
        requestCheck requests (request ++ [false])
        requestCheck requests (request.take (request.length - 1))
  for input in [[],[false],[true,false],[true,true,true]] do
    requestCheck requests input
  IO.println s!"REPLAY_TRAVERSAL_REGRESSIONS_GREEN: {← witnesses.get} literal witness executions; {← bytes.get} byte-function comparisons; {← requests.get} request comparisons")

#print axioms PNP.Concrete.ResidualReduction.SourceReplayWitness.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayTraversal.recovery_contract
#print axioms PNP.Concrete.ResidualReduction.SourceReplayTraversal.projection_contract
#print axioms PNP.Concrete.ResidualReduction.SourceReplayTraversal.answer_eq
#print axioms PNP.Concrete.ResidualReduction.SourceReplayTraversal.recovery_length

end PNP.Concrete.ResidualReduction.SourceReplayTraversalRegression
