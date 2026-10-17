import PNP.Concrete.ResidualReduction.SourceReplayEndpointExecute
import Lean

/-! Focused actual-input integration. This suite exercises the new connection
between the already verified loader and guarded replay; it does not rerun their
standalone suites. Every literal machine run is compared with the original
strict request specification. Serialized output and physical runtime remain open. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointExecuteRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

example (data : BitString) (s : SourceReplayEndpointState.Saved) :
    Exec SourceReplayEndpointReady.block (SourceReplayEndpointState.full (SourceReplayDataMachine.result data) s)
      (SourceReplayEndpointReady.fuel data) (SourceReplayEndpointReady.result data s) :=
  SourceReplayEndpointReady.block_exec data s
example (data : BitString) : SourceReplayEndpointReady.fuel data ≤ 4 * data.length + 37 :=
  SourceReplayEndpointReady.fuel_bound data
example (input : BitString) :
    SourceReplayEndpointReadyState.normalized (SourceReplayEndpointLoad.saved input) =
      SourceReplayEndpointRunState.saved (SourceReplayEndpointExecute.parameters input) (SourceReplayEndpointExecute.good input) :=
  SourceReplayEndpointExecute.normalized_saved input
example (input : BitString) :
    Exec SourceReplayEndpointReady.block (SourceReplayEndpointLoad.result input)
      (SourceReplayEndpointReady.fuel (SourceReplayEndpointExecute.data input)) (SourceReplayEndpointExecute.ready input) :=
  SourceReplayEndpointExecute.ready_exec input
example (input : BitString) :
    Exec SourceReplayEndpointExecute.block (SourceReplayEndpointState.initial input)
      (SourceReplayEndpointExecute.fuel input) (SourceReplayEndpointExecute.result input) :=
  SourceReplayEndpointExecute.block_exec input
example (input : BitString) :
    SourceReplayEndpointRun.observed (SourceReplayEndpointExecute.result input) = SourceReplayRequest.answer input :=
  SourceReplayEndpointExecute.answer_eq input
example (r : SourceReplayRequest.Request) :
    SourceReplayEndpointRun.answer (SourceReplayEndpointExecute.requestParameters r)
      (SourceReplayEndpointFields.count r.data) (SourceReplayEndpointFields.stream r.recover r.data) r.witness
      (SourceReplayDataFields.valid r.data) = SourceReplayEndpointFields.evaluate r :=
  SourceReplayEndpointExecute.request_answer r
example (data : BitString) : SourceReplayDataFields.valid data = (SourceEncoding.dataCodec.decode data).isSome :=
  SourceReplayEndpointExecute.data_acceptance data
example (input : BitString) :
    SourceReplayEndpointFields.count (SourceReplayEndpointExecute.data input) ≤ input.length ∧
      (SourceReplayEndpointFields.stream (SourceReplayEndpointExecute.parameters input).recover
        (SourceReplayEndpointExecute.data input)).length ≤ input.length ∧
      (SourceReplayEndpointExecute.parameters input).original ≤ input.length ∧
      (SourceReplayEndpointExecute.parameters input).terminal ≤ input.length ∧
      (SourceReplayEndpointExecute.parameters input).witness.length ≤ input.length :=
  SourceReplayEndpointExecute.input_bounds input
example (input : BitString) :
    SourceReplayEndpointExecute.fuel input ≤ input.length * (SourceReplayHistoryStack.allowance input.length +
      SourceReplayLoopMachine.allowance input.length (2 * input.length)) +
      (16 * input.length + 36) * input.length + 77 * input.length + 373 :=
  SourceReplayEndpointExecute.fuel_bound input

run_cmd do
  let names := [
    ``SourceReplayEndpointReadyState.core9_exec,
    ``SourceReplayEndpointReadyState.copy_exec,
    ``SourceReplayEndpointReadyState.push_exec,
    ``SourceReplayEndpointReadyState.read_history,
    ``SourceReplayEndpointReadyState.read_direction,
    ``SourceReplayEndpointReadyState.read_forward,
    ``SourceReplayEndpointReadyState.read_mode,
    ``SourceReplayEndpointReadyState.select_exec,
    ``SourceReplayEndpointReadyState.direction_exec,
    ``SourceReplayEndpointReadyState.normalize_exec,
    ``SourceReplayEndpointReadyState.clearExtras_exec,
    ``SourceReplayEndpointReadyState.reset_exec,
    ``SourceReplayEndpointReadyState.work_run,
    ``SourceReplayEndpointReady.loaded_view,
    ``SourceReplayEndpointReady.header_exec,
    ``SourceReplayEndpointReady.finish_exec,
    ``SourceReplayEndpointReady.block_exec,
    ``SourceReplayEndpointReady.fuel_bound,
    ``SourceReplayEndpointExecute.normalized_saved,
    ``SourceReplayEndpointExecute.ready_exec,
    ``SourceReplayEndpointExecute.block_exec,
    ``SourceReplayEndpointExecute.request_answer,
    ``SourceReplayEndpointExecute.data_acceptance,
    ``SourceReplayEndpointExecute.answer_eq,
    ``SourceReplayEndpointExecute.input_bounds,
    ``SourceReplayEndpointExecute.fuel_bound]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_ENDPOINT_EXECUTE_AXIOMS_GREEN: {names.length} declarations"

private def words : Nat → List BitString
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [false :: w,true :: w])
private def constantPoint : (n : Nat) → Bool → Point n
  | 0,_ => ()
  | n + 1,b => (b,constantPoint n b)
private def emptyRecord (n : Nat) : StepRecord :=
  ⟨n,[],⟨(),0,constantPoint n false,[]⟩⟩
private def descending : Nat → List StepRecord
  | 0 => []
  | n + 1 => emptyRecord n :: descending n
private def q0 : StepRecord := emptyRecord 0
private def q1 : StepRecord :=
  let F : Family 2 := [⟨false,(false,(true,false)),aConst 2 true⟩]
  ⟨1,F,⟨(true,()),0,(true,()),[⟨true,aConst 1 false,aConst 1 true⟩]⟩⟩
private def q2 : StepRecord :=
  let F : Family 3 := [⟨true,aConst 3 false,aConst 3 true⟩,⟨false,aConst 3 true,aConst 3 true⟩]
  ⟨2,F,⟨(true,(false,())),2,(true,(false,())),[]⟩⟩

private def d0 : SourceEncoding.ReductionData := ⟨0,[],[]⟩
private def d1 : SourceEncoding.ReductionData := ⟨0,[],[q1,q0]⟩
private def d2 : SourceEncoding.ReductionData := ⟨1,[⟨true,aConst 1 true,aConst 1 false⟩],[q0,q1]⟩
private def d3 : SourceEncoding.ReductionData := ⟨0,[],[q2,q1,q0]⟩

private def check (program : Program 40) (counts : IO.Ref (Nat × Nat)) (input : BitString) : IO (Store 40) := do
  let ticks := SourceReplayEndpointExecute.fuel input
  if ticks > input.length * (SourceReplayHistoryStack.allowance input.length +
      SourceReplayLoopMachine.allowance input.length (2 * input.length)) +
      (16 * input.length + 36) * input.length + 77 * input.length + 373 then
    throw (IO.userError "Closed replay exceeded its proved input-size instruction bound")
  let actual := BitRegister.run program (ticks + 1) ⟨.running 0,SourceReplayEndpointState.initial input⟩
  if actual.control != .accepted then throw (IO.userError "Closed replay did not halt")
  let expected := SourceReplayEndpointExecute.result input
  for i in List.finRange 40 do
    if actual.store.get i != expected.get i then throw (IO.userError "Closed replay complete register state differs")
    if (0 < i.val && i.val < 26) || (29 ≤ i.val && i.val < 35) then
      if actual.store.get i != [] then throw (IO.userError "Closed replay left scratch or countdown data")
  let reference := SourceReplayRequest.answer input
  if SourceReplayEndpointRun.observed actual.store != reference then
    throw (IO.userError "Closed replay differs from the original strict request answer")
  if (actual.store.get 0).length > input.length || (actual.store.get 26).length > 2 * input.length then
    throw (IO.userError "Closed replay exceeded source-size cursor or witness bounds")
  match SourceReplayRequest.codec.decode input with
  | none =>
    if actual.store.get 28 != [] || actual.store.get 38 != [] then
      throw (IO.userError "Malformed outer request reached replay")
  | some r =>
    if actual.store.get 27 != [r.recover] || actual.store.get 35 != [r.recover] ||
        actual.store.get 36 != List.replicate r.dimension true || actual.store.get 37 != r.witness then
      throw (IO.userError "Closed replay changed protected request fields")
    match SourceEncoding.dataCodec.decode r.data with
    | none =>
      if actual.store.get 28 != [] || actual.store.get 38 != [] then
        throw (IO.userError "Malformed saved data reached replay")
    | some d =>
      if actual.store.get 39 != List.replicate d.dimension true then
        throw (IO.userError "Closed replay terminal dimension differs from the actual data")
  match reference with
  | none =>
    if actual.store.get 38 != [] then throw (IO.userError "Closed replay repaired a rejected answer")
    counts.modify (fun (good,bad) => (good,bad + 1))
  | some point =>
    if actual.store.get 38 != [true] || actual.store.get 28 != [true] || actual.store.get 26 != point then
      throw (IO.userError "Closed replay did not expose the computed answer")
    counts.modify (fun (good,bad) => (good + 1,bad))
  pure actual.store

#eval (show IO Unit from do
  let counts ← IO.mkRef (0,0)
  let program := SourceReplayEndpointExecute.block.program 0 26
  for length in List.range 8 do
    for input in words length do
      discard (check program counts input)
  IO.println "REPLAY_ENDPOINT_EXECUTE_PHASE: hostile raw requests passed"
  for d in [d0,d1,d2,d3] do
    let data := SourceEncoding.dataCodec.encode d
    for dimension in List.range 4 do
      for point in [[],[true],[false,true],[true,false,true]] do
        for recover in [false,true] do
          let input := SourceReplayRequest.codec.encode ⟨recover,dimension,data,point⟩
          discard (check program counts input)
          discard (check program counts (input ++ [false]))
          discard (check program counts (input.take (input.length - 1)))
  let goodData := SourceEncoding.dataCodec.encode d1
  for bad in [[],[false],goodData ++ [true],goodData.take (goodData.length - 1)] do
    for recover in [false,true] do
      for point in [[],[true,false]] do
        discard (check program counts (SourceReplayRequest.codec.encode ⟨recover,2,bad,point⟩))
  let good := SourceReplayRequest.codec.encode ⟨true,2,goodData,[]⟩
  let accepted ← check program counts good
  if accepted.get 38 != [true] || (accepted.get 26).length != 2 then
    throw (IO.userError "Complete recovery did not reconstruct the requested witness")
  let trailing ← check program counts (good ++ [false])
  if trailing.get 28 != [] || trailing.get 38 != [] then
    throw (IO.userError "Valid inner data masked an outer trailing-input failure")
  let wrongStart ← check program counts (SourceReplayRequest.codec.encode ⟨true,2,goodData,[true]⟩)
  if wrongStart.get 28 != [] || wrongStart.get 38 != [] then
    throw (IO.userError "Initial width mismatch entered history replay")
  let wrongEnd ← check program counts (SourceReplayRequest.codec.encode ⟨true,3,goodData,[]⟩)
  if wrongEnd.get 28 != [true] || wrongEnd.get 38 != [] then
    throw (IO.userError "Final width mismatch was confused with a failed history")
  let late := SourceEncoding.dataCodec.encode (⟨0,[],[q1,q1,q0]⟩ : SourceEncoding.ReductionData)
  let failed ← check program counts (SourceReplayRequest.codec.encode ⟨true,3,late,[]⟩)
  if failed.get 28 != [] || failed.get 38 != [] || (failed.get 26).length != 2 then
    throw (IO.userError "Late replay rejection did not retain the last computed witness")
  for n in [0,1,4,8] do
    let data := SourceEncoding.dataCodec.encode (⟨0,[],descending n⟩ : SourceEncoding.ReductionData)
    let recovered ← check program counts (SourceReplayRequest.codec.encode ⟨true,n,data,[]⟩)
    if recovered.get 38 != [true] then throw (IO.userError "Longer generated recovery failed")
    for point in [List.replicate n false,List.replicate n true] do
      let projected ← check program counts (SourceReplayRequest.codec.encode ⟨false,n,data,point⟩)
      if projected.get 38 != [true] || projected.get 26 != [] then
        throw (IO.userError "Longer generated projection failed")
  for width in [8,32,64] do
    let empty := SourceEncoding.dataCodec.encode (⟨width,[],[]⟩ : SourceEncoding.ReductionData)
    for recover in [false,true] do
      discard (check program counts (SourceReplayRequest.codec.encode ⟨recover,width,empty,List.replicate width true⟩))
  let ticks := SourceReplayEndpointExecute.fuel good
  let early := BitRegister.run program ticks ⟨.running 0,SourceReplayEndpointState.initial good⟩
  if early.control == .accepted then throw (IO.userError "Closed replay accepted before its terminal instruction")
  let (good,bad) ← counts.get
  if good == 0 || bad == 0 then throw (IO.userError "Closed replay did not exercise both outcomes")
  IO.println s!"REPLAY_ENDPOINT_EXECUTE_REGRESSIONS_GREEN: {good + bad} literal executions; {good} accepted; {bad} rejected; each compared with the original strict request answer")

#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointReady.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointExecute.normalized_saved
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointExecute.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointExecute.request_answer
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointExecute.answer_eq
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointExecute.input_bounds
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointExecute.fuel_bound

end PNP.Concrete.ResidualReduction.SourceReplayEndpointExecuteRegression
