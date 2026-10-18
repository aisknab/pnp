import PNP.Concrete.ResidualReduction.SourceReplayEndpointLoad
import Lean

/-! Focused outer/inner reader integration. Successful loading is syntactic
acceptance, not a verified witness or a valid reduction. The complete replay
specification is checked separately from the forty-register loading machine.
Existing component reader and history-loop suites are not rerun here. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointLoadRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

example (input : BitString) : SourceReplayEndpointFields.answer input = SourceReplayRequest.answer input :=
  SourceReplayEndpointFields.answer_eq input
example (r : SourceReplayRequest.Request) : SourceReplayEndpointFields.evaluate r = SourceReplayRequest.evaluate r :=
  SourceReplayEndpointFields.evaluate_eq r
example (recover : Bool) (data : BitString) :
    SourceReplayEndpointFields.count data ≤ data.length ∧
      (SourceReplayEndpointFields.stream recover data).length ≤ data.length ∧
      SourceReplayDataFields.dimension data ≤ data.length := SourceReplayEndpointFields.input_bounds recover data
example (p : SourceReplayParserState.Saved) :
    Exec SourceReplayEndpointLoad.handoff
      (SourceReplayEndpointState.full (SourceReplayEndpointLoad.parserCore p) SourceReplayEndpointState.emptySaved) 43
      (SourceReplayEndpointState.work p.data (SourceReplayEndpointState.fromParser p)) :=
  SourceReplayEndpointLoad.handoff_exec p
example (input : BitString) :
    Exec SourceReplayEndpointLoad.block (SourceReplayEndpointState.initial input)
      (SourceReplayEndpointLoad.fuel input) (SourceReplayEndpointLoad.result input) :=
  SourceReplayEndpointLoad.block_exec input
example (input : BitString) :
    SourceReplayEndpointLoad.fuel input ≤ input.length * SourceReplayHistoryStack.allowance input.length +
      (16 * input.length + 36) * input.length + 41 * input.length + 279 := SourceReplayEndpointLoad.fuel_bound input
example (input : BitString) (r : SourceReplayRequest.Request)
    (parsed : SourceReplayRequest.codec.decode input = some r) :
    SourceReplayParser.completedSaved input =
      ⟨[r.recover],List.replicate r.dimension true,r.data,r.witness,[true]⟩ :=
  SourceReplayEndpointLoad.parsed_saved input r parsed
example (input : BitString) (r : SourceReplayRequest.Request) (d : SourceEncoding.ReductionData)
    (parsed : SourceReplayRequest.codec.decode input = some r)
    (decoded : SourceEncoding.dataCodec.decode r.data = some d) :
    SourceReplayEndpointLoad.result input = SourceReplayEndpointState.full (SourceReplayDataMachine.result r.data)
      ⟨[r.recover],List.replicate r.dimension true,r.witness,[true],List.replicate d.dimension true⟩ :=
  SourceReplayEndpointLoad.loaded_saved input r d parsed decoded
example (input : BitString) :
    (SourceReplayEndpointLoad.result input).get 38 = SourceReplayRecordState.flag
      ((SourceReplayRequest.codec.decode input).bind (fun r => SourceEncoding.dataCodec.decode r.data)).isSome :=
  SourceReplayEndpointLoad.acceptance_contract input
example (input : BitString) (bad : SourceReplayRequest.codec.decode input = none) :
    (SourceReplayEndpointLoad.result input).get 38 = [] := SourceReplayEndpointLoad.invalid_outer input bad

run_cmd do
  let names := [
    ``SourceReplayEndpointFields.decoded_fields,
    ``SourceReplayEndpointFields.count_decoded,
    ``SourceReplayEndpointFields.stream_decoded,
    ``SourceReplayEndpointFields.replay_eq,
    ``SourceReplayEndpointFields.evaluate_eq,
    ``SourceReplayEndpointFields.answer_eq,
    ``SourceReplayEndpointFields.input_bounds,
    ``SourceReplayEndpointFields.outer_bounds,
    ``SourceReplayEndpointFields.outer_flag,
    ``SourceReplayEndpointState.lift35_exec,
    ``SourceReplayEndpointState.lift14_exec,
    ``SourceReplayEndpointState.copy_saved_exec,
    ``SourceReplayEndpointState.copy_core_exec,
    ``SourceReplayEndpointState.clear_saved_exec,
    ``SourceReplayEndpointState.read_mode,
    ``SourceReplayEndpointState.read_dimension,
    ``SourceReplayEndpointState.read_witness,
    ``SourceReplayEndpointState.read_valid,
    ``SourceReplayEndpointState.read_terminal,
    ``SourceReplayEndpointState.guard_exec,
    ``SourceReplayEndpointState.clearWork_exec,
    ``SourceReplayEndpointLoad.handoff_exec,
    ``SourceReplayEndpointLoad.outer_exec,
    ``SourceReplayEndpointLoad.dataFinish_exec,
    ``SourceReplayEndpointLoad.inner_exec,
    ``SourceReplayEndpointLoad.block_exec,
    ``SourceReplayEndpointLoad.fuel_bound,
    ``SourceReplayEndpointLoad.parsed_saved,
    ``SourceReplayEndpointLoad.loaded_saved,
    ``SourceReplayEndpointLoad.invalid_outer,
    ``SourceReplayEndpointLoad.invalid_data,
    ``SourceReplayEndpointLoad.acceptance_contract]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_ENDPOINT_LOAD_AXIOMS_GREEN: {names.length} declarations"

private def words : Nat → List BitString
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [false :: w,true :: w])
private def q0 : StepRecord := ⟨0,[],⟨(),0,(),[]⟩⟩
private def q1 : StepRecord :=
  let F : Family 2 := [⟨false,(false,(true,false)),aConst 2 true⟩]
  ⟨1,F,⟨(true,()),0,(true,()),[]⟩⟩
private def d0 : SourceEncoding.ReductionData := ⟨0,[],[]⟩
private def d1 : SourceEncoding.ReductionData := ⟨0,[],[q1,q0]⟩
private def d2 : SourceEncoding.ReductionData := ⟨1,[⟨true,aConst 1 true,aConst 1 false⟩],[q0,q1]⟩

private def check (p : Program 40) (counts : IO.Ref (Nat × Nat)) (input : BitString) : IO (Store 40) := do
  let ticks := SourceReplayEndpointLoad.fuel input
  if ticks > input.length * SourceReplayHistoryStack.allowance input.length +
      (16 * input.length + 36) * input.length + 41 * input.length + 279 then
    throw (IO.userError "Closed input loader exceeded its proved instruction bound")
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,SourceReplayEndpointState.initial input⟩
  if actual.control != .accepted then throw (IO.userError "Closed input loader did not halt")
  let expected := SourceReplayEndpointLoad.result input
  for i in List.finRange 40 do
    if actual.store.get i != expected.get i then throw (IO.userError "Closed input loader complete register state differs")
  if SourceReplayEndpointFields.answer input != SourceReplayRequest.answer input then
    throw (IO.userError "Derived replay fields changed the original closed-request answer")
  match SourceReplayRequest.codec.decode input with
  | none =>
    if actual.store.get 38 != [] then throw (IO.userError "Invalid outer request was repaired by inner parsing")
    counts.modify (fun (good,bad) => (good,bad + 1))
  | some r =>
    if actual.store.get 35 != [r.recover] || actual.store.get 36 != List.replicate r.dimension true ||
        actual.store.get 37 != r.witness then throw (IO.userError "Protected outer fields changed")
    if r.dimension > input.length || r.data.length > input.length || r.witness.length > input.length then
      throw (IO.userError "Outer decoded fields exceed encoded-input bounds")
    for recover in [false,true] do
      if SourceReplayEndpointFields.count r.data > r.data.length ||
          (SourceReplayEndpointFields.stream recover r.data).length > r.data.length then
        throw (IO.userError "Derived history stream or count exceeds actual data size")
    match SourceEncoding.dataCodec.decode r.data with
    | none =>
      if actual.store.get 38 != [] then throw (IO.userError "Invalid saved data reached acceptance")
      counts.modify (fun (good,bad) => (good,bad + 1))
    | some d =>
      if actual.store.get 38 != [true] || actual.store.get 39 != List.replicate d.dimension true ||
          actual.store.get 30 != List.replicate d.dimension true || actual.store.get 0 != [] ||
          actual.store.get 31 != List.replicate d.core.length true ||
          actual.store.get 32 != SourceMatrixEncoding.familyBits d.core ||
          actual.store.get 33 != (listCodec SourceEncoding.recordCodec).encode d.history ||
          actual.store.get 26 != encodeSeq SourceEncoding.recordCodec.encode d.history.reverse then
        throw (IO.userError "Loaded data differs from independent strict codec")
      if d.dimension > r.data.length then throw (IO.userError "Terminal dimension exceeds encoded data size")
      counts.modify (fun (good,bad) => (good + 1,bad))
  pure actual.store

#eval (show IO Unit from do
  let counts ← IO.mkRef (0,0)
  let p := SourceReplayEndpointLoad.block.program 0 26
  for length in List.range 8 do
    for input in words length do
      discard (check p counts input)
  let good0 := SourceEncoding.dataCodec.encode d0
  let good1 := SourceEncoding.dataCodec.encode d1
  let good2 := SourceEncoding.dataCodec.encode d2
  for data in [good0,good1,good2,[],[false],good1 ++ [true]] do
    for dimension in List.range 4 do
      for point in [[],[true],[false,true],[true,false,true]] do
        for recover in [false,true] do
          let input := SourceReplayRequest.codec.encode ⟨recover,dimension,data,point⟩
          discard (check p counts input)
          discard (check p counts (input ++ [false]))
          discard (check p counts (input.take (input.length - 1)))
  IO.println "REPLAY_ENDPOINT_LOAD_PHASE: independent outer/inner acceptance and complete state passed"
  let valid := SourceReplayRequest.codec.encode ⟨true,2,good1,[]⟩
  let trailing ← check p counts (valid ++ [false])
  if trailing.get 34 != [true] || trailing.get 38 != [] then
    throw (IO.userError "A later valid data parse overwrote outer rejection")
  let wrongWidth := SourceReplayRequest.codec.encode ⟨true,2,good1,[true]⟩
  let loaded ← check p counts wrongWidth
  if loaded.get 38 != [true] || (SourceReplayEndpointFields.answer wrongWidth).isSome then
    throw (IO.userError "Syntactic loading was confused with witness acceptance")
  let wrongLink := SourceReplayRequest.codec.encode ⟨true,3,
    SourceEncoding.dataCodec.encode (⟨0,[],[q0,q1]⟩ : SourceEncoding.ReductionData),[]⟩
  let loadedBadLink ← check p counts wrongLink
  if loadedBadLink.get 38 != [true] || (SourceReplayEndpointFields.answer wrongLink).isSome then
    throw (IO.userError "Syntactic history was confused with a valid replay chain")
  for dimension in [8,32,64] do
    discard (check p counts (SourceReplayRequest.codec.encode ⟨false,dimension,good0,[true,false]⟩))
  let ticks := SourceReplayEndpointLoad.fuel valid
  let early := BitRegister.run p ticks ⟨.running 0,SourceReplayEndpointState.initial valid⟩
  if early.control == .accepted then throw (IO.userError "Closed input loader accepted before its terminal instruction")
  let (good,bad) ← counts.get
  if good == 0 || bad == 0 then throw (IO.userError "Closed input loader did not exercise both outcomes")
  IO.println s!"REPLAY_ENDPOINT_LOAD_REGRESSIONS_GREEN: {good + bad} literal executions; {good} syntactically accepted; {bad} rejected; each compared with original request semantics")

#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointFields.evaluate_eq
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointFields.answer_eq
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointLoad.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointLoad.fuel_bound
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointLoad.loaded_saved
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointLoad.acceptance_contract

end PNP.Concrete.ResidualReduction.SourceReplayEndpointLoadRegression
