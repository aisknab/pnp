import PNP.Concrete.ResidualReduction.SourceReplayStepMachine
import Lean

/-! Focused integration of the raw-record parser, witness check and computed
replay step. These tests do not rerun the component suites. The oracle decodes
the actual bytes independently and applies the original mathematical maps;
malformed inputs, width mismatches, both directions and preserved suffixes
are checked against all thirty registers. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayStepRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

example (recover : Bool) (input point : BitString) :
    Exec SourceReplayStepMachine.block (SourceReplayStepState.initial input point recover)
      (SourceReplayStepMachine.fuel recover input point) (SourceReplayStepMachine.result recover input point) :=
  SourceReplayStepMachine.block_exec recover input point
example (recover : Bool) (input point : BitString) :
    SourceReplayStepMachine.result recover input point =
      match SourceReplayStepMachine.answer recover input point with
      | none => SourceReplayStepState.work (SourceReplayRecordFields.rest input) point recover false
      | some (cursor,output) => SourceReplayStepState.work cursor output recover true :=
  SourceReplayStepMachine.result_contract recover input point
example (recover : Bool) (input point : BitString) :
    SourceReplayStepMachine.fuel recover input point ≤
      50 * input.length * input.length + 228 * input.length + 4 * point.length + 406 :=
  SourceReplayStepMachine.fuel_bound recover input point
example (recover : Bool) (input point cursor output : BitString)
    (accepted : SourceReplayStepMachine.answer recover input point = some (cursor,output)) :
    cursor.length ≤ input.length ∧
      (if recover then output.length = point.length + 1 else output.length + 1 = point.length) :=
  SourceReplayStepMachine.answer_bounds recover input point cursor output accepted
example (recover : Bool) (q : StepRecord) (cursor point : BitString) :
    Exec SourceReplayStepApply.block (SourceReplayStepMachine.prepared recover q cursor point)
      (SourceReplayStepMachine.applicationFuel recover q point)
      (SourceReplayStepMachine.mappedResult recover cursor point (SourceReplayStepApply.mapOne recover q point)) :=
  SourceReplayStepMachine.application_exec recover q cursor point
example (recover : Bool) (q : StepRecord) (point : BitString) (L : Nat)
    (dimension : q.dimension ≤ L) (rows : q.source.length ≤ L) :
    SourceReplayStepMachine.applicationFuel recover q point ≤ (18 * L + 49) * L + 29 * L + 77 :=
  SourceReplayStepMachine.applicationFuel_bound recover q point L dimension rows
example (input : BitString) (q : StepRecord) (cursor : BitString)
    (parsed : SourceEncoding.recordCodec.parse input = some (q,cursor)) :
    q.dimension ≤ input.length ∧ q.source.length ≤ input.length ∧ cursor.length ≤ input.length :=
  SourceReplayStepMachine.source_bounds input q cursor parsed
example (recover : Bool) (input point : BitString)
    (bad : SourceEncoding.recordCodec.parse input = none) :
    SourceReplayStepMachine.result recover input point =
      SourceReplayStepState.work (SourceReplayRecordFields.rest input) point recover false := by
  simp only [SourceReplayStepMachine.result,bad]

run_cmd do
  let names := [
    ``SourceReplayStepState.lift26_exec,
    ``SourceReplayStepState.lift16_exec,
    ``SourceReplayStepState.core9_exec,
    ``SourceReplayStepState.record_view,
    ``SourceReplayStepState.capture_exec,
    ``SourceReplayStepState.guard_exec,
    ``SourceReplayStepState.clear9_exec,
    ``SourceReplayStepState.witnessSeed_exec,
    ``SourceReplayStepState.mapSetup_exec,
    ``SourceReplayStepState.copyPoint_exec,
    ``SourceReplayStepState.finish_exec,
    ``SourceReplayStepPrepare.block_exec,
    ``SourceReplayStepPrepare.required_bound,
    ``SourceReplayStepPrepare.fuel_bound,
    ``SourceReplayStepPrepare.parsed_capture,
    ``SourceReplayStepPrepare.invalid_record,
    ``SourceReplayStepPrepare.parsed_valid,
    ``SourceReplayStepApply.failure_exec,
    ``SourceReplayStepApply.recover_exec,
    ``SourceReplayStepApply.project_exec,
    ``SourceReplayStepApply.mapFuel_bound,
    ``SourceReplayStepMachine.application_exec,
    ``SourceReplayStepMachine.block_exec,
    ``SourceReplayStepMachine.result_contract,
    ``SourceReplayStepMachine.source_bounds,
    ``SourceReplayStepMachine.applicationFuel_bound,
    ``SourceReplayStepMachine.afterFuel_bound,
    ``SourceReplayStepMachine.fuel_bound,
    ``SourceReplayStepMachine.answer_bounds]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_STEP_AXIOMS_GREEN: {names.length} declarations"

private def words : Nat → List BitString
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun w => [false :: w,true :: w])
private def q0 : StepRecord := ⟨0,[],⟨(),0,(),[]⟩⟩
private def q1 : StepRecord :=
  let F : Family 2 := [⟨false,(false,(true,false)),aConst 2 true⟩]
  ⟨1,F,⟨(true,()),0,(true,()),[⟨true,aConst 1 false,aConst 1 true⟩]⟩⟩
private def q2 : StepRecord :=
  let F : Family 3 := [⟨true,aConst 3 false,aConst 3 true⟩,⟨false,aConst 3 true,aConst 3 true⟩]
  ⟨2,F,⟨(true,(false,())),2,(true,(false,())),[]⟩⟩
private def q3 : StepRecord :=
  ⟨1,[],⟨(),1,(false,()),[⟨false,aConst 1 true,aConst 1 false⟩,⟨true,aConst 1 false,aConst 1 true⟩]⟩⟩

private def oracle (recover : Bool) (input point : BitString) : Option (BitString × BitString) := do
  let (q,cursor) ← SourceEncoding.recordCodec.parse input
  if recover then
    let z ← (SourceEncoding.pointCodec q.dimension).decode point
    pure (cursor,(SourceEncoding.pointCodec (q.dimension + 1)).encode
      (decode (SourceBalance.markSource q.source q.step.weights) q.step.pivot q.step.tail z))
  else
    let x ← (SourceEncoding.pointCodec (q.dimension + 1)).decode point
    pure (cursor,(SourceEncoding.pointCodec q.dimension).encode (encode q.step.pivot q.step.tail x))

private def check (p : Program 30) (counts : IO.Ref (Nat × Nat)) (recover : Bool)
    (input point : BitString) : IO Unit := do
  let ticks := SourceReplayStepMachine.fuel recover input point
  if ticks > 50 * input.length * input.length + 228 * input.length + 4 * point.length + 406 then
    throw (IO.userError "Replay step exceeded its proved instruction bound")
  let start := SourceReplayStepState.initial input point recover
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,start⟩
  if actual.control != .accepted then throw (IO.userError "Replay step did not halt within its exact instruction count")
  let expected := SourceReplayStepMachine.result recover input point
  for i in List.finRange 30 do
    if actual.store.get i != expected.get i then throw (IO.userError "Replay step full state differs")
    if (0 < i.val && i.val < 26) || i.val == 29 then
      if actual.store.get i != [] then throw (IO.userError "Replay step left stale scratch data")
  if actual.store.get 27 != [recover] then throw (IO.userError "Replay step changed its direction")
  let independent := oracle recover input point
  if SourceReplayStepMachine.answer recover input point != independent then
    throw (IO.userError "Replay step answer differs from independent decoding and mathematical map")
  match independent with
  | none =>
    if actual.store.get 28 != [] || actual.store.get 26 != point then
      throw (IO.userError "Rejected record or witness changed the original point")
    counts.modify (fun (good,bad) => (good,bad + 1))
  | some (cursor,output) =>
    if actual.store.get 28 != [true] || actual.store.get 0 != cursor || actual.store.get 26 != output then
      throw (IO.userError "Computed witness or preserved unread stream differs")
    if cursor.length > input.length then throw (IO.userError "Unread stream grew")
    if recover then
      if output.length != point.length + 1 then throw (IO.userError "Reconstruction width is incorrect")
    else
      if output.length + 1 != point.length then throw (IO.userError "Projection width is incorrect")
    counts.modify (fun (good,bad) => (good + 1,bad))

#eval (show IO Unit from do
  let counts ← IO.mkRef (0,0)
  let p := SourceReplayStepMachine.block.program 0 26
  for length in List.range 7 do
    for input in words length do
      for point in [[],[false],[true,false],[false,true,false]] do
        for recover in [false,true] do
          check p counts recover input point
  IO.println "REPLAY_STEP_PHASE: hostile raw inputs and exact rejection state passed"
  for q in [q0,q1,q2,q3] do
    for suffix in [[],[false,true,false],SourceEncoding.recordCodec.encode q1] do
      let input := SourceEncoding.recordCodec.encode q ++ suffix
      for width in List.range 5 do
        for point in words width do
          for recover in [false,true] do
            check p counts recover input point
    let encoded := SourceEncoding.recordCodec.encode q
    for amount in [1,2,3,encoded.length / 2,encoded.length - 1] do
      for point in [[],[true],[true,false]] do
        for recover in [false,true] do
          check p counts recover (encoded.take amount) point
  let input := SourceEncoding.recordCodec.encode q1 ++ [true,false]
  let first := oracle true input [false]
  let second := oracle true input [true]
  if first.isNone || second.isNone || first == second then
    throw (IO.userError "Reconstruction fixture failed to exercise input-dependent computed answers")
  let ticks := SourceReplayStepMachine.fuel true input [true]
  let early := BitRegister.run p ticks ⟨.running 0,SourceReplayStepState.initial input [true] true⟩
  if early.control == .accepted then throw (IO.userError "Replay step accepted before its exact terminal instruction")
  let (good,bad) ← counts.get
  if good == 0 || bad == 0 then throw (IO.userError "Replay step did not exercise both acceptance and rejection")
  IO.println s!"REPLAY_STEP_REGRESSIONS_GREEN: {good + bad} literal executions; {good} accepted; {bad} rejected")

#print axioms PNP.Concrete.ResidualReduction.SourceReplayStepPrepare.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayStepApply.recover_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayStepApply.project_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayStepMachine.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayStepMachine.result_contract
#print axioms PNP.Concrete.ResidualReduction.SourceReplayStepMachine.fuel_bound
#print axioms PNP.Concrete.ResidualReduction.SourceReplayStepMachine.answer_bounds

end PNP.Concrete.ResidualReduction.SourceReplayStepRegression
