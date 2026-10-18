import PNP.Concrete.ResidualReduction.SourceReplayEndpointRun
import Lean

/-! Focused forty-register guarded replay integration. Existing parser and
per-step suites are not repeated. Independent codecs and the original maps
check both witness boundaries, sticky rejection and untouched saved fields.
Instruction termination does not mean the mathematical answer was accepted. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointRunRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceReplayEndpointRunState

example (final : Bool) (input point : BitString) (count : Nat) (p : Parameters) (loopGood good : Bool) :
    Exec (SourceReplayEndpointCheck.block final) (work count input point p loopGood good)
      (SourceReplayEndpointCheck.fuel final p point)
      (work count input point p loopGood (good && SourceReplayEndpointCheck.valid final p point)) :=
  SourceReplayEndpointCheck.block_exec final input point count p loopGood good
example (final : Bool) (p : Parameters) (point : BitString) :
    SourceReplayEndpointCheck.fuel final p point ≤ 5 * (p.original + p.terminal) + 4 * point.length + 26 :=
  SourceReplayEndpointCheck.fuel_bound final p point
example (p : Parameters) (count : Nat) (input point : BitString) (good : Bool) :
    Exec SourceReplayEndpointRun.gate (work count input point p false good)
      (SourceReplayEndpointRun.gateFuel p count input point good)
      (work 0 (SourceReplayEndpointRun.iteration p count input point good).input
        (SourceReplayEndpointRun.iteration p count input point good).point p
        (SourceReplayEndpointRun.iteration p count input point good).valid
        (SourceReplayEndpointRun.iteration p count input point good).valid) :=
  SourceReplayEndpointRun.gate_exec p count input point good
example (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) :
    Exec SourceReplayEndpointRun.block (work count input point p false prior)
      (SourceReplayEndpointRun.fuel p count input point prior) (SourceReplayEndpointRun.result p count input point prior) :=
  SourceReplayEndpointRun.block_exec p count input point prior
example (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) :
    SourceReplayEndpointRun.observed (SourceReplayEndpointRun.result p count input point prior) =
      SourceReplayEndpointRun.answer p count input point prior := SourceReplayEndpointRun.observed_result p count input point prior
example (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) :
    SourceReplayEndpointRun.answer p count input point prior =
      if prior then
        (SourceReplayTraversal.finish (SourceReplayEndpointCheck.width false p) point).bind fun first =>
          (SourceReplayLoopFields.observe (SourceReplayLoopFields.scan p.recover count input first)).bind fun pair =>
            SourceReplayTraversal.finish (SourceReplayEndpointCheck.width true p) pair.2
      else none := SourceReplayEndpointRun.answer_contract p count input point prior
example (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) :
    SourceReplayEndpointRun.answer p count input point prior =
      if prior then
        (SourceReplayTraversal.finish (SourceReplayEndpointCheck.width false p) point).bind fun first =>
          ((parseN SourceEncoding.recordCodec.parse count input).bind fun (records,cursor) =>
            (SourceReplayTraversal.walk (SourceReplayStepApply.mapOne p.recover) records first).map fun output =>
              (cursor,output)).bind fun pair => SourceReplayTraversal.finish (SourceReplayEndpointCheck.width true p) pair.2
      else none := SourceReplayEndpointRun.parsed_contract p count input point prior
example (p : Parameters) (count : Nat) (input point : BitString) :
    SourceReplayEndpointRun.observed (SourceReplayEndpointRun.result p count input point false) = none :=
  SourceReplayEndpointRun.rejected_prior p count input point
example (p : Parameters) (count : Nat) (input point : BitString) (good : Bool) :
    (SourceReplayEndpointRun.iteration p count input point good).input.length ≤ input.length ∧
      (SourceReplayEndpointRun.iteration p count input point good).point.length ≤ point.length + count :=
  SourceReplayEndpointRun.iteration_bounds p count input point good
example (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) :
    SourceReplayEndpointRun.fuel p count input point prior ≤
      count * SourceReplayLoopMachine.allowance input.length (point.length + count) +
        10 * (p.original + p.terminal) + 8 * point.length + 4 * count + 57 :=
  SourceReplayEndpointRun.fuel_bound p count input point prior

run_cmd do
  let names := [
    ``SourceReplayEndpointRunState.lift31_exec,
    ``SourceReplayEndpointRunState.core9_exec,
    ``SourceReplayEndpointRunState.read_input,
    ``SourceReplayEndpointRunState.read_point,
    ``SourceReplayEndpointRunState.read_loop_valid,
    ``SourceReplayEndpointRunState.read_mode,
    ``SourceReplayEndpointRunState.read_valid,
    ``SourceReplayEndpointRunState.guard_exec,
    ``SourceReplayEndpointRunState.clear9_exec,
    ``SourceReplayEndpointRunState.backup_exec,
    ``SourceReplayEndpointRunState.point_exec,
    ``SourceReplayEndpointRunState.restore_exec,
    ``SourceReplayEndpointRunState.clear_count_exec,
    ``SourceReplayEndpointRunState.begin_loop_exec,
    ``SourceReplayEndpointCheck.select_exec,
    ``SourceReplayEndpointCheck.seed_exec,
    ``SourceReplayEndpointCheck.block_exec,
    ``SourceReplayEndpointCheck.width_bound,
    ``SourceReplayEndpointCheck.fuel_bound,
    ``SourceReplayEndpointRun.work_enclose,
    ``SourceReplayEndpointRun.gate_exec,
    ``SourceReplayEndpointRun.block_exec,
    ``SourceReplayEndpointRun.observed_result,
    ``SourceReplayEndpointRun.answer_contract,
    ``SourceReplayEndpointRun.rejected_prior,
    ``SourceReplayEndpointRun.parsed_contract,
    ``SourceReplayEndpointRun.iteration_bounds,
    ``SourceReplayEndpointRun.gateFuel_bound,
    ``SourceReplayEndpointRun.fuel_bound]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_ENDPOINT_EXECUTION_AXIOMS_GREEN: {names.length} declarations"

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

private def originalOne (recover : Bool) (q : StepRecord) (point : BitString) : Option BitString := do
  if recover then
    let z ← (SourceEncoding.pointCodec q.dimension).decode point
    pure ((SourceEncoding.pointCodec (q.dimension + 1)).encode
      (decode (SourceBalance.markSource q.source q.step.weights) q.step.pivot q.step.tail z))
  else
    let x ← (SourceEncoding.pointCodec (q.dimension + 1)).decode point
    pure ((SourceEncoding.pointCodec q.dimension).encode (encode q.step.pivot q.step.tail x))
private def originalWalk (recover : Bool) : List StepRecord → BitString → Option BitString
  | [],point => some point
  | q :: rest,point => (originalOne recover q point).bind (originalWalk recover rest)
private def independent (p : Parameters) (count : Nat) (input point : BitString) (prior : Bool) : Option BitString := do
  if !prior then none else do
    let firstWidth := if p.recover then p.terminal else p.original
    let lastWidth := if p.recover then p.original else p.terminal
    let _ ← (SourceEncoding.pointCodec firstWidth).decode point
    let (records,_) ← parseN SourceEncoding.recordCodec.parse count input
    let output ← originalWalk p.recover records point
    let _ ← (SourceEncoding.pointCodec lastWidth).decode output
    pure output

private def check (program : Program 40) (counts : IO.Ref (Nat × Nat)) (p : Parameters)
    (count : Nat) (input point : BitString) (prior : Bool) : IO (Store 40) := do
  let ticks := SourceReplayEndpointRun.fuel p count input point prior
  if ticks > count * SourceReplayLoopMachine.allowance input.length (point.length + count) +
      10 * (p.original + p.terminal) + 8 * point.length + 4 * count + 57 then
    throw (IO.userError "Guarded replay exceeded its proved instruction bound")
  let actual := BitRegister.run program (ticks + 1) ⟨.running 0,work count input point p false prior⟩
  if actual.control != .accepted then throw (IO.userError "Guarded replay did not halt")
  let expected := SourceReplayEndpointRun.result p count input point prior
  for i in List.finRange 40 do
    if actual.store.get i != expected.get i then throw (IO.userError "Guarded replay complete register state differs")
    if (0 < i.val && i.val < 26) || (29 ≤ i.val && i.val < 35) then
      if actual.store.get i != [] then throw (IO.userError "Guarded replay left scratch, backup or countdown data")
  if actual.store.get 27 != [p.recover] || actual.store.get 35 != [p.recover] ||
      actual.store.get 36 != List.replicate p.original true || actual.store.get 37 != p.witness ||
      actual.store.get 39 != List.replicate p.terminal true then
    throw (IO.userError "Guarded replay changed protected request fields")
  if (actual.store.get 0).length > input.length || (actual.store.get 26).length > point.length + count then
    throw (IO.userError "Guarded replay exceeded cursor or witness size bounds")
  let reference := independent p count input point prior
  if SourceReplayEndpointRun.observed actual.store != reference then
    throw (IO.userError "Guarded replay differs from independent codecs and original maps")
  let firstWidth := if p.recover then p.terminal else p.original
  if !prior || point.length != firstWidth then
    if actual.store.get 0 != input || actual.store.get 26 != point || actual.store.get 28 != [] ||
        actual.store.get 38 != [] then throw (IO.userError "Rejected input was replayed or repaired")
  if reference.isSome then counts.modify (fun (good,bad) => (good + 1,bad))
  else counts.modify (fun (good,bad) => (good,bad + 1))
  pure actual.store

#eval (show IO Unit from do
  let counts ← IO.mkRef (0,0)
  let program := SourceReplayEndpointRun.block.program 0 26
  for length in List.range 4 do
    for input in words length do
      for count in [0,1,3] do
        for point in [[],[true,false]] do
          for recover in [false,true] do
            let original := if recover then point.length + count else point.length
            let terminal := if recover then point.length else point.length - count
            let p : Parameters := ⟨recover,original,terminal,[true,false,true]⟩
            for prior in [false,true] do
              discard (check program counts p count input point prior)
  IO.println "REPLAY_ENDPOINT_EXECUTION_PHASE: raw histories, zero/nonzero counts and prior rejection passed"
  for history in [[],[q0],[q1,q0],[q2,q1,q0],descending 6] do
    let n := history.length
    for recover in [false,true] do
      let ordered := if recover then history.reverse else history
      let points := if recover || n == 0 then [[]] else [List.replicate n false,List.replicate n true]
      for point in points do
        for suffix in [[],[true,false]] do
          let input := encodeSeq SourceEncoding.recordCodec.encode ordered ++ suffix
          let p : Parameters := ⟨recover,n,0,[false,true,false,true]⟩
          let accepted ← check program counts p n input point true
          if accepted.get 38 != [true] || accepted.get 0 != suffix then
            throw (IO.userError "Valid complete history did not preserve its suffix")
          discard (check program counts p n input point false)
          discard (check program counts p n input (true :: point) true)
          let wrongEnd := if recover then {p with original := n + 1} else {p with terminal := 1}
          let rejected ← check program counts wrongEnd n input point true
          if rejected.get 28 != [true] || rejected.get 38 != [] then
            throw (IO.userError "Final width rejection was confused with replay failure")
  for history in [[q1,q1,q0],[q0,q2],[q2,q0],[q1]] do
    let raw := encodeSeq SourceEncoding.recordCodec.encode history ++ [true,false]
    for recover in [false,true] do
      let point := if recover then [true] else [true,false]
      let p : Parameters := ⟨recover,2,1,[true,false,true]⟩
      for count in [history.length,history.length + 1] do
        discard (check program counts p count raw point true)
        discard (check program counts p count (raw.take (raw.length / 2)) point true)
  let lateInput := encodeSeq SourceEncoding.recordCodec.encode [q1,q1,q0] ++ [false,true]
  for recover in [false,true] do
    let point := if recover then [true] else [true,false]
    let p : Parameters := ⟨recover,2,1,point⟩
    let actual ← check program counts p 3 lateInput point true
    let first := originalOne recover q1 point
    if first.isNone || first != some (actual.get 26) || actual.get 28 != [] || actual.get 38 != [] then
      throw (IO.userError "Late rejection did not preserve the last computed witness")
  for width in [8,32,64] do
    let point := List.replicate width true
    let p : Parameters := ⟨false,width,width,[false]⟩
    discard (check program counts p 0 [true,false] point true)
    discard (check program counts {p with terminal := width + 1} 0 [true,false] point true)
  let p : Parameters := ⟨true,0,0,[]⟩
  let ticks := SourceReplayEndpointRun.fuel p 0 [] [] true
  let early := BitRegister.run program ticks ⟨.running 0,work 0 [] [] p false true⟩
  if early.control == .accepted then throw (IO.userError "Guarded replay accepted before its terminal instruction")
  let (good,bad) ← counts.get
  if good == 0 || bad == 0 then throw (IO.userError "Guarded replay did not exercise both outcomes")
  IO.println s!"REPLAY_ENDPOINT_EXECUTION_REGRESSIONS_GREEN: {good + bad} literal executions; {good} accepted; {bad} rejected; each compared with independent codecs and original maps")

#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointCheck.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointRun.gate_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointRun.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointRun.answer_contract
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointRun.parsed_contract
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointRun.rejected_prior
#print axioms PNP.Concrete.ResidualReduction.SourceReplayEndpointRun.fuel_bound

end PNP.Concrete.ResidualReduction.SourceReplayEndpointRunRegression
