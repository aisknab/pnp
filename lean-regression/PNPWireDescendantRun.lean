import PNP.NANDWireDescendantRun

namespace PNP.Regression.WireDescendantRun

open PNP.DirectWire WireDescendantHistory

example {inputs outputs : Nat} {source : Implementation inputs outputs}
    {stages : List RawStage} (run : CompiledRun source stages) :
    (∀ valuation output, run.result.candidate.semantics valuation output =
      source.candidate.semantics valuation output) ∧
      run.result.gateCount + run.removedCount = source.gateCount + run.chargedCount :=
  ⟨run.semantics, run.gate_balance⟩

example {inputs outputs : Nat} (source : Implementation inputs outputs)
    (stage : RawStage) (stages : List RawStage)
    (first : StageCompilation source stage)
    (firstAt : compileStage source stage = some first)
    (failed : compile first.result stages = none) :
    compile source (stage :: stages) = none :=
  compile_tail_none source stage stages first firstAt failed

private def program : Program 2 4 :=
  ((((.empty : Program 2 0).snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 1⟩).snoc
    ⟨.gate 0, .input 1⟩).snoc ⟨.gate 1, .gate 2⟩

private def source : Implementation 2 2 :=
  (Candidate.ofDirectWireWord program
    ⟨fun output => if output.val = 0 then .gate 3 else .gate 2⟩).toImplementation

private def growing : RawStage :=
  ⟨0, [.gate 1], [⟨10, [], .createR5 0⟩, ⟨20, [], .restoreR8 10⟩]⟩

private def emptySource : Implementation 0 0 :=
  (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation

#eval show IO Unit from do
  let some unchanged := compile source []
    | throw (IO.userError "empty program rejected")
  if unchanged.result.gateCount != 4 || unchanged.chargedCount != 0 ||
      unchanged.removedCount != 0 then
    throw (IO.userError "empty program changed the source or fabricated work")
  let some twice := compile source [growing, growing]
    | throw (IO.userError "successive expanding stages or reused local identities rejected")
  if twice.result.gateCount != 6 || twice.chargedCount != 2 || twice.removedCount != 0 then
    throw (IO.userError "whole-program totals do not sum the actual expanding executions")
  -- The third stage refers to a physical gate absent from the original source.
  -- Its validity must be determined from the actual two-stage descendant.
  let laterSupport : RawStage := ⟨0, [.gate 5], []⟩
  let some later := compile source [growing, growing, laterSupport]
    | throw (IO.userError "later support was decoded against stale original bounds")
  if later.result.gateCount != 6 || later.chargedCount != 2 || later.removedCount != 0 then
    throw (IO.userError "accepted later stage changed the accumulated execution totals")
  let invalidSupport : RawStage := ⟨0, [.gate 6], []⟩
  if (compile source [growing, growing, invalidSupport]).isSome then
    throw (IO.userError "invalid later support returned an accepted prefix")
  let invalidField : RawStage := ⟨0, [.gate 5], [⟨1, [], .readFull 999⟩]⟩
  if (compile source [growing, growing, invalidField]).isSome then
    throw (IO.userError "invalid later field returned an accepted prefix")
  let unfinished : RawStage := ⟨0, [.gate 1], [⟨10, [], .createR5 0⟩]⟩
  if (compile source [growing, unfinished]).isSome then
    throw (IO.userError "unfinished later history returned an accepted prefix")
  let noGates : RawStage := ⟨0, [], [⟨1, [], .normalize⟩]⟩
  let some empty := compile emptySource [noGates, noGates]
    | throw (IO.userError "empty descendants or reused cross-stage identity rejected")
  if empty.result.gateCount != 0 || empty.chargedCount != 0 || empty.removedCount != 0 then
    throw (IO.userError "empty sequence fabricated a physical gate or cost")
  IO.println "M267 arbitrary-descendant-run-regressions-passed"

#print axioms CompiledRun.semantics
#print axioms CompiledRun.gate_balance
#print axioms compile_nil
#print axioms compile_cons
#print axioms compile_stage_none
#print axioms compile_tail_none
#print axioms compile_cons_some
#print axioms compile_sound

end PNP.Regression.WireDescendantRun
