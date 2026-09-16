import PNP.NANDWireDescendantGain

namespace PNP.Regression.WireDescendantGain

open PNP.DirectWire WireDescendantHistory

example {inputs outputs : Nat} {source : Implementation inputs outputs}
    {stages : List RawStage} (gain : GainResult source stages) :
    StrictEquivalentGain source gain.run.result :=
  gain.strictGain

example {inputs outputs : Nat} {source : Implementation inputs outputs}
    {stages : List RawStage} (gain : GainResult source stages) :
    residualSlack gain.run.result < residualSlack source :=
  gain.strictResidualDescent

private def usedProgram : Program 2 4 :=
  ((((.empty : Program 2 0).snoc ⟨.input 0, .input 0⟩).snoc ⟨.input 0, .input 1⟩).snoc
    ⟨.gate 0, .input 1⟩).snoc ⟨.gate 1, .gate 2⟩

/-- The fifth source gate is unused by both outputs. Each first-stage splice
retains it as exterior; only the final whole-result normalization removes it. -/
private def source : Implementation 2 2 :=
  (Candidate.ofDirectWireWord (usedProgram.snoc ⟨.input 0, .input 0⟩)
    ⟨fun output => if output.val = 0 then .gate 3 else .gate 2⟩).toImplementation

private def growing : RawStage :=
  ⟨0, [.gate 1], [⟨10, [], .createR5 0⟩, ⟨20, [], .restoreR8 10⟩]⟩

private def normalized : RawStage :=
  ⟨0, (List.range 7).map RawRecord.gate, [⟨20, [], .normalize⟩]⟩

#eval show IO Unit from do
  let some first := compile source [growing]
    | throw (IO.userError "valid expanding first stage rejected")
  let some second := compile source [growing, growing]
    | throw (IO.userError "valid expanding second stage rejected")
  if first.result.gateCount != 6 || second.result.gateCount != 7 then
    throw (IO.userError "gain fixture did not retain its temporarily expanding descendants")
  let stages := [growing, growing, normalized]
  let some gain := compileGain source stages
    | throw (IO.userError "strict net improvement rejected after valid intermediate expansion")
  if gain.run.result.gateCount != 4 || gain.run.chargedCount != 2 ||
      gain.run.removedCount != 3 || gain.run.ledger.charged.length != 2 ||
      gain.run.ledger.removed.length != 3 then
    throw (IO.userError "whole-source gain lost actual accounting or retained the unused source gate")
  if !(gain.run.ledger.removed.contains (.original ⟨4, by decide⟩)) ||
      !(gain.run.ledger.removed.contains (.allocated 0 20 0)) ||
      !(gain.run.ledger.removed.contains (.allocated 1 20 0)) then
    throw (IO.userError "net-gain removal history lost an original gate or a stage-qualified allocation")
  if (compileGain source []).isSome || (compileGain source [growing]).isSome then
    throw (IO.userError "equal-size or expanding final result was accepted as a strict gain")
  let malformed : RawStage := ⟨0, [.gate 100], []⟩
  if (compileGain source [growing, growing, malformed]).isSome then
    throw (IO.userError "malformed late stage returned a partial gain")
  let some invalidRun := compile source [growing, growing]
    | throw (IO.userError "valid non-gain program rejected")
  if invalidRun.result.gateCount ≤ source.gateCount then
    throw (IO.userError "non-gain regression did not actually expand")
  IO.println "M267 descendant-final-net-gain-regressions-passed"

#print axioms CompiledRun.strictGain
#print axioms GainResult.strictGain
#print axioms GainResult.strictResidualDescent
#print axioms compileGain_compile_none
#print axioms compileGain_no_gain
#print axioms compileGain_complete
#print axioms compileGain_exists_iff

end PNP.Regression.WireDescendantGain
