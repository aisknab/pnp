/-
Copyright (c) 2026 PNP Labs.

Accept a net gain only after the complete raw descendant program succeeds.
Intermediate stages may expand. Semantic equivalence comes from the structural
stage theorems; the only extra executable test is the final gate-count comparison.

This validates an offered finite program. It does not find a successful global
strategy, close open obligations across stages, prove terminal minimality or
establish polynomial bounds. No truth-table or reference-minimum search is used
to authorize the executable result.
-/

import PNP.NANDWireDescendantCharges
import PNP.ResidualRoutes

namespace PNP.DirectWire.WireDescendantHistory

variable {inputs outputs : Nat}

/-- Use the whole run's proved semantics, not an executable equivalence oracle. -/
theorem CompiledRun.strictGain {source : Implementation inputs outputs}
    {stages : List RawStage} (run : CompiledRun source stages)
    (smaller : run.result.gateCount < source.gateCount) :
    StrictEquivalentGain source run.result :=
  ⟨smaller, fun valuation output => run.semantics valuation output⟩

/-- A computed successful program and its checked final decrease.
These receipts are produced internally by the raw-input adapter. -/
structure GainResult (source : Implementation inputs outputs) (stages : List RawStage) where
  run : CompiledRun source stages
  runAt : compile source stages = some run
  smaller : run.result.gateCount < source.gateCount

namespace GainResult

variable {source : Implementation inputs outputs} {stages : List RawStage}
variable (gain : GainResult source stages)

theorem strictGain : StrictEquivalentGain source gain.run.result :=
  gain.run.strictGain gain.smaller

/-- Reuse the existing semantic residual-descent theorem. The reference minimum
is a specification quantity, not an executable search in the gain adapter. -/
theorem strictResidualDescent : residualSlack gain.run.result < residualSlack source :=
  gain.strictGain.strictResidualDescent

end GainResult

/-- No intermediate strict-gain premise is imposed. Any failed stage rejects
the whole program, and a final nondecrease returns no gain. -/
def compileGain (source : Implementation inputs outputs) (stages : List RawStage) :
    Option (GainResult source stages) :=
  match runAt : compile source stages with
  | none => none
  | some run =>
      if smaller : run.result.gateCount < source.gateCount then
        some ⟨run, runAt, smaller⟩
      else none

theorem compileGain_compile_none (source : Implementation inputs outputs)
    (stages : List RawStage) (rejected : compile source stages = none) :
    compileGain source stages = none := by
  unfold compileGain
  split
  · rfl
  · rename_i run accepted
    have impossible := accepted.symm.trans rejected
    cases impossible

theorem compileGain_no_gain (source : Implementation inputs outputs)
    (stages : List RawStage) (run : CompiledRun source stages)
    (accepted : compile source stages = some run)
    (notSmaller : ¬ run.result.gateCount < source.gateCount) :
    compileGain source stages = none := by
  unfold compileGain
  split
  · rfl
  · rename_i actual actualAt
    have same : actual = run := Option.some.inj (actualAt.symm.trans accepted)
    cases same
    rw [dif_neg notSmaller]

/-- A valid offered program with a strict final improvement is accepted,
including those with growing intermediate descendants. -/
theorem compileGain_complete (source : Implementation inputs outputs)
    (stages : List RawStage) (run : CompiledRun source stages)
    (accepted : compile source stages = some run)
    (smaller : run.result.gateCount < source.gateCount) :
    ∃ gain, compileGain source stages = some gain ∧ gain.run = run := by
  unfold compileGain
  split
  · rename_i rejected
    have impossible := rejected.symm.trans accepted
    cases impossible
  · rename_i actual actualAt
    have same : actual = run := Option.some.inj (actualAt.symm.trans accepted)
    cases same
    rw [dif_pos smaller]
    exact ⟨_, rfl, rfl⟩

/-- The final comparison is exact: an accepted stage program yields a gain
if and only if its whole-source result is strictly smaller. -/
theorem compileGain_exists_iff (source : Implementation inputs outputs)
    (stages : List RawStage) (run : CompiledRun source stages)
    (accepted : compile source stages = some run) :
    (∃ gain, compileGain source stages = some gain) ↔
      run.result.gateCount < source.gateCount := by
  constructor
  · rintro ⟨gain, _gainAt⟩
    have same : gain.run = run := Option.some.inj (gain.runAt.symm.trans accepted)
    simpa only [same] using gain.smaller
  · intro smaller
    obtain ⟨gain, gainAt, _same⟩ := compileGain_complete source stages run accepted smaller
    exact ⟨gain, gainAt⟩

end PNP.DirectWire.WireDescendantHistory
