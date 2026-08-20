/-
Copyright (c) 2026 PNP Labs.

Executable no-lower coverage for the finite terminal budget envelope.  Every
canonical terminal support seed is classified from the same candidate-derived
saturation model as exact, strict gain, or outside the supplied budget.  The
ledger checker accepts exactly when no governed budget-feasible seed has a
strict equivalent gain.

The budget caps remain supplied, and the complete subset scan, saturation, and
reference minimization may be exponential.  This is not the manuscript's BUD
grammar or polynomial BudgetResolve, does not compose the Packet or remaining
no-lower branches, and does not prove unconditional ZeroSlack, PCCMin, SAT in
P, or P = NP.
-/

import PNP.ResidualTerminalBudgetEnvelopeResolver

namespace PNP
namespace DirectWire

/-! ## Exact per-support routing -/

/-- Closed route vocabulary for every canonical support under one supplied
    terminal budget. -/
inductive TerminalBudgetNoLowerRoute where
  | exact
  | gain
  | noBudget
deriving Repr, DecidableEq

/-- Classify one support using only the recomputed budget predicate and its
    actual residual slack. -/
def terminalBudgetNoLowerClassify
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalBudgetNoLowerRoute :=
  if budget.check candidate model seed = true then
    if residualSlack
        (terminalHResolveSupportImplementation candidate model seed) = 0 then
      .exact
    else
      .gain
  else
    .noBudget

/-- The exact route is precisely a feasible semantic minimum. -/
theorem terminalBudgetNoLowerClassify_eq_exact_iff
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalBudgetNoLowerClassify budget candidate model seed = .exact ↔
      budget.Fits candidate model seed ∧
        IsSemanticallyMinimum
          (terminalHResolveSupportImplementation candidate model seed) := by
  by_cases checked : budget.check candidate model seed = true
  · have fits := (budget.check_eq_true_iff candidate model seed).1 checked
    by_cases zero : residualSlack
        (terminalHResolveSupportImplementation candidate model seed) = 0
    · have minimum : IsSemanticallyMinimum
          (terminalHResolveSupportImplementation candidate model seed) :=
        (terminalHResolveSupportExact_iff_semanticallyMinimum
          candidate model seed).1 zero
      simp [terminalBudgetNoLowerClassify, checked, zero, fits, minimum]
    · have notMinimum : ¬IsSemanticallyMinimum
          (terminalHResolveSupportImplementation candidate model seed) := by
        intro minimum
        exact zero ((terminalHResolveSupportExact_iff_semanticallyMinimum
          candidate model seed).2 minimum)
      simp [terminalBudgetNoLowerClassify, checked, zero, fits, notMinimum]
  · have notFits : ¬budget.Fits candidate model seed := by
      intro fits
      exact checked ((budget.check_eq_true_iff candidate model seed).2 fits)
    simp [terminalBudgetNoLowerClassify, checked, notFits]

/-- The gain route is precisely a feasible strict equivalent gain. -/
theorem terminalBudgetNoLowerClassify_eq_gain_iff
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalBudgetNoLowerClassify budget candidate model seed = .gain ↔
      budget.Fits candidate model seed ∧
        ∃ next, StrictEquivalentGain
          (terminalHResolveSupportImplementation candidate model seed) next := by
  by_cases checked : budget.check candidate model seed = true
  · have fits := (budget.check_eq_true_iff candidate model seed).1 checked
    by_cases zero : residualSlack
        (terminalHResolveSupportImplementation candidate model seed) = 0
    · have notGain : ¬TerminalHResolveSupportGain candidate model seed := by
        unfold TerminalHResolveSupportGain
        rw [zero]
        exact Nat.not_lt_zero 0
      have noWitness : ¬∃ next, StrictEquivalentGain
          (terminalHResolveSupportImplementation candidate model seed) next := by
        intro witness
        exact notGain
          ((terminalHResolveSupportGain_iff_exists_strictEquivalentGain
            candidate model seed).2 witness)
      simp [terminalBudgetNoLowerClassify, checked, zero, fits, noWitness]
    · have gain : TerminalHResolveSupportGain candidate model seed := by
        unfold TerminalHResolveSupportGain
        exact Nat.pos_of_ne_zero zero
      have witness :=
        (terminalHResolveSupportGain_iff_exists_strictEquivalentGain
          candidate model seed).1 gain
      simp [terminalBudgetNoLowerClassify, checked, zero, fits, witness]
  · have notFits : ¬budget.Fits candidate model seed := by
      intro fits
      exact checked ((budget.check_eq_true_iff candidate model seed).2 fits)
    simp [terminalBudgetNoLowerClassify, checked, notFits]

/-- The NoBudget route is precisely failure of the same recomputed envelope
    predicate; no caller supplies a sidecar flag. -/
theorem terminalBudgetNoLowerClassify_eq_noBudget_iff
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalBudgetNoLowerClassify budget candidate model seed = .noBudget ↔
      ¬budget.Fits candidate model seed := by
  by_cases checked : budget.check candidate model seed = true
  · have fits := (budget.check_eq_true_iff candidate model seed).1 checked
    by_cases zero : residualSlack
        (terminalHResolveSupportImplementation candidate model seed) = 0
    · simp [terminalBudgetNoLowerClassify, checked, zero, fits]
    · simp [terminalBudgetNoLowerClassify, checked, zero, fits]
  · have notFits : ¬budget.Fits candidate model seed := by
      intro fits
      exact checked ((budget.check_eq_true_iff candidate model seed).2 fits)
    simp [terminalBudgetNoLowerClassify, checked, notFits]

/-! ## Complete route ledger -/

/-- Materialize one route row for every canonical terminal support seed. -/
def terminalBudgetNoLowerRouteLedger
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    List
      (List (TerminalPrimitiveRecord inputs gates outputs profileWidth) ×
        TerminalBudgetNoLowerRoute) :=
  (allTerminalSupportSeeds inputs gates outputs profileWidth).map fun seed =>
    (seed, terminalBudgetNoLowerClassify budget candidate model seed)

/-- Every governed seed occurs with its computed route. -/
theorem terminalBudgetNoLowerRouteLedger_complete
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    {seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    (governed : seed ∈ allTerminalSupportSeeds
      inputs gates outputs profileWidth) :
    (seed, terminalBudgetNoLowerClassify budget candidate model seed) ∈
      terminalBudgetNoLowerRouteLedger budget candidate model := by
  exact List.mem_map.mpr ⟨seed, governed, rfl⟩

/-- Every materialized row comes from one governed seed and its exact computed
    route. -/
theorem terminalBudgetNoLowerRouteLedger_sound
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    {row : List
        (TerminalPrimitiveRecord inputs gates outputs profileWidth) ×
      TerminalBudgetNoLowerRoute}
    (member : row ∈ terminalBudgetNoLowerRouteLedger
      budget candidate model) :
    ∃ seed,
      seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth ∧
      row = (seed,
        terminalBudgetNoLowerClassify budget candidate model seed) := by
  rcases List.mem_map.mp member with ⟨seed, governed, equal⟩
  exact ⟨seed, governed, equal.symm⟩

/-! ## Executable no-lower acceptance -/

/-- Proposition recognized by the no-lower checker. -/
def TerminalBudgetNoLowerLedgerAccepted
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) : Prop :=
  ∀ seed,
    seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth →
      terminalBudgetNoLowerClassify budget candidate model seed ≠ .gain

/-- Accept exactly when every canonical support row avoids a strict-gain
    route. -/
def checkTerminalBudgetNoLowerLedger
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) : Bool :=
  (allTerminalSupportSeeds inputs gates outputs profileWidth).all fun seed =>
    decide (terminalBudgetNoLowerClassify budget candidate model seed ≠ .gain)

/-- The Boolean checker recognizes exactly complete gain-route exclusion. -/
theorem checkTerminalBudgetNoLowerLedger_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    checkTerminalBudgetNoLowerLedger budget candidate model = true ↔
      TerminalBudgetNoLowerLedgerAccepted budget candidate model := by
  constructor
  · intro accepted seed governed
    have rowChecked := (List.all_eq_true.mp accepted) seed governed
    exact of_decide_eq_true rowChecked
  · intro accepted
    apply List.all_eq_true.mpr
    intro seed governed
    exact decide_eq_true (accepted seed governed)

/-- Ledger acceptance is semantically equivalent to minimum status for every
    budget-feasible governed support. -/
theorem TerminalBudgetNoLowerLedgerAccepted.iff_all_feasible_minimum
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    TerminalBudgetNoLowerLedgerAccepted budget candidate model ↔
      ∀ seed,
        seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth →
        budget.Fits candidate model seed →
        IsSemanticallyMinimum
          (terminalHResolveSupportImplementation candidate model seed) := by
  constructor
  · intro accepted seed governed fits
    cases routeAt : terminalBudgetNoLowerClassify
        budget candidate model seed with
    | exact =>
        exact (terminalBudgetNoLowerClassify_eq_exact_iff
          budget candidate model seed).1 routeAt |>.2
    | gain =>
        exact False.elim (accepted seed governed routeAt)
    | noBudget =>
        exact False.elim
          ((terminalBudgetNoLowerClassify_eq_noBudget_iff
            budget candidate model seed).1 routeAt fits)
  · intro minimum seed governed gainAt
    have semantics := (terminalBudgetNoLowerClassify_eq_gain_iff
      budget candidate model seed).1 gainAt
    have exactRoute : TerminalHResolveSupportExact candidate model seed :=
      (terminalHResolveSupportExact_iff_semanticallyMinimum
        candidate model seed).2 (minimum seed governed semantics.1)
    have gainRoute : TerminalHResolveSupportGain candidate model seed :=
      (terminalHResolveSupportGain_iff_exists_strictEquivalentGain
        candidate model seed).2 semantics.2
    unfold TerminalHResolveSupportExact at exactRoute
    unfold TerminalHResolveSupportGain at gainRoute
    rw [exactRoute] at gainRoute
    exact Nat.not_lt_zero 0 gainRoute

/-- Named M172 endpoint: an accepted exhaustive terminal budget ledger makes
    every feasible governed support a semantic minimum and excludes every
    feasible strict-equivalent-gain witness. -/
theorem terminal_budget_no_lower_ledger_excludes_feasible_gain
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (accepted : checkTerminalBudgetNoLowerLedger
      budget candidate model = true) :
    (∀ seed,
      seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth →
      budget.Fits candidate model seed →
      IsSemanticallyMinimum
        (terminalHResolveSupportImplementation candidate model seed)) ∧
    ¬∃ seed,
      seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth ∧
      budget.Fits candidate model seed ∧
      ∃ next, StrictEquivalentGain
        (terminalHResolveSupportImplementation candidate model seed) next := by
  have ledgerAccepted :=
    (checkTerminalBudgetNoLowerLedger_eq_true_iff
      budget candidate model).1 accepted
  have allMinimum :=
    (TerminalBudgetNoLowerLedgerAccepted.iff_all_feasible_minimum
      budget candidate model).1 ledgerAccepted
  refine ⟨allMinimum, ?_⟩
  rintro ⟨seed, governed, fits, witness⟩
  have exactRoute : TerminalHResolveSupportExact candidate model seed :=
    (terminalHResolveSupportExact_iff_semanticallyMinimum
      candidate model seed).2 (allMinimum seed governed fits)
  have gainRoute : TerminalHResolveSupportGain candidate model seed :=
    (terminalHResolveSupportGain_iff_exists_strictEquivalentGain
      candidate model seed).2 witness
  unfold TerminalHResolveSupportExact at exactRoute
  unfold TerminalHResolveSupportGain at gainRoute
  rw [exactRoute] at gainRoute
  exact Nat.not_lt_zero 0 gainRoute

end DirectWire
end PNP
