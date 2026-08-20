/-
Copyright (c) 2026 PNP Labs.

Finite terminal-derived budget-envelope resolution for the residual support
boundary.  A budget bounds both the selected NAND count and the complete
candidate-derived saturated-record count.  The resolver exhaustively scans the
canonical terminal support universe, rejects supports without a gate or an
interface, and returns the first feasible support with an exact-minimum or
strict-equivalent-gain route.  If no support fits, the returned NoBudget branch excludes every
canonical seed by the same computed envelope predicate.

The budget caps remain supplied, and the subset search, saturation, and
reference minimization may be exponential.  This is not the manuscript's BUD
grammar or budget-envelope dynamic program, does not prove blocker dependency
semantics or polynomial BudgetResolve, and does not complete the no-lower
ledger, unconditional ZeroSlack, PCCMin, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalHResolveSupportResolver

namespace PNP
namespace DirectWire

/-! ## Computed terminal budget envelope -/

/-- Explicit resource caps for one terminal support.  Gate count is measured
    after candidate-derived saturation and extraction; record count is measured
    on the complete executable saturated support. -/
structure TerminalSupportBudget where
  maxGateCount : Nat
  maxSaturatedRecordCount : Nat
deriving Repr, DecidableEq

/-- A seed fits the terminal budget exactly when its saturated extraction has
    a gate and an interface and both computed resource measures respect the
    supplied caps. -/
def TerminalSupportBudget.Fits
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Prop :=
  let implementation :=
    terminalHResolveSupportImplementation candidate model seed
  let saturatedRecords := terminalSaturateRecords
    (terminalCandidateSaturationSystem candidate model) seed
  0 < implementation.gateCount ∧
    0 < (terminalInterfacePorts candidate saturatedRecords).length ∧
    implementation.gateCount ≤ budget.maxGateCount ∧
    saturatedRecords.length ≤ budget.maxSaturatedRecordCount

private def terminalSupportBudgetFitsDecidable
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Decidable (budget.Fits candidate model seed) := by
  unfold TerminalSupportBudget.Fits
  infer_instance

/-- Executable budget-feasibility check.  No caller supplies a feasibility
    flag or a prefiltered family. -/
def TerminalSupportBudget.check
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Bool :=
  @decide (budget.Fits candidate model seed)
    (terminalSupportBudgetFitsDecidable budget candidate model seed)

/-- The executable envelope test recognizes exactly the two computed resource
    caps together with nonempty gate and interface support. -/
theorem TerminalSupportBudget.check_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    budget.check candidate model seed = true ↔
      budget.Fits candidate model seed := by
  unfold TerminalSupportBudget.check
  constructor
  · exact fun checked => @of_decide_eq_true _
      (terminalSupportBudgetFitsDecidable budget candidate model seed) checked
  · exact fun fits => @decide_eq_true _
      (terminalSupportBudgetFitsDecidable budget candidate model seed) fits

/-! ## Exhaustive first-feasible search -/

private structure TerminalBudgetSeedResult
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seeds : List (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))) where
  seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  member : seed ∈ seeds
  fits : budget.Fits candidate model seed

private def firstTerminalBudgetFeasibleSupport
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    (seeds : List (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))) →
      Option (TerminalBudgetSeedResult budget candidate model seeds)
  | [] => none
  | seed :: seeds =>
      if checked : budget.check candidate model seed = true then
        some
          { seed := seed
            member := List.Mem.head seeds
            fits := (budget.check_eq_true_iff candidate model seed).1 checked }
      else
        match firstTerminalBudgetFeasibleSupport budget candidate model seeds with
        | none => none
        | some found =>
            some
              { seed := found.seed
                member := List.Mem.tail seed found.member
                fits := found.fits }

private theorem firstTerminalBudgetFeasibleSupport_exists_of_mem
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    {seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    {seeds : List (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))}
    (member : seed ∈ seeds)
    (fits : budget.Fits candidate model seed) :
    ∃ found, firstTerminalBudgetFeasibleSupport budget candidate model seeds =
      some found := by
  induction seeds generalizing seed with
  | nil => cases member
  | cons head tail ih =>
      cases List.mem_cons.mp member with
      | inl equal =>
          subst seed
          let checked := (budget.check_eq_true_iff
            candidate model head).2 fits
          refine ⟨
            { seed := head
              member := List.Mem.head tail
              fits := fits }, ?_⟩
          unfold firstTerminalBudgetFeasibleSupport
          rw [dif_pos checked]
      | inr tailMember =>
          if headFits : budget.check candidate model head = true then
            let proved := (budget.check_eq_true_iff
              candidate model head).1 headFits
            refine ⟨
              { seed := head
                member := List.Mem.head tail
                fits := proved }, ?_⟩
            unfold firstTerminalBudgetFeasibleSupport
            rw [dif_pos headFits]
          else
            obtain ⟨found, foundAt⟩ := ih tailMember fits
            refine ⟨
              { seed := found.seed
                member := List.Mem.tail head found.member
                fits := found.fits }, ?_⟩
            unfold firstTerminalBudgetFeasibleSupport
            rw [dif_neg headFits, foundAt]

/-- Proof-bearing member of the terminal-derived budget envelope. -/
structure TerminalBudgetFeasibleSupport
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) where
  seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  governed : seed ∈ allTerminalSupportSeeds
    inputs gates outputs profileWidth
  fits : budget.Fits candidate model seed

/-- Exhaustively scan the canonical terminal support universe and return its
    first member inside the computed budget envelope. -/
def findTerminalBudgetFeasibleSupport
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    Option (TerminalBudgetFeasibleSupport budget candidate model) :=
  match firstTerminalBudgetFeasibleSupport budget candidate model
      (allTerminalSupportSeeds inputs gates outputs profileWidth) with
  | none => none
  | some found =>
      some
        { seed := found.seed
          governed := found.member
          fits := found.fits }

/-- Every returned support is a canonical seed and satisfies the exact
    recomputed envelope predicate. -/
theorem findTerminalBudgetFeasibleSupport_sound
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (found : TerminalBudgetFeasibleSupport budget candidate model)
    (_foundAt : findTerminalBudgetFeasibleSupport
      budget candidate model = some found) :
    found.seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth ∧
      budget.Fits candidate model found.seed :=
  ⟨found.governed, found.fits⟩

/-- Any canonical seed inside the budget envelope forces the exhaustive search
    to return a proof-bearing result. -/
theorem findTerminalBudgetFeasibleSupport_exists_of_seed
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    {seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    (governed : seed ∈ allTerminalSupportSeeds
      inputs gates outputs profileWidth)
    (fits : budget.Fits candidate model seed) :
    ∃ found, findTerminalBudgetFeasibleSupport budget candidate model =
      some found := by
  obtain ⟨foundSeed, foundAt⟩ :=
    firstTerminalBudgetFeasibleSupport_exists_of_mem
      budget candidate model governed fits
  unfold findTerminalBudgetFeasibleSupport
  simp only [foundAt]
  exact ⟨_, rfl⟩

/-- Search failure is a strong NoBudget sidecar for this envelope: every
    canonical seed fails the same computed feasibility predicate. -/
theorem findTerminalBudgetFeasibleSupport_eq_none_iff
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    findTerminalBudgetFeasibleSupport budget candidate model = none ↔
      ∀ seed,
        seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth →
        ¬budget.Fits candidate model seed := by
  constructor
  · intro notFound seed governed fits
    obtain ⟨found, foundAt⟩ :=
      findTerminalBudgetFeasibleSupport_exists_of_seed
        budget candidate model governed fits
    rw [notFound] at foundAt
    cases foundAt
  · intro absent
    cases foundAt : findTerminalBudgetFeasibleSupport
        budget candidate model with
    | none => rfl
    | some found =>
        have sound := findTerminalBudgetFeasibleSupport_sound
          budget candidate model found foundAt
        exact False.elim (absent found.seed sound.1 sound.2)

/-- The canonical first-feasible search has at most one proof-bearing result. -/
theorem findTerminalBudgetFeasibleSupport_unique
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    {left right : TerminalBudgetFeasibleSupport budget candidate model}
    (leftAt : findTerminalBudgetFeasibleSupport
      budget candidate model = some left)
    (rightAt : findTerminalBudgetFeasibleSupport
      budget candidate model = some right) :
    left = right :=
  Option.some.inj (leftAt.symm.trans rightAt)

/-! ## Exact, gain, or NoBudget resolution -/

/-- Total result of resolving the finite terminal budget envelope.  Exact and
    gain routes are computed from actual residual slack; NoBudget carries
    complete exclusion over the canonical seed universe. -/
inductive TerminalBudgetEnvelopeOutcome
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) where
  | exact
      (support : TerminalBudgetFeasibleSupport budget candidate model)
      (route : TerminalHResolveSupportExact candidate model support.seed)
  | gain
      (support : TerminalBudgetFeasibleSupport budget candidate model)
      (route : TerminalHResolveSupportGain candidate model support.seed)
  | noBudget
      (excluded : ∀ seed,
        seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth →
        ¬budget.Fits candidate model seed)

/-- Resolve the first feasible terminal support.  Residual slack zero selects
    exact; successor slack selects gain; exhaustive search failure selects the
    strong NoBudget branch. -/
def resolveTerminalBudgetEnvelope
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    TerminalBudgetEnvelopeOutcome budget candidate model := by
  cases foundAt : findTerminalBudgetFeasibleSupport
      budget candidate model with
  | none =>
      exact .noBudget
        ((findTerminalBudgetFeasibleSupport_eq_none_iff
          budget candidate model).1 foundAt)
  | some support =>
      cases slackAt : residualSlack
          (terminalHResolveSupportImplementation
            candidate model support.seed) with
      | zero =>
          exact .exact support slackAt
      | succ slack =>
          exact .gain support (by
            unfold TerminalHResolveSupportGain
            rw [slackAt]
            exact Nat.zero_lt_succ slack)

/-- Kernel proposition exposed by each computed resolver branch. -/
def TerminalBudgetEnvelopeOutcome.Sound
    {inputs gates outputs profileWidth : Nat}
    {budget : TerminalSupportBudget}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (outcome : TerminalBudgetEnvelopeOutcome budget candidate model) : Prop :=
  match outcome with
  | .exact support _route =>
      support.seed ∈ allTerminalSupportSeeds
          inputs gates outputs profileWidth ∧
        budget.Fits candidate model support.seed ∧
        IsSemanticallyMinimum
          (terminalHResolveSupportImplementation
            candidate model support.seed)
  | .gain support _route =>
      support.seed ∈ allTerminalSupportSeeds
          inputs gates outputs profileWidth ∧
        budget.Fits candidate model support.seed ∧
        ∃ next, StrictEquivalentGain
          (terminalHResolveSupportImplementation
            candidate model support.seed) next
  | .noBudget _excluded =>
      ∀ seed,
        seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth →
        ¬budget.Fits candidate model seed

/-- Every computed resolver branch carries its claimed semantic evidence. -/
theorem TerminalBudgetEnvelopeOutcome.sound
    {inputs gates outputs profileWidth : Nat}
    {budget : TerminalSupportBudget}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (outcome : TerminalBudgetEnvelopeOutcome budget candidate model) :
    outcome.Sound := by
  cases outcome with
  | exact support route =>
      exact ⟨support.governed, support.fits,
        (terminalHResolveSupportExact_iff_semanticallyMinimum
          candidate model support.seed).1 route⟩
  | gain support route =>
      exact ⟨support.governed, support.fits,
        (terminalHResolveSupportGain_iff_exists_strictEquivalentGain
          candidate model support.seed).1 route⟩
  | noBudget excluded =>
      exact excluded

/-- Named M171 endpoint: the terminal-derived finite budget envelope returns a
    governed feasible semantic minimum, a governed feasible strict-equivalent
    gain, or complete NoBudget exclusion for every canonical seed. -/
theorem terminal_budget_envelope_resolver_constructive_complete
    {inputs gates outputs profileWidth : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    (∃ seed,
      seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth ∧
      budget.Fits candidate model seed ∧
      IsSemanticallyMinimum
        (terminalHResolveSupportImplementation candidate model seed)) ∨
    (∃ seed,
      seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth ∧
      budget.Fits candidate model seed ∧
      ∃ next, StrictEquivalentGain
        (terminalHResolveSupportImplementation candidate model seed) next) ∨
    (∀ seed,
      seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth →
      ¬budget.Fits candidate model seed) := by
  let outcome := resolveTerminalBudgetEnvelope budget candidate model
  cases outcome with
  | exact support route =>
      exact Or.inl ⟨support.seed, support.governed, support.fits,
        (terminalHResolveSupportExact_iff_semanticallyMinimum
          candidate model support.seed).1 route⟩
  | gain support route =>
      exact Or.inr (Or.inl ⟨support.seed, support.governed, support.fits,
        (terminalHResolveSupportGain_iff_exists_strictEquivalentGain
          candidate model support.seed).1 route⟩)
  | noBudget excluded =>
      exact Or.inr (Or.inr excluded)

end DirectWire
end PNP
