import PNP.ResidualTerminalBudgetZeroSlackSidecar

namespace PNP
namespace BudgetZeroSlackSidecarRegression

open DirectWire

abbrev FixtureRecord := TerminalPrimitiveRecord 1 2 1 0

def fixtureInput : Fin 1 := ⟨0, by decide⟩
def fixtureFirstGate : Fin 2 := ⟨0, by decide⟩
def fixtureSecondGate : Fin 2 := ⟨1, by decide⟩
def fixtureOutput : Fin 1 := ⟨0, by decide⟩

def fixtureProgram : Program 1 2 :=
  .snoc
    (.snoc .empty
      { left := .input fixtureInput
        right := .input fixtureInput })
    { left := .input fixtureInput
      right := .input fixtureInput }

def fixtureWord : DirectWireWord 1 2 1 :=
  ⟨fun _output => .gate fixtureSecondGate⟩

/-- The first gate is deliberately redundant; the one-gate support for the
    second gate already computes the complete output. -/
def fixtureCandidate : Candidate 1 2 1 :=
  Candidate.ofDirectWireWord fixtureProgram fixtureWord

def fixtureProfileSystem : TerminalProfileSystem 1 1 0 :=
  { role := fun coordinate => Fin.elim0 coordinate
    observe := fun _implementation coordinate => Fin.elim0 coordinate }

def fixtureProjection : TerminalProfileProjection 0 :=
  { keep := fun coordinate => Fin.elim0 coordinate }

def fixtureModel :
    TerminalCandidateSaturationModel (profileWidth := 0) fixtureCandidate :=
  { profileSystem := fixtureProfileSystem
    projection := fixtureProjection
    observe := fun _implementation coordinate => Fin.elim0 coordinate }

def fixtureExactSeed : List FixtureRecord :=
  canonicalTerminalSupportSeed 1 2 1 0 fun record =>
    decide (record = .gate fixtureSecondGate ∨
      record = .interface fixtureOutput)

def fixtureFullSeed : List FixtureRecord :=
  canonicalTerminalSupportSeed 1 2 1 0 fun _record => true

def zeroGateBudget : TerminalSupportBudget :=
  { maxGateCount := 0
    maxSaturatedRecordCount := 4 }

theorem zeroGateBudget_search_none :
    findTerminalBudgetFeasibleSupport
      zeroGateBudget fixtureCandidate fixtureModel = none := by
  apply (findTerminalBudgetFeasibleSupport_eq_none_iff
    zeroGateBudget fixtureCandidate fixtureModel).2
  intro seed _governed fits
  unfold TerminalSupportBudget.Fits at fits
  exact Nat.not_lt_zero _ (Nat.lt_of_lt_of_le fits.1 fits.2.2.1)

def checkedSidecar : BudgetSidecarCertificate :=
  { inputs := 1
    gates := 2
    outputs := 1
    profileWidth := 0
    budget := zeroGateBudget
    candidate := fixtureCandidate
    model := fixtureModel
    noBudgetSidecar := zeroGateBudget_search_none }

example : fixtureExactSeed ∈ allTerminalSupportSeeds 1 2 1 0 :=
  canonicalTerminalSupportSeed_mem 1 2 1 0 fun record =>
    decide (record = .gate fixtureSecondGate ∨
      record = .interface fixtureOutput)

example : fixtureFullSeed ∈ allTerminalSupportSeeds 1 2 1 0 :=
  canonicalTerminalSupportSeed_mem 1 2 1 0 fun _record => true

example : ∀ seed,
    seed ∈ allTerminalSupportSeeds 1 2 1 0 →
    ¬zeroGateBudget.Fits fixtureCandidate fixtureModel seed :=
  checkedSidecar.excluded

example : ¬∃ seed,
    seed ∈ allTerminalSupportSeeds 1 2 1 0 ∧
    zeroGateBudget.Fits fixtureCandidate fixtureModel seed :=
  checkedSidecar.no_feasible_support

example : IsSemanticallyMinimum
    (terminalHResolveSupportImplementation
      fixtureCandidate fixtureModel fixtureExactSeed) :=
  checkedSidecar.exact_route_sound fixtureExactSeed (by decide)

example : ∃ next, StrictEquivalentGain
    (terminalHResolveSupportImplementation
      fixtureCandidate fixtureModel fixtureFullSeed) next :=
  checkedSidecar.gain_route_sound fixtureFullSeed (by decide)

example :
    (∀ seed,
      seed ∈ allTerminalSupportSeeds 1 2 1 0 →
      ¬zeroGateBudget.Fits fixtureCandidate fixtureModel seed) ∧
    (¬∃ seed,
      seed ∈ allTerminalSupportSeeds 1 2 1 0 ∧
      zeroGateBudget.Fits fixtureCandidate fixtureModel seed) ∧
    (∀ seed : List FixtureRecord,
      TerminalHResolveSupportExact fixtureCandidate fixtureModel seed →
        IsSemanticallyMinimum
          (terminalHResolveSupportImplementation
            fixtureCandidate fixtureModel seed)) ∧
    (∀ seed : List FixtureRecord,
      TerminalHResolveSupportGain fixtureCandidate fixtureModel seed →
        ∃ next, StrictEquivalentGain
          (terminalHResolveSupportImplementation
            fixtureCandidate fixtureModel seed) next) :=
  budget_zeroslack_sidecar_checked_complete checkedSidecar

end BudgetZeroSlackSidecarRegression
end PNP
