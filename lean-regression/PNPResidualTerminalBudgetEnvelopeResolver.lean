import PNP.ResidualTerminalBudgetEnvelopeResolver

namespace PNP
namespace DirectWire
namespace BudgetEnvelopeResolverRegression

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

def oneGateBudget : TerminalSupportBudget :=
  { maxGateCount := 1
    maxSaturatedRecordCount := 4 }

def fullBudget : TerminalSupportBudget :=
  { maxGateCount := 2
    maxSaturatedRecordCount := 4 }

example : fixtureExactSeed ∈ allTerminalSupportSeeds 1 2 1 0 :=
  canonicalTerminalSupportSeed_mem 1 2 1 0 fun record =>
    decide (record = .gate fixtureSecondGate ∨
      record = .interface fixtureOutput)

example : fixtureFullSeed ∈ allTerminalSupportSeeds 1 2 1 0 :=
  canonicalTerminalSupportSeed_mem 1 2 1 0 fun _record => true

example : oneGateBudget.check
    fixtureCandidate fixtureModel fixtureExactSeed = true := by decide

example : oneGateBudget.Fits
    fixtureCandidate fixtureModel fixtureExactSeed :=
  (oneGateBudget.check_eq_true_iff
    fixtureCandidate fixtureModel fixtureExactSeed).1 (by decide)

example : TerminalHResolveSupportExact
    fixtureCandidate fixtureModel fixtureExactSeed := by decide

example : IsSemanticallyMinimum
    (terminalHResolveSupportImplementation
      fixtureCandidate fixtureModel fixtureExactSeed) :=
  (terminalHResolveSupportExact_iff_semanticallyMinimum
    fixtureCandidate fixtureModel fixtureExactSeed).1 (by decide)

example : fullBudget.check
    fixtureCandidate fixtureModel fixtureFullSeed = true := by decide

example : TerminalHResolveSupportGain
    fixtureCandidate fixtureModel fixtureFullSeed := by decide

example : ∃ next, StrictEquivalentGain
    (terminalHResolveSupportImplementation
      fixtureCandidate fixtureModel fixtureFullSeed) next :=
  (terminalHResolveSupportGain_iff_exists_strictEquivalentGain
    fixtureCandidate fixtureModel fixtureFullSeed).1 (by decide)

theorem zeroGateBudget_search_none :
    findTerminalBudgetFeasibleSupport
      zeroGateBudget fixtureCandidate fixtureModel = none := by
  apply (findTerminalBudgetFeasibleSupport_eq_none_iff
    zeroGateBudget fixtureCandidate fixtureModel).2
  intro seed _governed fits
  unfold TerminalSupportBudget.Fits at fits
  exact Nat.not_lt_zero _ (Nat.lt_of_lt_of_le fits.1 fits.2.2.1)

example : ∀ seed,
    seed ∈ allTerminalSupportSeeds 1 2 1 0 →
    ¬zeroGateBudget.Fits fixtureCandidate fixtureModel seed :=
  (findTerminalBudgetFeasibleSupport_eq_none_iff
    zeroGateBudget fixtureCandidate fixtureModel).1
      zeroGateBudget_search_none

example :
    (∃ seed,
      seed ∈ allTerminalSupportSeeds 1 2 1 0 ∧
      oneGateBudget.Fits fixtureCandidate fixtureModel seed ∧
      IsSemanticallyMinimum
        (terminalHResolveSupportImplementation
          fixtureCandidate fixtureModel seed)) ∨
    (∃ seed,
      seed ∈ allTerminalSupportSeeds 1 2 1 0 ∧
      oneGateBudget.Fits fixtureCandidate fixtureModel seed ∧
      ∃ next, StrictEquivalentGain
        (terminalHResolveSupportImplementation
          fixtureCandidate fixtureModel seed) next) ∨
    (∀ seed,
      seed ∈ allTerminalSupportSeeds 1 2 1 0 →
      ¬oneGateBudget.Fits fixtureCandidate fixtureModel seed) :=
  terminal_budget_envelope_resolver_constructive_complete
    oneGateBudget fixtureCandidate fixtureModel

end BudgetEnvelopeResolverRegression
end DirectWire
end PNP
