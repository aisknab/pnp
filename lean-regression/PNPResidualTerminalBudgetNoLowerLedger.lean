import PNP.ResidualTerminalBudgetNoLowerLedger

namespace PNP
namespace DirectWire
namespace BudgetNoLowerLedgerRegression

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

/-- The first gate is redundant, so the full support has a strict gain while
    every feasible one-gate support is minimum. -/
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

example : terminalBudgetNoLowerClassify
    oneGateBudget fixtureCandidate fixtureModel fixtureExactSeed = .exact := by
  decide

example : terminalBudgetNoLowerClassify
    fullBudget fixtureCandidate fixtureModel fixtureFullSeed = .gain := by
  decide

example : terminalBudgetNoLowerClassify
    zeroGateBudget fixtureCandidate fixtureModel fixtureExactSeed =
      .noBudget := by
  decide

example :
    (fixtureExactSeed,
      terminalBudgetNoLowerClassify
        oneGateBudget fixtureCandidate fixtureModel fixtureExactSeed) ∈
      terminalBudgetNoLowerRouteLedger
        oneGateBudget fixtureCandidate fixtureModel :=
  terminalBudgetNoLowerRouteLedger_complete
    oneGateBudget fixtureCandidate fixtureModel
      (canonicalTerminalSupportSeed_mem 1 2 1 0 fun record =>
        decide (record = .gate fixtureSecondGate ∨
          record = .interface fixtureOutput))

example : (terminalBudgetNoLowerRouteLedger
    oneGateBudget fixtureCandidate fixtureModel).length =
      (allTerminalSupportSeeds 1 2 1 0).length := by
  simp [terminalBudgetNoLowerRouteLedger]

example : checkTerminalBudgetNoLowerLedger
    zeroGateBudget fixtureCandidate fixtureModel = true := by
  decide

example : checkTerminalBudgetNoLowerLedger
    oneGateBudget fixtureCandidate fixtureModel = true := by
  decide

example : checkTerminalBudgetNoLowerLedger
    fullBudget fixtureCandidate fixtureModel = false := by
  decide

example :
    (∀ seed,
      seed ∈ allTerminalSupportSeeds 1 2 1 0 →
      oneGateBudget.Fits fixtureCandidate fixtureModel seed →
      IsSemanticallyMinimum
        (terminalHResolveSupportImplementation
          fixtureCandidate fixtureModel seed)) ∧
    ¬∃ seed,
      seed ∈ allTerminalSupportSeeds 1 2 1 0 ∧
      oneGateBudget.Fits fixtureCandidate fixtureModel seed ∧
      ∃ next, StrictEquivalentGain
        (terminalHResolveSupportImplementation
          fixtureCandidate fixtureModel seed) next :=
  terminal_budget_no_lower_ledger_excludes_feasible_gain
    oneGateBudget fixtureCandidate fixtureModel (by decide)

end BudgetNoLowerLedgerRegression
end DirectWire
end PNP
