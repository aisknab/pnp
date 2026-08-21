import PNP.ResidualTerminalPacketBudgetNoLowerComposition

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PacketBudgetNoLowerCompositionRegression

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

/-- The first gate is redundant. -/
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

def fixtureFullSeed : List FixtureRecord :=
  canonicalTerminalSupportSeed 1 2 1 0 fun _record => true

def oneGateBudget : TerminalSupportBudget :=
  { maxGateCount := 1
    maxSaturatedRecordCount := 4 }

def fullBudget : TerminalSupportBudget :=
  { maxGateCount := 2
    maxSaturatedRecordCount := 4 }

abbrev Payload (rankCount : Nat) :=
  TerminalPacketSelectorBN5BudgetPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat Nat Nat

abbrev Atom := Fin 2

def emptyFamily : TerminalBN6GroupedFamily Atom (Payload 1) where
  carrier := []
  carrierNodup := by simp
  groups := []
  groupCarrier := by simp
  groupFootprintLarge := by simp
  groupFootprintsNodup := by simp
  cutValue := 1
  cutValuePositive := by decide

def residual : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 0 0 0 0 0

def environment :
    TerminalPacketTypedRealizerEnvironment
      emptyFamily.PacketSelectorHandle 1 where
  rankOf := fun _handle => 0
  faithful := fun _handle => false
  hnActive := fun _rank => false
  budgetActive := fun _rank => false

def table : TerminalPacketTypedRealizerTable
    fixtureCandidate.toImplementation emptyFamily 1 where
  environment := environment
  claim := fun _handle => .bot (.hn 0)

def dependencyTable : TerminalPacketHBDependencyTable 1 where
  rankTuple := fun _rank => residual
  dependencies := fun _node => []

def beforeRank : emptyFamily.PacketSelectorHandle → TerminalResidualRank :=
  fun _handle => residual

def afterRank : emptyFamily.PacketSelectorHandle → TerminalResidualRank :=
  fun _handle => residual

/-! Both finite ledgers accept when the budget excludes the redundant full
    support and the Packet family is empty. -/
example : checkTerminalPacketBudgetNoLowerComposition oneGateBudget
    fixtureCandidate fixtureModel table dependencyTable beforeRank afterRank =
      true := by
  decide

example : TerminalPacketBudgetNoLowerAccepted oneGateBudget fixtureCandidate
    fixtureModel table dependencyTable beforeRank afterRank :=
  (checkTerminalPacketBudgetNoLowerComposition_eq_true_iff oneGateBudget
    fixtureCandidate fixtureModel table dependencyTable beforeRank afterRank).1
      (by decide)

example :
    (∀ seed,
      seed ∈ allTerminalSupportSeeds 1 2 1 0 →
      oneGateBudget.Fits fixtureCandidate fixtureModel seed →
      IsSemanticallyMinimum
        (terminalHResolveSupportImplementation
          fixtureCandidate fixtureModel seed)) ∧
    (¬∃ seed,
      seed ∈ allTerminalSupportSeeds 1 2 1 0 ∧
      oneGateBudget.Fits fixtureCandidate fixtureModel seed ∧
      ∃ next, StrictEquivalentGain
        (terminalHResolveSupportImplementation
          fixtureCandidate fixtureModel seed) next) ∧
    ¬TerminalBN6PacketConclusion emptyFamily :=
  terminal_packet_budget_no_lower_composition_excludes_gain_and_packet
    oneGateBudget fixtureCandidate fixtureModel table dependencyTable
      beforeRank afterRank (by decide)

/-! The full support is feasible under this cap and has a strict gain, so the
    composition rejects even though the empty Packet branch accepts. -/
example : checkTerminalPacketBudgetNoLowerComposition fullBudget
    fixtureCandidate fixtureModel table dependencyTable beforeRank afterRank =
      false := by
  decide

example {seed : List FixtureRecord}
    (governed : seed ∈ allTerminalSupportSeeds 1 2 1 0)
    (fits : fullBudget.Fits fixtureCandidate fixtureModel seed)
    (gain : ∃ next, StrictEquivalentGain
      (terminalHResolveSupportImplementation
        fixtureCandidate fixtureModel seed) next) :
    checkTerminalPacketBudgetNoLowerComposition fullBudget fixtureCandidate
      fixtureModel table dependencyTable beforeRank afterRank = false :=
  checkTerminalPacketBudgetNoLowerComposition_eq_false_of_feasible_gain
    fullBudget fixtureCandidate fixtureModel table dependencyTable beforeRank
      afterRank governed fits gain

/-! The positive-Packet rejection interface remains polymorphic in every
    supplied Packet carrier and table coordinate. -/

variable {Anchor ActivationAtom SemanticSignature TransportType Frontier
  ChargeOwner Obligation OriginKernel ModeProjection Direction
  PacketBudget : Type}
variable [DecidableEq Anchor] [DecidableEq ActivationAtom]
  [DecidableEq Frontier] [DecidableEq Obligation] [DecidableEq Direction]
  [DecidableEq PacketBudget]
variable {inputs gates outputs profileWidth rankCount : Nat}
variable {candidate : Candidate inputs gates outputs}
variable {model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate}
variable {genericFamily : TerminalBN6GroupedFamily Anchor
  (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
    SemanticSignature TransportType Frontier ChargeOwner Obligation
    OriginKernel ModeProjection Direction PacketBudget)}

example
    (budget : TerminalSupportBudget)
    (conclusion : TerminalBN6PacketConclusion genericFamily)
    (genericTable : TerminalPacketTypedRealizerTable
      candidate.toImplementation genericFamily rankCount)
    (genericDependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : genericFamily.PacketSelectorHandle → TerminalResidualRank) :
    checkTerminalPacketBudgetNoLowerComposition budget candidate model
      genericTable genericDependencyTable before after = false :=
  conclusion.checkTerminalPacketBudgetNoLowerComposition_eq_false budget
    candidate model genericTable genericDependencyTable before after

end PacketBudgetNoLowerCompositionRegression
end DirectWire
end PNP
