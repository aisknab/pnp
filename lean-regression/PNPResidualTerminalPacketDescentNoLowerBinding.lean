import PNP.ResidualTerminalPacketDescentNoLowerBinding

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PacketDescentNoLowerBindingRegression

abbrev Coordinate := TerminalPacketSelectorBN5Coordinate
  Nat Nat Nat Nat Nat Nat Nat Nat

abbrev Payload (rankCount : Nat) :=
  TerminalPacketSelectorBN5BudgetPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat Nat Nat

def coordinate (frontier : Nat) : Coordinate :=
  { key :=
      { atom := 1
        semanticSignature := 2
        transportType := 3 }
    frontier := frontier
    chargeOwner := 5
    obligation := 6
    originKernel := 7
    modeProjection := 8 }

def baseChecks : TerminalPacketSelectorFaithfulnessPayload 1 :=
  { colourChecked := false
    frontierChecked := false
    chargeChecked := false
    obligationChecked := false
    activationChecked := false
    directionChecked := false
    budgetChecked := false
    rankTag := 0
    exactRouteClear := false
    strictDescentClear := false }

def payload (sourceFrontier selectorFrontier : Nat) : Payload 1 :=
  { checks :=
      { checks :=
          { checks := baseChecks
            sourceCoordinate := coordinate sourceFrontier
            selectorCoordinate := coordinate selectorFrontier }
        sourceDirection := 9
        selectorDirection := 9 }
    sourceBudget := 10
    selectorBudget := 10 }

def agreeingPayload : Payload 1 := payload 4 4

def frontierMismatchPayload : Payload 1 := payload 4 14

abbrev Atom := Fin 2

def consumerSystem : TerminalV54ConsumerSystem Atom where
  carrier := [0, 1]
  carrierNodup := by decide
  consumers := [[0], [1]]
  consumersNodup := by decide
  consumerNodup := by simp
  consumerNonempty := by simp
  consumerContained := by simp [TerminalV54Included]
  consumerAntichain := by simp [TerminalV54Included]

theorem consumerSystem_singletonized :
    consumerSystem.DisjointPairsSingletonized := by
  apply terminalBN6_disjointPairsSingletonized_of_all_singletons
  intro consumer consumerMember
  simp [consumerSystem] at consumerMember
  rcases consumerMember with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

def group (value : Payload 1) : TerminalBN6GroupedCell Atom (Payload 1) where
  consumerSystem := consumerSystem
  singletonized := consumerSystem_singletonized
  atoms := [{ mass := 1, massPositive := by decide, payload := value }]
  atomsNonempty := by simp

def family (value : Payload 1) : TerminalBN6GroupedFamily Atom (Payload 1) where
  carrier := [0, 1]
  carrierNodup := by decide
  groups := [group value]
  groupCarrier := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    rfl
  groupFootprintLarge := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp [group, consumerSystem, TerminalBN6GroupedCell.footprint,
      TerminalV54ConsumerSystem.singletonFootprint]
  groupFootprintsNodup := by
    simp [group, consumerSystem, TerminalBN6GroupedCell.footprint,
      TerminalV54ConsumerSystem.singletonFootprint]
  cutValue := 1
  cutValuePositive := by decide

def residual : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 0 0 0 0 0

def rankOf {value : Payload 1} : (family value).PacketSelectorHandle → Fin 1 :=
  fun _handle => 0

def beforeRank {value : Payload 1} :
    (family value).PacketSelectorHandle → TerminalResidualRank :=
  fun _handle => residual

def afterRank {value : Payload 1} :
    (family value).PacketSelectorHandle → TerminalResidualRank :=
  fun _handle => residual

/-! A prior frontier failure satisfies the local no-lower row. -/
example : (family frontierMismatchPayload).checkPacketDescentNoLower
    rankOf beforeRank afterRank = true := by
  decide

example : (family frontierMismatchPayload).PacketDescentNoLower
    rankOf beforeRank afterRank :=
  ((family frontierMismatchPayload).checkPacketDescentNoLower_eq_true_iff
    rankOf beforeRank afterRank).1 (by decide)

/-! Fully agreeing fields and equal residual ranks expose `.descent`, so the
    checker rejects. -/
example : (family agreeingPayload).checkPacketDescentNoLower
    rankOf beforeRank afterRank = false := by
  decide

/-! The exported interfaces remain arbitrary in family size and rank count. -/

variable {Anchor : Type} [DecidableEq Anchor]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {genericFamily : TerminalBN6GroupedFamily Anchor (Payload rankCount)}

example
    (genericRankOf : genericFamily.PacketSelectorHandle → Fin rankCount)
    (before after : genericFamily.PacketSelectorHandle → TerminalResidualRank) :
    genericFamily.checkPacketDescentNoLower genericRankOf before after = true ↔
      genericFamily.PacketDescentNoLower
        genericRankOf before after :=
  genericFamily.checkPacketDescentNoLower_eq_true_iff
    genericRankOf before after

example
    (conclusion : TerminalBN6PacketConclusion genericFamily)
    (genericTable : TerminalPacketTypedRealizerTable current genericFamily rankCount)
    (genericDependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : genericFamily.PacketSelectorHandle → TerminalResidualRank)
    (semanticBindingAccepted :
      (genericTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        before after).checkPacketSemanticHNActivityBinding = true)
    (budgetBindingAccepted :
      (genericTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        before after).checkPacketBudgetHBActivityBinding = true)
    (silenceAccepted :
      (genericTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        before after).checkSelectorSilent = true)
    (closureAccepted : genericDependencyTable.checkNoOutcomeActiveClosure
      (genericTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        before after).environment = true) :
    genericFamily.checkPacketDescentNoLower genericTable.environment.rankOf
      before after = false :=
  terminalBN6_packet_descent_no_lower_rejected conclusion genericTable
    genericDependencyTable before after semanticBindingAccepted
      budgetBindingAccepted silenceAccepted closureAccepted

example
    (conclusion : TerminalBN6PacketConclusion genericFamily)
    (genericTable : TerminalPacketTypedRealizerTable current genericFamily rankCount)
    (genericDependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : genericFamily.PacketSelectorHandle → TerminalResidualRank)
    (semanticBindingAccepted :
      (genericTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        before after).checkPacketSemanticHNActivityBinding = true)
    (budgetBindingAccepted :
      (genericTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        before after).checkPacketBudgetHBActivityBinding = true)
    (silenceAccepted :
      (genericTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        before after).checkSelectorSilent = true)
    (closureAccepted : genericDependencyTable.checkNoOutcomeActiveClosure
      (genericTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        before after).environment = true)
    (noLowerAccepted : genericFamily.checkPacketDescentNoLower
      genericTable.environment.rankOf before after = true) : False :=
  conclusion.false_of_checkedPacketDescentNoLower_and_selectorSilence
    genericTable genericDependencyTable before after semanticBindingAccepted
      budgetBindingAccepted silenceAccepted closureAccepted noLowerAccepted

end PacketDescentNoLowerBindingRegression
end DirectWire
end PNP
