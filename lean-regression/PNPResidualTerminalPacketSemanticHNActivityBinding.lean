import PNP.ResidualTerminalPacketSemanticHNActivityBinding

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PacketSemanticHNActivityBindingRegression

abbrev Coordinate := TerminalPacketSelectorBN5Coordinate
  Nat Nat Nat Nat Nat Nat Nat Nat

abbrev Payload (rankCount : Nat) :=
  TerminalPacketSelectorBN5BudgetPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat Nat Nat

def coordinate (atom frontier obligation : Nat) : Coordinate :=
  { key :=
      { atom := atom
        semanticSignature := 2
        transportType := 3 }
    frontier := frontier
    chargeOwner := 5
    obligation := obligation
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

def payload
    (sourceAtom selectorAtom sourceFrontier selectorFrontier
      sourceObligation selectorObligation sourceDirection selectorDirection
      sourceBudget selectorBudget : Nat) : Payload 1 :=
  { checks :=
      { checks :=
          { checks := baseChecks
            sourceCoordinate :=
              coordinate sourceAtom sourceFrontier sourceObligation
            selectorCoordinate :=
              coordinate selectorAtom selectorFrontier selectorObligation }
        sourceDirection := sourceDirection
        selectorDirection := selectorDirection }
    sourceBudget := sourceBudget
    selectorBudget := selectorBudget }

def agreeingPayload : Payload 1 :=
  payload 1 1 4 4 6 6 9 9 10 10

def frontierMismatchPayload : Payload 1 :=
  payload 1 1 4 14 6 6 9 9 10 10

def obligationMismatchPayload : Payload 1 :=
  payload 1 1 4 4 6 16 9 9 10 10

def activationMismatchPayload : Payload 1 :=
  payload 1 11 4 4 6 6 9 9 10 10

def directionMismatchPayload : Payload 1 :=
  payload 1 1 4 4 6 6 9 19 10 10

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

def environment
    {value : Payload 1}
    (hnActive budgetActive : Bool) :
    TerminalPacketTypedRealizerEnvironment
      (family value).PacketSelectorHandle 1 where
  rankOf := fun _handle => 0
  faithful := fun _handle => false
  hnActive := fun _rank => hnActive
  budgetActive := fun _rank => budgetActive

def table
    {value : Payload 1}
    (hnActive budgetActive : Bool) :
    TerminalPacketTypedRealizerTable redundantIdentityImplementation
      (family value) 1 where
  environment := environment hnActive budgetActive
  claim := fun _handle => .bot (.hn 0)

def dependencyTable : TerminalPacketHBDependencyTable 1 where
  rankTuple := fun _rank => TerminalResidualRank.mk 0 0 0 0 0 0 0 0 0 0
  dependencies := fun _node => []

example :
    (@table agreeingPayload false false
      ).checkPacketSemanticHNActivityBinding = true := by
  decide

example :
    (@table frontierMismatchPayload true false
      ).checkPacketSemanticHNActivityBinding = true := by
  decide

example :
    (@table obligationMismatchPayload true false
      ).checkPacketSemanticHNActivityBinding = true := by
  decide

example :
    (@table activationMismatchPayload true false
      ).checkPacketSemanticHNActivityBinding = true := by
  decide

example :
    (@table directionMismatchPayload true false
      ).checkPacketSemanticHNActivityBinding = true := by
  decide

/-! Every individual semantic mismatch fails closed when its authoritative HN
    node is inactive. -/
example :
    (@table frontierMismatchPayload false false
      ).checkPacketSemanticHNActivityBinding = false := by
  decide

example :
    (@table obligationMismatchPayload false false
      ).checkPacketSemanticHNActivityBinding = false := by
  decide

example :
    (@table activationMismatchPayload false false
      ).checkPacketSemanticHNActivityBinding = false := by
  decide

example :
    (@table directionMismatchPayload false false
      ).checkPacketSemanticHNActivityBinding = false := by
  decide

example : dependencyTable.checkNoOutcomeActiveClosure
    (@table agreeingPayload false false).environment = true := by
  decide

/-! An active mismatch can pass the local binding, but it cannot also pass the
    independently ranked no-outcome closure. -/
example : dependencyTable.checkNoOutcomeActiveClosure
    (@table directionMismatchPayload true false).environment = false := by
  decide

example :
    (@table agreeingPayload false false).PacketSemanticHNActivityBound :=
  ((@table agreeingPayload false false
    ).checkPacketSemanticHNActivityBinding_eq_true_iff).1 (by decide)

example (handle : (family agreeingPayload).PacketSelectorHandle) :
    (@table agreeingPayload false false).PacketSemanticFieldsAgree handle :=
  (@table agreeingPayload false false
    ).packetSemanticFieldsAgree_of_checkedHNActivityBinding
      dependencyTable (by decide) (by decide) handle

/-! The exported interfaces remain arbitrary in family size and rank count. -/

variable {Anchor : Type} [DecidableEq Anchor]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {genericFamily : TerminalBN6GroupedFamily Anchor (Payload rankCount)}

example
    (genericTable : TerminalPacketTypedRealizerTable current genericFamily rankCount) :
    genericTable.checkPacketSemanticHNActivityBinding = true ↔
      genericTable.PacketSemanticHNActivityBound :=
  genericTable.checkPacketSemanticHNActivityBinding_eq_true_iff

example
    (genericTable : TerminalPacketTypedRealizerTable current genericFamily rankCount)
    (genericDependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : genericFamily.PacketSelectorHandle → TerminalResidualRank)
    (bindingAccepted :
      genericTable.checkPacketSemanticHNActivityBinding = true)
    (closureAccepted : genericDependencyTable.checkNoOutcomeActiveClosure
      genericTable.environment = true)
    (handle : genericFamily.PacketSelectorHandle) :
    genericFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        genericTable.environment.rankOf before after handle ≠ some .frontier ∧
      genericFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        genericTable.environment.rankOf before after handle ≠ some .obligation ∧
      genericFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        genericTable.environment.rankOf before after handle ≠ some .activation ∧
      genericFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        genericTable.environment.rankOf before after handle ≠ some .direction :=
  genericTable.packetSelectorSemanticFirstRoutes_ne_of_checkedHNActivityBinding
    genericDependencyTable before after bindingAccepted closureAccepted handle

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
    ∃ handle : genericFamily.PacketSelectorHandle,
      genericFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
          genericTable.environment.rankOf before after handle = some .descent ∧
        genericFamily.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
          genericTable.environment.rankOf before after handle .descent ∧
        ¬(after handle).LexLT (before handle) :=
  terminalBN6_packet_semantic_hn_activity_bound_descent_failure conclusion
    genericTable genericDependencyTable before after semanticBindingAccepted
      budgetBindingAccepted silenceAccepted closureAccepted

end PacketSemanticHNActivityBindingRegression
end DirectWire
end PNP
