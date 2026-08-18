import PNP.ResidualTerminalPacketBudgetHBActivityBinding

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PacketBudgetHBActivityBindingRegression

abbrev Coordinate := TerminalPacketSelectorBN5Coordinate
  Nat Nat Nat Nat Nat Nat Nat Nat

abbrev ActivationPayload (rankCount : Nat) :=
  TerminalPacketSelectorBN5ObligationPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat

abbrev DirectionPayload (rankCount : Nat) :=
  TerminalPacketSelectorBN5DirectionPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat Nat

abbrev Payload (rankCount : Nat) :=
  TerminalPacketSelectorBN5BudgetPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat Nat Nat

def coordinate : Coordinate :=
  { key :=
      { atom := 1
        semanticSignature := 2
        transportType := 3 }
    frontier := 4
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

def payload (sourceBudget selectorBudget : Nat) : Payload 1 :=
  { checks :=
      { checks :=
          { checks := baseChecks
            sourceCoordinate := coordinate
            selectorCoordinate := coordinate }
        sourceDirection := 9
        selectorDirection := 9 }
    sourceBudget := sourceBudget
    selectorBudget := selectorBudget }

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

def equalFamily := family (payload 10 10)
def unequalFamily := family (payload 10 11)

def environment
    {value : Payload 1}
    (budgetActive : Bool) :
    TerminalPacketTypedRealizerEnvironment
      (family value).PacketSelectorHandle 1 where
  rankOf := fun _handle => 0
  faithful := fun _handle => false
  hnActive := fun _rank => false
  budgetActive := fun _rank => budgetActive

def table
    {value : Payload 1}
    (budgetActive : Bool) :
    TerminalPacketTypedRealizerTable redundantIdentityImplementation
      (family value) 1 where
  environment := environment budgetActive
  claim := fun _handle => .bot (.hn 0)

def dependencyTable : TerminalPacketHBDependencyTable 1 where
  rankTuple := fun _rank => TerminalResidualRank.mk 0 0 0 0 0 0 0 0 0 0
  dependencies := fun _node => []

example :
    (@table (payload 10 10) false).checkPacketBudgetHBActivityBinding = true := by
  decide

example :
    (@table (payload 10 11) true).checkPacketBudgetHBActivityBinding = true := by
  decide

/-- One inactive typed mismatch is rejected even though the family has only
    one otherwise canonical handle. -/
example :
    (@table (payload 10 11) false).checkPacketBudgetHBActivityBinding = false := by
  decide

example : dependencyTable.checkNoOutcomeActiveClosure
    (@table (payload 10 10) false).environment = true := by
  decide

/-- An active mismatch can pass the local binding, but it cannot also pass the
    independently ranked no-outcome closure. -/
example : dependencyTable.checkNoOutcomeActiveClosure
    (@table (payload 10 11) true).environment = false := by
  decide

example :
    (@table (payload 10 10) false).PacketBudgetHBActivityBound :=
  ((@table (payload 10 10) false
    ).checkPacketBudgetHBActivityBinding_eq_true_iff).1 (by decide)

example (handle : equalFamily.PacketSelectorHandle) :
    (equalFamily.packetSelectorPayloadAtom handle).payload.sourceBudget =
      (equalFamily.packetSelectorPayloadAtom handle).payload.selectorBudget :=
  (@table (payload 10 10) false).packetBudget_eq_of_checkedHBActivityBinding
    dependencyTable (by decide) (by decide) handle

/-! The exported interfaces remain arbitrary in family size and rank count. -/

variable {Anchor : Type} [DecidableEq Anchor]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {genericFamily : TerminalBN6GroupedFamily Anchor (Payload rankCount)}

example
    (genericTable : TerminalPacketTypedRealizerTable current genericFamily rankCount) :
    genericTable.checkPacketBudgetHBActivityBinding = true ↔
      genericTable.PacketBudgetHBActivityBound :=
  genericTable.checkPacketBudgetHBActivityBinding_eq_true_iff

example
    (genericTable : TerminalPacketTypedRealizerTable current genericFamily rankCount)
    (genericDependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : genericFamily.PacketSelectorHandle → TerminalResidualRank)
    (bindingAccepted : genericTable.checkPacketBudgetHBActivityBinding = true)
    (closureAccepted : genericDependencyTable.checkNoOutcomeActiveClosure
      genericTable.environment = true)
    (handle : genericFamily.PacketSelectorHandle) :
    genericFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        genericTable.environment.rankOf before after handle ≠ some .budget :=
  genericTable.packetSelectorBudgetFirstRoute_ne_of_checkedHBActivityBinding
    genericDependencyTable before after bindingAccepted closureAccepted handle

example
    (conclusion : TerminalBN6PacketConclusion genericFamily)
    (genericTable : TerminalPacketTypedRealizerTable current genericFamily rankCount)
    (genericDependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : genericFamily.PacketSelectorHandle → TerminalResidualRank)
    (bindingAccepted :
      (genericTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        before after).checkPacketBudgetHBActivityBinding = true)
    (silenceAccepted :
      (genericTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        before after).checkSelectorSilent = true)
    (closureAccepted : genericDependencyTable.checkNoOutcomeActiveClosure
      (genericTable.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        before after).environment = true) :
    ∃ handle : genericFamily.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        genericFamily.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
            genericTable.environment.rankOf before after handle = some route ∧
          genericFamily.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
            genericTable.environment.rankOf before after handle route ∧
          route ≠ .colour ∧ route ≠ .charge ∧ route ≠ .rank ∧
          route ≠ .exactRoute ∧ route ≠ .budget ∧
          (route = .frontier ∨ route = .obligation ∨ route = .activation ∨
            route = .direction ∨ route = .descent) ∧
          (route ≠ .descent ∨ ¬(after handle).LexLT (before handle)) :=
  terminalBN6_packet_budget_hb_activity_bound_first_route_failure conclusion
    genericTable genericDependencyTable before after bindingAccepted
      silenceAccepted closureAccepted

end PacketBudgetHBActivityBindingRegression
end DirectWire
end PNP
