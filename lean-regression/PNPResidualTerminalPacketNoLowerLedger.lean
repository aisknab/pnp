import PNP.ResidualTerminalPacketNoLowerLedger

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PacketNoLowerLedgerRegression

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

def environment
    {familyValue : TerminalBN6GroupedFamily Atom (Payload 1)}
    (hnActive budgetActive : Bool) :
    TerminalPacketTypedRealizerEnvironment
      familyValue.PacketSelectorHandle 1 where
  rankOf := fun _handle => 0
  faithful := fun _handle => false
  hnActive := fun _rank => hnActive
  budgetActive := fun _rank => budgetActive

def table
    {familyValue : TerminalBN6GroupedFamily Atom (Payload 1)}
    (hnActive budgetActive : Bool) :
    TerminalPacketTypedRealizerTable redundantIdentityImplementation
      familyValue 1 where
  environment := environment hnActive budgetActive
  claim := fun _handle => .bot (.hn 0)

def dependencyTable : TerminalPacketHBDependencyTable 1 where
  rankTuple := fun _rank => residual
  dependencies := fun _node => []

def beforeRank
    {familyValue : TerminalBN6GroupedFamily Atom (Payload 1)} :
    familyValue.PacketSelectorHandle → TerminalResidualRank :=
  fun _handle => residual

def afterRank
    {familyValue : TerminalBN6GroupedFamily Atom (Payload 1)} :
    familyValue.PacketSelectorHandle → TerminalResidualRank :=
  fun _handle => residual

/-! An empty arbitrary finite family has no Packet handle, so every exact
    ledger scan accepts and the positive-Packet conclusion is excluded. -/
example : (@table emptyFamily false false).checkPacketNoLowerLedger
    dependencyTable beforeRank afterRank = true := by
  decide

example : (@table emptyFamily false false).PacketNoLowerLedgerAccepted
    dependencyTable beforeRank afterRank :=
  ((@table emptyFamily false false).checkPacketNoLowerLedger_eq_true_iff
    dependencyTable beforeRank afterRank).1 (by decide)

example : ¬TerminalBN6PacketConclusion emptyFamily :=
  terminalBN6_packet_no_lower_ledger_excludes_positive_packet
    (@table emptyFamily false false) dependencyTable beforeRank afterRank
      (by decide)

/-! A positive pair with agreeing typed fields and equal residual ranks exposes
    `.descent`; the composite ledger therefore rejects. -/
example : (@table (family agreeingPayload) false false).checkPacketNoLowerLedger
    dependencyTable beforeRank afterRank = false := by
  decide

/-! Making a semantic mismatch active can satisfy its local binding, but the
    independent no-outcome HB closure rejects the active node. -/
example : (@table (family frontierMismatchPayload) true false
    ).checkPacketNoLowerLedger dependencyTable beforeRank afterRank = false := by
  decide

/-! The exported interfaces remain arbitrary in family size and rank count. -/

variable {Anchor : Type} [DecidableEq Anchor]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {genericFamily : TerminalBN6GroupedFamily Anchor
  (TerminalPacketSelectorBN5BudgetPayload rankCount
    Nat Nat Nat Nat Nat Nat Nat Nat Nat Nat)}

example
    (genericTable : TerminalPacketTypedRealizerTable current genericFamily rankCount)
    (genericDependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : genericFamily.PacketSelectorHandle → TerminalResidualRank) :
    genericTable.checkPacketNoLowerLedger genericDependencyTable before after = true ↔
      genericTable.PacketNoLowerLedgerAccepted genericDependencyTable before after :=
  genericTable.checkPacketNoLowerLedger_eq_true_iff genericDependencyTable
    before after

example
    (conclusion : TerminalBN6PacketConclusion genericFamily)
    (genericTable : TerminalPacketTypedRealizerTable current genericFamily rankCount)
    (genericDependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : genericFamily.PacketSelectorHandle → TerminalResidualRank) :
    genericTable.checkPacketNoLowerLedger genericDependencyTable before after = false :=
  conclusion.checkPacketNoLowerLedger_eq_false genericTable
    genericDependencyTable before after

example
    (genericTable : TerminalPacketTypedRealizerTable current genericFamily rankCount)
    (genericDependencyTable : TerminalPacketHBDependencyTable rankCount)
    (before after : genericFamily.PacketSelectorHandle → TerminalResidualRank)
    (ledgerAccepted : genericTable.checkPacketNoLowerLedger
      genericDependencyTable before after = true) :
    ¬TerminalBN6PacketConclusion genericFamily :=
  terminalBN6_packet_no_lower_ledger_excludes_positive_packet genericTable
    genericDependencyTable before after ledgerAccepted

end PacketNoLowerLedgerRegression
end DirectWire
end PNP
