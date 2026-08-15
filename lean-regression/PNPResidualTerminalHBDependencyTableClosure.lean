import PNP.ResidualTerminalHBDependencyTableClosure

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

/-! ## Total descending table and hostile variants -/

def hbTableRankTuple3 (rank : Fin 3) : TerminalResidualRank :=
  TerminalResidualRank.mk rank.val 0 0 0 0 0 0 0 0 0

def hbDescendingDependencies : TerminalPacketHBNode 3 ->
    List (TerminalPacketHBNode 3)
  | .hn rank =>
      if rank = (2 : Fin 3) then [.budget (1 : Fin 3)] else []
  | .budget rank =>
      if rank = (1 : Fin 3) then [.hn (0 : Fin 3)] else []

def hbDescendingTable : TerminalPacketHBDependencyTable 3 where
  rankTuple := hbTableRankTuple3
  dependencies := hbDescendingDependencies

def hbSameRankDependencies : TerminalPacketHBNode 3 ->
    List (TerminalPacketHBNode 3)
  | .hn rank =>
      if rank = (1 : Fin 3) then [.budget (1 : Fin 3)] else []
  | .budget _rank => []

def hbSameRankTable : TerminalPacketHBDependencyTable 3 where
  rankTuple := hbTableRankTuple3
  dependencies := hbSameRankDependencies

def hbUpwardDependencies : TerminalPacketHBNode 3 ->
    List (TerminalPacketHBNode 3)
  | .hn rank =>
      if rank = (1 : Fin 3) then [.budget (2 : Fin 3)] else []
  | .budget _rank => []

def hbUpwardTable : TerminalPacketHBDependencyTable 3 where
  rankTuple := hbTableRankTuple3
  dependencies := hbUpwardDependencies

def hbCyclicDependencies : TerminalPacketHBNode 3 ->
    List (TerminalPacketHBNode 3)
  | .hn rank =>
      if rank = (2 : Fin 3) then [.budget (1 : Fin 3)] else []
  | .budget rank =>
      if rank = (1 : Fin 3) then [.hn (2 : Fin 3)] else []

def hbCyclicTable : TerminalPacketHBDependencyTable 3 where
  rankTuple := hbTableRankTuple3
  dependencies := hbCyclicDependencies

example : (allTerminalPacketHBNodes 3).length = 6 := by
  rfl

example (node : TerminalPacketHBNode 3) :
    node ∈ allTerminalPacketHBNodes 3 :=
  mem_allTerminalPacketHBNodes node

example : hbDescendingTable.check = true := by
  rfl

example : hbSameRankTable.check = false := by
  rfl

example : hbUpwardTable.check = false := by
  rfl

example : hbCyclicTable.check = false := by
  rfl

example : hbDescendingTable.Valid :=
  hbDescendingTable.check_eq_true_iff.mp (by rfl)

example : hbDescendingTable.Depends
    (.budget (1 : Fin 3)) (.hn (2 : Fin 3)) := by
  simp [TerminalPacketHBDependencyTable.Depends,
    hbDescendingTable, hbDescendingDependencies]

example : hbDescendingTable.toGraph.Depends
    (.budget (1 : Fin 3)) (.hn (2 : Fin 3)) := by
  rw [hbDescendingTable.toGraph_depends_iff]
  simp [TerminalPacketHBDependencyTable.Depends,
    hbDescendingTable, hbDescendingDependencies]

example :
    ({ blocked := .hn (2 : Fin 3), dependency := .budget (1 : Fin 3) } :
      TerminalPacketHBDependencyEdge 3) ∈ hbDescendingTable.toGraph.edges := by
  rw [hbDescendingTable.edge_mem_toGraph_iff]
  simp [hbDescendingTable, hbDescendingDependencies]

example : hbDescendingTable.RowCovered (.hn (2 : Fin 3)) :=
  hbDescendingTable.rowCovered _

example : (hbDescendingTable.exactRank (.budget (1 : Fin 3))).LexLT
    (hbDescendingTable.exactRank (.hn (2 : Fin 3))) :=
  hbDescendingTable.depends_rank_lt (by rfl) (by
    simp [TerminalPacketHBDependencyTable.Depends,
      hbDescendingTable, hbDescendingDependencies])

example : WellFounded hbDescendingTable.Depends :=
  hbDescendingTable.depends_wellFounded (by rfl)

example : Acc hbDescendingTable.Depends (.hn (2 : Fin 3)) :=
  hbDescendingTable.depends_accessible (by rfl) _

example : ∀ node : TerminalPacketHBNode 3, node.rankIndex.val < 3 :=
  hbDescendingTable.depends_induction (by rfl) (fun node _local =>
    node.rankIndex.isLt)

example : ¬ Relation.TransGen hbDescendingTable.Depends
    (.hn (2 : Fin 3)) (.hn (2 : Fin 3)) :=
  hbDescendingTable.noCycle (by rfl) _

/-! ## Canonical typed-realizer composition remains arbitrary -/

variable {Atom Payload : Type} [DecidableEq Atom]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {family : TerminalBN6GroupedFamily Atom Payload}

example
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (realizerAccepted : realizerTable.checkFaithful = true)
    (dependencyAccepted : dependencyTable.check = true)
    (handle : family.PacketSelectorHandle)
    (faithful : realizerTable.environment.faithful handle = true) :
    (realizerTable.claim handle).HBTableSound
        realizerTable.environment handle dependencyTable ∧
      dependencyTable.Valid ∧
      (∀ node, dependencyTable.RowCovered node) ∧
      WellFounded dependencyTable.Depends ∧
      ∀ node, ¬ Relation.TransGen dependencyTable.Depends node node :=
  terminalBN6_packet_typed_realizer_hb_dependency_table_closure_contract
    realizerTable dependencyTable realizerAccepted dependencyAccepted handle
    faithful

end DirectWire
end PNP
