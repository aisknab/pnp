import PNP.ResidualTerminalHBBlockerGraphAcyclicity

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

/-! ## Explicit exact-rank graph -/

def hbRankTuple3 (rank : Fin 3) : TerminalResidualRank :=
  TerminalResidualRank.mk rank.val 0 0 0 0 0 0 0 0 0

def hbDescendingGraph : TerminalPacketHBDependencyGraph 3 where
  rankTuple := hbRankTuple3
  edges := [
    { blocked := .hn (2 : Fin 3), dependency := .budget (1 : Fin 3) },
    { blocked := .budget (1 : Fin 3), dependency := .hn (0 : Fin 3) }
  ]

def hbSameRankGraph : TerminalPacketHBDependencyGraph 3 where
  rankTuple := hbRankTuple3
  edges := [
    { blocked := .hn (1 : Fin 3), dependency := .budget (1 : Fin 3) }
  ]

def hbUpwardGraph : TerminalPacketHBDependencyGraph 3 where
  rankTuple := hbRankTuple3
  edges := [
    { blocked := .hn (1 : Fin 3), dependency := .budget (2 : Fin 3) }
  ]

def hbCyclicGraph : TerminalPacketHBDependencyGraph 3 where
  rankTuple := hbRankTuple3
  edges := [
    { blocked := .hn (2 : Fin 3), dependency := .budget (1 : Fin 3) },
    { blocked := .budget (1 : Fin 3), dependency := .hn (2 : Fin 3) }
  ]

example : hbDescendingGraph.checkRankEmbedding = true := by
  rfl

example : hbDescendingGraph.check = true := by
  rfl

example : hbSameRankGraph.check = false := by
  rfl

example : hbUpwardGraph.check = false := by
  rfl

example : hbCyclicGraph.check = false := by
  rfl

example : hbDescendingGraph.Valid :=
  hbDescendingGraph.check_eq_true_iff.mp (by rfl)

example : hbDescendingGraph.Depends
    (.budget (1 : Fin 3)) (.hn (2 : Fin 3)) := by
  simp [TerminalPacketHBDependencyGraph.Depends, hbDescendingGraph]

example : (hbDescendingGraph.exactRank (.budget (1 : Fin 3))).LexLT
    (hbDescendingGraph.exactRank (.hn (2 : Fin 3))) :=
  hbDescendingGraph.depends_rank_lt (by rfl) (by
    simp [TerminalPacketHBDependencyGraph.Depends, hbDescendingGraph])

example : WellFounded hbDescendingGraph.Depends :=
  hbDescendingGraph.depends_wellFounded (by rfl)

example : Acc hbDescendingGraph.Depends (.hn (2 : Fin 3)) :=
  hbDescendingGraph.depends_accessible (by rfl) _

example : ¬ Relation.TransGen hbDescendingGraph.Depends
    (.hn (2 : Fin 3)) (.hn (2 : Fin 3)) :=
  hbDescendingGraph.noCycle (by rfl) _

/-! ## Exact-rank alignment of a valid lower seed -/

def hbTypedEnvironment :
    TerminalPacketTypedRealizerEnvironment (Fin 3) 3 where
  rankOf := fun selector => selector
  faithful := fun _selector => true
  hnActive := fun _rank => true
  budgetActive := fun _rank => true

example : (hbDescendingGraph.rankTuple
      (hbTypedEnvironment.rankOf (1 : Fin 3))).LexLT
    (hbDescendingGraph.rankTuple
      (hbTypedEnvironment.rankOf (2 : Fin 3))) :=
  hbDescendingGraph.lowerSeed_rankTuple_lt_of_valid (by rfl)
    hbTypedEnvironment (2 : Fin 3) (1 : Fin 3) (by
      change (1 : Fin 3) < (2 : Fin 3) ∧ true = true
      exact ⟨by decide, rfl⟩)

/-! ## Canonical typed-realizer composition remains arbitrary -/

variable {Atom Payload : Type} [DecidableEq Atom]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {family : TerminalBN6GroupedFamily Atom Payload}

example
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (graph : TerminalPacketHBDependencyGraph rankCount)
    (tableAccepted : table.checkFaithful = true)
    (graphAccepted : graph.check = true)
    (handle : family.PacketSelectorHandle)
    (faithful : table.environment.faithful handle = true) :
    (table.claim handle).Sound table.environment handle ∧
      graph.RankEmbeddingValid ∧
      WellFounded graph.Depends ∧
      ∀ node, ¬ Relation.TransGen graph.Depends node node :=
  terminalBN6_packet_typed_realizer_hb_acyclicity_contract table graph
    tableAccepted graphAccepted handle faithful

end DirectWire
end PNP
