/-
Copyright (c) 2026 PNP Labs.

Data-only acyclicity validation for a supplied finite HN/BUD blocker graph.
Each HN or budget node names one index in the existing Packet typed-realizer
rank carrier.  A supplied rank table maps those indices into the exact
ten-coordinate terminal residual rank, and a supplied finite edge list names
the dependency relation.  The checker validates that the rank table preserves
every strict finite-index comparison and that every dependency edge strictly
decreases the exact residual rank.

Acceptance proves well-foundedness and excludes every nonempty directed cycle
in the exact supplied edge relation.  The graph, edge list, rank mapping,
selector family, faithfulness and activity tables, and realizer claims remain
explicit inputs.  This module does not prove dependency completeness, blocker
semantics, rank-complete selector silence, the full HB negative closure,
construction from terminal data, polynomial size or runtime, unconditional
ZeroSlack or PCCMin, SAT in P, removal of a project assumption, or P = NP.
-/

import PNP.ResidualTerminalPacketTypedRealizerContract
import PNP.ResidualTerminalRankWF

namespace PNP
namespace DirectWire

/-! ## Data-only HN/BUD dependency graph -/

/-- The two closed blocker-node forms admitted by the HB graph. -/
inductive TerminalPacketHBNode (rankCount : Nat) : Type where
  | hn (rank : Fin rankCount)
  | budget (rank : Fin rankCount)
deriving DecidableEq

/-- The finite rank index named by either blocker-node form. -/
def TerminalPacketHBNode.rankIndex
    {rankCount : Nat} : TerminalPacketHBNode rankCount -> Fin rankCount
  | .hn rank => rank
  | .budget rank => rank

/-- One directed data edge.  `dependency` is the lower-rank node used by
    `blocked`; neither field carries a proof or semantic certificate. -/
structure TerminalPacketHBDependencyEdge (rankCount : Nat) where
  blocked : TerminalPacketHBNode rankCount
  dependency : TerminalPacketHBNode rankCount
deriving DecidableEq

/-- One explicit finite dependency graph plus its finite-index embedding into
    the exact ten-coordinate residual rank. -/
structure TerminalPacketHBDependencyGraph (rankCount : Nat) where
  rankTuple : Fin rankCount -> TerminalResidualRank
  edges : List (TerminalPacketHBDependencyEdge rankCount)

/-- Exact residual rank carried by one graph node. -/
def TerminalPacketHBDependencyGraph.exactRank
    {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount)
    (node : TerminalPacketHBNode rankCount) : TerminalResidualRank :=
  graph.rankTuple node.rankIndex

/-- The supplied rank table preserves every strict finite-index comparison. -/
def TerminalPacketHBDependencyGraph.RankEmbeddingValid
    {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount) : Prop :=
  ∀ lower upper : Fin rankCount,
    lower < upper →
      (graph.rankTuple lower).LexLT (graph.rankTuple upper)

/-- Fail-closed exhaustive checker for the finite-to-exact rank embedding. -/
def TerminalPacketHBDependencyGraph.checkRankEmbedding
    {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount) : Bool :=
  (allFin rankCount).all (fun lower =>
    (allFin rankCount).all (fun upper =>
      !decide (lower < upper) ||
        terminalResidualRankLTBool
          (graph.rankTuple lower) (graph.rankTuple upper)))

/-- The finite embedding checker recognizes exactly strict-order preservation. -/
theorem TerminalPacketHBDependencyGraph.checkRankEmbedding_eq_true_iff
    {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount) :
    graph.checkRankEmbedding = true ↔ graph.RankEmbeddingValid := by
  constructor
  · intro accepted lower upper lowerLT
    have lowerChecked :=
      (List.all_eq_true.mp accepted) lower (mem_allFin lower)
    have pairChecked :=
      (List.all_eq_true.mp lowerChecked) upper (mem_allFin upper)
    have exactChecked : terminalResidualRankLTBool
        (graph.rankTuple lower) (graph.rankTuple upper) = true := by
      simpa [lowerLT] using pairChecked
    exact (terminalResidualRankLTBool_eq_true_iff _ _).1 exactChecked
  · intro valid
    apply List.all_eq_true.mpr
    intro lower _lowerMember
    apply List.all_eq_true.mpr
    intro upper _upperMember
    by_cases lowerLT : lower < upper
    · have exactLT := valid lower upper lowerLT
      have exactChecked :=
        (terminalResidualRankLTBool_eq_true_iff _ _).2 exactLT
      simp [lowerLT, exactChecked]
    · simp [lowerLT]

/-- Exact proposition required of one supplied dependency edge. -/
def TerminalPacketHBDependencyEdge.Valid
    {rankCount : Nat}
    (edge : TerminalPacketHBDependencyEdge rankCount)
    (graph : TerminalPacketHBDependencyGraph rankCount) : Prop :=
  (graph.exactRank edge.dependency).LexLT
    (graph.exactRank edge.blocked)

/-- Executable exact-rank check for one data-only edge. -/
def TerminalPacketHBDependencyEdge.check
    {rankCount : Nat}
    (edge : TerminalPacketHBDependencyEdge rankCount)
    (graph : TerminalPacketHBDependencyGraph rankCount) : Bool :=
  terminalResidualRankLTBool
    (graph.exactRank edge.dependency) (graph.exactRank edge.blocked)

/-- The edge checker recognizes exactly strict exact-rank descent. -/
theorem TerminalPacketHBDependencyEdge.check_eq_true_iff
    {rankCount : Nat}
    (edge : TerminalPacketHBDependencyEdge rankCount)
    (graph : TerminalPacketHBDependencyGraph rankCount) :
    edge.check graph = true ↔ edge.Valid graph :=
  terminalResidualRankLTBool_eq_true_iff _ _

/-- Complete proposition enforced by graph acceptance. -/
def TerminalPacketHBDependencyGraph.Valid
    {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount) : Prop :=
  graph.RankEmbeddingValid ∧
    ∀ edge, edge ∈ graph.edges → edge.Valid graph

/-- Validate the complete rank embedding and every supplied graph edge. -/
def TerminalPacketHBDependencyGraph.check
    {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount) : Bool :=
  graph.checkRankEmbedding && graph.edges.all (fun edge => edge.check graph)

/-- Graph acceptance is exactly rank-embedding validity plus edgewise descent. -/
theorem TerminalPacketHBDependencyGraph.check_eq_true_iff
    {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount) :
    graph.check = true ↔ graph.Valid := by
  constructor
  · intro accepted
    have checks : graph.checkRankEmbedding = true ∧
        graph.edges.all (fun edge => edge.check graph) = true := by
      simpa only [TerminalPacketHBDependencyGraph.check, Bool.and_eq_true]
        using accepted
    refine ⟨(graph.checkRankEmbedding_eq_true_iff).1 checks.1, ?_⟩
    intro edge edgeMember
    have edgeChecked :=
      (List.all_eq_true.mp checks.2) edge edgeMember
    exact (edge.check_eq_true_iff graph).1 edgeChecked
  · intro valid
    have embeddingChecked :=
      (graph.checkRankEmbedding_eq_true_iff).2 valid.1
    have edgesChecked : graph.edges.all (fun edge => edge.check graph) = true := by
      apply List.all_eq_true.mpr
      intro edge edgeMember
      exact (edge.check_eq_true_iff graph).2 (valid.2 edge edgeMember)
    simpa only [TerminalPacketHBDependencyGraph.check, Bool.and_eq_true]
      using And.intro embeddingChecked edgesChecked

/-! ## Exact dependency relation and well-foundedness -/

/-- The checked directed relation, oriented from a dependency to the node that
    uses it so it has the same orientation as a well-founded descent relation. -/
def TerminalPacketHBDependencyGraph.Depends
    {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount)
    (dependency blocked : TerminalPacketHBNode rankCount) : Prop :=
  { blocked := blocked, dependency := dependency } ∈ graph.edges

/-- Every accepted strict finite-rank comparison descends in the exact rank. -/
theorem TerminalPacketHBDependencyGraph.rankTuple_lt_of_lt
    {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount)
    (accepted : graph.check = true)
    {lower upper : Fin rankCount}
    (lowerLT : lower < upper) :
    (graph.rankTuple lower).LexLT (graph.rankTuple upper) :=
  (graph.check_eq_true_iff.mp accepted).1 lower upper lowerLT

/-- Every accepted graph edge strictly decreases the exact residual rank. -/
theorem TerminalPacketHBDependencyGraph.depends_rank_lt
    {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount)
    (accepted : graph.check = true)
    {dependency blocked : TerminalPacketHBNode rankCount}
    (depends : graph.Depends dependency blocked) :
    (graph.exactRank dependency).LexLT (graph.exactRank blocked) :=
  (graph.check_eq_true_iff.mp accepted).2
    { blocked := blocked, dependency := dependency } depends

/-- The accepted supplied dependency relation is well-founded by inverse image
    of the exact ten-coordinate residual rank. -/
theorem TerminalPacketHBDependencyGraph.depends_wellFounded
    {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount)
    (accepted : graph.check = true) :
    WellFounded graph.Depends :=
  Subrelation.wf
    (fun relation => graph.depends_rank_lt accepted relation)
    (InvImage.wf graph.exactRank terminalResidualRankLexLT_wellFounded)

/-- Every node is accessible under the accepted dependency relation. -/
theorem TerminalPacketHBDependencyGraph.depends_accessible
    {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount)
    (accepted : graph.check = true)
    (node : TerminalPacketHBNode rankCount) :
    Acc graph.Depends node :=
  (graph.depends_wellFounded accepted).apply node

/-- No accepted supplied graph contains a nonempty directed dependency cycle. -/
theorem TerminalPacketHBDependencyGraph.noCycle
    {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount)
    (accepted : graph.check = true)
    (node : TerminalPacketHBNode rankCount) :
    ¬ Relation.TransGen graph.Depends node node := by
  have accessible : Acc (Relation.TransGen graph.Depends) node :=
    (graph.depends_wellFounded accepted).transGen.apply node
  induction accessible with
  | intro current _ inductionHypothesis =>
      intro cycle
      exact inductionHypothesis current cycle cycle

/-! ## Composition with the canonical Packet typed-realizer table -/

/-- A valid lower-seed bot also descends under an accepted exact-rank mapping,
    rather than only under the finite index used by the earlier checker. -/
theorem TerminalPacketHBDependencyGraph.lowerSeed_rankTuple_lt_of_valid
    {Selector : Type} {rankCount : Nat}
    (graph : TerminalPacketHBDependencyGraph rankCount)
    (accepted : graph.check = true)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (selector lower : Selector)
    (valid : TerminalPacketTypedRealizerBot.Valid environment selector
      (.lowerSeed lower)) :
    (graph.rankTuple (environment.rankOf lower)).LexLT
      (graph.rankTuple (environment.rankOf selector)) :=
  graph.rankTuple_lt_of_lt accepted valid.1

/-- Named finite Packet interface: the existing four-way faithful-realizer
    result composes with an exact-rank-preserving, well-founded, cycle-free
    supplied HN/BUD dependency graph. -/
theorem terminalBN6_packet_typed_realizer_hb_acyclicity_contract
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (graph : TerminalPacketHBDependencyGraph rankCount)
    (tableAccepted : table.checkFaithful = true)
    (graphAccepted : graph.check = true)
    (handle : family.PacketSelectorHandle)
    (faithful : table.environment.faithful handle = true) :
    (table.claim handle).Sound table.environment handle ∧
      graph.RankEmbeddingValid ∧
      WellFounded graph.Depends ∧
      ∀ node, ¬ Relation.TransGen graph.Depends node node := by
  refine ⟨terminalBN6_packet_typed_realizer_contract table tableAccepted
    handle faithful, ?_⟩
  exact ⟨(graph.check_eq_true_iff.mp graphAccepted).1,
    graph.depends_wellFounded graphAccepted,
    graph.noCycle graphAccepted⟩

end DirectWire
end PNP
