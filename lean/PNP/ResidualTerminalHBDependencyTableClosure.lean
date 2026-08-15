/-
Copyright (c) 2026 PNP Labs.

Total-table closure for a supplied finite HN/BUD dependency system.  Instead
of accepting an independent edge list, the input assigns one data-only finite
dependency row to every HN and budget node.  The graph is materialized
mechanically from all rows, and the checker validates every row dependency
against the existing exact ten-coordinate terminal residual rank.

Acceptance proves exact table-to-edge coverage, strict rank descent,
well-foundedness, generic rank induction, and absence of every nonempty cycle
in the materialized supplied relation.  It also composes with the checked
Packet typed-realizer contract so HN and budget bots name covered table rows
and lower-seed bots descend in the exact rank.

The table, rank mapping, selector family, faithfulness and activity tables,
and realizer claims remain explicit inputs.  Total representation coverage
does not prove blocker semantics, semantic dependency completeness relative to
terminal data, a local invariant premise, rank-complete selector silence, the
full HB negative closure, polynomial size or runtime, unconditional ZeroSlack
or PCCMin, SAT in P, removal of a project assumption, or P = NP.
-/

import PNP.ResidualTerminalHBBlockerGraphAcyclicity

namespace PNP
namespace DirectWire

/-! ## Exact finite HN/BUD node enumeration -/

/-- Every HN node followed by every budget node at the supplied finite ranks. -/
def allTerminalPacketHBNodes (rankCount : Nat) :
    List (TerminalPacketHBNode rankCount) :=
  (allFin rankCount).map TerminalPacketHBNode.hn ++
    (allFin rankCount).map TerminalPacketHBNode.budget

/-- The total node enumeration contains every HN and budget node. -/
@[simp] theorem mem_allTerminalPacketHBNodes
    {rankCount : Nat}
    (node : TerminalPacketHBNode rankCount) :
    node ∈ allTerminalPacketHBNodes rankCount := by
  cases node with
  | hn rank =>
      simp [allTerminalPacketHBNodes, mem_allFin]
  | budget rank =>
      simp [allTerminalPacketHBNodes, mem_allFin]

/-! ## Total data-only dependency table and materialized graph -/

/-- A total dependency row for every finite HN/BUD node, plus the exact-rank
    embedding.  No edge list or proof field is supplied independently. -/
structure TerminalPacketHBDependencyTable (rankCount : Nat) where
  rankTuple : Fin rankCount -> TerminalResidualRank
  dependencies : TerminalPacketHBNode rankCount ->
    List (TerminalPacketHBNode rankCount)

/-- Exact rank of one node in the supplied table. -/
def TerminalPacketHBDependencyTable.exactRank
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (node : TerminalPacketHBNode rankCount) : TerminalResidualRank :=
  table.rankTuple node.rankIndex

/-- Materialize every dependency in every total table row as one graph edge. -/
def TerminalPacketHBDependencyTable.toGraph
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount) :
    TerminalPacketHBDependencyGraph rankCount where
  rankTuple := table.rankTuple
  edges := (allTerminalPacketHBNodes rankCount).flatMap (fun blocked =>
    (table.dependencies blocked).map (fun dependency =>
      { blocked := blocked, dependency := dependency }))

/-- The table relation reads directly from the unique row selected by its
    blocked node. -/
def TerminalPacketHBDependencyTable.Depends
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (dependency blocked : TerminalPacketHBNode rankCount) : Prop :=
  dependency ∈ table.dependencies blocked

/-- A materialized edge occurs exactly when the dependency occurs in the row
    selected by that edge's blocked node. -/
theorem TerminalPacketHBDependencyTable.edge_mem_toGraph_iff
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (edge : TerminalPacketHBDependencyEdge rankCount) :
    edge ∈ table.toGraph.edges ↔
      edge.dependency ∈ table.dependencies edge.blocked := by
  constructor
  · intro edgeMember
    simp only [TerminalPacketHBDependencyTable.toGraph,
      List.mem_flatMap, List.mem_map] at edgeMember
    obtain ⟨blocked, _blockedMember, dependency, dependencyMember,
      edgeEquation⟩ := edgeMember
    cases edgeEquation
    exact dependencyMember
  · intro dependencyMember
    simp only [TerminalPacketHBDependencyTable.toGraph,
      List.mem_flatMap, List.mem_map]
    exact ⟨edge.blocked, mem_allTerminalPacketHBNodes edge.blocked,
      edge.dependency, dependencyMember, rfl⟩

/-- The materialized graph relation is definitionally complete for the total
    supplied table relation. -/
theorem TerminalPacketHBDependencyTable.toGraph_depends_iff
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (dependency blocked : TerminalPacketHBNode rankCount) :
    table.toGraph.Depends dependency blocked ↔
      table.Depends dependency blocked := by
  exact table.edge_mem_toGraph_iff
    { blocked := blocked, dependency := dependency }

/-- Every node has exactly the row selected by the total dependency function,
    and that row is represented exactly in the materialized graph. -/
def TerminalPacketHBDependencyTable.RowCovered
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (node : TerminalPacketHBNode rankCount) : Prop :=
  node ∈ allTerminalPacketHBNodes rankCount ∧
    ∀ dependency,
      table.Depends dependency node ↔
        table.toGraph.Depends dependency node

/-- Every HN/BUD node is covered by exactly its total table row. -/
theorem TerminalPacketHBDependencyTable.rowCovered
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (node : TerminalPacketHBNode rankCount) :
    table.RowCovered node := by
  refine ⟨mem_allTerminalPacketHBNodes node, ?_⟩
  intro dependency
  exact (table.toGraph_depends_iff dependency node).symm

/-! ## Exhaustive checker and exact proposition -/

/-- Exact proposition enforced by table acceptance. -/
def TerminalPacketHBDependencyTable.Valid
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount) : Prop :=
  table.toGraph.RankEmbeddingValid ∧
    ∀ blocked dependency,
      dependency ∈ table.dependencies blocked →
        (table.exactRank dependency).LexLT (table.exactRank blocked)

/-- Check the exact-rank embedding and every dependency from every total row. -/
def TerminalPacketHBDependencyTable.check
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount) : Bool :=
  table.toGraph.check

/-- Table acceptance is exactly rank-embedding validity plus strict descent of
    every dependency in every row. -/
theorem TerminalPacketHBDependencyTable.check_eq_true_iff
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount) :
    table.check = true ↔ table.Valid := by
  rw [TerminalPacketHBDependencyTable.check]
  rw [TerminalPacketHBDependencyGraph.check_eq_true_iff]
  constructor
  · intro graphValid
    refine ⟨graphValid.1, ?_⟩
    intro blocked dependency dependencyMember
    have edgeMember :
        ({ blocked := blocked, dependency := dependency } :
          TerminalPacketHBDependencyEdge rankCount) ∈ table.toGraph.edges :=
      (table.edge_mem_toGraph_iff
        { blocked := blocked, dependency := dependency }).2 dependencyMember
    simpa [TerminalPacketHBDependencyEdge.Valid,
      TerminalPacketHBDependencyTable.toGraph,
      TerminalPacketHBDependencyTable.exactRank,
      TerminalPacketHBDependencyGraph.exactRank] using
        graphValid.2
          ({ blocked := blocked, dependency := dependency } :
            TerminalPacketHBDependencyEdge rankCount) edgeMember
  · intro tableValid
    refine ⟨tableValid.1, ?_⟩
    intro edge edgeMember
    have dependencyMember :
        edge.dependency ∈ table.dependencies edge.blocked :=
      (table.edge_mem_toGraph_iff edge).1 edgeMember
    simpa [TerminalPacketHBDependencyEdge.Valid,
      TerminalPacketHBDependencyTable.toGraph,
      TerminalPacketHBDependencyTable.exactRank,
      TerminalPacketHBDependencyGraph.exactRank] using
        tableValid.2 edge.blocked edge.dependency dependencyMember

/-! ## Exact-rank closure and induction -/

/-- Every dependency in an accepted total row strictly decreases the exact
    ten-coordinate residual rank. -/
theorem TerminalPacketHBDependencyTable.depends_rank_lt
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (accepted : table.check = true)
    {dependency blocked : TerminalPacketHBNode rankCount}
    (depends : table.Depends dependency blocked) :
    (table.exactRank dependency).LexLT (table.exactRank blocked) :=
  (table.check_eq_true_iff.mp accepted).2 blocked dependency depends

/-- The complete supplied table relation is well-founded by inverse image of
    the exact terminal residual rank. -/
theorem TerminalPacketHBDependencyTable.depends_wellFounded
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (accepted : table.check = true) :
    WellFounded table.Depends :=
  Subrelation.wf
    (fun relation => table.depends_rank_lt accepted relation)
    (InvImage.wf table.exactRank terminalResidualRankLexLT_wellFounded)

/-- Every node is accessible in an accepted total dependency table. -/
theorem TerminalPacketHBDependencyTable.depends_accessible
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (accepted : table.check = true)
    (node : TerminalPacketHBNode rankCount) :
    Acc table.Depends node :=
  (table.depends_wellFounded accepted).apply node

/-- Rank induction over the complete supplied table.  The caller must still
    prove the domain-specific local invariant from all listed dependencies. -/
theorem TerminalPacketHBDependencyTable.depends_induction
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (accepted : table.check = true)
    {motive : TerminalPacketHBNode rankCount -> Prop}
    (localStep : ∀ node,
      (∀ dependency, table.Depends dependency node → motive dependency) →
        motive node) :
    ∀ node, motive node := by
  intro node
  exact (table.depends_wellFounded accepted).induction node localStep

/-- No accepted total table contains a nonempty directed dependency cycle. -/
theorem TerminalPacketHBDependencyTable.noCycle
    {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (accepted : table.check = true)
    (node : TerminalPacketHBNode rankCount) :
    ¬ Relation.TransGen table.Depends node node := by
  have accessible : Acc (Relation.TransGen table.Depends) node :=
    (table.depends_wellFounded accepted).transGen.apply node
  induction accessible with
  | intro current _ inductionHypothesis =>
      intro cycle
      exact inductionHypothesis current cycle cycle

/-! ## Composition with the checked Packet typed-realizer contract -/

/-- Public meaning of one typed realizer claim after composition with an
    accepted total HB table.  HN and budget branches name covered rows; the
    lower-seed branch carries exact-rank descent. -/
def TerminalPacketTypedRealizerClaim.HBTableSound
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (selector : Selector)
    (claim : TerminalPacketTypedRealizerClaim current Selector rankCount)
    (table : TerminalPacketHBDependencyTable rankCount) : Prop :=
  (∃ blueprint : TerminalPacketUnitChargeBlueprint current,
    claim = .gain blueprint ∧ blueprint.Valid ∧
      StrictEquivalentGain current blueprint.next) ∨
  (∃ rank : Fin rankCount,
    claim = .bot (.hn rank) ∧
      rank ≤ environment.rankOf selector ∧
      environment.hnActive rank = true ∧
      table.RowCovered (.hn rank)) ∨
  (∃ rank : Fin rankCount,
    claim = .bot (.budget rank) ∧
      rank ≤ environment.rankOf selector ∧
      environment.budgetActive rank = true ∧
      table.RowCovered (.budget rank)) ∨
  (∃ lower : Selector,
    claim = .bot (.lowerSeed lower) ∧
      environment.rankOf lower < environment.rankOf selector ∧
      environment.faithful lower = true ∧
      (table.rankTuple (environment.rankOf lower)).LexLT
        (table.rankTuple (environment.rankOf selector)))

/-- Checked typed-realizer evidence upgrades to exact total-table coverage and
    exact-rank descent without accepting a caller-supplied closure claim. -/
theorem TerminalPacketTypedRealizerEvidence.hbTableSound
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {environment : TerminalPacketTypedRealizerEnvironment Selector rankCount}
    {selector : Selector}
    {claim : TerminalPacketTypedRealizerClaim current Selector rankCount}
    (evidence : TerminalPacketTypedRealizerEvidence
      current environment selector claim)
    (table : TerminalPacketHBDependencyTable rankCount)
    (accepted : table.check = true) :
    claim.HBTableSound environment selector table := by
  unfold TerminalPacketTypedRealizerClaim.HBTableSound
  cases evidence with
  | gain blueprint claimEquation valid =>
      exact Or.inl ⟨blueprint, claimEquation, valid,
        valid.chargeSurplusRealization.strictEquivalentGain⟩
  | hn rank claimEquation rankBound active =>
      exact Or.inr (Or.inl
        ⟨rank, claimEquation, rankBound, active, table.rowCovered (.hn rank)⟩)
  | budget rank claimEquation rankBound active =>
      exact Or.inr (Or.inr (Or.inl
        ⟨rank, claimEquation, rankBound, active,
          table.rowCovered (.budget rank)⟩))
  | lowerSeed lower claimEquation rankStrict faithful =>
      have exactStrict :
          (table.rankTuple (environment.rankOf lower)).LexLT
            (table.rankTuple (environment.rankOf selector)) :=
        (table.check_eq_true_iff.mp accepted).1
          (environment.rankOf lower) (environment.rankOf selector) rankStrict
      exact Or.inr (Or.inr (Or.inr
        ⟨lower, claimEquation, rankStrict, faithful, exactStrict⟩))

/-- Named finite Packet interface: every faithful handle retains its checked
    four-way meaning, HN/BUD bots name total covered rows, lower seeds descend
    in the exact rank, and the supplied table relation is well-founded and
    cycle-free. -/
theorem terminalBN6_packet_typed_realizer_hb_dependency_table_closure_contract
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
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
      ∀ node, ¬ Relation.TransGen dependencyTable.Depends node node := by
  have evidence := realizerTable.checkFaithful_handle
    realizerAccepted handle faithful
  exact ⟨evidence.hbTableSound dependencyTable dependencyAccepted,
    dependencyTable.check_eq_true_iff.mp dependencyAccepted,
    dependencyTable.rowCovered,
    dependencyTable.depends_wellFounded dependencyAccepted,
    dependencyTable.noCycle dependencyAccepted⟩

end DirectWire
end PNP
