/-
Copyright (c) 2026 PNP Labs.

Proof-bearing composition of the residual terminal HResolve H-disjoint-family
selector with the terminal HN/BWL certified-path minimum.  Every supplied
hereditary candidate carries its own footprint, expected frontier, nonempty
finite certified-path family, governed predicate, completeness proof, and
path-to-footprint coherence.  The executable selector constructs a maximal
pairwise H-disjoint candidate family.  Every retained candidate has an exact
four-coordinate certified-path minimum; every rejected candidate names a
retained blocker and the first of eight interference domains.

The candidates, footprints, certified paths, governed predicates, family
completeness, and path-to-footprint coherence remain explicit inputs.  This
module does not derive paths or footprints from terminal data, prove HN shape
grammar soundness or completeness, LN confluence, ParseOrExit, independent
leaf tightness, the H0--H4 sidecar, full or polynomial HResolve, the complete
no-lower ledger, unconditional ZeroSlack, PCCMin, polynomial runtime, SAT in
P, or P = NP.
-/

import PNP.ResidualTerminalHNBWLCertifiedPathMinimum
import PNP.ResidualTerminalHResolveHDisjointFamily

namespace PNP
namespace DirectWire

/-! ## Proof-bearing hereditary candidates -/

/-- One supplied hereditary candidate whose footprint is coherently realized
    by a nonempty complete finite family of certified HN/BWL paths.  The
    expected frontier is candidate-specific, so different candidates may be
    genuinely H-disjoint. -/
structure TerminalHResolveCertifiedPathCandidate
    {inputs outputs : Nat} (current : Implementation inputs outputs)
    (Atom Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type) where
  expectedFrontier : List Frontier
  footprint : TerminalHereditaryFootprint Atom Frontier Origin Kernel
    Obligation PrefixTail Charge Interface
  paths : List (TerminalHNBWLCertifiedPath current Atom Frontier
    expectedFrontier)
  pathsNonempty : paths ≠ []
  governed : TerminalHNBWLCertifiedPath current Atom Frontier
    expectedFrontier → Prop
  pathsComplete : TerminalHNBWLFamilyComplete paths governed
  pathFootprintFaithful : ∀ path, path ∈ paths →
    path.support = footprint.support ∧ path.frontier = footprint.frontier

/-- Candidate H-disjointness is exact H-disjointness of the carried
    eight-domain footprints. -/
def TerminalHResolveCertifiedPathCandidate.HDisjoint
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    (left right : TerminalHResolveCertifiedPathCandidate current Atom Frontier
      Origin Kernel Obligation PrefixTail Charge Interface) : Prop :=
  left.footprint.HDisjoint right.footprint

/-- Executable candidate H-disjointness delegates to the exact footprint
    checker; no caller supplies an acceptance bit. -/
def TerminalHResolveCertifiedPathCandidate.checkHDisjoint
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Atom] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (left right : TerminalHResolveCertifiedPathCandidate current Atom Frontier
      Origin Kernel Obligation PrefixTail Charge Interface) : Bool :=
  left.footprint.checkHDisjoint right.footprint

/-- The candidate checker accepts exactly the mathematical H-disjointness
    relation on the two carried footprints. -/
theorem TerminalHResolveCertifiedPathCandidate.checkHDisjoint_eq_true_iff
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Atom] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (left right : TerminalHResolveCertifiedPathCandidate current Atom Frontier
      Origin Kernel Obligation PrefixTail Charge Interface) :
    left.checkHDisjoint right = true ↔ left.HDisjoint right := by
  exact left.footprint.checkHDisjoint_eq_true_iff right.footprint

/-- Return the first exact footprint-interference domain between two supplied
    candidates. -/
def TerminalHResolveCertifiedPathCandidate.firstInterference?
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Atom] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (left right : TerminalHResolveCertifiedPathCandidate current Atom Frontier
      Origin Kernel Obligation PrefixTail Charge Interface) :
    Option TerminalHInterferenceRoute :=
  left.footprint.firstInterference? right.footprint

/-- Compute the exact BWL minimum of the candidate's carried path family. -/
def TerminalHResolveCertifiedPathCandidate.minimum?
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    (candidate : TerminalHResolveCertifiedPathCandidate current Atom Frontier
      Origin Kernel Obligation PrefixTail Charge Interface) :
    Option (TerminalHNBWLCertifiedPath current Atom Frontier
      candidate.expectedFrontier) :=
  terminalHNBWLMinimum? candidate.paths

/-- Every supplied candidate has a computed exact governed-family minimum,
    and the chosen path remains coherent with the candidate footprint. -/
theorem TerminalHResolveCertifiedPathCandidate.minimum?_complete
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    (candidate : TerminalHResolveCertifiedPathCandidate current Atom Frontier
      Origin Kernel Obligation PrefixTail Charge Interface) :
    ∃ chosen,
      candidate.minimum? = some chosen ∧
      chosen ∈ candidate.paths ∧
      (∀ alternative, candidate.governed alternative →
        chosen.objective.LexLE alternative.objective) ∧
      Equivalent chosen.implementation.candidate.program
        chosen.implementation.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      chosen.frontier = candidate.expectedFrontier ∧
      chosen.blocks ≠ [] ∧
      chosen.blocks.flatten = chosen.support ∧
      chosen.support = candidate.footprint.support ∧
      chosen.frontier = candidate.footprint.frontier ∧
      (chosen.shape = .pair ∨ chosen.shape = .tripod ∨
        chosen.shape = .spine ∨ chosen.shape = .nonflat) := by
  obtain ⟨chosen, minimumAt, member, lowerBound, semanticFaithful,
      frontierFaithful, blocksNonempty, blocksCover, shape⟩ :=
    terminal_hn_bwl_certified_path_minimum_complete candidate.paths
      candidate.governed candidate.pathsNonempty candidate.pathsComplete
  have footprintFaithful := candidate.pathFootprintFaithful chosen member
  exact ⟨chosen, minimumAt, member, lowerBound, semanticFaithful,
    frontierFaithful, blocksNonempty, blocksCover, footprintFaithful.1,
    footprintFaithful.2, shape⟩

/-! ## Maximal H-disjoint selection over proof-bearing candidates -/

/-- Process candidates from the tail and retain a candidate exactly when its
    carried footprint is H-disjoint from every already retained footprint. -/
def terminalHResolveGreedyCertifiedPathFamily
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Atom] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface] :
    List (TerminalHResolveCertifiedPathCandidate current Atom Frontier Origin
      Kernel Obligation PrefixTail Charge Interface) →
    List (TerminalHResolveCertifiedPathCandidate current Atom Frontier Origin
      Kernel Obligation PrefixTail Charge Interface)
  | [] => []
  | candidate :: remaining =>
      let selected := terminalHResolveGreedyCertifiedPathFamily remaining
      if selected.all (fun accepted => candidate.checkHDisjoint accepted) then
        candidate :: selected
      else
        selected

/-- Every retained proof-bearing candidate belongs to the supplied family. -/
theorem terminalHResolveGreedyCertifiedPathFamily_subset
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Atom] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (family : List (TerminalHResolveCertifiedPathCandidate current Atom
      Frontier Origin Kernel Obligation PrefixTail Charge Interface)) :
    ∀ candidate,
      candidate ∈ terminalHResolveGreedyCertifiedPathFamily family →
      candidate ∈ family := by
  induction family with
  | nil =>
      simp [terminalHResolveGreedyCertifiedPathFamily]
  | cons head tail inductionHypothesis =>
      simp only [terminalHResolveGreedyCertifiedPathFamily]
      split
      · intro candidate selected
        cases List.mem_cons.mp selected with
        | inl atHead =>
            exact atHead ▸ List.Mem.head tail
        | inr inTail =>
            exact List.Mem.tail head (inductionHypothesis candidate inTail)
      · intro candidate selected
        exact List.Mem.tail head (inductionHypothesis candidate selected)

/-- Duplicate-free supplied candidates yield duplicate-free retained
    candidates. -/
theorem terminalHResolveGreedyCertifiedPathFamily_nodup
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Atom] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    {family : List (TerminalHResolveCertifiedPathCandidate current Atom
      Frontier Origin Kernel Obligation PrefixTail Charge Interface)}
    (unique : family.Nodup) :
    (terminalHResolveGreedyCertifiedPathFamily family).Nodup := by
  induction family with
  | nil =>
      exact List.nodup_nil
  | cons head tail inductionHypothesis =>
      have uniqueParts := List.nodup_cons.mp unique
      simp only [terminalHResolveGreedyCertifiedPathFamily]
      split
      · apply List.nodup_cons.mpr
        constructor
        · intro selectedHead
          exact uniqueParts.1
            (terminalHResolveGreedyCertifiedPathFamily_subset tail head
              selectedHead)
        · exact inductionHypothesis uniqueParts.2
      · exact inductionHypothesis uniqueParts.2

/-- The retained proof-bearing candidates are pairwise H-disjoint. -/
theorem terminalHResolveGreedyCertifiedPathFamily_pairwise
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Atom] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (family : List (TerminalHResolveCertifiedPathCandidate current Atom
      Frontier Origin Kernel Obligation PrefixTail Charge Interface)) :
    (terminalHResolveGreedyCertifiedPathFamily family).Pairwise
      TerminalHResolveCertifiedPathCandidate.HDisjoint := by
  induction family with
  | nil =>
      exact List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      simp only [terminalHResolveGreedyCertifiedPathFamily]
      split
      next accepted =>
        apply List.pairwise_cons.mpr
        constructor
        · intro candidate member
          exact (head.checkHDisjoint_eq_true_iff candidate).mp
            ((List.all_eq_true.mp accepted) candidate member)
        · exact inductionHypothesis
      · exact inductionHypothesis

private theorem exists_false_of_certified_list_all_ne_true
    {Item : Type} (items : List Item) (check : Item → Bool)
    (rejected : items.all check ≠ true) :
    ∃ item, item ∈ items ∧ check item = false := by
  induction items with
  | nil =>
      exact False.elim (rejected rfl)
  | cons head tail inductionHypothesis =>
      cases headCheck : check head with
      | false =>
          exact ⟨head, List.Mem.head tail, headCheck⟩
      | true =>
          have tailRejected : tail.all check ≠ true := by
            intro tailAccepted
            apply rejected
            simp [headCheck, tailAccepted]
          obtain ⟨item, member, failed⟩ := inductionHypothesis tailRejected
          exact ⟨item, List.Mem.tail head member, failed⟩

/-- Maximality certificate: every supplied proof-bearing candidate is
    retained or names a retained blocker and its exact first interference
    domain. -/
theorem terminalHResolveGreedyCertifiedPathFamily_maximal
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Atom] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (family : List (TerminalHResolveCertifiedPathCandidate current Atom
      Frontier Origin Kernel Obligation PrefixTail Charge Interface)) :
    ∀ candidate, candidate ∈ family →
      candidate ∈ terminalHResolveGreedyCertifiedPathFamily family ∨
        ∃ blocker,
          blocker ∈ terminalHResolveGreedyCertifiedPathFamily family ∧
            ∃ route, candidate.firstInterference? blocker = some route := by
  induction family with
  | nil =>
      intro candidate member
      exact False.elim (List.not_mem_nil member)
  | cons head tail inductionHypothesis =>
      simp only [terminalHResolveGreedyCertifiedPathFamily]
      split
      next accepted =>
        intro candidate governed
        cases List.mem_cons.mp governed with
        | inl atHead =>
            exact Or.inl (atHead ▸ List.Mem.head _)
        | inr inTail =>
            cases inductionHypothesis candidate inTail with
            | inl selected =>
                exact Or.inl (List.Mem.tail head selected)
            | inr blocked =>
                obtain ⟨blocker, blockerSelected, route, interferes⟩ :=
                  blocked
                exact Or.inr ⟨blocker, List.Mem.tail head blockerSelected,
                  route, interferes⟩
      next rejected =>
        obtain ⟨blocker, blockerSelected, blockerRejected⟩ :=
          exists_false_of_certified_list_all_ne_true
            (terminalHResolveGreedyCertifiedPathFamily tail)
            (fun accepted => head.checkHDisjoint accepted) rejected
        have blockerExists :
            ∃ blocker,
              blocker ∈ terminalHResolveGreedyCertifiedPathFamily tail ∧
                ¬head.HDisjoint blocker := by
          refine ⟨blocker, blockerSelected, ?_⟩
          intro disjoint
          have accepted :=
            (head.checkHDisjoint_eq_true_iff blocker).mpr disjoint
          simp [blockerRejected] at accepted
        obtain ⟨blocker, blockerSelected, interferes⟩ := blockerExists
        have blockerRoute :
            ∃ route, head.firstInterference? blocker = some route := by
          cases routeEquation : head.firstInterference? blocker with
          | none =>
              exact False.elim (interferes
                ((head.footprint.firstInterference?_eq_none_iff_hDisjoint
                  blocker.footprint).mp routeEquation))
          | some route =>
              exact ⟨route, rfl⟩
        intro candidate governed
        cases List.mem_cons.mp governed with
        | inl atHead =>
            obtain ⟨route, routeEquation⟩ := blockerRoute
            exact Or.inr ⟨blocker, blockerSelected, route,
              atHead ▸ routeEquation⟩
        | inr inTail =>
            exact inductionHypothesis candidate inTail

/-- Named bounded endpoint for the composed HResolve surface: the greedy
    selector is duplicate-free, governed, pairwise H-disjoint, and maximal;
    every retained candidate also exposes its exact governed-family BWL
    minimum with all carried semantic, frontier, block, shape, and footprint
    evidence preserved. -/
theorem terminal_hresolve_certified_path_family_complete
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Atom] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (family : List (TerminalHResolveCertifiedPathCandidate current Atom
      Frontier Origin Kernel Obligation PrefixTail Charge Interface))
    (unique : family.Nodup) :
    let selected := terminalHResolveGreedyCertifiedPathFamily family
    selected.Nodup ∧
      (∀ candidate, candidate ∈ selected → candidate ∈ family) ∧
      selected.Pairwise TerminalHResolveCertifiedPathCandidate.HDisjoint ∧
      (∀ candidate, candidate ∈ family →
        candidate ∈ selected ∨
          ∃ blocker, blocker ∈ selected ∧
            ∃ route, candidate.firstInterference? blocker = some route) ∧
      (∀ candidate, candidate ∈ selected →
        ∃ chosen,
          candidate.minimum? = some chosen ∧
          chosen ∈ candidate.paths ∧
          (∀ alternative, candidate.governed alternative →
            chosen.objective.LexLE alternative.objective) ∧
          Equivalent chosen.implementation.candidate.program
            chosen.implementation.candidate.directWireWord
            current.candidate.program current.candidate.directWireWord ∧
          chosen.frontier = candidate.expectedFrontier ∧
          chosen.blocks ≠ [] ∧
          chosen.blocks.flatten = chosen.support ∧
          chosen.support = candidate.footprint.support ∧
          chosen.frontier = candidate.footprint.frontier ∧
          (chosen.shape = .pair ∨ chosen.shape = .tripod ∨
            chosen.shape = .spine ∨ chosen.shape = .nonflat)) := by
  exact ⟨terminalHResolveGreedyCertifiedPathFamily_nodup unique,
    terminalHResolveGreedyCertifiedPathFamily_subset family,
    terminalHResolveGreedyCertifiedPathFamily_pairwise family,
    terminalHResolveGreedyCertifiedPathFamily_maximal family,
    fun candidate _selected => candidate.minimum?_complete⟩

end DirectWire
end PNP
