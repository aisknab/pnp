/-
Copyright (c) 2026 PNP Labs.

Executable maximal H-disjoint-family assembly for the residual terminal
HResolve boundary.  A hereditary footprint records the eight interference
domains named by the manuscript: support, frontier, origin, kernel,
obligation, prefix-tail, charge, and interface.  The selector recursively
retains a candidate exactly when it is H-disjoint from the already selected
tail.  It therefore constructs a duplicate-free pairwise H-disjoint family
and records an exact interference route for every rejected candidate.

The footprints remain supplied inputs.  This module does not derive HN
leaves, formalize the pair/tripod/spine grammar, prove BWL or ParseOrExit,
establish leaf tightness, solve a leaf, construct the full H0--H4 sidecar,
connect blockers to HB ranks, prove a polynomial HResolve implementation,
complete the no-lower ledger, prove unconditional ZeroSlack or PCCMin, remove
a project assumption, prove SAT in P, or prove P = NP.
-/

import PNP.ResidualTerminalHResolveCoverageLedger

namespace PNP
namespace DirectWire

/-! ## Exact eight-domain H-disjointness -/

/-- The eight finite coordinate domains whose simultaneous noninterference is
    the manuscript's H-disjointness condition. -/
structure TerminalHereditaryFootprint
    (Support Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type) where
  support : List Support
  frontier : List Frontier
  origin : List Origin
  kernel : List Kernel
  obligation : List Obligation
  prefixTail : List PrefixTail
  charge : List Charge
  interface : List Interface
  deriving Repr, DecidableEq

/-- The first coordinate domain witnessing interference between two supplied
    hereditary footprints. -/
inductive TerminalHInterferenceRoute where
  | support
  | frontier
  | origin
  | kernel
  | obligation
  | prefixTail
  | charge
  | interface
  deriving Repr, DecidableEq

/-- Exact H-disjointness is simultaneous list disjointness in all eight
    manuscript coordinate domains. -/
def terminalHCoordinateDisjoint {Coordinate : Type}
    (left right : List Coordinate) : Prop :=
  ∀ coordinate, coordinate ∈ left → coordinate ∈ right → False

/-- Executable finite-list reflection of one coordinate-domain disjointness
    proposition. -/
def checkTerminalHCoordinateDisjoint {Coordinate : Type}
    [DecidableEq Coordinate] (left right : List Coordinate) : Bool :=
  left.all (fun coordinate => !(right.contains coordinate))

/-- The coordinate checker accepts exactly when the two finite lists have no
    common member. -/
theorem checkTerminalHCoordinateDisjoint_eq_true_iff
    {Coordinate : Type} [DecidableEq Coordinate]
    (left right : List Coordinate) :
    checkTerminalHCoordinateDisjoint left right = true ↔
      terminalHCoordinateDisjoint left right := by
  simp [checkTerminalHCoordinateDisjoint, terminalHCoordinateDisjoint,
    List.all_eq_true]

/-- Coordinate-domain disjointness is symmetric. -/
theorem terminalHCoordinateDisjoint_symm
    {Coordinate : Type} {left right : List Coordinate}
    (disjoint : terminalHCoordinateDisjoint left right) :
    terminalHCoordinateDisjoint right left := by
  intro coordinate inRight inLeft
  exact disjoint coordinate inLeft inRight

/-- Exact H-disjointness combines all eight coordinate-domain predicates. -/
def TerminalHereditaryFootprint.HDisjoint
    {Support Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    (left right : TerminalHereditaryFootprint Support Frontier Origin Kernel
      Obligation PrefixTail Charge Interface) : Prop :=
  terminalHCoordinateDisjoint left.support right.support ∧
    terminalHCoordinateDisjoint left.frontier right.frontier ∧
    terminalHCoordinateDisjoint left.origin right.origin ∧
    terminalHCoordinateDisjoint left.kernel right.kernel ∧
    terminalHCoordinateDisjoint left.obligation right.obligation ∧
    terminalHCoordinateDisjoint left.prefixTail right.prefixTail ∧
    terminalHCoordinateDisjoint left.charge right.charge ∧
    terminalHCoordinateDisjoint left.interface right.interface

/-- Executable reflection of exact eight-domain H-disjointness. -/
def TerminalHereditaryFootprint.checkHDisjoint
    {Support Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Support] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (left right : TerminalHereditaryFootprint Support Frontier Origin Kernel
      Obligation PrefixTail Charge Interface) : Bool :=
  checkTerminalHCoordinateDisjoint left.support right.support &&
    (checkTerminalHCoordinateDisjoint left.frontier right.frontier &&
    (checkTerminalHCoordinateDisjoint left.origin right.origin &&
    (checkTerminalHCoordinateDisjoint left.kernel right.kernel &&
    (checkTerminalHCoordinateDisjoint left.obligation right.obligation &&
    (checkTerminalHCoordinateDisjoint left.prefixTail right.prefixTail &&
    (checkTerminalHCoordinateDisjoint left.charge right.charge &&
      checkTerminalHCoordinateDisjoint left.interface right.interface))))))

/-- The executable checker accepts exactly the mathematical H-disjointness
    proposition. -/
theorem TerminalHereditaryFootprint.checkHDisjoint_eq_true_iff
    {Support Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Support] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (left right : TerminalHereditaryFootprint Support Frontier Origin Kernel
      Obligation PrefixTail Charge Interface) :
    left.checkHDisjoint right = true ↔ left.HDisjoint right := by
  simp [TerminalHereditaryFootprint.checkHDisjoint,
    TerminalHereditaryFootprint.HDisjoint,
    checkTerminalHCoordinateDisjoint_eq_true_iff]

/-- H-disjointness is symmetric in the two hereditary footprints. -/
theorem TerminalHereditaryFootprint.hDisjoint_symm
    {Support Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    {left right : TerminalHereditaryFootprint Support Frontier Origin Kernel
      Obligation PrefixTail Charge Interface}
    (disjoint : left.HDisjoint right) : right.HDisjoint left := by
  rcases disjoint with
    ⟨support, frontier, origin, kernel, obligation, prefixTail, charge,
      interface⟩
  exact ⟨terminalHCoordinateDisjoint_symm support,
    terminalHCoordinateDisjoint_symm frontier,
    terminalHCoordinateDisjoint_symm origin,
    terminalHCoordinateDisjoint_symm kernel,
    terminalHCoordinateDisjoint_symm obligation,
    terminalHCoordinateDisjoint_symm prefixTail,
    terminalHCoordinateDisjoint_symm charge,
    terminalHCoordinateDisjoint_symm interface⟩

/-- Return the first interfering domain in manuscript order, or `none`
    exactly when the two footprints are H-disjoint. -/
private def firstFailedTerminalHInterferenceRoute :
    List (Bool × TerminalHInterferenceRoute) →
      Option TerminalHInterferenceRoute
  | [] => none
  | (accepted, route) :: remaining =>
      if accepted then firstFailedTerminalHInterferenceRoute remaining
      else some route

private theorem firstFailedTerminalHInterferenceRoute_eq_none_iff
    (checks : List (Bool × TerminalHInterferenceRoute)) :
    firstFailedTerminalHInterferenceRoute checks = none ↔
      checks.all (fun check => check.1) = true := by
  induction checks with
  | nil =>
      simp [firstFailedTerminalHInterferenceRoute]
  | cons check checks inductionHypothesis =>
      rcases check with ⟨accepted, route⟩
      cases accepted <;>
        simp [firstFailedTerminalHInterferenceRoute, inductionHypothesis]

def TerminalHereditaryFootprint.firstInterference?
    {Support Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Support] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (left right : TerminalHereditaryFootprint Support Frontier Origin Kernel
      Obligation PrefixTail Charge Interface) :
    Option TerminalHInterferenceRoute :=
  firstFailedTerminalHInterferenceRoute [
    (checkTerminalHCoordinateDisjoint left.support right.support, .support),
    (checkTerminalHCoordinateDisjoint left.frontier right.frontier, .frontier),
    (checkTerminalHCoordinateDisjoint left.origin right.origin, .origin),
    (checkTerminalHCoordinateDisjoint left.kernel right.kernel, .kernel),
    (checkTerminalHCoordinateDisjoint
      left.obligation right.obligation, .obligation),
    (checkTerminalHCoordinateDisjoint
      left.prefixTail right.prefixTail, .prefixTail),
    (checkTerminalHCoordinateDisjoint left.charge right.charge, .charge),
    (checkTerminalHCoordinateDisjoint
      left.interface right.interface, .interface)]

/-- Absence of an interference route is equivalent to exact simultaneous
    disjointness across all eight coordinate domains. -/
theorem TerminalHereditaryFootprint.firstInterference?_eq_none_iff_hDisjoint
    {Support Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Support] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (left right : TerminalHereditaryFootprint Support Frontier Origin Kernel
      Obligation PrefixTail Charge Interface) :
    left.firstInterference? right = none ↔ left.HDisjoint right := by
  rw [TerminalHereditaryFootprint.firstInterference?,
    firstFailedTerminalHInterferenceRoute_eq_none_iff]
  simp [
    TerminalHereditaryFootprint.HDisjoint,
    checkTerminalHCoordinateDisjoint_eq_true_iff]

/-! ## Deterministic maximal family -/

/-- Process the family from the tail and retain a footprint exactly when it
    is H-disjoint from every footprint already retained. -/
def terminalHResolveGreedyHDisjointFamily
    {Support Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Support] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface] :
    List (TerminalHereditaryFootprint Support Frontier Origin Kernel
      Obligation PrefixTail Charge Interface) →
    List (TerminalHereditaryFootprint Support Frontier Origin Kernel
      Obligation PrefixTail Charge Interface)
  | [] => []
  | candidate :: remaining =>
      let selected := terminalHResolveGreedyHDisjointFamily remaining
      if selected.all (fun accepted => candidate.checkHDisjoint accepted) then
        candidate :: selected
      else
        selected

/-- Every selected footprint belongs to the governed input family. -/
theorem terminalHResolveGreedyHDisjointFamily_subset
    {Support Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Support] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (family : List (TerminalHereditaryFootprint Support Frontier Origin Kernel
      Obligation PrefixTail Charge Interface)) :
    ∀ candidate, candidate ∈ terminalHResolveGreedyHDisjointFamily family →
      candidate ∈ family := by
  induction family with
  | nil =>
      simp [terminalHResolveGreedyHDisjointFamily]
  | cons head tail inductionHypothesis =>
      simp only [terminalHResolveGreedyHDisjointFamily]
      split
      · intro candidate selected
        cases List.mem_cons.mp selected with
        | inl atHead =>
            exact atHead ▸ List.Mem.head tail
        | inr inTail =>
            exact List.Mem.tail head (inductionHypothesis candidate inTail)
      · intro candidate selected
        exact List.Mem.tail head (inductionHypothesis candidate selected)

/-- Duplicate-free governed input yields duplicate-free selected output. -/
theorem terminalHResolveGreedyHDisjointFamily_nodup
    {Support Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Support] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    {family : List (TerminalHereditaryFootprint Support Frontier Origin Kernel
      Obligation PrefixTail Charge Interface)}
    (unique : family.Nodup) :
    (terminalHResolveGreedyHDisjointFamily family).Nodup := by
  induction family with
  | nil =>
      exact List.nodup_nil
  | cons head tail inductionHypothesis =>
      have uniqueParts := List.nodup_cons.mp unique
      simp only [terminalHResolveGreedyHDisjointFamily]
      split
      · apply List.nodup_cons.mpr
        constructor
        · intro selectedHead
          exact uniqueParts.1
            (terminalHResolveGreedyHDisjointFamily_subset tail head selectedHead)
        · exact inductionHypothesis uniqueParts.2
      · exact inductionHypothesis uniqueParts.2

/-- The greedy output is pairwise H-disjoint. -/
theorem terminalHResolveGreedyHDisjointFamily_pairwise
    {Support Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Support] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (family : List (TerminalHereditaryFootprint Support Frontier Origin Kernel
      Obligation PrefixTail Charge Interface)) :
    (terminalHResolveGreedyHDisjointFamily family).Pairwise
      TerminalHereditaryFootprint.HDisjoint := by
  induction family with
  | nil =>
      exact List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      simp only [terminalHResolveGreedyHDisjointFamily]
      split
      next accepted =>
        apply List.pairwise_cons.mpr
        constructor
        · intro candidate member
          exact (head.checkHDisjoint_eq_true_iff candidate).mp
            ((List.all_eq_true.mp accepted) candidate member)
        · exact inductionHypothesis
      · exact inductionHypothesis

/-- Maximality certificate: every governed footprint is retained or names a
    retained blocker together with its exact first interference domain. -/
private theorem exists_false_of_list_all_ne_true
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

theorem terminalHResolveGreedyHDisjointFamily_maximal
    {Support Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Support] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (family : List (TerminalHereditaryFootprint Support Frontier Origin Kernel
      Obligation PrefixTail Charge Interface)) :
    ∀ candidate, candidate ∈ family →
      candidate ∈ terminalHResolveGreedyHDisjointFamily family ∨
        ∃ blocker,
          blocker ∈ terminalHResolveGreedyHDisjointFamily family ∧
            ∃ route, candidate.firstInterference? blocker = some route := by
  induction family with
  | nil =>
      intro candidate member
      exact False.elim (List.not_mem_nil member)
  | cons head tail inductionHypothesis =>
      simp only [terminalHResolveGreedyHDisjointFamily]
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
                obtain ⟨blocker, blockerSelected, route, interferes⟩ := blocked
                exact Or.inr ⟨blocker, List.Mem.tail head blockerSelected,
                  route, interferes⟩
      next rejected =>
        obtain ⟨blocker, blockerSelected, blockerRejected⟩ :=
          exists_false_of_list_all_ne_true
            (terminalHResolveGreedyHDisjointFamily tail)
            (fun accepted => head.checkHDisjoint accepted) rejected
        have blockerExists :
            ∃ blocker,
              blocker ∈ terminalHResolveGreedyHDisjointFamily tail ∧
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
                ((head.firstInterference?_eq_none_iff_hDisjoint blocker).mp
                  routeEquation))
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

/-- Named bounded endpoint for terminal HResolve family assembly: the
    executable selector returns only governed candidates, preserves
    duplicate-freedom, is pairwise H-disjoint, and is maximal with exact
    eight-domain blocker routes. -/
theorem terminal_hresolve_maximal_hdisjoint_family_complete
    {Support Frontier Origin Kernel Obligation PrefixTail Charge Interface :
      Type}
    [DecidableEq Support] [DecidableEq Frontier] [DecidableEq Origin]
    [DecidableEq Kernel] [DecidableEq Obligation] [DecidableEq PrefixTail]
    [DecidableEq Charge] [DecidableEq Interface]
    (family : List (TerminalHereditaryFootprint Support Frontier Origin Kernel
      Obligation PrefixTail Charge Interface))
    (unique : family.Nodup) :
    let selected := terminalHResolveGreedyHDisjointFamily family
    selected.Nodup ∧
      (∀ candidate, candidate ∈ selected → candidate ∈ family) ∧
      selected.Pairwise TerminalHereditaryFootprint.HDisjoint ∧
      (∀ candidate, candidate ∈ family →
        candidate ∈ selected ∨
          ∃ blocker, blocker ∈ selected ∧
            ∃ route, candidate.firstInterference? blocker = some route) := by
  exact ⟨terminalHResolveGreedyHDisjointFamily_nodup unique,
    terminalHResolveGreedyHDisjointFamily_subset family,
    terminalHResolveGreedyHDisjointFamily_pairwise family,
    terminalHResolveGreedyHDisjointFamily_maximal family⟩

end DirectWire
end PNP
