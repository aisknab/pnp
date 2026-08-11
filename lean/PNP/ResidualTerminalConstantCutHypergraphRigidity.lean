/-
Copyright (c) 2026 PNP Labs.

Constructive finite reconstruction of the pinned manuscript's theorem V53,
`constant-cut hypergraph rigidity`.  A finite nonnegative weighted hypergraph
whose every nonempty proper cut has one positive value has only the manuscript's
three possible shapes: one pair on two anchors, equal pair weights together
with an optional full-span weight on three anchors, or only full-span weight on
four or more anchors.

The anchor carrier is an arbitrary duplicate-free finite list and every cell
footprint is an order-preserving sublist of that carrier.  No fixed anchor
cardinality or hard-coded cut coordinate occurs in the theorem.  This closes
the mathematical V53 rigidity edge consumed after V54 by BN6.  It does not
construct PkgC, derive BN6 cells or payloads, prove global route or selector
completeness, establish polynomial runtime, prove ZeroSlack or PCCMin, put SAT
in P, or prove P = NP.
-/

import PNP.ResidualTerminalConsumerAntichainNormalForm

namespace PNP
namespace DirectWire

/-! ## Canonical finite-set helpers -/

/-- Two order-preserving sublists of one duplicate-free carrier inherit the
    carrier order: extensional inclusion is therefore an actual sublist. -/
theorem terminalV53Sublist_of_included
    {Atom : Type} {small medium carrier : List Atom}
    (smallCarrier : small.Sublist carrier)
    (mediumCarrier : medium.Sublist carrier)
    (carrierNodup : carrier.Nodup)
    (included : TerminalV54Included small medium) :
    small.Sublist medium := by
  induction carrier generalizing small medium with
  | nil =>
      have smallNil : small = [] := by
        cases smallCarrier
        rfl
      have mediumNil : medium = [] := by
        cases mediumCarrier
        rfl
      subst small
      subst medium
      exact List.Sublist.slnil
  | cons head tail ih =>
      simp only [List.nodup_cons] at carrierNodup
      obtain ⟨headNotTail, tailNodup⟩ := carrierNodup
      cases smallCarrier with
      | @cons smallList _ _ smallTailCarrier =>
          cases mediumCarrier with
          | @cons mediumList _ _ mediumTailCarrier =>
              exact ih smallTailCarrier mediumTailCarrier tailNodup included
          | @cons_cons mediumTail _ _ mediumTailCarrier =>
              apply List.Sublist.cons head
              apply ih smallTailCarrier mediumTailCarrier tailNodup
              intro atom atomSmall
              have atomMedium : atom ∈ head :: mediumTail :=
                included atom atomSmall
              cases atomMedium with
              | head =>
                  exact False.elim (headNotTail
                    (smallTailCarrier.subset atomSmall))
              | tail _ atomMediumTail =>
                  exact atomMediumTail
      | @cons_cons smallTail _ _ smallTailCarrier =>
          cases mediumCarrier with
          | @cons _ _ _ mediumTailCarrier =>
              exact False.elim (headNotTail
                (mediumTailCarrier.subset (included head (by simp))))
          | @cons_cons mediumTail _ _ mediumTailCarrier =>
              apply List.Sublist.cons_cons head
              apply ih smallTailCarrier mediumTailCarrier tailNodup
              intro atom atomSmall
              have atomMedium : atom ∈ head :: mediumTail :=
                included atom (by simp [atomSmall])
              cases atomMedium with
              | head =>
                  exact False.elim (headNotTail
                    (smallTailCarrier.subset atomSmall))
              | tail _ atomMediumTail =>
                  exact atomMediumTail

/-- Executable extensional inclusion for one finite list representative. -/
def terminalV53IncludedBool
    {Atom : Type} [DecidableEq Atom]
    (left right : List Atom) : Bool :=
  left.all fun atom => decide (atom ∈ right)

theorem terminalV53IncludedBool_eq_true_iff
    {Atom : Type} [DecidableEq Atom]
    (left right : List Atom) :
    terminalV53IncludedBool left right = true ↔
      TerminalV54Included left right := by
  simp [terminalV53IncludedBool, TerminalV54Included]

/-- Failure of finite inclusion has a concrete missing member. -/
theorem terminalV53_notIncluded_has_witness
    {Atom : Type} [DecidableEq Atom]
    (left right : List Atom)
    (notIncluded : ¬ TerminalV54Included left right) :
    ∃ atom, atom ∈ left ∧ atom ∉ right := by
  induction left with
  | nil =>
      exact False.elim (notIncluded (by
        intro atom atomMember
        simp at atomMember))
  | cons head tail ih =>
      by_cases headRight : head ∈ right
      · have tailNotIncluded : ¬ TerminalV54Included tail right := by
          intro tailIncluded
          apply notIncluded
          intro atom atomMember
          simp at atomMember
          rcases atomMember with rfl | atomTail
          · exact headRight
          · exact tailIncluded atom atomTail
        obtain ⟨atom, atomTail, atomNotRight⟩ := ih tailNotIncluded
        exact ⟨atom, by simp [atomTail], atomNotRight⟩
      · exact ⟨head, by simp, headRight⟩

/-- The carrier-ordered representative of the pair of two named anchors. -/
def terminalV53CanonicalPair
    {Atom : Type} [DecidableEq Atom]
    (carrier : List Atom) (left right : Atom) : List Atom :=
  carrier.filter fun atom => decide (atom = left ∨ atom = right)

theorem mem_terminalV53CanonicalPair_iff
    {Atom : Type} [DecidableEq Atom]
    (carrier : List Atom) (left right atom : Atom) :
    atom ∈ terminalV53CanonicalPair carrier left right ↔
      atom ∈ carrier ∧ (atom = left ∨ atom = right) := by
  simp [terminalV53CanonicalPair]

theorem terminalV53CanonicalPair_sublist
    {Atom : Type} [DecidableEq Atom]
    (carrier : List Atom) (left right : Atom) :
    (terminalV53CanonicalPair carrier left right).Sublist carrier := by
  exact List.filter_sublist

/-- Two distinct named members give a genuine two-element canonical pair. -/
theorem terminalV53CanonicalPair_length
    {Atom : Type} [DecidableEq Atom]
    (carrier : List Atom) (left right : Atom)
    (carrierNodup : carrier.Nodup)
    (leftCarrier : left ∈ carrier) (rightCarrier : right ∈ carrier)
    (different : left ≠ right) :
    (terminalV53CanonicalPair carrier left right).length = 2 := by
  generalize pairEquation :
    terminalV53CanonicalPair carrier left right = pair
  have pairNodup : pair.Nodup :=
    pairEquation ▸
      (terminalV53CanonicalPair_sublist carrier left right).nodup carrierNodup
  have leftPair : left ∈ pair :=
    pairEquation ▸
      (mem_terminalV53CanonicalPair_iff carrier left right left).2
        ⟨leftCarrier, Or.inl rfl⟩
  have rightPair : right ∈ pair :=
    pairEquation ▸
      (mem_terminalV53CanonicalPair_iff carrier left right right).2
        ⟨rightCarrier, Or.inr rfl⟩
  have onlyPair : ∀ atom, atom ∈ pair -> atom = left ∨ atom = right := by
    intro atom atomPair
    exact (mem_terminalV53CanonicalPair_iff carrier left right atom).1
      (pairEquation.symm ▸ atomPair) |>.2
  cases pair with
  | nil => simp at leftPair
  | cons first tail =>
      cases tail with
      | nil =>
          simp at leftPair rightPair
          exact False.elim (different (leftPair.trans rightPair.symm))
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third remaining =>
              have firstChoice := onlyPair first (by simp)
              have secondChoice := onlyPair second (by simp)
              have thirdChoice := onlyPair third (by simp)
              simp only [List.nodup_cons] at pairNodup
              rcases pairNodup with
                ⟨firstAbsent, secondAbsent, _thirdAbsent, _remainingNodup⟩
              rcases firstChoice with rfl | rfl <;>
                rcases secondChoice with rfl | rfl <;>
                  rcases thirdChoice with rfl | rfl <;> simp_all

theorem terminalV53_filter_congr
    {Atom : Type} (items : List Atom) (left right : Atom -> Bool)
    (agree : ∀ atom, atom ∈ items -> left atom = right atom) :
    items.filter left = items.filter right := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      have headAgree := agree head (by simp)
      have tailAgree : ∀ atom, atom ∈ tail ->
          left atom = right atom := by
        intro atom atomTail
        exact agree atom (by simp [atomTail])
      simp only [List.filter_cons]
      rw [headAgree, ih tailAgree]

theorem terminalV53Complement_sublist
    {Atom : Type} [DecidableEq Atom]
    (carrier cut : List Atom) :
    (terminalV54Complement carrier cut).Sublist carrier := by
  exact List.filter_sublist

theorem terminalV53_nil_sublist
    {Atom : Type} (items : List Atom) :
    ([] : List Atom).Sublist items := by
  induction items with
  | nil => exact List.Sublist.slnil
  | cons head tail ih => exact List.Sublist.cons head ih

theorem terminalV53_singleton_sublist_of_mem
    {Atom : Type} {carrier : List Atom} {atom : Atom}
    (atomCarrier : atom ∈ carrier) : [atom].Sublist carrier := by
  induction carrier with
  | nil => simp at atomCarrier
  | cons head tail ih =>
      simp only [List.mem_cons] at atomCarrier
      rcases atomCarrier with atomHead | atomTail
      · subst atom
        exact List.Sublist.cons_cons head (terminalV53_nil_sublist tail)
      · exact List.Sublist.cons head (ih atomTail)

theorem terminalV53_two_distinct_members
    {Atom : Type} (items : List Atom) (itemsNodup : items.Nodup)
    (itemsLarge : 2 ≤ items.length) :
    ∃ first second, first ∈ items ∧ second ∈ items ∧ first ≠ second := by
  cases items with
  | nil => simp at itemsLarge
  | cons first tail =>
      cases tail with
      | nil => simp at itemsLarge
      | cons second remaining =>
          simp only [List.nodup_cons] at itemsNodup
          obtain ⟨firstAbsent, _⟩ := itemsNodup
          refine ⟨first, second, by simp, by simp, ?_⟩
          intro firstSecond
          subst second
          exact firstAbsent (by simp)

theorem terminalV53_eq_three_of_length
    {Atom : Type} (items : List Atom) (itemsLength : items.length = 3) :
    ∃ first second third, items = [first, second, third] := by
  cases items with
  | nil => simp at itemsLength
  | cons first tail =>
      cases tail with
      | nil => simp at itemsLength
      | cons second rest =>
          cases rest with
          | nil => simp at itemsLength
          | cons third remaining =>
              cases remaining with
              | nil => exact ⟨first, second, third, rfl⟩
              | cons fourth further => simp at itemsLength

theorem terminalV53_sublist_cons_cases
    {Atom : Type} {small tail : List Atom} {head : Atom}
    (included : small.Sublist (head :: tail)) :
    small.Sublist tail ∨
      ∃ rest, small = head :: rest ∧ rest.Sublist tail := by
  cases included with
  | @cons left right skipped smaller => exact Or.inl smaller
  | @cons_cons left right kept smaller =>
      exact Or.inr ⟨left, rfl, smaller⟩

/-- Completeness of the canonical finite subset enumerator for every actual
    order-preserving sublist. -/
theorem terminalV53_sublist_mem_terminalListSubsets
    {Atom : Type} {subset items : List Atom}
    (included : subset.Sublist items) :
    subset ∈ terminalListSubsets items := by
  induction included with
  | slnil => simp [terminalListSubsets]
  | @cons left right skipped smaller ih =>
      unfold terminalListSubsets
      exact List.mem_append_left _ ih
  | @cons_cons left right kept smaller ih =>
      unfold terminalListSubsets
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨left, ih, rfl⟩

/-- The only canonical sublists of size at least two in a three-anchor carrier
    are its three pairs and the full carrier. -/
theorem terminalV53_threeCarrier_largeSublist_classification
    {Atom : Type} {first second third : Atom} {footprint : List Atom}
    (included : footprint.Sublist [first, second, third])
    (large : 2 ≤ footprint.length) :
    footprint = [first, second] ∨
      footprint = [first, third] ∨
      footprint = [second, third] ∨
      footprint = [first, second, third] := by
  rcases terminalV53_sublist_cons_cases included with
      skipFirst | ⟨firstRest, rfl, firstRestSublist⟩
  · rcases terminalV53_sublist_cons_cases skipFirst with
        skipSecond | ⟨secondRest, rfl, secondRestSublist⟩
    · rcases terminalV53_sublist_cons_cases skipSecond with
          skipThird | ⟨thirdRest, rfl, thirdRestSublist⟩
      · have footprintNil : footprint = [] := by
          cases skipThird
          rfl
        subst footprint
        simp at large
      · have thirdRestNil : thirdRest = [] := by
          cases thirdRestSublist
          rfl
        subst thirdRest
        simp at large
    · rcases terminalV53_sublist_cons_cases secondRestSublist with
          skipThird | ⟨thirdRest, rfl, thirdRestSublist⟩
      · have secondRestNil : secondRest = [] := by
          cases skipThird
          rfl
        subst secondRest
        simp at large
      · have thirdRestNil : thirdRest = [] := by
          cases thirdRestSublist
          rfl
        subst thirdRest
        exact Or.inr (Or.inr (Or.inl rfl))
  · rcases terminalV53_sublist_cons_cases firstRestSublist with
        skipSecond | ⟨secondRest, rfl, secondRestSublist⟩
    · rcases terminalV53_sublist_cons_cases skipSecond with
          skipThird | ⟨thirdRest, rfl, thirdRestSublist⟩
      · have firstRestNil : firstRest = [] := by
          cases skipThird
          rfl
        subst firstRest
        simp at large
      · have thirdRestNil : thirdRest = [] := by
          cases thirdRestSublist
          rfl
        subst thirdRest
        exact Or.inr (Or.inl rfl)
    · rcases terminalV53_sublist_cons_cases secondRestSublist with
          skipThird | ⟨thirdRest, rfl, thirdRestSublist⟩
      · have secondRestNil : secondRest = [] := by
          cases skipThird
          rfl
        subst secondRest
        exact Or.inl rfl
      · have thirdRestNil : thirdRest = [] := by
          cases thirdRestSublist
          rfl
        subst thirdRest
        exact Or.inr (Or.inr (Or.inr rfl))

/-- Deleting a canonical sublist from a duplicate-free carrier preserves the
    exact finite cardinality partition. -/
theorem terminalV53Complement_length_add
    {Atom : Type} [DecidableEq Atom]
    {carrier cut : List Atom}
    (cutSublist : cut.Sublist carrier)
    (carrierNodup : carrier.Nodup) :
    (terminalV54Complement carrier cut).length + cut.length =
      carrier.length := by
  induction cutSublist with
  | slnil => simp [terminalV54Complement]
  | @cons cutList carrierTail head cutTailSublist ih =>
      simp only [List.nodup_cons] at carrierNodup
      obtain ⟨headNotTail, tailNodup⟩ := carrierNodup
      have headNotCut : head ∉ cutList := by
        intro headCut
        exact headNotTail (cutTailSublist.subset headCut)
      have tailResult := ih tailNodup
      unfold terminalV54Complement
      simp only [List.filter_cons]
      have headAccepted : decide (head ∉ cutList) = true := by
        simp [headNotCut]
      rw [headAccepted]
      simp only [if_true, List.length_cons]
      change (terminalV54Complement carrierTail cutList).length + 1 +
        cutList.length = carrierTail.length + 1
      omega
  | @cons_cons cutTail carrierTail head cutTailSublist ih =>
      simp only [List.nodup_cons] at carrierNodup
      obtain ⟨headNotTail, tailNodup⟩ := carrierNodup
      have tailFilter :
          (carrierTail.filter fun atom => decide (atom ∉ head :: cutTail)) =
            (carrierTail.filter fun atom => decide (atom ∉ cutTail)) := by
        apply terminalV53_filter_congr
        intro atom atomTail
        have atomNotHead : atom ≠ head := by
          intro atomHead
          subst atom
          exact headNotTail atomTail
        simp [atomNotHead]
      have tailResult := ih tailNodup
      unfold terminalV54Complement
      simp only [List.filter_cons]
      have headRejected : decide (head ∉ head :: cutTail) = false := by
        simp
      rw [headRejected]
      simp only [List.length_cons]
      rw [tailFilter]
      change (terminalV54Complement carrierTail cutTail).length +
        (cutTail.length + 1) = carrierTail.length + 1
      omega

/-! ## Sparse nonnegative hypergraphs and exact cut sums -/

/-- One positive sparse hypergraph cell.  Omitted footprints have implicit
    weight zero. -/
structure TerminalV53Hyperedge (Atom : Type) where
  footprint : List Atom
  mass : Nat
deriving DecidableEq, Repr

/-- Arbitrary finite nonnegative hypergraph data on one canonical anchor
    carrier.  Footprints are unique order-preserving carrier sublists of size
    at least two, matching the manuscript's sparse positive-cell convention. -/
structure TerminalV53Hypergraph (Atom : Type) where
  carrier : List Atom
  carrierNodup : carrier.Nodup
  cells : List (TerminalV53Hyperedge Atom)
  footprintsNodup : (cells.map TerminalV53Hyperedge.footprint).Nodup
  footprintSublist : ∀ cell, cell ∈ cells -> cell.footprint.Sublist carrier
  footprintLarge : ∀ cell, cell ∈ cells -> 2 ≤ cell.footprint.length
  massPositive : ∀ cell, cell ∈ cells -> 0 < cell.mass
  cutValue : Nat
  cutValuePositive : 0 < cutValue

/-- A footprint crosses a cut when it has an anchor on each side. -/
def TerminalV53Hyperedge.Crosses
    {Atom : Type} (cell : TerminalV53Hyperedge Atom)
    (cut : List Atom) : Prop :=
  (∃ atom, atom ∈ cell.footprint ∧ atom ∈ cut) ∧
    ∃ atom, atom ∈ cell.footprint ∧ atom ∉ cut

/-- Executable crossing predicate. -/
def TerminalV53Hyperedge.crossesBool
    {Atom : Type} [DecidableEq Atom]
    (cell : TerminalV53Hyperedge Atom)
    (cut : List Atom) : Bool :=
  (cell.footprint.any fun atom => decide (atom ∈ cut)) &&
    (cell.footprint.any fun atom => decide (atom ∉ cut))

theorem TerminalV53Hyperedge.crossesBool_eq_true_iff
    {Atom : Type} [DecidableEq Atom]
    (cell : TerminalV53Hyperedge Atom)
    (cut : List Atom) :
    cell.crossesBool cut = true ↔ cell.Crosses cut := by
  simp [TerminalV53Hyperedge.crossesBool, TerminalV53Hyperedge.Crosses]

/-- Contribution of one cell wholly inside a canonical region. -/
def TerminalV53Hyperedge.insideContribution
    {Atom : Type} [DecidableEq Atom]
    (cell : TerminalV53Hyperedge Atom)
    (region : List Atom) : Nat :=
  if terminalV53IncludedBool cell.footprint region then cell.mass else 0

/-- Contribution of one cell crossing a cut. -/
def TerminalV53Hyperedge.cutContribution
    {Atom : Type} [DecidableEq Atom]
    (cell : TerminalV53Hyperedge Atom)
    (cut : List Atom) : Nat :=
  if cell.crossesBool cut then cell.mass else 0

/-- Total cell mass contained in one region. -/
def TerminalV53Hypergraph.insideWeight
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (region : List Atom) : Nat :=
  (system.cells.map fun cell => cell.insideContribution region).sum

/-- Total hyperedge mass crossing one cut. -/
def TerminalV53Hypergraph.cutWeight
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (cut : List Atom) : Nat :=
  (system.cells.map fun cell => cell.cutContribution cut).sum

/-- Total sparse mass at one exact canonical footprint. -/
def TerminalV53Hypergraph.footprintWeight
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (footprint : List Atom) : Nat :=
  (system.cells.map fun cell =>
    if cell.footprint = footprint then cell.mass else 0).sum

/-- Total mass of every sparse hypergraph cell. -/
def TerminalV53Hypergraph.totalWeight
    {Atom : Type} (system : TerminalV53Hypergraph Atom) : Nat :=
  (system.cells.map TerminalV53Hyperedge.mass).sum

/-- Canonical nonempty proper cuts are exactly the manuscript's cut domain. -/
def TerminalV53Hypergraph.ProperCut
    {Atom : Type} (system : TerminalV53Hypergraph Atom)
    (cut : List Atom) : Prop :=
  cut.Sublist system.carrier ∧ cut ≠ [] ∧ cut ≠ system.carrier

/-- V53's hypothesis: every nonempty proper cut has the same declared positive
    crossing weight. -/
def TerminalV53Hypergraph.ConstantProperCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) : Prop :=
  ∀ cut, system.ProperCut cut -> system.cutWeight cut = system.cutValue

/-! ## Exact cut partition -/

private theorem terminalV53Included_complement_false
    {Atom : Type} [DecidableEq Atom]
    (carrier cut edge : List Atom)
    (edgeNonempty : edge ≠ [])
    (edgeCut : TerminalV54Included edge cut)
    (edgeComplement :
      TerminalV54Included edge (terminalV54Complement carrier cut)) : False := by
  cases edge with
  | nil => exact edgeNonempty rfl
  | cons head tail =>
      have headCut : head ∈ cut := edgeCut head (by simp)
      have headComplement :
          head ∈ terminalV54Complement carrier cut :=
        edgeComplement head (by simp)
      exact (mem_terminalV54Complement_iff carrier cut head).1
        headComplement |>.2 headCut

/-- Every canonical hyperedge lies wholly on the left, wholly on the right, or
    crosses the cut, with its mass counted exactly once. -/
theorem TerminalV53Hypergraph.cell_partition
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (cell : TerminalV53Hyperedge Atom)
    (cellMember : cell ∈ system.cells)
    (cut : List Atom) :
    cell.insideContribution cut +
        cell.insideContribution
          (terminalV54Complement system.carrier cut) +
        cell.cutContribution cut =
      cell.mass := by
  have edgeNonempty : cell.footprint ≠ [] := by
    intro edgeNil
    have large := system.footprintLarge cell cellMember
    simp [edgeNil] at large
  by_cases cutTrue :
      terminalV53IncludedBool cell.footprint cut = true
  · have edgeCut : TerminalV54Included cell.footprint cut :=
      (terminalV53IncludedBool_eq_true_iff _ _).1 cutTrue
    have complementFalse :
        terminalV53IncludedBool cell.footprint
            (terminalV54Complement system.carrier cut) = false := by
      apply Bool.eq_false_iff.mpr
      intro complementTrue
      exact terminalV53Included_complement_false system.carrier cut
        cell.footprint edgeNonempty edgeCut
        ((terminalV53IncludedBool_eq_true_iff _ _).1 complementTrue)
    have crossesFalse : cell.crossesBool cut = false := by
      apply Bool.eq_false_iff.mpr
      intro crossesTrue
      obtain ⟨leftWitness, rightWitness⟩ :=
        (cell.crossesBool_eq_true_iff cut).1 crossesTrue
      obtain ⟨rightAtom, rightMember, rightNotCut⟩ := rightWitness
      exact rightNotCut (edgeCut rightAtom rightMember)
    simp [TerminalV53Hyperedge.insideContribution,
      TerminalV53Hyperedge.cutContribution, cutTrue, complementFalse,
      crossesFalse]
  · have cutFalse :
        terminalV53IncludedBool cell.footprint cut = false :=
      Bool.eq_false_iff.mpr cutTrue
    have edgeCut : ¬ TerminalV54Included cell.footprint cut := by
      intro included
      exact cutTrue ((terminalV53IncludedBool_eq_true_iff _ _).2 included)
    by_cases complementTrue :
        terminalV53IncludedBool cell.footprint
          (terminalV54Complement system.carrier cut) = true
    · have edgeComplement : TerminalV54Included cell.footprint
          (terminalV54Complement system.carrier cut) :=
        (terminalV53IncludedBool_eq_true_iff _ _).1 complementTrue
      have crossesFalse : cell.crossesBool cut = false := by
        apply Bool.eq_false_iff.mpr
        intro crossesTrue
        obtain ⟨leftWitness, rightWitness⟩ :=
          (cell.crossesBool_eq_true_iff cut).1 crossesTrue
        obtain ⟨leftAtom, leftMember, leftCut⟩ := leftWitness
        have leftComplement := edgeComplement leftAtom leftMember
        exact (mem_terminalV54Complement_iff system.carrier cut
          leftAtom).1 leftComplement |>.2 leftCut
      simp [TerminalV53Hyperedge.insideContribution,
        TerminalV53Hyperedge.cutContribution, cutFalse, complementTrue,
        crossesFalse]
    · have complementFalse :
          terminalV53IncludedBool cell.footprint
              (terminalV54Complement system.carrier cut) = false :=
        Bool.eq_false_iff.mpr complementTrue
      have edgeComplement : ¬ TerminalV54Included cell.footprint
          (terminalV54Complement system.carrier cut) := by
        intro included
        exact complementTrue
          ((terminalV53IncludedBool_eq_true_iff _ _).2 included)
      obtain ⟨rightAtom, rightMember, rightNotCut⟩ :=
        terminalV53_notIncluded_has_witness cell.footprint cut edgeCut
      obtain ⟨leftAtom, leftMember, leftNotComplement⟩ :=
        terminalV53_notIncluded_has_witness cell.footprint
          (terminalV54Complement system.carrier cut) edgeComplement
      have leftCarrier : leftAtom ∈ system.carrier :=
        (system.footprintSublist cell cellMember).subset leftMember
      have leftCut : leftAtom ∈ cut := by
        by_cases atomCut : leftAtom ∈ cut
        · exact atomCut
        · exact False.elim (leftNotComplement
            ((mem_terminalV54Complement_iff system.carrier cut leftAtom).2
              ⟨leftCarrier, atomCut⟩))
      have crossesTrue : cell.crossesBool cut = true :=
        (cell.crossesBool_eq_true_iff cut).2
          ⟨⟨leftAtom, leftMember, leftCut⟩,
            rightAtom, rightMember, rightNotCut⟩
      simp [TerminalV53Hyperedge.insideContribution,
        TerminalV53Hyperedge.cutContribution, cutFalse, complementFalse,
        crossesTrue]

/-- Pointwise equality is preserved by a finite natural-valued list sum. -/
theorem terminalV53_sum_congr
    {alpha : Type} (items : List alpha) (left right : alpha -> Nat)
    (equal : ∀ item, item ∈ items -> left item = right item) :
    (items.map left).sum = (items.map right).sum := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map, List.sum_cons]
      have headEqual := equal head (by simp)
      have tailEqual : ∀ item, item ∈ tail -> left item = right item := by
        intro item itemTail
        exact equal item (by simp [itemTail])
      rw [headEqual, ih tailEqual]

/-- Three pointwise contributions that partition each item also partition the
    three corresponding finite sums. -/
theorem terminalV53_sum_partition
    {alpha : Type} (items : List alpha)
    (first second third total : alpha -> Nat)
    (partition : ∀ item, item ∈ items ->
      first item + second item + third item = total item) :
    (items.map first).sum + (items.map second).sum +
        (items.map third).sum =
      (items.map total).sum := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map, List.sum_cons]
      have headPartition := partition head (by simp)
      have tailPartition : ∀ item, item ∈ tail ->
          first item + second item + third item = total item := by
        intro item itemTail
        exact partition item (by simp [itemTail])
      have tailResult := ih tailPartition
      omega

/-- Pointwise two-term domination is preserved by finite natural-valued sums. -/
theorem terminalV53_sum_pair_le
    {alpha : Type} (items : List alpha)
    (first second total : alpha -> Nat)
    (bounded : ∀ item, item ∈ items ->
      first item + second item ≤ total item) :
    (items.map first).sum + (items.map second).sum ≤
      (items.map total).sum := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map, List.sum_cons]
      have headBound := bounded head (by simp)
      have tailBound : ∀ item, item ∈ tail ->
          first item + second item ≤ total item := by
        intro item itemTail
        exact bounded item (by simp [itemTail])
      have tailResult := ih tailBound
      omega

/-- Pointwise three-term domination is preserved by finite natural-valued
    sums. -/
theorem terminalV53_sum_triple_le
    {alpha : Type} (items : List alpha)
    (first second third total : alpha -> Nat)
    (bounded : ∀ item, item ∈ items ->
      first item + second item + third item ≤ total item) :
    (items.map first).sum + (items.map second).sum +
        (items.map third).sum ≤
      (items.map total).sum := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map, List.sum_cons]
      have headBound := bounded head (by simp)
      have tailBound : ∀ item, item ∈ tail ->
          first item + second item + third item ≤ total item := by
        intro item itemTail
        exact bounded item (by simp [itemTail])
      have tailResult := ih tailBound
      omega

/-- One listed nonnegative term is bounded by its finite sum. -/
theorem terminalV53_term_le_sum
    {alpha : Type} (items : List alpha) (value : alpha -> Nat)
    (item : alpha) (itemMember : item ∈ items) :
    value item ≤ (items.map value).sum := by
  induction items with
  | nil => simp at itemMember
  | cons head tail ih =>
      simp only [List.mem_cons] at itemMember
      simp only [List.map, List.sum_cons]
      rcases itemMember with itemHead | itemTail
      · subst item
        omega
      · have tailBound := ih itemTail
        omega

/-- Exact finite mass conservation across a cut: inside-left, inside-right,
    and crossing cells partition the whole sparse hypergraph. -/
theorem TerminalV53Hypergraph.cut_partition
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (cut : List Atom) :
    system.insideWeight cut +
        system.insideWeight
          (terminalV54Complement system.carrier cut) +
        system.cutWeight cut =
      system.totalWeight := by
  unfold TerminalV53Hypergraph.insideWeight
    TerminalV53Hypergraph.cutWeight TerminalV53Hypergraph.totalWeight
  exact terminalV53_sum_partition system.cells
    (fun cell => cell.insideContribution cut)
    (fun cell => cell.insideContribution
      (terminalV54Complement system.carrier cut))
    (fun cell => cell.cutContribution cut)
    TerminalV53Hyperedge.mass
    (fun cell cellMember => system.cell_partition cell cellMember cut)

/-- A region with fewer than two anchors contains no legal V53 hyperedge. -/
theorem TerminalV53Hypergraph.insideWeight_eq_zero_of_length_lt_two
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (region : List Atom)
    (regionSublist : region.Sublist system.carrier)
    (regionSmall : region.length < 2) :
    system.insideWeight region = 0 := by
  unfold TerminalV53Hypergraph.insideWeight
  have contributionZero : ∀ cell, cell ∈ system.cells ->
      cell.insideContribution region = 0 := by
    intro cell cellMember
    unfold TerminalV53Hyperedge.insideContribution
    by_cases includedTrue :
        terminalV53IncludedBool cell.footprint region = true
    · have included : TerminalV54Included cell.footprint region :=
        (terminalV53IncludedBool_eq_true_iff _ _).1 includedTrue
      have footprintRegion : cell.footprint.Sublist region :=
        terminalV53Sublist_of_included
          (system.footprintSublist cell cellMember) regionSublist
          system.carrierNodup included
      have lengthBound := footprintRegion.length_le
      have large := system.footprintLarge cell cellMember
      omega
    · have includedFalse :
          terminalV53IncludedBool cell.footprint region = false := by
        exact Bool.eq_false_iff.mpr includedTrue
      rw [includedFalse]
      simp
  have sumEqual := terminalV53_sum_congr system.cells
    (fun cell => cell.insideContribution region) (fun _ => 0)
    contributionZero
  calc
    (List.map (fun cell => cell.insideContribution region)
        system.cells).sum =
        (List.map (fun _ => 0) system.cells).sum := sumEqual
    _ = 0 := by
      induction system.cells with
      | nil => simp
      | cons head tail ih => simp [ih]

/-- On a canonical two-anchor region, the contained mass is exactly the mass
    grouped at that one pair footprint. -/
theorem TerminalV53Hypergraph.insideWeight_eq_footprintWeight_of_length_two
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (region : List Atom)
    (regionSublist : region.Sublist system.carrier)
    (regionLength : region.length = 2) :
    system.insideWeight region = system.footprintWeight region := by
  unfold TerminalV53Hypergraph.insideWeight
    TerminalV53Hypergraph.footprintWeight
  apply terminalV53_sum_congr
  intro cell cellMember
  unfold TerminalV53Hyperedge.insideContribution
  by_cases includedTrue :
      terminalV53IncludedBool cell.footprint region = true
  · have included : TerminalV54Included cell.footprint region :=
      (terminalV53IncludedBool_eq_true_iff _ _).1 includedTrue
    have footprintRegion : cell.footprint.Sublist region :=
      terminalV53Sublist_of_included
        (system.footprintSublist cell cellMember) regionSublist
        system.carrierNodup included
    have lengthBound := footprintRegion.length_le
    have large := system.footprintLarge cell cellMember
    have equalLength : cell.footprint.length = region.length := by omega
    have footprintEqual : cell.footprint = region :=
      footprintRegion.eq_of_length equalLength
    rw [includedTrue]
    simp [footprintEqual]
  · have includedFalse :
        terminalV53IncludedBool cell.footprint region = false := by
      exact Bool.eq_false_iff.mpr includedTrue
    have footprintNotEqual : cell.footprint ≠ region := by
      intro footprintEqual
      apply includedTrue
      apply (terminalV53IncludedBool_eq_true_iff _ _).2
      intro atom atomMember
      simpa [footprintEqual] using atomMember
    rw [includedFalse]
    simp [footprintNotEqual]

/-- Every legal sparse cell is contained in the full anchor carrier. -/
theorem TerminalV53Hypergraph.insideWeight_carrier_eq_totalWeight
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) :
    system.insideWeight system.carrier = system.totalWeight := by
  unfold TerminalV53Hypergraph.insideWeight
    TerminalV53Hypergraph.totalWeight
  apply terminalV53_sum_congr
  intro cell cellMember
  unfold TerminalV53Hyperedge.insideContribution
  have includedTrue :
      terminalV53IncludedBool cell.footprint system.carrier = true :=
    (terminalV53IncludedBool_eq_true_iff _ _).2
      (system.footprintSublist cell cellMember).subset
  rw [includedTrue]
  simp

/-- A listed sparse cell's positive mass appears in the exact weight grouped at
    its own footprint. -/
theorem TerminalV53Hypergraph.cellMass_le_footprintWeight
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (cell : TerminalV53Hyperedge Atom) (cellMember : cell ∈ system.cells) :
    cell.mass ≤ system.footprintWeight cell.footprint := by
  unfold TerminalV53Hypergraph.footprintWeight
  have present := terminalV53_term_le_sum system.cells
    (fun candidate =>
      if candidate.footprint = cell.footprint then candidate.mass else 0)
    cell cellMember
  simpa using present

/-- If every sparse cell spans the carrier, the exact full-span weight is the
    total hypergraph mass. -/
theorem TerminalV53Hypergraph.footprintWeight_carrier_eq_total_of_cellsFull
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (cellsFull : ∀ cell, cell ∈ system.cells ->
      cell.footprint = system.carrier) :
    system.footprintWeight system.carrier = system.totalWeight := by
  unfold TerminalV53Hypergraph.footprintWeight
    TerminalV53Hypergraph.totalWeight
  apply terminalV53_sum_congr
  intro cell cellMember
  simp [cellsFull cell cellMember]

/-- Full-span-only support leaves no cell wholly inside the complement of a
    carrier member. -/
theorem TerminalV53Hypergraph.insideWeight_complement_singleton_eq_zero_of_cellsFull
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (cellsFull : ∀ cell, cell ∈ system.cells ->
      cell.footprint = system.carrier)
    (excluded : Atom) (excludedCarrier : excluded ∈ system.carrier) :
    system.insideWeight
      (terminalV54Complement system.carrier [excluded]) = 0 := by
  unfold TerminalV53Hypergraph.insideWeight
  have contributionZero : ∀ cell, cell ∈ system.cells ->
      cell.insideContribution
        (terminalV54Complement system.carrier [excluded]) = 0 := by
    intro cell cellMember
    unfold TerminalV53Hyperedge.insideContribution
    have includedFalse :
        terminalV53IncludedBool cell.footprint
            (terminalV54Complement system.carrier [excluded]) = false := by
      apply Bool.eq_false_iff.mpr
      intro includedTrue
      have included :=
        (terminalV53IncludedBool_eq_true_iff _ _).1 includedTrue
      have excludedComplement := included excluded (by
        rw [cellsFull cell cellMember]
        exact excludedCarrier)
      exact (mem_terminalV54Complement_iff system.carrier [excluded]
        excluded).1 excludedComplement |>.2 (by simp)
    rw [includedFalse]
    simp
  have zeroSum := terminalV53_sum_congr system.cells
    (fun cell => cell.insideContribution
      (terminalV54Complement system.carrier [excluded]))
    (fun _ => 0) contributionZero
  calc
    (List.map
        (fun cell => cell.insideContribution
          (terminalV54Complement system.carrier [excluded]))
        system.cells).sum =
      (List.map (fun _ => 0) system.cells).sum := zeroSum
    _ = 0 := by
      induction system.cells with
      | nil => simp
      | cons head tail ih => simp [ih]

/-- Full-span-only support converts any singleton constant-cut equation into
    the exact full-span weight identity. -/
theorem TerminalV53Hypergraph.fullWeight_eq_cutValue_of_cellsFull
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (constant : system.ConstantProperCuts)
    (carrierLarge : 2 ≤ system.carrier.length)
    (cellsFull : ∀ cell, cell ∈ system.cells ->
      cell.footprint = system.carrier) :
    system.footprintWeight system.carrier = system.cutValue := by
  obtain ⟨excluded, _other, excludedCarrier, _otherCarrier,
      _different⟩ := terminalV53_two_distinct_members system.carrier
    system.carrierNodup carrierLarge
  have singletonSublist : [excluded].Sublist system.carrier :=
    terminalV53_singleton_sublist_of_mem excludedCarrier
  have singletonNotCarrier : [excluded] ≠ system.carrier := by
    intro singletonCarrier
    have lengths := congrArg List.length singletonCarrier
    simp at lengths
    omega
  have singletonProper : system.ProperCut [excluded] :=
    ⟨singletonSublist, by simp, singletonNotCarrier⟩
  have singletonInside : system.insideWeight [excluded] = 0 :=
    system.insideWeight_eq_zero_of_length_lt_two [excluded]
      singletonSublist (by simp)
  have complementInside :=
    system.insideWeight_complement_singleton_eq_zero_of_cellsFull
      cellsFull excluded excludedCarrier
  have partition := system.cut_partition [excluded]
  have constantCut := constant [excluded] singletonProper
  have fullTotal :=
    system.footprintWeight_carrier_eq_total_of_cellsFull cellsFull
  rw [singletonInside, complementInside, constantCut] at partition
  omega

/-- If a target footprint lies in a large region but not a nested small
    region, its exact mass and all mass inside the small region fit disjointly
    inside the large region. -/
theorem TerminalV53Hypergraph.insideWeight_add_footprintWeight_le
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (small large target : List Atom)
    (smallLarge : TerminalV54Included small large)
    (targetLarge : TerminalV54Included target large)
    (targetNotSmall : ¬ TerminalV54Included target small) :
    system.insideWeight small + system.footprintWeight target ≤
      system.insideWeight large := by
  unfold TerminalV53Hypergraph.insideWeight
    TerminalV53Hypergraph.footprintWeight
  apply terminalV53_sum_pair_le
  intro cell cellMember
  unfold TerminalV53Hyperedge.insideContribution
  by_cases exactTarget : cell.footprint = target
  · have smallFalse :
        terminalV53IncludedBool cell.footprint small = false := by
      apply Bool.eq_false_iff.mpr
      intro smallTrue
      apply targetNotSmall
      intro atom atomTarget
      apply (terminalV53IncludedBool_eq_true_iff _ _).1 smallTrue
      simpa [exactTarget] using atomTarget
    have largeTrue :
        terminalV53IncludedBool cell.footprint large = true := by
      apply (terminalV53IncludedBool_eq_true_iff _ _).2
      intro atom atomFootprint
      apply targetLarge atom
      simpa [exactTarget] using atomFootprint
    rw [smallFalse, largeTrue]
    simp [exactTarget]
  · by_cases smallTrue :
        terminalV53IncludedBool cell.footprint small = true
    · have smallIncluded : TerminalV54Included cell.footprint small :=
        (terminalV53IncludedBool_eq_true_iff _ _).1 smallTrue
      have largeTrue :
          terminalV53IncludedBool cell.footprint large = true :=
        (terminalV53IncludedBool_eq_true_iff _ _).2
          (fun atom atomFootprint =>
            smallLarge atom (smallIncluded atom atomFootprint))
      rw [smallTrue, largeTrue]
      simp [exactTarget]
    · have smallFalse :
          terminalV53IncludedBool cell.footprint small = false :=
        Bool.eq_false_iff.mpr smallTrue
      rw [smallFalse]
      simp [exactTarget]

/-- Two distinct target footprints can be lower-bounded simultaneously in
    the same region-difference identity. -/
theorem TerminalV53Hypergraph.insideWeight_add_twoFootprintWeights_le
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (small large firstTarget secondTarget : List Atom)
    (smallLarge : TerminalV54Included small large)
    (firstLarge : TerminalV54Included firstTarget large)
    (secondLarge : TerminalV54Included secondTarget large)
    (firstNotSmall : ¬ TerminalV54Included firstTarget small)
    (secondNotSmall : ¬ TerminalV54Included secondTarget small)
    (targetsDifferent : firstTarget ≠ secondTarget) :
    system.insideWeight small + system.footprintWeight firstTarget +
        system.footprintWeight secondTarget ≤
      system.insideWeight large := by
  unfold TerminalV53Hypergraph.insideWeight
    TerminalV53Hypergraph.footprintWeight
  apply terminalV53_sum_triple_le
  intro cell cellMember
  unfold TerminalV53Hyperedge.insideContribution
  by_cases firstExact : cell.footprint = firstTarget
  · have secondNotExact : cell.footprint ≠ secondTarget := by
      intro secondExact
      exact targetsDifferent (firstExact.symm.trans secondExact)
    have smallFalse :
        terminalV53IncludedBool cell.footprint small = false := by
      apply Bool.eq_false_iff.mpr
      intro smallTrue
      apply firstNotSmall
      intro atom atomFirst
      apply (terminalV53IncludedBool_eq_true_iff _ _).1 smallTrue
      simpa [firstExact] using atomFirst
    have largeTrue :
        terminalV53IncludedBool cell.footprint large = true := by
      apply (terminalV53IncludedBool_eq_true_iff _ _).2
      intro atom atomFootprint
      apply firstLarge atom
      simpa [firstExact] using atomFootprint
    rw [smallFalse, largeTrue]
    simp [firstExact, targetsDifferent]
  · by_cases secondExact : cell.footprint = secondTarget
    · have smallFalse :
          terminalV53IncludedBool cell.footprint small = false := by
        apply Bool.eq_false_iff.mpr
        intro smallTrue
        apply secondNotSmall
        intro atom atomSecond
        apply (terminalV53IncludedBool_eq_true_iff _ _).1 smallTrue
        simpa [secondExact] using atomSecond
      have largeTrue :
          terminalV53IncludedBool cell.footprint large = true := by
        apply (terminalV53IncludedBool_eq_true_iff _ _).2
        intro atom atomFootprint
        apply secondLarge atom
        simpa [secondExact] using atomFootprint
      rw [smallFalse, largeTrue]
      have reverseDifferent : secondTarget ≠ firstTarget := targetsDifferent.symm
      simp [secondExact, reverseDifferent]
    · by_cases smallTrue :
          terminalV53IncludedBool cell.footprint small = true
      · have smallIncluded : TerminalV54Included cell.footprint small :=
          (terminalV53IncludedBool_eq_true_iff _ _).1 smallTrue
        have largeTrue :
            terminalV53IncludedBool cell.footprint large = true :=
          (terminalV53IncludedBool_eq_true_iff _ _).2
            (fun atom atomFootprint =>
              smallLarge atom (smallIncluded atom atomFootprint))
        rw [smallTrue, largeTrue]
        simp [firstExact, secondExact]
      · have smallFalse :
            terminalV53IncludedBool cell.footprint small = false :=
          Bool.eq_false_iff.mpr smallTrue
        rw [smallFalse]
        simp [firstExact, secondExact]

/-! ## Constant-cut pair comparisons -/

/-- Comparing a singleton cut with a proper pair cut isolates the exact pair
    weight as one finite region difference. -/
theorem TerminalV53Hypergraph.pair_complement_identity
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (constant : system.ConstantProperCuts)
    (carrierLarge : 3 ≤ system.carrier.length)
    (pair : List Atom) (pairSublist : pair.Sublist system.carrier)
    (pairLength : pair.length = 2)
    (excluded : Atom) (excludedPair : excluded ∈ pair) :
    system.footprintWeight pair +
        system.insideWeight
          (terminalV54Complement system.carrier pair) =
      system.insideWeight
        (terminalV54Complement system.carrier [excluded]) := by
  have excludedCarrier : excluded ∈ system.carrier :=
    pairSublist.subset excludedPair
  have singletonSublist : [excluded].Sublist system.carrier :=
    terminalV53_singleton_sublist_of_mem excludedCarrier
  have singletonNotCarrier : [excluded] ≠ system.carrier := by
    intro singletonCarrier
    have lengths := congrArg List.length singletonCarrier
    simp at lengths
    omega
  have pairNotCarrier : pair ≠ system.carrier := by
    intro pairCarrier
    have lengths := congrArg List.length pairCarrier
    omega
  have singletonProper : system.ProperCut [excluded] :=
    ⟨singletonSublist, by simp, singletonNotCarrier⟩
  have pairProper : system.ProperCut pair :=
    ⟨pairSublist, by
      intro pairNil
      simp [pairNil] at pairLength, pairNotCarrier⟩
  have singletonInside : system.insideWeight [excluded] = 0 :=
    system.insideWeight_eq_zero_of_length_lt_two [excluded]
      singletonSublist (by simp)
  have pairInside : system.insideWeight pair =
      system.footprintWeight pair :=
    system.insideWeight_eq_footprintWeight_of_length_two pair pairSublist
      pairLength
  have singletonPartition := system.cut_partition [excluded]
  have pairPartition := system.cut_partition pair
  have singletonConstant := constant [excluded] singletonProper
  have pairConstant := constant pair pairProper
  rw [singletonInside, singletonConstant] at singletonPartition
  rw [pairInside, pairConstant] at pairPartition
  omega

/-- Removing a larger cut leaves a region contained in the region left after
    removing any one member of that cut. -/
theorem terminalV53Complement_pair_in_singleton
    {Atom : Type} [DecidableEq Atom]
    (carrier pair : List Atom) (excluded : Atom)
    (excludedPair : excluded ∈ pair) :
    TerminalV54Included (terminalV54Complement carrier pair)
      (terminalV54Complement carrier [excluded]) := by
  intro atom atomSmall
  obtain ⟨atomCarrier, atomNotPair⟩ :=
    (mem_terminalV54Complement_iff carrier pair atom).1 atomSmall
  apply (mem_terminalV54Complement_iff carrier [excluded] atom).2
  refine ⟨atomCarrier, ?_⟩
  intro atomSingleton
  have atomExcluded : atom = excluded := by simpa using atomSingleton
  subst atom
  exact atomNotPair excludedPair

/-- Any footprint containing a retained pair member but excluding the removed
    pair member is dominated by that pair's exact weight. -/
theorem TerminalV53Hypergraph.footprintWeight_le_pairWeight
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (constant : system.ConstantProperCuts)
    (carrierLarge : 3 ≤ system.carrier.length)
    (pair target : List Atom)
    (pairSublist : pair.Sublist system.carrier)
    (pairLength : pair.length = 2)
    (targetSublist : target.Sublist system.carrier)
    (excluded shared : Atom)
    (excludedPair : excluded ∈ pair)
    (excludedNotTarget : excluded ∉ target)
    (sharedPair : shared ∈ pair)
    (sharedTarget : shared ∈ target) :
    system.footprintWeight target ≤ system.footprintWeight pair := by
  let small := terminalV54Complement system.carrier pair
  let large := terminalV54Complement system.carrier [excluded]
  have smallLarge : TerminalV54Included small large :=
    terminalV53Complement_pair_in_singleton system.carrier pair excluded
      excludedPair
  have targetLarge : TerminalV54Included target large := by
    intro atom atomTarget
    apply (mem_terminalV54Complement_iff system.carrier [excluded] atom).2
    refine ⟨targetSublist.subset atomTarget, ?_⟩
    intro atomSingleton
    have atomExcluded : atom = excluded := by simpa using atomSingleton
    subst atom
    exact excludedNotTarget atomTarget
  have targetNotSmall : ¬ TerminalV54Included target small := by
    intro targetSmall
    have sharedSmall := targetSmall shared sharedTarget
    exact (mem_terminalV54Complement_iff system.carrier pair shared).1
      sharedSmall |>.2 sharedPair
  have lowerBound := system.insideWeight_add_footprintWeight_le
    small large target smallLarge targetLarge targetNotSmall
  have exactDifference := system.pair_complement_identity constant
    carrierLarge pair pairSublist pairLength excluded excludedPair
  dsimp [small, large] at lowerBound
  omega

/-- Any two canonical pair footprints sharing an anchor have equal weight once
    the carrier has at least three anchors. -/
theorem TerminalV53Hypergraph.pairWeights_equal_of_shared
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (constant : system.ConstantProperCuts)
    (carrierLarge : 3 ≤ system.carrier.length)
    (leftPair rightPair : List Atom)
    (leftSublist : leftPair.Sublist system.carrier)
    (rightSublist : rightPair.Sublist system.carrier)
    (leftLength : leftPair.length = 2)
    (rightLength : rightPair.length = 2)
    (shared : Atom) (sharedLeft : shared ∈ leftPair)
    (sharedRight : shared ∈ rightPair) :
    system.footprintWeight leftPair =
      system.footprintWeight rightPair := by
  by_cases pairsEqual : leftPair = rightPair
  · simp [pairsEqual]
  · have leftNotIncluded :
        ¬ TerminalV54Included leftPair rightPair := by
      intro leftIncluded
      have leftRightSublist := terminalV53Sublist_of_included
        leftSublist rightSublist system.carrierNodup leftIncluded
      exact pairsEqual
        (leftRightSublist.eq_of_length (by omega))
    have rightNotIncluded :
        ¬ TerminalV54Included rightPair leftPair := by
      intro rightIncluded
      have rightLeftSublist := terminalV53Sublist_of_included
        rightSublist leftSublist system.carrierNodup rightIncluded
      exact pairsEqual
        (rightLeftSublist.eq_of_length (by omega)).symm
    obtain ⟨leftOnly, leftOnlyLeft, leftOnlyNotRight⟩ :=
      terminalV53_notIncluded_has_witness leftPair rightPair
        leftNotIncluded
    obtain ⟨rightOnly, rightOnlyRight, rightOnlyNotLeft⟩ :=
      terminalV53_notIncluded_has_witness rightPair leftPair
        rightNotIncluded
    have rightLeLeft := system.footprintWeight_le_pairWeight constant
      carrierLarge leftPair rightPair leftSublist leftLength rightSublist
      leftOnly shared leftOnlyLeft leftOnlyNotRight sharedLeft sharedRight
    have leftLeRight := system.footprintWeight_le_pairWeight constant
      carrierLarge rightPair leftPair rightSublist rightLength leftSublist
      rightOnly shared rightOnlyRight rightOnlyNotLeft sharedRight sharedLeft
    omega

/-- With four or more anchors, every exact two-anchor footprint has zero
    weight.  Two distinct outside anchors give two disjoint lower-bound terms
    in the singleton-to-pair region difference, while shared-pair equality
    makes all three terms equal. -/
theorem TerminalV53Hypergraph.pairWeight_eq_zero_of_four
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (constant : system.ConstantProperCuts)
    (carrierLarge : 4 ≤ system.carrier.length)
    (pair : List Atom) (pairSublist : pair.Sublist system.carrier)
    (pairLength : pair.length = 2) :
    system.footprintWeight pair = 0 := by
  have pairNodup : pair.Nodup := pairSublist.nodup system.carrierNodup
  obtain ⟨excluded, shared, excludedPair, sharedPair, excludedShared⟩ :=
    terminalV53_two_distinct_members pair pairNodup (by omega)
  let outside := terminalV54Complement system.carrier pair
  have outsideSublist : outside.Sublist system.carrier :=
    terminalV53Complement_sublist system.carrier pair
  have outsideNodup : outside.Nodup :=
    outsideSublist.nodup system.carrierNodup
  have complementLength := terminalV53Complement_length_add pairSublist
    system.carrierNodup
  have outsideLarge : 2 ≤ outside.length := by
    dsimp [outside]
    omega
  obtain ⟨firstOutside, secondOutside, firstOutsideMember,
      secondOutsideMember, outsideDifferent⟩ :=
    terminalV53_two_distinct_members outside outsideNodup outsideLarge
  obtain ⟨firstOutsideCarrier, firstOutsideNotPair⟩ :=
    (mem_terminalV54Complement_iff system.carrier pair firstOutside).1
      firstOutsideMember
  obtain ⟨secondOutsideCarrier, secondOutsideNotPair⟩ :=
    (mem_terminalV54Complement_iff system.carrier pair secondOutside).1
      secondOutsideMember
  have excludedCarrier : excluded ∈ system.carrier :=
    pairSublist.subset excludedPair
  have sharedCarrier : shared ∈ system.carrier :=
    pairSublist.subset sharedPair
  have sharedNotFirstOutside : shared ≠ firstOutside := by
    intro sharedFirst
    subst firstOutside
    exact firstOutsideNotPair sharedPair
  have sharedNotSecondOutside : shared ≠ secondOutside := by
    intro sharedSecond
    subst secondOutside
    exact secondOutsideNotPair sharedPair
  let firstTarget := terminalV53CanonicalPair system.carrier shared firstOutside
  let secondTarget := terminalV53CanonicalPair system.carrier shared secondOutside
  have firstTargetSublist : firstTarget.Sublist system.carrier :=
    terminalV53CanonicalPair_sublist system.carrier shared firstOutside
  have secondTargetSublist : secondTarget.Sublist system.carrier :=
    terminalV53CanonicalPair_sublist system.carrier shared secondOutside
  have firstTargetLength : firstTarget.length = 2 :=
    terminalV53CanonicalPair_length system.carrier shared firstOutside
      system.carrierNodup sharedCarrier firstOutsideCarrier
      sharedNotFirstOutside
  have secondTargetLength : secondTarget.length = 2 :=
    terminalV53CanonicalPair_length system.carrier shared secondOutside
      system.carrierNodup sharedCarrier secondOutsideCarrier
      sharedNotSecondOutside
  have sharedFirstTarget : shared ∈ firstTarget :=
    (mem_terminalV53CanonicalPair_iff system.carrier shared firstOutside
      shared).2 ⟨sharedCarrier, Or.inl rfl⟩
  have sharedSecondTarget : shared ∈ secondTarget :=
    (mem_terminalV53CanonicalPair_iff system.carrier shared secondOutside
      shared).2 ⟨sharedCarrier, Or.inl rfl⟩
  have firstOutsideFirstTarget : firstOutside ∈ firstTarget :=
    (mem_terminalV53CanonicalPair_iff system.carrier shared firstOutside
      firstOutside).2 ⟨firstOutsideCarrier, Or.inr rfl⟩
  have targetsDifferent : firstTarget ≠ secondTarget := by
    intro targetsEqual
    have firstOutsideSecondTarget : firstOutside ∈ secondTarget :=
      targetsEqual ▸ firstOutsideFirstTarget
    have firstChoice :=
      (mem_terminalV53CanonicalPair_iff system.carrier shared secondOutside
        firstOutside).1 firstOutsideSecondTarget |>.2
    rcases firstChoice with firstShared | firstSecond
    · exact sharedNotFirstOutside firstShared.symm
    · exact outsideDifferent firstSecond
  have excludedNotFirstTarget : excluded ∉ firstTarget := by
    intro excludedFirst
    have excludedChoice :=
      (mem_terminalV53CanonicalPair_iff system.carrier shared firstOutside
        excluded).1 excludedFirst |>.2
    rcases excludedChoice with excludedIsShared | excludedIsOutside
    · exact excludedShared excludedIsShared
    · subst firstOutside
      exact firstOutsideNotPair excludedPair
  have excludedNotSecondTarget : excluded ∉ secondTarget := by
    intro excludedSecond
    have excludedChoice :=
      (mem_terminalV53CanonicalPair_iff system.carrier shared secondOutside
        excluded).1 excludedSecond |>.2
    rcases excludedChoice with excludedIsShared | excludedIsOutside
    · exact excludedShared excludedIsShared
    · subst secondOutside
      exact secondOutsideNotPair excludedPair
  have firstPairEqual := system.pairWeights_equal_of_shared constant
    (by omega) pair firstTarget pairSublist firstTargetSublist pairLength
    firstTargetLength shared sharedPair sharedFirstTarget
  have secondPairEqual := system.pairWeights_equal_of_shared constant
    (by omega) pair secondTarget pairSublist secondTargetSublist pairLength
    secondTargetLength shared sharedPair sharedSecondTarget
  let small := terminalV54Complement system.carrier pair
  let large := terminalV54Complement system.carrier [excluded]
  have smallLarge : TerminalV54Included small large :=
    terminalV53Complement_pair_in_singleton system.carrier pair excluded
      excludedPair
  have firstLarge : TerminalV54Included firstTarget large := by
    intro atom atomTarget
    apply (mem_terminalV54Complement_iff system.carrier [excluded] atom).2
    refine ⟨firstTargetSublist.subset atomTarget, ?_⟩
    intro atomSingleton
    have atomExcluded : atom = excluded := by simpa using atomSingleton
    subst atom
    exact excludedNotFirstTarget atomTarget
  have secondLarge : TerminalV54Included secondTarget large := by
    intro atom atomTarget
    apply (mem_terminalV54Complement_iff system.carrier [excluded] atom).2
    refine ⟨secondTargetSublist.subset atomTarget, ?_⟩
    intro atomSingleton
    have atomExcluded : atom = excluded := by simpa using atomSingleton
    subst atom
    exact excludedNotSecondTarget atomTarget
  have firstNotSmall : ¬ TerminalV54Included firstTarget small := by
    intro firstSmall
    have sharedSmall := firstSmall shared sharedFirstTarget
    exact (mem_terminalV54Complement_iff system.carrier pair shared).1
      sharedSmall |>.2 sharedPair
  have secondNotSmall : ¬ TerminalV54Included secondTarget small := by
    intro secondSmall
    have sharedSmall := secondSmall shared sharedSecondTarget
    exact (mem_terminalV54Complement_iff system.carrier pair shared).1
      sharedSmall |>.2 sharedPair
  have lowerBound := system.insideWeight_add_twoFootprintWeights_le
    small large firstTarget secondTarget smallLarge firstLarge secondLarge
    firstNotSmall secondNotSmall targetsDifferent
  have exactDifference := system.pair_complement_identity constant
    (by omega) pair pairSublist pairLength excluded excludedPair
  dsimp [small, large] at lowerBound
  omega

/-- On four or more anchors, every proper canonical footprint has implicit
    weight zero. -/
theorem TerminalV53Hypergraph.properFootprintWeight_eq_zero_of_four
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (constant : system.ConstantProperCuts)
    (carrierLarge : 4 ≤ system.carrier.length)
    (target : List Atom) (targetSublist : target.Sublist system.carrier)
    (targetLarge : 2 ≤ target.length)
    (targetProper : target ≠ system.carrier) :
    system.footprintWeight target = 0 := by
  have carrierNotIncluded :
      ¬ TerminalV54Included system.carrier target := by
    intro carrierIncluded
    have carrierTargetSublist := terminalV53Sublist_of_included
      (List.Sublist.refl system.carrier) targetSublist system.carrierNodup
      carrierIncluded
    have equalLength : system.carrier.length = target.length := by
      have forward := carrierTargetSublist.length_le
      have backward := targetSublist.length_le
      omega
    have carrierTarget := carrierTargetSublist.eq_of_length equalLength
    exact targetProper carrierTarget.symm
  obtain ⟨excluded, excludedCarrier, excludedNotTarget⟩ :=
    terminalV53_notIncluded_has_witness system.carrier target
      carrierNotIncluded
  have targetNodup : target.Nodup :=
    targetSublist.nodup system.carrierNodup
  obtain ⟨shared, _other, sharedTarget, _otherTarget, _different⟩ :=
    terminalV53_two_distinct_members target targetNodup targetLarge
  have sharedCarrier : shared ∈ system.carrier :=
    targetSublist.subset sharedTarget
  have excludedShared : excluded ≠ shared := by
    intro excludedIsShared
    subst shared
    exact excludedNotTarget sharedTarget
  let pair := terminalV53CanonicalPair system.carrier excluded shared
  have pairSublist : pair.Sublist system.carrier :=
    terminalV53CanonicalPair_sublist system.carrier excluded shared
  have pairLength : pair.length = 2 :=
    terminalV53CanonicalPair_length system.carrier excluded shared
      system.carrierNodup excludedCarrier sharedCarrier excludedShared
  have excludedPair : excluded ∈ pair :=
    (mem_terminalV53CanonicalPair_iff system.carrier excluded shared
      excluded).2 ⟨excludedCarrier, Or.inl rfl⟩
  have sharedPair : shared ∈ pair :=
    (mem_terminalV53CanonicalPair_iff system.carrier excluded shared
      shared).2 ⟨sharedCarrier, Or.inr rfl⟩
  have targetLePair := system.footprintWeight_le_pairWeight constant
    (by omega) pair target pairSublist pairLength targetSublist excluded shared
    excludedPair excludedNotTarget sharedPair sharedTarget
  have pairZero := system.pairWeight_eq_zero_of_four constant carrierLarge
    pair pairSublist pairLength
  omega

/-- Positive sparse support plus proper-footprint zero forces every listed cell
    to be full-span on four or more anchors. -/
theorem TerminalV53Hypergraph.cellsFull_of_four
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (constant : system.ConstantProperCuts)
    (carrierLarge : 4 ≤ system.carrier.length) :
    ∀ cell, cell ∈ system.cells -> cell.footprint = system.carrier := by
  intro cell cellMember
  by_cases cellFull : cell.footprint = system.carrier
  · exact cellFull
  · have footprintZero :=
      system.properFootprintWeight_eq_zero_of_four constant carrierLarge
        cell.footprint (system.footprintSublist cell cellMember)
        (system.footprintLarge cell cellMember) cellFull
    have massBound := system.cellMass_le_footprintWeight cell cellMember
    have massPositive := system.massPositive cell cellMember
    omega

/-- The two-anchor V53 branch: every legal sparse cell is full-span and its
    exact weight is the common cut value. -/
theorem TerminalV53Hypergraph.twoAnchor_fullWeight
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (constant : system.ConstantProperCuts)
    (carrierLength : system.carrier.length = 2) :
    system.footprintWeight system.carrier = system.cutValue := by
  have cellsFull : ∀ cell, cell ∈ system.cells ->
      cell.footprint = system.carrier := by
    intro cell cellMember
    have footprintSublist := system.footprintSublist cell cellMember
    have footprintBound := footprintSublist.length_le
    have footprintLarge := system.footprintLarge cell cellMember
    apply footprintSublist.eq_of_length
    omega
  exact system.fullWeight_eq_cutValue_of_cellsFull constant (by omega)
    cellsFull

/-- The three-anchor V53 branch: every pair has one common weight `p`, and
    the full-span mass plus two copies of `p` is the common cut value. -/
theorem TerminalV53Hypergraph.threeAnchor_rigidity
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (constant : system.ConstantProperCuts)
    (carrierLength : system.carrier.length = 3) :
    ∃ p,
      (∀ footprint, footprint.Sublist system.carrier ->
        footprint.length = 2 -> system.footprintWeight footprint = p) ∧
      system.footprintWeight system.carrier + 2 * p = system.cutValue := by
  obtain ⟨first, second, third, carrierEquation⟩ :=
    terminalV53_eq_three_of_length system.carrier carrierLength
  have concreteNodup : [first, second, third].Nodup := by
    rw [← carrierEquation]
    exact system.carrierNodup
  have firstNotSecond : first ≠ second := by
    intro firstSecond
    subst second
    simp at concreteNodup
  have firstNotThird : first ≠ third := by
    intro firstThird
    subst third
    simp at concreteNodup
  have secondNotThird : second ≠ third := by
    intro secondThird
    subst third
    simp at concreteNodup
  have firstSecondSublist : [first, second].Sublist system.carrier := by
    rw [carrierEquation]
    exact List.Sublist.cons_cons first
      (List.Sublist.cons_cons second
        (List.Sublist.cons third List.Sublist.slnil))
  have firstThirdSublist : [first, third].Sublist system.carrier := by
    rw [carrierEquation]
    exact List.Sublist.cons_cons first
      (List.Sublist.cons second
        (List.Sublist.cons_cons third List.Sublist.slnil))
  have secondThirdSublist : [second, third].Sublist system.carrier := by
    rw [carrierEquation]
    exact List.Sublist.cons first
      (List.Sublist.cons_cons second
        (List.Sublist.cons_cons third List.Sublist.slnil))
  have firstSecond_eq_firstThird :=
    system.pairWeights_equal_of_shared constant (by omega)
      [first, second] [first, third] firstSecondSublist firstThirdSublist
      (by simp) (by simp) first (by simp) (by simp)
  have firstSecond_eq_secondThird :=
    system.pairWeights_equal_of_shared constant (by omega)
      [first, second] [second, third] firstSecondSublist secondThirdSublist
      (by simp) (by simp) second (by simp) (by simp)
  let p := system.footprintWeight [first, second]
  have everyPair : ∀ footprint, footprint.Sublist system.carrier ->
      footprint.length = 2 -> system.footprintWeight footprint = p := by
    intro footprint footprintSublist footprintLength
    have concreteSublist :
        footprint.Sublist [first, second, third] := by
      rw [← carrierEquation]
      exact footprintSublist
    have classified := terminalV53_threeCarrier_largeSublist_classification
      concreteSublist (by omega)
    rcases classified with footprintFirstSecond | footprintFirstThird |
        footprintSecondThird | footprintFull
    · subst footprint
      rfl
    · subst footprint
      dsimp [p]
      exact firstSecond_eq_firstThird.symm
    · subst footprint
      dsimp [p]
      exact firstSecond_eq_secondThird.symm
    · subst footprint
      simp at footprintLength
  have cutDecomposition :
      system.footprintWeight [first, second] +
          system.footprintWeight [first, third] +
          system.footprintWeight system.carrier =
        system.cutWeight [first] := by
    unfold TerminalV53Hypergraph.footprintWeight
      TerminalV53Hypergraph.cutWeight
    apply terminalV53_sum_partition
    intro cell cellMember
    have concreteFootprint :
        cell.footprint.Sublist [first, second, third] := by
      rw [← carrierEquation]
      exact system.footprintSublist cell cellMember
    have classified := terminalV53_threeCarrier_largeSublist_classification
      concreteFootprint (system.footprintLarge cell cellMember)
    rcases classified with footprintFirstSecond | footprintFirstThird |
        footprintSecondThird | footprintFull
    · simp [TerminalV53Hyperedge.cutContribution,
        TerminalV53Hyperedge.crossesBool, footprintFirstSecond,
        carrierEquation, secondNotThird, Ne.symm firstNotSecond]
    · simp [TerminalV53Hyperedge.cutContribution,
        TerminalV53Hyperedge.crossesBool, footprintFirstThird,
        carrierEquation, Ne.symm firstNotThird, Ne.symm secondNotThird]
    · simp [TerminalV53Hyperedge.cutContribution,
        TerminalV53Hyperedge.crossesBool, footprintSecondThird,
        carrierEquation, Ne.symm firstNotSecond, Ne.symm firstNotThird,
        Ne.symm secondNotThird]
    · simp [TerminalV53Hyperedge.cutContribution,
        TerminalV53Hyperedge.crossesBool, footprintFull,
        carrierEquation, Ne.symm firstNotSecond, Ne.symm firstNotThird]
  have firstCarrier : first ∈ system.carrier := by
    rw [carrierEquation]
    simp
  have singletonSublist : [first].Sublist system.carrier :=
    terminalV53_singleton_sublist_of_mem firstCarrier
  have singletonNotCarrier : [first] ≠ system.carrier := by
    intro singletonCarrier
    have lengths := congrArg List.length singletonCarrier
    simp at lengths
    omega
  have singletonProper : system.ProperCut [first] :=
    ⟨singletonSublist, by simp, singletonNotCarrier⟩
  have singletonConstant := constant [first] singletonProper
  rw [singletonConstant] at cutDecomposition
  refine ⟨p, everyPair, ?_⟩
  dsimp [p]
  omega

/-- The four-or-more-anchor V53 branch: all proper footprint weights vanish
    and the remaining full-span weight is exactly the common cut value. -/
theorem TerminalV53Hypergraph.fourAnchor_rigidity
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (constant : system.ConstantProperCuts)
    (carrierLarge : 4 ≤ system.carrier.length) :
    (∀ footprint, footprint.Sublist system.carrier ->
        2 ≤ footprint.length -> footprint ≠ system.carrier ->
        system.footprintWeight footprint = 0) ∧
      system.footprintWeight system.carrier = system.cutValue := by
  have properZero : ∀ footprint, footprint.Sublist system.carrier ->
      2 ≤ footprint.length -> footprint ≠ system.carrier ->
      system.footprintWeight footprint = 0 := by
    intro footprint footprintSublist footprintLarge footprintProper
    exact system.properFootprintWeight_eq_zero_of_four constant carrierLarge
      footprint footprintSublist footprintLarge footprintProper
  have cellsFull := system.cellsFull_of_four constant carrierLarge
  exact ⟨properZero,
    system.fullWeight_eq_cutValue_of_cellsFull constant (by omega) cellsFull⟩

/-- Manuscript theorem V53, `constant-cut hypergraph rigidity`, over an
    arbitrary finite duplicate-free anchor carrier.  At two anchors the full
    edge has weight `D`; at three anchors all pairs have one weight `p` and the
    full edge satisfies `w_A + 2p = D`; at four or more anchors every proper
    footprint has weight zero and the full edge again has weight `D`. -/
theorem terminalV53_constantCut_hypergraph_rigidity
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (_carrierAtLeastTwo : 2 ≤ system.carrier.length)
    (constant : system.ConstantProperCuts) :
    (system.carrier.length = 2 ->
      system.footprintWeight system.carrier = system.cutValue) ∧
    (system.carrier.length = 3 ->
      ∃ p,
        (∀ footprint, footprint.Sublist system.carrier ->
          footprint.length = 2 ->
          system.footprintWeight footprint = p) ∧
        system.footprintWeight system.carrier + 2 * p = system.cutValue) ∧
    (4 ≤ system.carrier.length ->
      (∀ footprint, footprint.Sublist system.carrier ->
        2 ≤ footprint.length -> footprint ≠ system.carrier ->
        system.footprintWeight footprint = 0) ∧
      system.footprintWeight system.carrier = system.cutValue) := by
  refine ⟨?_, ?_, ?_⟩
  · intro carrierLength
    exact system.twoAnchor_fullWeight constant carrierLength
  · intro carrierLength
    exact system.threeAnchor_rigidity constant carrierLength
  · intro carrierLarge
    exact system.fourAnchor_rigidity constant carrierLarge

end DirectWire
end PNP
