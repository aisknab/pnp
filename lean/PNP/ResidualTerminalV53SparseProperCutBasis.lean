/-
Copyright (c) 2026 PNP Labs.

Quadratic singleton/pair test family for the V53 constant-cut boundary.

M199 replaces the inherited powerset scan on the coherent branch, but a
rejected shape basis does not name an exact proper cut.  This module enumerates
only singleton and two-anchor order-preserving cuts, proves that their constant
equation already forces the complete V53 equation, and returns the first exact
small-cut mismatch otherwise.

The construction is relative to an explicit sparse positive hypergraph.  It
does not derive that hypergraph from terminal data, map a mismatch into a
globally decreasing route, or prove a complete encoded-input polynomial bound.
-/

import PNP.ResidualTerminalV53CanonicalConstantCutBasis

namespace PNP
namespace DirectWire

/-! ## Canonical singleton/pair test family -/

/-- Every singleton and order-preserving pair from one carrier.  The
    recursion emits only one- and two-element lists and never constructs the
    carrier powerset. -/
def terminalV53SingletonPairCuts {Atom : Type} :
    List Atom -> List (List Atom)
  | [] => []
  | head :: tail =>
      [head] :: ((tail.map fun other => [head, other]) ++
        terminalV53SingletonPairCuts tail)

/-- Exact membership characterization for the canonical singleton/pair
    generator. -/
theorem mem_terminalV53SingletonPairCuts_iff
    {Atom : Type} {carrier cut : List Atom} :
    cut ∈ terminalV53SingletonPairCuts carrier ↔
      cut.Sublist carrier ∧ cut ≠ [] ∧ cut.length ≤ 2 := by
  induction carrier with
  | nil =>
      constructor
      · intro member
        simp [terminalV53SingletonPairCuts] at member
      · rintro ⟨included, nonempty, _small⟩
        have cutNil : cut = [] := by cases included; rfl
        exact False.elim (nonempty cutNil)
  | cons head tail ih =>
      constructor
      · intro member
        have cases : cut = [head] ∨
            cut ∈ tail.map (fun other => [head, other]) ∨
            cut ∈ terminalV53SingletonPairCuts tail := by
          simpa [terminalV53SingletonPairCuts, List.mem_append] using member
        rcases cases with cutSingleton | cutPair | cutTail
        · subst cut
          exact ⟨by simp, by simp, by simp⟩
        · obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp cutPair
          exact ⟨List.Sublist.cons_cons head
              (terminalV53_singleton_sublist_of_mem otherMember),
            by simp, by simp⟩
        · have tailFacts := ih.mp cutTail
          exact ⟨List.Sublist.cons head tailFacts.1,
            tailFacts.2.1, tailFacts.2.2⟩
      · rintro ⟨included, nonempty, small⟩
        rcases terminalV53_sublist_cons_cases included with
            inTail | ⟨rest, rfl, restIncluded⟩
        · have tailMember := ih.mpr ⟨inTail, nonempty, small⟩
          simp [terminalV53SingletonPairCuts, tailMember]
        · cases rest with
          | nil => simp [terminalV53SingletonPairCuts]
          | cons other remaining =>
              have remainingLength : remaining.length = 0 := by
                simp only [List.length_cons] at small
                omega
              have remainingNil : remaining = [] :=
                List.eq_nil_of_length_eq_zero remainingLength
              subst remaining
              have otherMember : other ∈ tail := restIncluded.subset (by simp)
              simp [terminalV53SingletonPairCuts, otherMember]

/-- The canonical singleton/pair family has a direct quadratic length bound. -/
theorem terminalV53SingletonPairCuts_length_le
    {Atom : Type} (carrier : List Atom) :
    (terminalV53SingletonPairCuts carrier).length ≤
      carrier.length + carrier.length * carrier.length := by
  induction carrier with
  | nil => simp [terminalV53SingletonPairCuts]
  | cons head tail ih =>
      simp only [terminalV53SingletonPairCuts, List.length_cons,
        List.length_append, List.length_map]
      calc
        tail.length + (terminalV53SingletonPairCuts tail).length + 1 ≤
            tail.length +
              (tail.length + tail.length * tail.length) + 1 := by
          omega
        _ ≤ tail.length + 1 +
            (tail.length + 1) * (tail.length + 1) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
          omega

private theorem terminalV53PairCuts_nodup
    {Atom : Type} (head : Atom) {tail : List Atom}
    (distinct : tail.Nodup) :
    (tail.map fun other => [head, other]).Nodup := by
  induction tail with
  | nil => exact List.nodup_nil
  | cons other rest ih =>
      have split := List.nodup_cons.mp distinct
      change ([head, other] ::
        (rest.map fun candidate => [head, candidate])).Nodup
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨candidate, candidateMember, equal⟩ := List.mem_map.mp member
        have tailsEqual : [other] = [candidate] :=
          (List.cons.inj equal |>.2).symm
        have otherEqual : other = candidate :=
          List.cons.inj tailsEqual |>.1
        exact split.1 (otherEqual ▸ candidateMember)
      · exact ih split.2

/-- The canonical singleton/pair generator is duplicate-free whenever its
    carrier is duplicate-free. -/
theorem terminalV53SingletonPairCuts_nodup
    {Atom : Type} {carrier : List Atom}
    (distinct : carrier.Nodup) :
    (terminalV53SingletonPairCuts carrier).Nodup := by
  induction carrier with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      have split := List.nodup_cons.mp distinct
      change ([head] :: ((tail.map fun other => [head, other]) ++
        terminalV53SingletonPairCuts tail)).Nodup
      apply List.nodup_cons.mpr
      constructor
      · intro member
        rcases List.mem_append.mp member with pairMember | tailMember
        · obtain ⟨other, _otherMember, equal⟩ := List.mem_map.mp pairMember
          simp at equal
        · have tailSublist :=
            (mem_terminalV53SingletonPairCuts_iff.mp tailMember).1
          exact split.1 (tailSublist.subset (by simp))
      · apply List.nodup_append.mpr
        refine ⟨terminalV53PairCuts_nodup head split.2,
          ih split.2, ?_⟩
        intro left leftMember right rightMember equal
        obtain ⟨other, _otherMember, leftEqual⟩ :=
          List.mem_map.mp leftMember
        have headRight : head ∈ right := by
          rw [← equal, ← leftEqual]
          simp
        have rightSublist :=
          (mem_terminalV53SingletonPairCuts_iff.mp rightMember).1
        exact split.1 (rightSublist.subset headRight)

/-- Keep only proper cuts.  Nonemptiness and containment are already enforced
    by the generator. -/
def TerminalV53Hypergraph.smallProperCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) : List (List Atom) :=
  (terminalV53SingletonPairCuts system.carrier).filter fun cut =>
    decide (cut ≠ system.carrier)

theorem TerminalV53Hypergraph.mem_smallProperCuts_iff
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) (cut : List Atom) :
    cut ∈ system.smallProperCuts ↔
      system.ProperCut cut ∧ cut.length ≤ 2 := by
  rw [TerminalV53Hypergraph.smallProperCuts, List.mem_filter]
  rw [mem_terminalV53SingletonPairCuts_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨⟨included, nonempty, small⟩, proper⟩
    exact ⟨⟨included, nonempty, proper⟩, small⟩
  · rintro ⟨⟨included, nonempty, proper⟩, small⟩
    exact ⟨⟨included, nonempty, small⟩, proper⟩

/-- Exact semantic boundary tested by the canonical small-cut family. -/
def TerminalV53Hypergraph.SmallProperCutEquation
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) : Prop :=
  ∀ cut, system.ProperCut cut -> cut.length ≤ 2 ->
    system.cutWeight cut = system.cutValue

/-- The list-facing and semantic forms of the small-cut equation coincide. -/
theorem TerminalV53Hypergraph.smallProperCutEquation_iff_list
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) :
    system.SmallProperCutEquation ↔
      ∀ cut, cut ∈ system.smallProperCuts ->
        system.cutWeight cut = system.cutValue := by
  constructor
  · intro equation cut cutMember
    have facts := (system.mem_smallProperCuts_iff cut).1 cutMember
    exact equation cut facts.1 facts.2
  · intro equation cut proper small
    exact equation cut ((system.mem_smallProperCuts_iff cut).2
      ⟨proper, small⟩)

/-- The filtered list inherits the direct quadratic bound. -/
theorem TerminalV53Hypergraph.smallProperCuts_length_le
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) :
    system.smallProperCuts.length ≤
      system.carrier.length + system.carrier.length * system.carrier.length := by
  exact Nat.le_trans (List.length_filter_le _ _)
    (terminalV53SingletonPairCuts_length_le system.carrier)

/-- Filtering out the complete carrier preserves duplicate-freedom. -/
theorem TerminalV53Hypergraph.smallProperCuts_nodup
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) :
    system.smallProperCuts.Nodup := by
  exact (terminalV53SingletonPairCuts_nodup system.carrierNodup).filter _

/-! ## V53 rigidity from small cuts only -/

/-- Full-span support plus one singleton equation fixes the exact full-span
    weight. -/
theorem TerminalV53Hypergraph.fullWeight_eq_cutValue_of_cellsFull_of_smallCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (smallConstant : system.SmallProperCutEquation)
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
  have constantCut := smallConstant [excluded] singletonProper (by simp)
  have fullTotal :=
    system.footprintWeight_carrier_eq_total_of_cellsFull cellsFull
  rw [singletonInside, complementInside, constantCut] at partition
  omega

/-- The singleton-to-pair region identity needs only the two named small-cut
    equations, not the complete proper-cut hypothesis. -/
theorem TerminalV53Hypergraph.pair_complement_identity_of_smallCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (smallConstant : system.SmallProperCutEquation)
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
  have singletonConstant :=
    smallConstant [excluded] singletonProper (by simp)
  have pairConstant := smallConstant pair pairProper (by omega)
  rw [singletonInside, singletonConstant] at singletonPartition
  rw [pairInside, pairConstant] at pairPartition
  omega

/-- Any footprint separated from one member of a retained pair is dominated
    by that pair using only small-cut equations. -/
theorem TerminalV53Hypergraph.footprintWeight_le_pairWeight_of_smallCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (smallConstant : system.SmallProperCutEquation)
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
  have exactDifference := system.pair_complement_identity_of_smallCuts
    smallConstant carrierLarge pair pairSublist pairLength excluded excludedPair
  dsimp [small, large] at lowerBound
  omega

/-- Pair weights sharing an anchor agree under the small-cut equation. -/
theorem TerminalV53Hypergraph.pairWeights_equal_of_shared_of_smallCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (smallConstant : system.SmallProperCutEquation)
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
      exact pairsEqual (leftRightSublist.eq_of_length (by omega))
    have rightNotIncluded :
        ¬ TerminalV54Included rightPair leftPair := by
      intro rightIncluded
      have rightLeftSublist := terminalV53Sublist_of_included
        rightSublist leftSublist system.carrierNodup rightIncluded
      exact pairsEqual
        (rightLeftSublist.eq_of_length (by omega)).symm
    obtain ⟨leftOnly, leftOnlyLeft, leftOnlyNotRight⟩ :=
      terminalV53_notIncluded_has_witness leftPair rightPair leftNotIncluded
    obtain ⟨rightOnly, rightOnlyRight, rightOnlyNotLeft⟩ :=
      terminalV53_notIncluded_has_witness rightPair leftPair rightNotIncluded
    have rightLeLeft := system.footprintWeight_le_pairWeight_of_smallCuts
      smallConstant carrierLarge leftPair rightPair leftSublist leftLength
      rightSublist leftOnly shared leftOnlyLeft leftOnlyNotRight sharedLeft
      sharedRight
    have leftLeRight := system.footprintWeight_le_pairWeight_of_smallCuts
      smallConstant carrierLarge rightPair leftPair rightSublist rightLength
      leftSublist rightOnly shared rightOnlyRight rightOnlyNotLeft sharedRight
      sharedLeft
    omega

/-- Four-anchor pair rigidity uses only singleton and pair equations. -/
theorem TerminalV53Hypergraph.pairWeight_eq_zero_of_four_of_smallCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (smallConstant : system.SmallProperCutEquation)
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
  have firstPairEqual := system.pairWeights_equal_of_shared_of_smallCuts
    smallConstant (by omega) pair firstTarget pairSublist firstTargetSublist
    pairLength firstTargetLength shared sharedPair sharedFirstTarget
  have secondPairEqual := system.pairWeights_equal_of_shared_of_smallCuts
    smallConstant (by omega) pair secondTarget pairSublist secondTargetSublist
    pairLength secondTargetLength shared sharedPair sharedSecondTarget
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
  have exactDifference := system.pair_complement_identity_of_smallCuts
    smallConstant (by omega) pair pairSublist pairLength excluded excludedPair
  dsimp [small, large] at lowerBound
  omega

/-- Every proper sparse footprint has zero weight under the small-cut
    equation on four or more anchors. -/
theorem TerminalV53Hypergraph.properFootprintWeight_eq_zero_of_four_of_smallCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (smallConstant : system.SmallProperCutEquation)
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
  have targetLePair := system.footprintWeight_le_pairWeight_of_smallCuts
    smallConstant (by omega) pair target pairSublist pairLength targetSublist
    excluded shared excludedPair excludedNotTarget sharedPair sharedTarget
  have pairZero := system.pairWeight_eq_zero_of_four_of_smallCuts
    smallConstant carrierLarge pair pairSublist pairLength
  omega

/-- Positive sparse support therefore forces full-span cells on four or more
    anchors using only the small-cut equation. -/
theorem TerminalV53Hypergraph.cellsFull_of_four_of_smallCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (smallConstant : system.SmallProperCutEquation)
    (carrierLarge : 4 ≤ system.carrier.length) :
    ∀ cell, cell ∈ system.cells -> cell.footprint = system.carrier := by
  intro cell cellMember
  by_cases cellFull : cell.footprint = system.carrier
  · exact cellFull
  · have footprintZero :=
      system.properFootprintWeight_eq_zero_of_four_of_smallCuts
        smallConstant carrierLarge cell.footprint
        (system.footprintSublist cell cellMember)
        (system.footprintLarge cell cellMember) cellFull
    have massBound := system.cellMass_le_footprintWeight cell cellMember
    have massPositive := system.massPositive cell cellMember
    omega

private theorem TerminalV53Hypergraph.cellsFull_of_carrierLengthTwo_smallCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (carrierLength : system.carrier.length = 2) :
    ∀ cell, cell ∈ system.cells -> cell.footprint = system.carrier := by
  intro cell cellMember
  have footprintSublist := system.footprintSublist cell cellMember
  apply footprintSublist.eq_of_length
  have footprintBound := footprintSublist.length_le
  have footprintLarge := system.footprintLarge cell cellMember
  omega

/-- The small-cut equation constructs M199's exact canonical shape basis. -/
theorem TerminalV53Hypergraph.canonicalConstantCutBasis_of_smallProperCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (carrierAtLeastTwo : 2 ≤ system.carrier.length)
    (smallConstant : system.SmallProperCutEquation) :
    system.CanonicalConstantCutBasis := by
  cases carrierEquation : system.carrier with
  | nil => simp [carrierEquation] at carrierAtLeastTwo
  | cons first tail =>
    cases tail with
    | nil => simp [carrierEquation] at carrierAtLeastTwo
    | cons second tail =>
      cases tail with
      | nil =>
        have cellsFull := system.cellsFull_of_carrierLengthTwo_smallCuts
          (by simp [carrierEquation])
        have fullWeight :=
          system.fullWeight_eq_cutValue_of_cellsFull_of_smallCuts
            smallConstant carrierAtLeastTwo cellsFull
        simpa [TerminalV53Hypergraph.CanonicalConstantCutBasis,
          carrierEquation] using fullWeight
      | cons third tail =>
        cases tail with
        | nil =>
          have firstProper : system.ProperCut [first] := by
            unfold TerminalV53Hypergraph.ProperCut
            rw [carrierEquation]
            simp
          have secondProper : system.ProperCut [second] := by
            unfold TerminalV53Hypergraph.ProperCut
            rw [carrierEquation]
            simp
          have thirdProper : system.ProperCut [third] := by
            unfold TerminalV53Hypergraph.ProperCut
            rw [carrierEquation]
            simp
          have singletonCuts :
              system.cutWeight [first] = system.cutValue ∧
              system.cutWeight [second] = system.cutValue ∧
              system.cutWeight [third] = system.cutValue :=
            ⟨smallConstant [first] firstProper (by simp),
              smallConstant [second] secondProper (by simp),
              smallConstant [third] thirdProper (by simp)⟩
          simpa [TerminalV53Hypergraph.CanonicalConstantCutBasis,
            carrierEquation] using singletonCuts
        | cons fourth rest =>
          have carrierLarge : 4 ≤ system.carrier.length := by
            simp [carrierEquation]
          have cellsFull :=
            system.cellsFull_of_four_of_smallCuts smallConstant carrierLarge
          have fullWeight :=
            system.fullWeight_eq_cutValue_of_cellsFull_of_smallCuts
              smallConstant (by omega) cellsFull
          have largeBasis :
              (∀ cell, cell ∈ system.cells ->
                cell.footprint = system.carrier) ∧
              system.footprintWeight system.carrier = system.cutValue :=
            ⟨cellsFull, fullWeight⟩
          simpa [TerminalV53Hypergraph.CanonicalConstantCutBasis,
            carrierEquation] using largeBasis

/-- Singleton/pair equations are exactly equivalent to the complete V53
    proper-cut equation once the carrier has at least two anchors. -/
theorem terminalV53_smallProperCutEquation_iff_constantProperCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (carrierAtLeastTwo : 2 ≤ system.carrier.length) :
    system.SmallProperCutEquation ↔ system.ConstantProperCuts := by
  constructor
  · intro smallConstant
    exact (terminalV53_canonicalConstantCutBasis_iff_constantProperCuts
      system carrierAtLeastTwo).1
        (system.canonicalConstantCutBasis_of_smallProperCuts
          carrierAtLeastTwo smallConstant)
  · intro constant cut proper _small
    exact constant cut proper

/-! ## Total first-mismatch classifier -/

/-- First canonical singleton/pair proper cut whose weight misses the declared
    constant. -/
def firstTerminalV53SmallProperCutMismatch?
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) : Option (List Atom) :=
  system.smallProperCuts.find? fun cut =>
    decide (system.cutWeight cut ≠ system.cutValue)

theorem firstTerminalV53SmallProperCutMismatch?_sound
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) (cut : List Atom)
    (found : firstTerminalV53SmallProperCutMismatch? system = some cut) :
    (system.ProperCut cut ∧ cut.length ≤ 2) ∧
      system.cutWeight cut ≠ system.cutValue := by
  have member : cut ∈ system.smallProperCuts :=
    List.mem_of_find?_eq_some found
  have expanded : system.smallProperCuts.find? (fun candidateCut =>
      decide (system.cutWeight candidateCut ≠ system.cutValue)) =
      some cut := by
    simpa only [firstTerminalV53SmallProperCutMismatch?] using found
  have mismatchChecked : decide
      (system.cutWeight cut ≠ system.cutValue) = true :=
    @List.find?_some (List Atom)
      (fun candidateCut =>
        decide (system.cutWeight candidateCut ≠ system.cutValue))
      cut system.smallProperCuts expanded
  exact ⟨(system.mem_smallProperCuts_iff cut).1 member,
    of_decide_eq_true mismatchChecked⟩

theorem firstTerminalV53SmallProperCutMismatch?_eq_none_all
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom)
    (noneFound : firstTerminalV53SmallProperCutMismatch? system = none) :
    ∀ cut, cut ∈ system.smallProperCuts ->
      system.cutWeight cut = system.cutValue := by
  intro cut member
  by_cases weightMatches : system.cutWeight cut = system.cutValue
  · exact weightMatches
  · have mismatchChecked : decide
        (system.cutWeight cut ≠ system.cutValue) = true :=
      decide_eq_true weightMatches
    have someMismatch :
        (firstTerminalV53SmallProperCutMismatch? system).isSome = true :=
      (List.find?_isSome).mpr ⟨cut, member, mismatchChecked⟩
    rw [noneFound] at someMismatch
    exact Bool.noConfusion someMismatch

/-- Proof-bearing exact small-cut mismatch. -/
structure TerminalV53SmallProperCutMismatch
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) where
  cut : List Atom
  proper : system.ProperCut cut
  length_le_two : cut.length ≤ 2
  mismatch : system.cutWeight cut ≠ system.cutValue

/-- Total classifier outcome.  Small carriers are retained as an explicit
    structural route; every carrier of size at least two is either fully
    coherent or has one exact singleton/pair mismatch. -/
inductive TerminalV53SmallProperCutClassification
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) where
  | insufficient (carrierSmall : system.carrier.length < 2)
  | coherent (constant : system.ConstantProperCuts)
  | routed (route : TerminalV53SmallProperCutMismatch system)

def classifyTerminalV53SmallProperCuts
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) :
    TerminalV53SmallProperCutClassification system := by
  by_cases carrierAtLeastTwo : 2 ≤ system.carrier.length
  · match found : firstTerminalV53SmallProperCutMismatch? system with
    | some cut =>
        have sound :=
          firstTerminalV53SmallProperCutMismatch?_sound system cut found
        exact .routed
          { cut := cut
            proper := sound.1.1
            length_le_two := sound.1.2
            mismatch := sound.2 }
    | none =>
        have listEquation :=
          firstTerminalV53SmallProperCutMismatch?_eq_none_all system found
        have smallConstant :=
          (system.smallProperCutEquation_iff_list).2 listEquation
        exact .coherent
          ((terminalV53_smallProperCutEquation_iff_constantProperCuts
            system carrierAtLeastTwo).1 smallConstant)
  · exact .insufficient (by omega)

/-- Every arbitrary finite sparse system receives one proof-bearing result. -/
theorem classifyTerminalV53SmallProperCuts_exhaustive
    {Atom : Type} [DecidableEq Atom]
    (system : TerminalV53Hypergraph Atom) :
    Nonempty (TerminalV53SmallProperCutClassification system) :=
  ⟨classifyTerminalV53SmallProperCuts system⟩

end DirectWire
end PNP
