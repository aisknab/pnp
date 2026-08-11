/-
Copyright (c) 2026 PNP Labs.

Constructive finite reconstruction of the pinned manuscript's BN6 bridge from
V54 consumer systems to V53 constant-cut hypergraph rigidity.  An arbitrary
finite family of already-grouped positive residual cells retains one verified
minimal-consumer system and a nonempty list of payload-bearing atoms per exact
singleton footprint.  V54 identifies each cell's two-sided activation with
crossing of that footprint.  The family therefore constructs the sparse
nonnegative hypergraph consumed by V53, with the same cut sum.

The named theorem returns every cardinality branch without fixing the anchor
carrier: a positive pair packet at two anchors; the complete possibly mixed
balanced-triple/full-span alternative at three anchors; or a positive full-span
packet with every proper footprint zero at four or more anchors.  Every positive
packet footprint has an original payload-bearing atom witness.

The family, its exact grouping, its PkgC singletonization proofs, its positive
atom ledger, and the BCEL constant-cut equation remain explicit inputs.  This
does not construct PkgC or derive the family from a terminal candidate, complete
the Packet selector universe or realizer routes, establish polynomial runtime,
prove ZeroSlack or PCCMin, put SAT in P, or prove P = NP.
-/

import PNP.ResidualTerminalConstantCutHypergraphRigidity

namespace PNP
namespace DirectWire

/-! ## Payload-bearing grouped residual cells -/

/-- A consumer presentation containing only singleton consumers satisfies the
    exact PkgC premise consumed by V54.  Disjointness is still checked by the
    premise, but no listed consumer can carry a hidden nonsingleton footprint. -/
theorem terminalBN6_disjointPairsSingletonized_of_all_singletons
    {Atom : Type} (system : TerminalV54ConsumerSystem Atom)
    (allSingletons : ∀ consumer, consumer ∈ system.consumers ->
      ∃ atom, consumer = [atom]) :
    system.DisjointPairsSingletonized := by
  intro left leftMember right rightMember _disjoint
  obtain ⟨leftAtom, leftEquation⟩ := allSingletons left leftMember
  obtain ⟨rightAtom, rightEquation⟩ := allSingletons right rightMember
  exact ⟨leftAtom, rightAtom, leftEquation, rightEquation⟩

/-- One positive residual atom retained by a grouped BN6 cell. -/
structure TerminalBN6PayloadAtom (Payload : Type) where
  mass : Nat
  massPositive : 0 < mass
  payload : Payload

/-- One exact footprint group.  The consumer system and the singletonization
    proof are the checked V54 input; `atoms` retains concrete selector payloads
    and their positive integer masses. -/
structure TerminalBN6GroupedCell (Atom Payload : Type) where
  consumerSystem : TerminalV54ConsumerSystem Atom
  singletonized : consumerSystem.DisjointPairsSingletonized
  atoms : List (TerminalBN6PayloadAtom Payload)
  atomsNonempty : atoms ≠ []

/-- Exact grouped mass, defined rather than trusted as an independent field. -/
def TerminalBN6GroupedCell.mass
    {Atom Payload : Type} (cell : TerminalBN6GroupedCell Atom Payload) : Nat :=
  (cell.atoms.map TerminalBN6PayloadAtom.mass).sum

theorem TerminalBN6GroupedCell.massPositive
    {Atom Payload : Type} (cell : TerminalBN6GroupedCell Atom Payload) :
    0 < cell.mass := by
  cases atomsEquation : cell.atoms with
  | nil =>
      exact False.elim (cell.atomsNonempty atomsEquation)
  | cons head tail =>
      unfold TerminalBN6GroupedCell.mass
      rw [atomsEquation]
      simp only [List.map, List.sum_cons]
      have headPositive := head.massPositive
      omega

/-- V54's exact singleton footprint for this grouped residual cell. -/
def TerminalBN6GroupedCell.footprint
    {Atom Payload : Type} [DecidableEq Atom]
    (cell : TerminalBN6GroupedCell Atom Payload) : List Atom :=
  cell.consumerSystem.singletonFootprint

/-- The sparse positive V53 hyperedge represented by one grouped cell. -/
def TerminalBN6GroupedCell.toHyperedge
    {Atom Payload : Type} [DecidableEq Atom]
    (cell : TerminalBN6GroupedCell Atom Payload) :
    TerminalV53Hyperedge Atom :=
  { footprint := cell.footprint, mass := cell.mass }

/-- Crossing of the V54 singleton footprint is exactly crossing of the V53
    hyperedge. -/
theorem TerminalBN6GroupedCell.crosses_iff_footprintCrosses
    {Atom Payload : Type} [DecidableEq Atom]
    (cell : TerminalBN6GroupedCell Atom Payload)
    (cut : List Atom) :
    cell.toHyperedge.Crosses cut ↔
      cell.consumerSystem.FootprintCrossesCut cut := by
  constructor
  · rintro ⟨⟨leftAtom, leftFootprint, leftCut⟩,
      ⟨rightAtom, rightFootprint, rightNotCut⟩⟩
    have rightCarrier : rightAtom ∈ cell.consumerSystem.carrier :=
      (cell.consumerSystem.mem_singletonFootprint_iff rightAtom).1
        rightFootprint |>.1
    refine ⟨leftAtom, leftFootprint, leftCut,
      rightAtom, rightFootprint, ?_⟩
    exact (mem_terminalV54Complement_iff
      cell.consumerSystem.carrier cut rightAtom).2
        ⟨rightCarrier, rightNotCut⟩
  · rintro ⟨leftAtom, leftFootprint, leftCut,
      rightAtom, rightFootprint, rightComplement⟩
    have rightNotCut : rightAtom ∉ cut :=
      (mem_terminalV54Complement_iff
        cell.consumerSystem.carrier cut rightAtom).1
          rightComplement |>.2
    exact ⟨⟨leftAtom, leftFootprint, leftCut⟩,
      ⟨rightAtom, rightFootprint, rightNotCut⟩⟩

theorem TerminalBN6GroupedCell.crossesBool_eq_cutIndicatorBool
    {Atom Payload : Type} [DecidableEq Atom]
    (cell : TerminalBN6GroupedCell Atom Payload)
    (cut : List Atom) :
    cell.toHyperedge.crossesBool cut =
      cell.consumerSystem.cutIndicatorBool cut := by
  have equalTrue :
      cell.toHyperedge.crossesBool cut = true ↔
        cell.consumerSystem.cutIndicatorBool cut = true := by
    rw [cell.toHyperedge.crossesBool_eq_true_iff,
      cell.consumerSystem.cutIndicatorBool_eq_true_iff]
    exact cell.crosses_iff_footprintCrosses cut
  cases edgeValue : cell.toHyperedge.crossesBool cut <;>
    cases indicatorValue : cell.consumerSystem.cutIndicatorBool cut <;>
      simp_all

/-- V54 plus the checked PkgC singletonization premise identifies the exact
    activation bit used by BN4/BN5 with the V53 crossing bit. -/
theorem TerminalBN6GroupedCell.crossesBool_eq_cutActivationBool
    {Atom Payload : Type} [DecidableEq Atom]
    (cell : TerminalBN6GroupedCell Atom Payload)
    (cut : List Atom) :
    cell.toHyperedge.crossesBool cut =
      cell.consumerSystem.cutActivationBool cut := by
  calc
    cell.toHyperedge.crossesBool cut =
        cell.consumerSystem.cutIndicatorBool cut :=
      cell.crossesBool_eq_cutIndicatorBool cut
    _ = cell.consumerSystem.cutActivationBool cut :=
      (terminalV54_consumerAntichain_normal_form
        cell.consumerSystem cell.singletonized cut).symm

/-! ## The constructed BN6 hypergraph -/

/-- Arbitrary finite already-grouped surviving residual cells over one common
    anchor carrier.  Unique footprints verify that grouping is exact at the
    interface; no anchor cardinality is fixed. -/
structure TerminalBN6GroupedFamily
    (Atom Payload : Type) [DecidableEq Atom] where
  carrier : List Atom
  carrierNodup : carrier.Nodup
  groups : List (TerminalBN6GroupedCell Atom Payload)
  groupCarrier : ∀ cell, cell ∈ groups ->
    cell.consumerSystem.carrier = carrier
  groupFootprintLarge : ∀ cell, cell ∈ groups ->
    2 ≤ cell.footprint.length
  groupFootprintsNodup : (groups.map
    TerminalBN6GroupedCell.footprint).Nodup
  cutValue : Nat
  cutValuePositive : 0 < cutValue

/-- Sum of the grouped positive masses whose original V54 requests activate on
    this cut. -/
def TerminalBN6GroupedFamily.activationWeight
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (cut : List Atom) : Nat :=
  (family.groups.map fun cell =>
    if cell.consumerSystem.cutActivationBool cut then cell.mass else 0).sum

/-- The BCEL-ready constant-cut premise, still explicit at this bounded
    reconstruction edge. -/
def TerminalBN6GroupedFamily.ConstantActivation
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) : Prop :=
  ∀ cut, cut.Sublist family.carrier -> cut ≠ [] ->
    cut ≠ family.carrier ->
      family.activationWeight cut = family.cutValue

/-- The exact sparse nonnegative hypergraph mechanically obtained from the
    grouped cells. -/
def TerminalBN6GroupedFamily.hypergraph
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) :
    TerminalV53Hypergraph Atom where
  carrier := family.carrier
  carrierNodup := family.carrierNodup
  cells := family.groups.map TerminalBN6GroupedCell.toHyperedge
  footprintsNodup := by
    rw [List.map_map]
    change (family.groups.map TerminalBN6GroupedCell.footprint).Nodup
    exact family.groupFootprintsNodup
  footprintSublist := by
    intro edge edgeMember
    simp only [List.mem_map] at edgeMember
    obtain ⟨cell, cellMember, edgeEquation⟩ := edgeMember
    subst edge
    have footprintSublist :
        cell.footprint.Sublist cell.consumerSystem.carrier := by
      unfold TerminalBN6GroupedCell.footprint
        TerminalV54ConsumerSystem.singletonFootprint
      exact List.filter_sublist
    rw [family.groupCarrier cell cellMember] at footprintSublist
    exact footprintSublist
  footprintLarge := by
    intro edge edgeMember
    simp only [List.mem_map] at edgeMember
    obtain ⟨cell, cellMember, edgeEquation⟩ := edgeMember
    subst edge
    exact family.groupFootprintLarge cell cellMember
  massPositive := by
    intro edge edgeMember
    simp only [List.mem_map] at edgeMember
    obtain ⟨cell, _cellMember, edgeEquation⟩ := edgeMember
    subst edge
    exact cell.massPositive
  cutValue := family.cutValue
  cutValuePositive := family.cutValuePositive

/-- The constructed V53 cut sum is exactly the original sum of V54 activation
    masses, cell by cell. -/
theorem TerminalBN6GroupedFamily.cutWeight_eq_activationWeight
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (cut : List Atom) :
    family.hypergraph.cutWeight cut = family.activationWeight cut := by
  unfold TerminalV53Hypergraph.cutWeight
    TerminalBN6GroupedFamily.activationWeight
    TerminalBN6GroupedFamily.hypergraph
  rw [List.map_map]
  apply terminalV53_sum_congr
  intro cell _cellMember
  change (if cell.toHyperedge.crossesBool cut then cell.toHyperedge.mass else 0) =
    if cell.consumerSystem.cutActivationBool cut then cell.mass else 0
  rw [cell.crossesBool_eq_cutActivationBool cut]
  rfl

/-- Therefore a BCEL activation equation supplies exactly V53's constant-cut
    hypothesis, without sampling or enumerating a fixed carrier. -/
theorem TerminalBN6GroupedFamily.constantProperCuts
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (constant : family.ConstantActivation) :
    family.hypergraph.ConstantProperCuts := by
  intro cut proper
  rw [family.cutWeight_eq_activationWeight cut]
  exact constant cut proper.1 proper.2.1 proper.2.2

/-! ## Payload preservation -/

/-- A grouped footprint retains at least one original payload-bearing atom. -/
def TerminalBN6GroupedFamily.HasPayloadAt
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom) : Prop :=
  ∃ cell, cell ∈ family.groups ∧ cell.footprint = footprint ∧
    ∃ atom, atom ∈ cell.atoms

private theorem terminalBN6_exists_positive_term
    {alpha : Type} (items : List alpha) (value : alpha -> Nat)
    (positive : 0 < (items.map value).sum) :
    ∃ item, item ∈ items ∧ 0 < value item := by
  induction items with
  | nil => simp at positive
  | cons head tail ih =>
      simp only [List.map, List.sum_cons] at positive
      by_cases headPositive : 0 < value head
      · exact ⟨head, by simp, headPositive⟩
      · have headZero : value head = 0 := by omega
        have tailPositive : 0 < (tail.map value).sum := by omega
        obtain ⟨item, itemMember, itemPositive⟩ := ih tailPositive
        exact ⟨item, by simp [itemMember], itemPositive⟩

theorem TerminalBN6GroupedFamily.footprintWeight_eq_groupedMass
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom) :
    family.hypergraph.footprintWeight footprint =
      (family.groups.map fun cell =>
        if cell.footprint = footprint then cell.mass else 0).sum := by
  unfold TerminalV53Hypergraph.footprintWeight
    TerminalBN6GroupedFamily.hypergraph
  rw [List.map_map]
  apply terminalV53_sum_congr
  intro cell _cellMember
  rfl

/-- Positive grouped footprint mass cannot be detached from concrete payload
    data. -/
theorem TerminalBN6GroupedFamily.hasPayloadAt_of_footprintWeight_positive
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom)
    (positive : 0 < family.hypergraph.footprintWeight footprint) :
    family.HasPayloadAt footprint := by
  rw [family.footprintWeight_eq_groupedMass footprint] at positive
  obtain ⟨cell, cellMember, contributionPositive⟩ :=
    terminalBN6_exists_positive_term family.groups
      (fun cell => if cell.footprint = footprint then cell.mass else 0)
      positive
  by_cases footprintEqual : cell.footprint = footprint
  · cases atomsEquation : cell.atoms with
    | nil => exact False.elim (cell.atomsNonempty atomsEquation)
    | cons head tail =>
        exact ⟨cell, cellMember, footprintEqual,
          head, by simp [atomsEquation]⟩
  · simp [footprintEqual] at contributionPositive

/-! ## Exact packet classification -/

/-- The complete finite BN6 conclusion.  The three-anchor constructor exposes
    both conditional packet witnesses, so a mixed balanced-triple/full-span
    system is represented without choosing one branch and forgetting the
    other. -/
inductive TerminalBN6PacketConclusion
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) : Prop where
  | pair
      (carrierLength : family.carrier.length = 2)
      (fullWeight : family.hypergraph.footprintWeight family.carrier =
        family.cutValue)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (payload : family.HasPayloadAt family.carrier) :
      TerminalBN6PacketConclusion family
  | balancedTripleOrFullSpan
      (carrierLength : family.carrier.length = 3)
      (pairMass : Nat)
      (everyPair : ∀ footprint, footprint.Sublist family.carrier ->
        footprint.length = 2 ->
          family.hypergraph.footprintWeight footprint = pairMass)
      (massEquation :
        family.hypergraph.footprintWeight family.carrier +
          2 * pairMass = family.cutValue)
      (positiveAlternative :
        0 < pairMass ∨
          0 < family.hypergraph.footprintWeight family.carrier)
      (balancedPayloads : 0 < pairMass ->
        ∀ footprint, footprint.Sublist family.carrier ->
          footprint.length = 2 -> family.HasPayloadAt footprint)
      (fullSpanPayload :
        0 < family.hypergraph.footprintWeight family.carrier ->
          family.HasPayloadAt family.carrier) :
      TerminalBN6PacketConclusion family
  | fullSpan
      (carrierLarge : 4 ≤ family.carrier.length)
      (properFootprintsZero :
        ∀ footprint, footprint.Sublist family.carrier ->
          2 ≤ footprint.length -> footprint ≠ family.carrier ->
          family.hypergraph.footprintWeight footprint = 0)
      (fullWeight : family.hypergraph.footprintWeight family.carrier =
        family.cutValue)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (payload : family.HasPayloadAt family.carrier) :
      TerminalBN6PacketConclusion family

/-- Manuscript BN6, `hypergraph cellization and packet collapse`, over an
    arbitrary finite grouped survivor family.  V54 supplies exact hyperedge
    indicators, V53 exhausts all anchor-cardinality branches, and positive
    packet mass always retains an atom payload witness. -/
theorem terminalBN6_hypergraph_packet
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (carrierAtLeastTwo : 2 ≤ family.carrier.length)
    (constant : family.ConstantActivation) :
    TerminalBN6PacketConclusion family := by
  have hypergraphConstant := family.constantProperCuts constant
  have rigidity := terminalV53_constantCut_hypergraph_rigidity
    family.hypergraph carrierAtLeastTwo hypergraphConstant
  by_cases twoAnchors : family.carrier.length = 2
  · have fullWeightRaw := rigidity.1 twoAnchors
    have fullWeight :
        family.hypergraph.footprintWeight family.carrier =
          family.cutValue := by
      simpa only [TerminalBN6GroupedFamily.hypergraph] using fullWeightRaw
    have fullPositive :
        0 < family.hypergraph.footprintWeight family.carrier := by
      rw [fullWeight]
      exact family.cutValuePositive
    exact TerminalBN6PacketConclusion.pair twoAnchors fullWeight
      fullPositive
      (family.hasPayloadAt_of_footprintWeight_positive family.carrier
        fullPositive)
  · by_cases threeAnchors : family.carrier.length = 3
    · obtain ⟨pairMass, everyPair, massEquation⟩ :=
        rigidity.2.1 threeAnchors
      change family.hypergraph.footprintWeight family.carrier +
        2 * pairMass = family.cutValue at massEquation
      have positiveAlternative :
          0 < pairMass ∨
            0 < family.hypergraph.footprintWeight family.carrier := by
        by_cases pairPositive : 0 < pairMass
        · exact Or.inl pairPositive
        · have pairZero : pairMass = 0 := by omega
          apply Or.inr
          rw [pairZero] at massEquation
          simp only [Nat.mul_zero, Nat.add_zero] at massEquation
          rw [massEquation]
          exact family.cutValuePositive
      have balancedPayloads : 0 < pairMass ->
          ∀ footprint, footprint.Sublist family.carrier ->
            footprint.length = 2 -> family.HasPayloadAt footprint := by
        intro pairPositive footprint footprintSublist footprintLength
        apply family.hasPayloadAt_of_footprintWeight_positive footprint
        rw [everyPair footprint footprintSublist footprintLength]
        exact pairPositive
      have fullSpanPayload :
          0 < family.hypergraph.footprintWeight family.carrier ->
            family.HasPayloadAt family.carrier :=
        family.hasPayloadAt_of_footprintWeight_positive family.carrier
      exact TerminalBN6PacketConclusion.balancedTripleOrFullSpan
        threeAnchors pairMass everyPair massEquation positiveAlternative
        balancedPayloads fullSpanPayload
    · have carrierLarge : 4 ≤ family.carrier.length := by omega
      obtain ⟨properFootprintsZero, fullWeight⟩ :=
        rigidity.2.2 carrierLarge
      change family.hypergraph.footprintWeight family.carrier =
        family.cutValue at fullWeight
      have fullPositive :
          0 < family.hypergraph.footprintWeight family.carrier := by
        rw [fullWeight]
        exact family.cutValuePositive
      exact TerminalBN6PacketConclusion.fullSpan carrierLarge
        properFootprintsZero fullWeight fullPositive
        (family.hasPayloadAt_of_footprintWeight_positive family.carrier
          fullPositive)

end DirectWire
end PNP
