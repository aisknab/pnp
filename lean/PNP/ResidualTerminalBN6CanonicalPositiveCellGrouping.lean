/-
Copyright (c) 2026 PNP Labs.

Constructive canonical grouping for the finite positive cells consumed by BN6.
Each raw cell supplies one support list and one strictly positive payload atom.
The support is normalized by filtering the common duplicate-free carrier, so
its footprint is an ordered carrier sublist. The constructor builds the V54
consumer system from the footprint's singleton consumers, coalesces equal
footprints, and retains every payload atom in the unique resulting group.

This removes supplied consumer systems, singletonization certificates, and
grouping proofs. The raw supports and payloads remain explicit inputs. It does
not derive those cells from PkgC or terminal data, establish the remaining
constant-activation equation, prove polynomial bounds for the complete route,
ZeroSlack, PCCMin, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalBN6HypergraphPacket

namespace PNP
namespace DirectWire

/-! ## Carrier-normalized positive cells -/

/-- Normalize one raw support into the common carrier order. -/
def terminalBN6NormalizeSupport
    {Atom : Type} [DecidableEq Atom]
    (carrier support : List Atom) : List Atom :=
  carrier.filter fun atom => decide (atom ∈ support)

theorem terminalBN6NormalizeSupport_sublist
    {Atom : Type} [DecidableEq Atom]
    (carrier support : List Atom) :
    (terminalBN6NormalizeSupport carrier support).Sublist carrier :=
  List.filter_sublist

theorem terminalBN6NormalizeSupport_nodup
    {Atom : Type} [DecidableEq Atom]
    {carrier : List Atom} (carrierNodup : carrier.Nodup)
    (support : List Atom) :
    (terminalBN6NormalizeSupport carrier support).Nodup :=
  (terminalBN6NormalizeSupport_sublist carrier support).nodup carrierNodup

/-- One ungrouped positive payload cell. The support is raw data; its exact
    BN6 footprint is computed in the common carrier order. -/
structure TerminalBN6PositiveCell
    (Atom Payload : Type) [DecidableEq Atom]
    (carrier : List Atom) where
  support : List Atom
  payloadAtom : TerminalBN6PayloadAtom Payload
  footprintLarge :
    2 ≤ (terminalBN6NormalizeSupport carrier support).length

def TerminalBN6PositiveCell.footprint
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalBN6PositiveCell Atom Payload carrier) : List Atom :=
  terminalBN6NormalizeSupport carrier cell.support

theorem TerminalBN6PositiveCell.footprint_sublist
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalBN6PositiveCell Atom Payload carrier) :
    cell.footprint.Sublist carrier :=
  terminalBN6NormalizeSupport_sublist carrier cell.support

theorem TerminalBN6PositiveCell.footprint_nodup
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom} (carrierNodup : carrier.Nodup)
    (cell : TerminalBN6PositiveCell Atom Payload carrier) :
    cell.footprint.Nodup :=
  cell.footprint_sublist.nodup carrierNodup

/-! ## Canonical singleton-consumer systems -/

private theorem terminalBN6_nodup_map_injective
    {alpha beta : Type} (mapping : alpha → beta)
    (injective : Function.Injective mapping)
    {items : List alpha} (distinct : items.Nodup) :
    (items.map mapping).Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      have split := List.nodup_cons.mp distinct
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨item, itemMember, equal⟩ := List.mem_map.mp member
        exact split.1 (injective equal.symm ▸ itemMember)
      · exact ih split.2

private theorem terminalBN6_filter_membership_eq_sublist
    {Atom : Type} [DecidableEq Atom]
    {footprint carrier : List Atom}
    (footprintSublist : footprint.Sublist carrier)
    (carrierNodup : carrier.Nodup) :
    carrier.filter (fun atom => decide (atom ∈ footprint)) = footprint := by
  induction footprintSublist with
  | slnil => simp
  | @cons footprint carrierTail head tailSublist ih =>
      simp only [List.nodup_cons] at carrierNodup
      obtain ⟨headNotTail, tailNodup⟩ := carrierNodup
      have headNotFootprint : head ∉ footprint := by
        intro headFootprint
        exact headNotTail (tailSublist.subset headFootprint)
      simp only [List.filter_cons]
      have headRejected : decide (head ∈ footprint) = false := by
        simp [headNotFootprint]
      rw [headRejected]
      exact ih tailNodup
  | @cons_cons footprint carrierTail head tailSublist ih =>
      simp only [List.nodup_cons] at carrierNodup
      obtain ⟨headNotTail, tailNodup⟩ := carrierNodup
      have tailFilter :
          carrierTail.filter (fun atom => decide (atom ∈ head :: footprint)) =
            carrierTail.filter (fun atom => decide (atom ∈ footprint)) := by
        apply terminalV53_filter_congr
        intro atom atomTail
        have atomNotHead : atom ≠ head := by
          intro atomHead
          subst atom
          exact headNotTail atomTail
        simp [atomNotHead]
      simp only [List.filter_cons]
      have headAccepted : decide (head ∈ head :: footprint) = true := by simp
      rw [headAccepted]
      simp only [if_true]
      rw [tailFilter, ih tailNodup]

/-- The V54 consumer system canonically associated with one ordered footprint:
    its minimal consumers are exactly the footprint singletons. -/
def terminalBN6SingletonConsumerSystem
    {Atom : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (footprint : List Atom) (footprintSublist : footprint.Sublist carrier)
    (footprintNodup : footprint.Nodup) :
    TerminalV54ConsumerSystem Atom where
  carrier := carrier
  carrierNodup := carrierNodup
  consumers := footprint.map fun atom => [atom]
  consumersNodup := terminalBN6_nodup_map_injective
    (fun atom => [atom]) (by
      intro left right equal
      exact List.cons.inj equal |>.1) footprintNodup
  consumerNodup := by
    intro consumer consumerMember
    obtain ⟨atom, _atomMember, atomEquation⟩ :=
      List.mem_map.mp consumerMember
    subst consumer
    simp
  consumerNonempty := by
    intro consumer consumerMember
    obtain ⟨atom, _atomMember, atomEquation⟩ :=
      List.mem_map.mp consumerMember
    subst consumer
    simp
  consumerContained := by
    intro consumer consumerMember
    obtain ⟨atom, atomMember, atomEquation⟩ :=
      List.mem_map.mp consumerMember
    subst consumer
    intro item itemMember
    have itemEqual : item = atom := by simpa using itemMember
    subst item
    exact footprintSublist.subset atomMember
  consumerAntichain := by
    intro left leftMember right rightMember included
    obtain ⟨leftAtom, _leftAtomMember, leftEquation⟩ :=
      List.mem_map.mp leftMember
    obtain ⟨rightAtom, _rightAtomMember, rightEquation⟩ :=
      List.mem_map.mp rightMember
    subst left
    subst right
    have leftInRight : leftAtom ∈ [rightAtom] := included leftAtom (by simp)
    have atomEqual : leftAtom = rightAtom := by simpa using leftInRight
    rw [atomEqual]

/-- The singleton consumers recover exactly the ordered input footprint. -/
theorem terminalBN6SingletonConsumerSystem_singletonFootprint
    {Atom : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (footprint : List Atom) (footprintSublist : footprint.Sublist carrier)
    (footprintNodup : footprint.Nodup) :
    (terminalBN6SingletonConsumerSystem carrier carrierNodup footprint
      footprintSublist footprintNodup).singletonFootprint = footprint := by
  unfold TerminalV54ConsumerSystem.singletonFootprint
  change
    carrier.filter
        (fun atom => decide ([atom] ∈ footprint.map (fun item => [item]))) =
      footprint
  have normalized :
      carrier.filter
          (fun atom => decide ([atom] ∈ footprint.map (fun item => [item]))) =
        carrier.filter (fun atom => decide (atom ∈ footprint)) := by
    apply terminalV53_filter_congr
    intro atom _atomCarrier
    simp
  rw [normalized]
  exact terminalBN6_filter_membership_eq_sublist footprintSublist carrierNodup

theorem terminalBN6SingletonConsumerSystem_singletonized
    {Atom : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (footprint : List Atom) (footprintSublist : footprint.Sublist carrier)
    (footprintNodup : footprint.Nodup) :
    (terminalBN6SingletonConsumerSystem carrier carrierNodup footprint
      footprintSublist footprintNodup).DisjointPairsSingletonized := by
  apply terminalBN6_disjointPairsSingletonized_of_all_singletons
  intro consumer consumerMember
  obtain ⟨atom, _atomMember, atomEquation⟩ :=
    List.mem_map.mp consumerMember
  exact ⟨atom, atomEquation.symm⟩

/-! ## Duplicate-free footprint universe and grouped payloads -/

/-- Duplicate-free last-occurrence footprint order from a raw positive ledger. -/
def terminalBN6CanonicalPositiveFootprints
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier)) :
    List (List Atom) :=
  match cells with
  | [] => []
  | cell :: tail =>
      let tailFootprints :=
        terminalBN6CanonicalPositiveFootprints carrier tail
      if cell.footprint ∈ tailFootprints then
        tailFootprints
      else
        cell.footprint :: tailFootprints

theorem terminalBN6CanonicalPositiveFootprints_nodup
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier)) :
    (terminalBN6CanonicalPositiveFootprints carrier cells).Nodup := by
  induction cells with
  | nil => simp [terminalBN6CanonicalPositiveFootprints]
  | cons cell tail ih =>
      simp only [terminalBN6CanonicalPositiveFootprints]
      split
      · exact ih
      · exact List.nodup_cons.2 ⟨by assumption, ih⟩

theorem mem_terminalBN6CanonicalPositiveFootprints_iff
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier))
    (footprint : List Atom) :
    footprint ∈ terminalBN6CanonicalPositiveFootprints carrier cells ↔
      ∃ cell, cell ∈ cells ∧ cell.footprint = footprint := by
  induction cells with
  | nil => simp [terminalBN6CanonicalPositiveFootprints]
  | cons cell tail ih =>
      simp only [terminalBN6CanonicalPositiveFootprints]
      split
      · rename_i headAlreadyPresent
        constructor
        · intro footprintMember
          obtain ⟨found, foundMember, foundFootprint⟩ := ih.1 footprintMember
          exact ⟨found, by simp [foundMember], foundFootprint⟩
        · rintro ⟨found, foundMember, foundFootprint⟩
          simp only [List.mem_cons] at foundMember
          cases foundMember with
          | inl foundHead =>
              subst found
              rw [foundFootprint] at headAlreadyPresent
              exact headAlreadyPresent
          | inr foundTail =>
              exact ih.2 ⟨found, foundTail, foundFootprint⟩
      · rename_i headFresh
        constructor
        · intro footprintMember
          simp only [List.mem_cons] at footprintMember
          cases footprintMember with
          | inl footprintHead =>
              exact ⟨cell, by simp, footprintHead.symm⟩
          | inr footprintTail =>
              obtain ⟨found, foundMember, foundFootprint⟩ :=
                ih.1 footprintTail
              exact ⟨found, by simp [foundMember], foundFootprint⟩
        · rintro ⟨found, foundMember, foundFootprint⟩
          simp only [List.mem_cons] at foundMember
          simp only [List.mem_cons]
          cases foundMember with
          | inl foundHead =>
              subst found
              exact Or.inl foundFootprint.symm
          | inr foundTail =>
              exact Or.inr (ih.2 ⟨found, foundTail, foundFootprint⟩)

/-- Collect every positive payload atom whose normalized support is one exact
    footprint. -/
def terminalBN6PositiveAtomsAt
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier))
    (footprint : List Atom) : List (TerminalBN6PayloadAtom Payload) :=
  match cells with
  | [] => []
  | cell :: tail =>
      if cell.footprint = footprint then
        cell.payloadAtom :: terminalBN6PositiveAtomsAt carrier tail footprint
      else
        terminalBN6PositiveAtomsAt carrier tail footprint

theorem TerminalBN6PositiveCell.payloadAtom_mem_positiveAtomsAt
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    {cells : List (TerminalBN6PositiveCell Atom Payload carrier)}
    (cell : TerminalBN6PositiveCell Atom Payload carrier)
    (cellMember : cell ∈ cells) :
    cell.payloadAtom ∈
      terminalBN6PositiveAtomsAt carrier cells cell.footprint := by
  induction cells with
  | nil => simp at cellMember
  | cons head tail ih =>
      simp only [List.mem_cons] at cellMember
      cases cellMember with
      | inl cellHead =>
          subst head
          simp [terminalBN6PositiveAtomsAt]
      | inr cellTail =>
          unfold terminalBN6PositiveAtomsAt
          split
          · simp [ih cellTail]
          · exact ih cellTail

/-- Build one group at a certified canonical footprint. All data fields are
    computed; the attached membership proof is used only for proof fields. -/
def terminalBN6CanonicalPositiveGroup
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier))
    (footprint : { value //
      value ∈ terminalBN6CanonicalPositiveFootprints carrier cells }) :
    TerminalBN6GroupedCell Atom Payload where
  consumerSystem := terminalBN6SingletonConsumerSystem
    carrier carrierNodup footprint.1
    (by
      obtain ⟨cell, _cellMember, cellFootprint⟩ :=
        (mem_terminalBN6CanonicalPositiveFootprints_iff
          carrier cells footprint.1).1 footprint.2
      rw [← cellFootprint]
      exact cell.footprint_sublist)
    (by
      obtain ⟨cell, _cellMember, cellFootprint⟩ :=
        (mem_terminalBN6CanonicalPositiveFootprints_iff
          carrier cells footprint.1).1 footprint.2
      rw [← cellFootprint]
      exact cell.footprint_nodup carrierNodup)
  singletonized := terminalBN6SingletonConsumerSystem_singletonized
    carrier carrierNodup footprint.1
    (by
      obtain ⟨cell, _cellMember, cellFootprint⟩ :=
        (mem_terminalBN6CanonicalPositiveFootprints_iff
          carrier cells footprint.1).1 footprint.2
      rw [← cellFootprint]
      exact cell.footprint_sublist)
    (by
      obtain ⟨cell, _cellMember, cellFootprint⟩ :=
        (mem_terminalBN6CanonicalPositiveFootprints_iff
          carrier cells footprint.1).1 footprint.2
      rw [← cellFootprint]
      exact cell.footprint_nodup carrierNodup)
  atoms := terminalBN6PositiveAtomsAt carrier cells footprint.1
  atomsNonempty := by
    obtain ⟨cell, cellMember, cellFootprint⟩ :=
      (mem_terminalBN6CanonicalPositiveFootprints_iff
        carrier cells footprint.1).1 footprint.2
    intro atomsEmpty
    have payloadMember := cell.payloadAtom_mem_positiveAtomsAt cellMember
    rw [cellFootprint, atomsEmpty] at payloadMember
    exact List.not_mem_nil payloadMember

theorem terminalBN6CanonicalPositiveGroup_carrier
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier))
    (footprint : { value //
      value ∈ terminalBN6CanonicalPositiveFootprints carrier cells }) :
    (terminalBN6CanonicalPositiveGroup carrier carrierNodup cells footprint).consumerSystem.carrier =
      carrier := rfl

theorem terminalBN6CanonicalPositiveGroup_footprint
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier))
    (footprint : { value //
      value ∈ terminalBN6CanonicalPositiveFootprints carrier cells }) :
    (terminalBN6CanonicalPositiveGroup carrier carrierNodup cells footprint).footprint =
      footprint.1 := by
  apply terminalBN6SingletonConsumerSystem_singletonFootprint
  · obtain ⟨cell, _cellMember, cellFootprint⟩ :=
      (mem_terminalBN6CanonicalPositiveFootprints_iff
        carrier cells footprint.1).1 footprint.2
    rw [← cellFootprint]
    exact cell.footprint_sublist
  · obtain ⟨cell, _cellMember, cellFootprint⟩ :=
      (mem_terminalBN6CanonicalPositiveFootprints_iff
        carrier cells footprint.1).1 footprint.2
    rw [← cellFootprint]
    exact cell.footprint_nodup carrierNodup

theorem terminalBN6CanonicalPositiveGroup_footprintLarge
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier))
    (footprint : { value //
      value ∈ terminalBN6CanonicalPositiveFootprints carrier cells }) :
    2 ≤ (terminalBN6CanonicalPositiveGroup carrier carrierNodup cells
      footprint).footprint.length := by
  rw [terminalBN6CanonicalPositiveGroup_footprint]
  obtain ⟨cell, _cellMember, cellFootprint⟩ :=
    (mem_terminalBN6CanonicalPositiveFootprints_iff
      carrier cells footprint.1).1 footprint.2
  rw [← cellFootprint]
  exact cell.footprintLarge

/-- The complete canonical grouped ledger. `List.attach` supplies each builder
    only its constructive membership proof; no representative is chosen. -/
def terminalBN6CanonicalPositiveGroups
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier)) :
    List (TerminalBN6GroupedCell Atom Payload) :=
  (terminalBN6CanonicalPositiveFootprints carrier cells).attach.map
    (terminalBN6CanonicalPositiveGroup carrier carrierNodup cells)

theorem terminalBN6CanonicalPositiveGroups_footprints
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier)) :
    (terminalBN6CanonicalPositiveGroups carrier carrierNodup cells).map
        TerminalBN6GroupedCell.footprint =
      terminalBN6CanonicalPositiveFootprints carrier cells := by
  unfold terminalBN6CanonicalPositiveGroups
  rw [List.map_map]
  calc
    _ = (terminalBN6CanonicalPositiveFootprints carrier cells).attach.map
        Subtype.val := by
      apply List.map_congr_left
      intro footprint _footprintMember
      exact terminalBN6CanonicalPositiveGroup_footprint
        carrier carrierNodup cells footprint
    _ = terminalBN6CanonicalPositiveFootprints carrier cells :=
      List.attach_map_subtype_val
        (terminalBN6CanonicalPositiveFootprints carrier cells)

theorem terminalBN6CanonicalPositiveGroups_footprintsNodup
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier)) :
    ((terminalBN6CanonicalPositiveGroups carrier carrierNodup cells).map
      TerminalBN6GroupedCell.footprint).Nodup := by
  rw [terminalBN6CanonicalPositiveGroups_footprints]
  exact terminalBN6CanonicalPositiveFootprints_nodup carrier cells

theorem terminalBN6CanonicalPositiveGroups_carrier
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier))
    (group : TerminalBN6GroupedCell Atom Payload)
    (groupMember : group ∈
      terminalBN6CanonicalPositiveGroups carrier carrierNodup cells) :
    group.consumerSystem.carrier = carrier := by
  obtain ⟨footprint, _footprintMember, groupEquation⟩ :=
    List.mem_map.mp groupMember
  subst group
  exact terminalBN6CanonicalPositiveGroup_carrier
    carrier carrierNodup cells footprint

theorem terminalBN6CanonicalPositiveGroups_footprintLarge
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier))
    (group : TerminalBN6GroupedCell Atom Payload)
    (groupMember : group ∈
      terminalBN6CanonicalPositiveGroups carrier carrierNodup cells) :
    2 ≤ group.footprint.length := by
  obtain ⟨footprint, _footprintMember, groupEquation⟩ :=
    List.mem_map.mp groupMember
  subst group
  exact terminalBN6CanonicalPositiveGroup_footprintLarge
    carrier carrierNodup cells footprint

/-- No raw payload disappears during canonical coalescing. -/
theorem TerminalBN6PositiveCell.exists_canonical_group
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom} (carrierNodup : carrier.Nodup)
    {cells : List (TerminalBN6PositiveCell Atom Payload carrier)}
    (cell : TerminalBN6PositiveCell Atom Payload carrier)
    (cellMember : cell ∈ cells) :
    ∃ group,
      group ∈ terminalBN6CanonicalPositiveGroups carrier carrierNodup cells ∧
      group.footprint = cell.footprint ∧
      cell.payloadAtom ∈ group.atoms := by
  have footprintMember :
      cell.footprint ∈
        terminalBN6CanonicalPositiveFootprints carrier cells :=
    (mem_terminalBN6CanonicalPositiveFootprints_iff
      carrier cells cell.footprint).2 ⟨cell, cellMember, rfl⟩
  let footprint : { value //
      value ∈ terminalBN6CanonicalPositiveFootprints carrier cells } :=
    ⟨cell.footprint, footprintMember⟩
  refine ⟨terminalBN6CanonicalPositiveGroup carrier carrierNodup cells footprint,
    ?_, ?_, ?_⟩
  · unfold terminalBN6CanonicalPositiveGroups
    apply List.mem_map.mpr
    exact ⟨footprint, by simp [footprint], rfl⟩
  · exact terminalBN6CanonicalPositiveGroup_footprint
      carrier carrierNodup cells footprint
  · exact cell.payloadAtom_mem_positiveAtomsAt cellMember

end DirectWire
end PNP
