/-
Copyright (c) 2026 PNP Labs.

Exact cut-ledger conservation for the canonical BN6 positive-cell grouping.
The raw ledger contributes each positive payload mass directly when its
carrier-normalized footprint crosses the cut.  Canonical grouping coalesces
equal footprints and sums their payload masses.  This module proves, for every
finite ledger and every cut, that the grouped activation sum is exactly the raw
crossing-mass sum.

The carrier, raw supports, positive payloads, and cut remain explicit inputs.
This does not derive the ledger from terminal data, establish the remaining
constant-activation equation, turn a mismatch into a gain, prove polynomial
bounds for the complete route, ZeroSlack, PCCMin, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalBN6CanonicalPositiveCellGrouping

namespace PNP
namespace DirectWire

/-! ## Raw positive-cell cut ledger -/

/-- The existing V53 hyperedge represented directly by one raw positive cell. -/
def TerminalBN6PositiveCell.toHyperedge
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalBN6PositiveCell Atom Payload carrier) :
    TerminalV53Hyperedge Atom :=
  { footprint := cell.footprint, mass := cell.payloadAtom.mass }

/-- One raw cell's exact contribution on a cut. -/
def TerminalBN6PositiveCell.cutContribution
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalBN6PositiveCell Atom Payload carrier)
    (cut : List Atom) : Nat :=
  cell.toHyperedge.cutContribution cut

/-- The direct crossing-mass sum before equal footprints are coalesced. -/
def terminalBN6PositiveCellsActivationWeight
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier))
    (cut : List Atom) : Nat :=
  (cells.map fun cell => cell.cutContribution cut).sum

/-- Crossing depends only on the footprint, not on the hyperedge mass. -/
def terminalBN6FootprintCrossesBool
    {Atom : Type} [DecidableEq Atom]
    (footprint cut : List Atom) : Bool :=
  ({ footprint := footprint, mass := 0 } : TerminalV53Hyperedge Atom).crossesBool cut

theorem TerminalBN6PositiveCell.crossesBool_eq_footprintCrossesBool
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalBN6PositiveCell Atom Payload carrier)
    (cut : List Atom) :
    cell.toHyperedge.crossesBool cut =
      terminalBN6FootprintCrossesBool cell.footprint cut := rfl

/-! ## Constructive finite partition lemmas -/

private theorem terminalBN6_sum_map_add
    {Item : Type} (items : List Item) (left right : Item -> Nat) :
    (items.map fun item => left item + right item).sum =
      (items.map left).sum + (items.map right).sum := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map, List.sum_cons]
      rw [ih]
      omega

private theorem terminalBN6_sum_indicator_of_not_mem
    {Key : Type} [DecidableEq Key]
    (keys : List Key) (target : Key) (value : Nat)
    (targetNotMember : target ∉ keys) :
    (keys.map fun key => if target = key then value else 0).sum = 0 := by
  induction keys with
  | nil => simp
  | cons head tail ih =>
      have targetNotHead : target ≠ head := by
        intro targetHead
        exact targetNotMember (by simp [targetHead])
      have targetNotTail : target ∉ tail := by
        intro targetTail
        exact targetNotMember (by simp [targetTail])
      simp [targetNotHead, ih targetNotTail]

private theorem terminalBN6_sum_single_indicator
    {Key : Type} [DecidableEq Key]
    (keys : List Key) (keysNodup : keys.Nodup)
    (target : Key) (targetMember : target ∈ keys) (value : Nat) :
    (keys.map fun key => if target = key then value else 0).sum = value := by
  induction keys with
  | nil => simp at targetMember
  | cons head tail ih =>
      have split := List.nodup_cons.mp keysNodup
      by_cases targetHead : target = head
      · subst target
        simp [terminalBN6_sum_indicator_of_not_mem tail head value split.1]
      · have targetTail : target ∈ tail := by
          simpa [targetHead] using targetMember
        simp [targetHead, ih split.2 targetTail]

private theorem terminalBN6_sum_map_zero
    {Item : Type} (items : List Item) :
    (items.map fun _item => 0).sum = 0 := by
  induction items with
  | nil => simp
  | cons head tail ih => simp [ih]

private theorem terminalBN6_sum_partition_by_key
    {Item Key : Type} [DecidableEq Key]
    (keys : List Key) (keysNodup : keys.Nodup)
    (items : List Item) (keyOf : Item -> Key) (value : Item -> Nat)
    (keyMember : ∀ item, item ∈ items -> keyOf item ∈ keys)
    (active : Key -> Bool) :
    (keys.map fun key =>
      if active key then
        (items.map fun item =>
          if keyOf item = key then value item else 0).sum
      else 0).sum =
      (items.map fun item =>
        if active (keyOf item) then value item else 0).sum := by
  induction items with
  | nil => simpa using (terminalBN6_sum_map_zero keys)
  | cons head tail ih =>
      have headKeyMember : keyOf head ∈ keys := keyMember head (by simp)
      have tailKeyMember : ∀ item, item ∈ tail -> keyOf item ∈ keys := by
        intro item itemMember
        exact keyMember item (by simp [itemMember])
      have tailPartition := ih tailKeyMember
      let headPart : Key -> Nat := fun key =>
        if active key then
          (if keyOf head = key then value head else 0)
        else 0
      let tailPart : Key -> Nat := fun key =>
        if active key then
          (tail.map fun item =>
            if keyOf item = key then value item else 0).sum
        else 0
      have splitPointwise : ∀ key, key ∈ keys ->
          (if active key then
            ((head :: tail).map fun item =>
              if keyOf item = key then value item else 0).sum
          else 0) = headPart key + tailPart key := by
        intro current _currentMember
        unfold headPart tailPart
        cases active current <;> simp
      have splitSum :
          (keys.map fun key =>
            if active key then
              ((head :: tail).map fun item =>
                if keyOf item = key then value item else 0).sum
            else 0).sum =
          (keys.map headPart).sum + (keys.map tailPart).sum := by
        calc
          _ = (keys.map fun key => headPart key + tailPart key).sum :=
            terminalV53_sum_congr keys _ _ splitPointwise
          _ = (keys.map headPart).sum + (keys.map tailPart).sum :=
            terminalBN6_sum_map_add keys headPart tailPart
      have headSum :
          (keys.map headPart).sum =
            if active (keyOf head) then value head else 0 := by
        let headValue := if active (keyOf head) then value head else 0
        have headPointwise : ∀ key, key ∈ keys ->
            headPart key =
              if keyOf head = key then headValue else 0 := by
          intro current _currentMember
          unfold headPart headValue
          by_cases sameKey : keyOf head = current <;> simp [sameKey]
        calc
          _ = (keys.map fun key =>
              if keyOf head = key then headValue else 0).sum :=
            terminalV53_sum_congr keys _ _ headPointwise
          _ = headValue := terminalBN6_sum_single_indicator
            keys keysNodup (keyOf head) headKeyMember headValue
          _ = _ := rfl
      have tailSum :
          (keys.map tailPart).sum =
            (tail.map fun item =>
              if active (keyOf item) then value item else 0).sum := by
        exact tailPartition
      rw [splitSum, headSum, tailSum]
      simp

/-! ## Exact conservation under canonical coalescing -/

/-- The collected atoms at one footprint carry exactly the mass of the matching
    raw cells. -/
theorem terminalBN6PositiveAtomsAt_mass_sum
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier))
    (footprint : List Atom) :
    ((terminalBN6PositiveAtomsAt carrier cells footprint).map
      TerminalBN6PayloadAtom.mass).sum =
      (cells.map fun cell =>
        if cell.footprint = footprint then cell.payloadAtom.mass else 0).sum := by
  induction cells with
  | nil => simp [terminalBN6PositiveAtomsAt]
  | cons cell tail ih =>
      unfold terminalBN6PositiveAtomsAt
      split <;> simp_all

private theorem terminalBN6CanonicalPositiveGroup_cutContribution
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier))
    (footprint : { value //
      value ∈ terminalBN6CanonicalPositiveFootprints carrier cells })
    (cut : List Atom) :
    (if (terminalBN6CanonicalPositiveGroup carrier carrierNodup cells footprint).consumerSystem.cutActivationBool cut then
        (terminalBN6CanonicalPositiveGroup carrier carrierNodup cells footprint).mass
      else 0) =
      if terminalBN6FootprintCrossesBool footprint.1 cut then
        ((terminalBN6PositiveAtomsAt carrier cells footprint.1).map
          TerminalBN6PayloadAtom.mass).sum
      else 0 := by
  let group := terminalBN6CanonicalPositiveGroup
    carrier carrierNodup cells footprint
  have crossesEqual :
      group.consumerSystem.cutActivationBool cut =
        terminalBN6FootprintCrossesBool footprint.1 cut := by
    rw [← group.crossesBool_eq_cutActivationBool cut]
    unfold terminalBN6FootprintCrossesBool
      TerminalBN6GroupedCell.toHyperedge
      TerminalV53Hyperedge.crossesBool
    rw [terminalBN6CanonicalPositiveGroup_footprint]
  have massEqual :
      group.mass =
        ((terminalBN6PositiveAtomsAt carrier cells footprint.1).map
          TerminalBN6PayloadAtom.mass).sum := rfl
  change (if group.consumerSystem.cutActivationBool cut then group.mass else 0) = _
  rw [crossesEqual, massEqual]

private theorem terminalBN6_sum_attach_map
    {Item : Type} (items : List Item) (value : Item -> Nat) :
    (items.attach.map fun item => value item.1).sum =
      (items.map value).sum := by
  have mapped :
      items.attach.map (fun item => value item.1) =
        (items.attach.map Subtype.val).map value := by
    rw [List.map_map]
    apply List.map_congr_left
    intro item _itemMember
    rfl
  rw [mapped, List.attach_map_subtype_val]

/-- Coalescing duplicate normalized footprints preserves the exact positive
    crossing-mass ledger on every cut. -/
theorem terminalBN6CanonicalPositiveGroups_activationWeight_eq_raw
    {Atom Payload : Type} [DecidableEq Atom]
    (carrier : List Atom) (carrierNodup : carrier.Nodup)
    (cells : List (TerminalBN6PositiveCell Atom Payload carrier))
    (cut : List Atom) :
    ((terminalBN6CanonicalPositiveGroups carrier carrierNodup cells).map
      fun group =>
        if group.consumerSystem.cutActivationBool cut then group.mass else 0).sum =
      terminalBN6PositiveCellsActivationWeight carrier cells cut := by
  let footprints := terminalBN6CanonicalPositiveFootprints carrier cells
  have everyKey : ∀ cell, cell ∈ cells -> cell.footprint ∈ footprints := by
    intro cell cellMember
    exact (mem_terminalBN6CanonicalPositiveFootprints_iff
      carrier cells cell.footprint).2 ⟨cell, cellMember, rfl⟩
  have partition := terminalBN6_sum_partition_by_key
    footprints (terminalBN6CanonicalPositiveFootprints_nodup carrier cells)
    cells (fun cell => cell.footprint) (fun cell => cell.payloadAtom.mass)
    everyKey (fun footprint => terminalBN6FootprintCrossesBool footprint cut)
  calc
    _ = (footprints.attach.map fun footprint =>
        if terminalBN6FootprintCrossesBool footprint.1 cut then
          ((terminalBN6PositiveAtomsAt carrier cells footprint.1).map
            TerminalBN6PayloadAtom.mass).sum
        else 0).sum := by
      unfold terminalBN6CanonicalPositiveGroups
      rw [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro footprint _footprintMember
      exact terminalBN6CanonicalPositiveGroup_cutContribution
        carrier carrierNodup cells footprint cut
    _ = (footprints.map fun footprint =>
        if terminalBN6FootprintCrossesBool footprint cut then
          ((terminalBN6PositiveAtomsAt carrier cells footprint).map
            TerminalBN6PayloadAtom.mass).sum
        else 0).sum := by
      exact terminalBN6_sum_attach_map footprints fun footprint =>
        if terminalBN6FootprintCrossesBool footprint cut then
          ((terminalBN6PositiveAtomsAt carrier cells footprint).map
            TerminalBN6PayloadAtom.mass).sum
        else 0
    _ = (footprints.map fun footprint =>
        if terminalBN6FootprintCrossesBool footprint cut then
          (cells.map fun cell =>
            if cell.footprint = footprint then cell.payloadAtom.mass else 0).sum
        else 0).sum := by
      apply terminalV53_sum_congr
      intro footprint _footprintMember
      rw [terminalBN6PositiveAtomsAt_mass_sum]
    _ = (cells.map fun cell =>
        if terminalBN6FootprintCrossesBool cell.footprint cut then
          cell.payloadAtom.mass else 0).sum := partition
    _ = terminalBN6PositiveCellsActivationWeight carrier cells cut := by
      unfold terminalBN6PositiveCellsActivationWeight
        TerminalBN6PositiveCell.cutContribution
        TerminalV53Hyperedge.cutContribution
      apply terminalV53_sum_congr
      intro cell _cellMember
      rw [cell.crossesBool_eq_footprintCrossesBool cut]
      rfl

end DirectWire
end PNP
