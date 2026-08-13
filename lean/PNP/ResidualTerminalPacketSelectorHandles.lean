/-
Copyright (c) 2026 PNP Labs.

Canonical finite handles for the exact grouped-footprint Packet selector
universe.  A handle is a position in the duplicate-free input-relative list;
decoding therefore recovers exactly one footprint.  Every decoded footprint
retains the same carrier-containment, nontrivial-size, grouped-cell, and atom
payload evidence already present in the explicit BN6 family.

These are list positions, not the manuscript's bit encoding or a polynomially
enumerable selector universe.  This module does not prove manuscript-level
selector faithfulness or compatibility, construct a realizer or route, derive
the grouped family from a terminal candidate, establish polynomial bounds,
complete PkgC, ZeroSlack, or PCCMin, put SAT in P, or prove P = NP.
-/

import PNP.ResidualTerminalPacketSelectorUniverse

namespace PNP
namespace DirectWire

private def locatePacketSelectorFootprint
    {Atom : Type} [DecidableEq Atom] (footprint : List Atom) :
    (items : List (List Atom)) -> footprint ∈ items ->
      {index : Fin items.length // items.get index = footprint}
  | [], member => False.elim (by cases member)
  | head :: tail, member =>
      if equal : footprint = head then
        ⟨⟨0, Nat.zero_lt_succ _⟩, by simp [equal]⟩
      else
        let tailMember : footprint ∈ tail :=
          (List.mem_cons.mp member).resolve_left equal
        let located := locatePacketSelectorFootprint footprint tail tailMember
        ⟨located.1.succ, located.2⟩

private theorem get_injective_of_nodup
    {alpha : Type} {items : List alpha} (distinct : items.Nodup)
    {left right : Fin items.length}
    (equal : items.get left = items.get right) : left = right := by
  apply Fin.ext
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro rightBeforeLeft
    have separated :=
      (List.pairwise_iff_getElem.mp distinct) right.val left.val
        right.isLt left.isLt rightBeforeLeft
    change items.get right ≠ items.get left at separated
    exact separated equal.symm
  · apply Nat.le_of_not_gt
    intro leftBeforeRight
    have separated :=
      (List.pairwise_iff_getElem.mp distinct) left.val right.val
        left.isLt right.isLt leftBeforeRight
    change items.get left ≠ items.get right at separated
    exact separated equal

/-! ## Exact input-relative handles -/

/-- A canonical handle is a position in the exact finite grouped-footprint
    universe of this explicit family. -/
def TerminalBN6GroupedFamily.PacketSelectorHandle
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) : Type :=
  Fin family.packetPayloadSelectorUniverse.length

/-- Total decoding of a finite handle to its exact grouped footprint. -/
def TerminalBN6GroupedFamily.packetSelectorFootprint
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) : List Atom :=
  family.packetPayloadSelectorUniverse.get handle

/-- Every decoded handle is a member of the same exact finite universe. -/
theorem TerminalBN6GroupedFamily.packetSelectorFootprint_mem_universe
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorFootprint handle ∈
      family.packetPayloadSelectorUniverse :=
  List.get_mem family.packetPayloadSelectorUniverse handle

/-- Duplicate-free grouped footprints make decoding injective. -/
theorem TerminalBN6GroupedFamily.packetSelectorFootprint_injective
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    {left right : family.PacketSelectorHandle}
    (equal : family.packetSelectorFootprint left =
      family.packetSelectorFootprint right) :
    left = right :=
  get_injective_of_nodup family.packetPayloadSelectorUniverse_nodup equal

/-- A decoded footprint lies in the common anchor carrier of its source
    grouped cell. -/
theorem TerminalBN6GroupedFamily.packetSelectorFootprint_sublist_carrier
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorFootprint handle).Sublist family.carrier := by
  obtain ⟨cell, cellMember, cellFootprint⟩ :=
    (family.mem_packetPayloadSelectorUniverse_iff
      (family.packetSelectorFootprint handle)).1
      (family.packetSelectorFootprint_mem_universe handle)
  have footprintSublist :
      cell.footprint.Sublist cell.consumerSystem.carrier := by
    unfold TerminalBN6GroupedCell.footprint
      TerminalV54ConsumerSystem.singletonFootprint
    exact List.filter_sublist
  rw [family.groupCarrier cell cellMember] at footprintSublist
  rw [← cellFootprint]
  exact footprintSublist

/-- Every decoded grouped footprint has selector-relevant size. -/
theorem TerminalBN6GroupedFamily.packetSelectorFootprint_large
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    2 ≤ (family.packetSelectorFootprint handle).length := by
  obtain ⟨cell, cellMember, cellFootprint⟩ :=
    (family.mem_packetPayloadSelectorUniverse_iff
      (family.packetSelectorFootprint handle)).1
      (family.packetSelectorFootprint_mem_universe handle)
  rw [← cellFootprint]
  exact family.groupFootprintLarge cell cellMember

/-- Decoding retains an original grouped cell and atom payload witness. -/
theorem TerminalBN6GroupedFamily.packetSelectorFootprint_hasPayloadAt
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    family.HasPayloadAt (family.packetSelectorFootprint handle) := by
  obtain ⟨cell, cellMember, cellFootprint⟩ :=
    (family.mem_packetPayloadSelectorUniverse_iff
      (family.packetSelectorFootprint handle)).1
      (family.packetSelectorFootprint_mem_universe handle)
  refine ⟨cell, cellMember, cellFootprint, ?_⟩
  cases atomsEquation : cell.atoms with
  | nil => exact False.elim (cell.atomsNonempty atomsEquation)
  | cons head tail => exact ⟨head, by simp⟩

/-- Every handle decodes to a payload-backed raw Packet seed. -/
theorem TerminalBN6GroupedFamily.packetSelectorFootprint_hasPacketSelectorSeedAt
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    family.HasPacketSelectorSeedAt
      (family.packetSelectorFootprint handle) :=
  ⟨family.packetSelectorFootprint_sublist_carrier handle,
    family.packetSelectorFootprint_large handle,
    family.packetSelectorFootprint_hasPayloadAt handle⟩

/-- Every handle therefore decodes to an exact finite payload selector. -/
theorem TerminalBN6GroupedFamily.packetSelectorFootprint_hasPacketPayloadSelectorAt
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    family.HasPacketPayloadSelectorAt
      (family.packetSelectorFootprint handle) :=
  ⟨family.packetSelectorFootprint_mem_universe handle,
    family.packetSelectorFootprint_hasPacketSelectorSeedAt handle⟩

/-- Existence of an input-relative handle decoding to this footprint. -/
def TerminalBN6GroupedFamily.HasFinitePacketSelectorHandleAt
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom) : Prop :=
  ∃ handle : family.PacketSelectorHandle,
    family.packetSelectorFootprint handle = footprint

/-- Exact finite handles and finite payload selectors describe the same
    footprints. -/
theorem TerminalBN6GroupedFamily.hasFinitePacketSelectorHandleAt_iff_payloadSelector
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom) :
    family.HasFinitePacketSelectorHandleAt footprint ↔
      family.HasPacketPayloadSelectorAt footprint := by
  constructor
  · rintro ⟨handle, decodeEquation⟩
    rw [← decodeEquation]
    exact family.packetSelectorFootprint_hasPacketPayloadSelectorAt handle
  · intro selector
    let located := locatePacketSelectorFootprint footprint
      family.packetPayloadSelectorUniverse selector.1
    exact ⟨located.1, located.2⟩

/-- A finite payload selector has exactly one handle, rather than merely an
    arbitrary representative. -/
theorem TerminalBN6GroupedFamily.existsUnique_packetSelectorHandle_iff_payloadSelector
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom) :
    (∃ handle : family.PacketSelectorHandle,
      family.packetSelectorFootprint handle = footprint ∧
        ∀ other : family.PacketSelectorHandle,
          family.packetSelectorFootprint other = footprint ->
            other = handle) ↔
      family.HasPacketPayloadSelectorAt footprint := by
  constructor
  · rintro ⟨handle, decodeEquation, _unique⟩
    rw [← decodeEquation]
    exact family.packetSelectorFootprint_hasPacketPayloadSelectorAt handle
  · intro selector
    let located := locatePacketSelectorFootprint footprint
      family.packetPayloadSelectorUniverse selector.1
    refine ⟨located.1, located.2, ?_⟩
    intro other otherEquation
    apply family.packetSelectorFootprint_injective
    exact otherEquation.trans located.2.symm

/-! ## Exhaustive handle outcome -/

/-- The exact finite handle information available in every Packet branch. -/
inductive TerminalPacketSelectorHandleConclusion
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) : Prop where
  | pair
      (carrierLength : family.carrier.length = 2)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (selector : family.HasFinitePacketSelectorHandleAt family.carrier) :
      TerminalPacketSelectorHandleConclusion family
  | balancedTriple
      (carrierLength : family.carrier.length = 3)
      (pairMass : Nat)
      (pairPositive : 0 < pairMass)
      (everyPair : ∀ footprint, footprint.Sublist family.carrier ->
        footprint.length = 2 ->
          family.hypergraph.footprintWeight footprint = pairMass)
      (selectors : ∀ footprint, footprint.Sublist family.carrier ->
        footprint.length = 2 ->
          family.HasFinitePacketSelectorHandleAt footprint) :
      TerminalPacketSelectorHandleConclusion family
  | fullSpan
      (carrierLength : 3 ≤ family.carrier.length)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (selector : family.HasFinitePacketSelectorHandleAt family.carrier) :
      TerminalPacketSelectorHandleConclusion family

/-- Upgrade every exact finite payload-selector branch to canonical handle
    existence without changing its alternatives. -/
theorem TerminalPacketPayloadSelectorConclusion.selectorHandles
    {Atom Payload : Type} [DecidableEq Atom]
    {family : TerminalBN6GroupedFamily Atom Payload}
    (conclusion : TerminalPacketPayloadSelectorConclusion family) :
    TerminalPacketSelectorHandleConclusion family := by
  cases conclusion with
  | pair carrierLength fullPositive selector =>
      exact TerminalPacketSelectorHandleConclusion.pair carrierLength
        fullPositive
        ((family.hasFinitePacketSelectorHandleAt_iff_payloadSelector
          family.carrier).2 selector)
  | balancedTriple carrierLength pairMass pairPositive everyPair selectors =>
      apply TerminalPacketSelectorHandleConclusion.balancedTriple
        carrierLength pairMass pairPositive everyPair
      intro footprint footprintSublist footprintLength
      exact (family.hasFinitePacketSelectorHandleAt_iff_payloadSelector
        footprint).2 (selectors footprint footprintSublist footprintLength)
  | fullSpan carrierLength fullPositive selector =>
      exact TerminalPacketSelectorHandleConclusion.fullSpan carrierLength
        fullPositive
        ((family.hasFinitePacketSelectorHandleAt_iff_payloadSelector
          family.carrier).2 selector)

/-- Every exact BN6 packet conclusion has a canonical finite selector handle
    in the same explicit grouped family. -/
theorem TerminalBN6PacketConclusion.selectorHandles
    {Atom Payload : Type} [DecidableEq Atom]
    {family : TerminalBN6GroupedFamily Atom Payload}
    (conclusion : TerminalBN6PacketConclusion family) :
    TerminalPacketSelectorHandleConclusion family :=
  conclusion.payloadSelectors.selectorHandles

/-- BN6 followed by seed extraction, finite-universe membership, and canonical
    input-relative handle construction. -/
theorem terminalBN6_packet_selector_handles
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (carrierAtLeastTwo : 2 ≤ family.carrier.length)
    (constant : family.ConstantActivation) :
    TerminalPacketSelectorHandleConclusion family :=
  (terminalBN6_hypergraph_packet family carrierAtLeastTwo constant)
    |>.selectorHandles

end DirectWire
end PNP
