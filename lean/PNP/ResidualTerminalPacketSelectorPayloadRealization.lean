/-
Copyright (c) 2026 PNP Labs.

Total fail-closed payload realization for canonical Packet selector codes over
one explicit grouped BN6 family.  An accepted code determines its exact
input-relative handle, grouped footprint, source cell, and one original
positive payload atom.  Malformed, trailing, and out-of-range codes remain
rejected by the existing total decoder.

This is payload materialization for the finite explicit grouped-family
interface.  It is not the manuscript's gain-or-blocker selector realizer: it
does not build a replacement circuit, establish selector faithfulness or
compatibility, produce a gain or typed blocker route, derive the grouped
family, bound it by encoded circuit size, prove polynomial generation or
runtime, complete PkgC, ZeroSlack, or PCCMin, put SAT in P, or prove P = NP.
-/

import PNP.ResidualTerminalPacketSelectorCodec

namespace PNP
namespace DirectWire

/-! ## Canonical source payload -/

/-- The exact grouped cell at a decoded selector position. -/
def TerminalBN6GroupedFamily.packetSelectorCell
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    TerminalBN6GroupedCell Atom Payload :=
  family.groups.get ⟨handle.val, by
    simpa [TerminalBN6GroupedFamily.packetPayloadSelectorUniverse] using
      handle.isLt⟩

/-- The selected cell is an original member of the explicit grouped family. -/
theorem TerminalBN6GroupedFamily.packetSelectorCell_mem_groups
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorCell handle ∈ family.groups :=
  List.get_mem family.groups _

/-- The selected cell has exactly the footprint decoded by the handle. -/
theorem TerminalBN6GroupedFamily.packetSelectorCell_footprint
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorCell handle).footprint =
      family.packetSelectorFootprint handle := by
  unfold TerminalBN6GroupedFamily.packetSelectorCell
    TerminalBN6GroupedFamily.packetSelectorFootprint
    TerminalBN6GroupedFamily.packetPayloadSelectorUniverse
  simp

/-- Canonically choose the first original positive payload atom in the
    selected nonempty grouped cell. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadAtom
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    TerminalBN6PayloadAtom Payload :=
  let cell := family.packetSelectorCell handle
  cell.atoms.get ⟨0, by
    cases atomsEquation : cell.atoms with
    | nil => exact False.elim (cell.atomsNonempty atomsEquation)
    | cons head tail => simp⟩

/-- The canonical payload atom is one of the selected source cell's original
    atoms. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadAtom_mem
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadAtom handle ∈
      (family.packetSelectorCell handle).atoms :=
  List.get_mem (family.packetSelectorCell handle).atoms _

/-! ## Total fail-closed realization -/

/-- Proof-bearing result of realizing one accepted canonical Packet selector
    code into its exact source cell and an original positive payload atom. -/
structure TerminalPacketSelectorPayloadRealization
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) where
  handle : family.PacketSelectorHandle
  cell : TerminalBN6GroupedCell Atom Payload
  cellMember : cell ∈ family.groups
  cellFootprint : cell.footprint = family.packetSelectorFootprint handle
  atom : TerminalBN6PayloadAtom Payload
  atomMember : atom ∈ cell.atoms

/-- Materialize the exact source cell and canonical first positive payload atom
    for one already-decoded handle. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadRealization
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    TerminalPacketSelectorPayloadRealization family :=
  {
    handle := handle
    cell := family.packetSelectorCell handle
    cellMember := family.packetSelectorCell_mem_groups handle
    cellFootprint := family.packetSelectorCell_footprint handle
    atom := family.packetSelectorPayloadAtom handle
    atomMember := family.packetSelectorPayloadAtom_mem handle
  }

/-- Decode and realize every accepted selector code; reject every other
    bitstring. -/
def TerminalBN6GroupedFamily.realizePacketSelectorPayload
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (bits : Concrete.BitString) :
    Option (TerminalPacketSelectorPayloadRealization family) :=
  (family.decodePacketSelectorHandle bits).map
    family.packetSelectorPayloadRealization

/-- Payload realization rejects exactly when the canonical decoder rejects. -/
theorem TerminalBN6GroupedFamily.realizePacketSelectorPayload_eq_none_iff
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (bits : Concrete.BitString) :
    family.realizePacketSelectorPayload bits = none ↔
      family.decodePacketSelectorHandle bits = none := by
  simp [TerminalBN6GroupedFamily.realizePacketSelectorPayload]

/-- A returned payload realization carries exactly the handle accepted by the
    canonical decoder. -/
theorem TerminalBN6GroupedFamily.decodePacketSelectorHandle_eq_some_of_realize
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (bits : Concrete.BitString)
    (realized : TerminalPacketSelectorPayloadRealization family)
    (result : family.realizePacketSelectorPayload bits = some realized) :
    family.decodePacketSelectorHandle bits = some realized.handle := by
  have projected := congrArg
    (Option.map (fun value : TerminalPacketSelectorPayloadRealization family =>
      value.handle)) result
  simpa [TerminalBN6GroupedFamily.realizePacketSelectorPayload,
    TerminalBN6GroupedFamily.packetSelectorPayloadRealization] using projected

/-- A realization exists exactly when the total decoder accepts one handle. -/
theorem TerminalBN6GroupedFamily.exists_realizePacketSelectorPayload_iff
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (bits : Concrete.BitString) :
    (∃ realized, family.realizePacketSelectorPayload bits = some realized) ↔
      ∃ handle, family.decodePacketSelectorHandle bits = some handle := by
  constructor
  · rintro ⟨realized, result⟩
    exact ⟨realized.handle,
      family.decodePacketSelectorHandle_eq_some_of_realize bits realized
        result⟩
  · rintro ⟨handle, decoded⟩
    refine ⟨family.packetSelectorPayloadRealization handle, ?_⟩
    simp [TerminalBN6GroupedFamily.realizePacketSelectorPayload, decoded]

/-- Every canonical handle code has one successfully materialized payload. -/
theorem TerminalBN6GroupedFamily.exists_realizePacketSelectorPayload_encode
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    ∃ realized,
      family.realizePacketSelectorPayload
        (family.encodePacketSelectorHandle handle) = some realized ∧
      realized.handle = handle := by
  refine ⟨family.packetSelectorPayloadRealization handle, ?_, rfl⟩
  simp [TerminalBN6GroupedFamily.realizePacketSelectorPayload,
    family.decodePacketSelectorHandle_encode handle]

/-- Every successful realization is canonical and retains an original source
    cell and a strictly positive payload atom at the decoded footprint. -/
theorem TerminalBN6GroupedFamily.realizePacketSelectorPayload_sound
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (bits : Concrete.BitString)
    (realized : TerminalPacketSelectorPayloadRealization family)
    (result : family.realizePacketSelectorPayload bits = some realized) :
    family.encodePacketSelectorHandle realized.handle = bits ∧
      realized.cell ∈ family.groups ∧
      realized.cell.footprint =
        family.packetSelectorFootprint realized.handle ∧
      realized.atom ∈ realized.cell.atoms ∧
      0 < realized.atom.mass :=
  ⟨family.decodePacketSelectorHandle_canonical bits realized.handle
      (family.decodePacketSelectorHandle_eq_some_of_realize bits realized
        result),
    realized.cellMember,
    realized.cellFootprint,
    realized.atomMember,
    realized.atom.massPositive⟩

/-! ## Exact realized selectors -/

/-- One accepted code realizes an original positive payload at the requested
    footprint. -/
def TerminalBN6GroupedFamily.IsRealizedPacketSelectorAt
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (bits : Concrete.BitString) (footprint : List Atom) : Prop :=
  ∃ realized : TerminalPacketSelectorPayloadRealization family,
    family.realizePacketSelectorPayload bits = some realized ∧
      family.packetSelectorFootprint realized.handle = footprint

/-- Existence of one successfully realized accepted code for a footprint. -/
def TerminalBN6GroupedFamily.HasRealizedPacketSelectorAt
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom) : Prop :=
  ∃ bits : Concrete.BitString,
    family.IsRealizedPacketSelectorAt bits footprint

/-- Realized selectors are exactly accepted canonical selectors at the same
    footprint. -/
theorem TerminalBN6GroupedFamily.isRealizedPacketSelectorAt_iff_encoded
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (bits : Concrete.BitString) (footprint : List Atom) :
    family.IsRealizedPacketSelectorAt bits footprint ↔
      family.IsEncodedPacketSelectorAt bits footprint := by
  constructor
  · rintro ⟨realized, result, footprintEquation⟩
    exact ⟨realized.handle,
      family.decodePacketSelectorHandle_eq_some_of_realize bits realized
        result,
      footprintEquation⟩
  · rintro ⟨handle, decoded, footprintEquation⟩
    obtain ⟨realized, realizedEquation⟩ :=
      (family.exists_realizePacketSelectorPayload_iff bits).2
        ⟨handle, decoded⟩
    refine ⟨realized, realizedEquation, ?_⟩
    have realizedDecoded :=
      family.decodePacketSelectorHandle_eq_some_of_realize bits realized
        realizedEquation
    rw [decoded] at realizedDecoded
    have handleEquation : realized.handle = handle := by
      exact (Option.some.inj realizedDecoded).symm
    rw [handleEquation]
    exact footprintEquation

/-- Payload realization neither loses nor invents a finite payload selector. -/
theorem TerminalBN6GroupedFamily.hasRealizedPacketSelectorAt_iff_payloadSelector
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom) :
    family.HasRealizedPacketSelectorAt footprint ↔
      family.HasPacketPayloadSelectorAt footprint := by
  constructor
  · rintro ⟨bits, realized⟩
    exact (family.hasEncodedPacketSelectorAt_iff_payloadSelector footprint).1
      ⟨bits,
        (family.isRealizedPacketSelectorAt_iff_encoded bits footprint).1
          realized⟩
  · intro selector
    obtain ⟨bits, encoded⟩ :=
      (family.hasEncodedPacketSelectorAt_iff_payloadSelector footprint).2
        selector
    exact ⟨bits,
      (family.isRealizedPacketSelectorAt_iff_encoded bits footprint).2
        encoded⟩

/-! ## Exhaustive realized Packet outcome -/

/-- The exact payload-realization information available in every finite Packet
    branch. -/
inductive TerminalPacketRealizedSelectorConclusion
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) : Prop where
  | pair
      (carrierLength : family.carrier.length = 2)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (selector : family.HasRealizedPacketSelectorAt family.carrier) :
      TerminalPacketRealizedSelectorConclusion family
  | balancedTriple
      (carrierLength : family.carrier.length = 3)
      (pairMass : Nat)
      (pairPositive : 0 < pairMass)
      (everyPair : ∀ footprint, footprint.Sublist family.carrier ->
        footprint.length = 2 ->
          family.hypergraph.footprintWeight footprint = pairMass)
      (selectors : ∀ footprint, footprint.Sublist family.carrier ->
        footprint.length = 2 ->
          family.HasRealizedPacketSelectorAt footprint) :
      TerminalPacketRealizedSelectorConclusion family
  | fullSpan
      (carrierLength : 3 ≤ family.carrier.length)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (selector : family.HasRealizedPacketSelectorAt family.carrier) :
      TerminalPacketRealizedSelectorConclusion family

/-- Upgrade every encoded Packet selector branch to a proof-bearing original
    payload realization without changing its alternatives. -/
theorem TerminalPacketEncodedSelectorConclusion.selectorPayloadRealizations
    {Atom Payload : Type} [DecidableEq Atom]
    {family : TerminalBN6GroupedFamily Atom Payload}
    (conclusion : TerminalPacketEncodedSelectorConclusion family) :
    TerminalPacketRealizedSelectorConclusion family := by
  cases conclusion with
  | pair carrierLength fullPositive selector =>
      exact TerminalPacketRealizedSelectorConclusion.pair carrierLength
        fullPositive
        ((family.hasRealizedPacketSelectorAt_iff_payloadSelector
          family.carrier).2
            ((family.hasEncodedPacketSelectorAt_iff_payloadSelector
              family.carrier).1 selector))
  | balancedTriple carrierLength pairMass pairPositive everyPair selectors =>
      apply TerminalPacketRealizedSelectorConclusion.balancedTriple
        carrierLength pairMass pairPositive everyPair
      intro footprint footprintSublist footprintLength
      exact (family.hasRealizedPacketSelectorAt_iff_payloadSelector
        footprint).2
          ((family.hasEncodedPacketSelectorAt_iff_payloadSelector
            footprint).1
              (selectors footprint footprintSublist footprintLength))
  | fullSpan carrierLength fullPositive selector =>
      exact TerminalPacketRealizedSelectorConclusion.fullSpan carrierLength
        fullPositive
        ((family.hasRealizedPacketSelectorAt_iff_payloadSelector
          family.carrier).2
            ((family.hasEncodedPacketSelectorAt_iff_payloadSelector
              family.carrier).1 selector))

/-- Every exact BN6 Packet conclusion has a successfully materialized original
    payload in the same explicit grouped family. -/
theorem TerminalBN6PacketConclusion.selectorPayloadRealizations
    {Atom Payload : Type} [DecidableEq Atom]
    {family : TerminalBN6GroupedFamily Atom Payload}
    (conclusion : TerminalBN6PacketConclusion family) :
    TerminalPacketRealizedSelectorConclusion family :=
  conclusion.selectorCodes.selectorPayloadRealizations

/-- BN6 followed by canonical coding and total fail-closed source-payload
    materialization. -/
theorem terminalBN6_packet_selector_payload_realizations
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (carrierAtLeastTwo : 2 ≤ family.carrier.length)
    (constant : family.ConstantActivation) :
    TerminalPacketRealizedSelectorConclusion family :=
  (terminalBN6_packet_selector_codes family carrierAtLeastTwo constant)
    |>.selectorPayloadRealizations

end DirectWire
end PNP
