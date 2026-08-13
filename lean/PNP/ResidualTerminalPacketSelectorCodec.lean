/-
Copyright (c) 2026 PNP Labs.

Canonical total bitstring codec for the input-relative Packet selector handles.
The unary code for position `i` is `i` one-bits followed by one zero delimiter.
Decoding rejects a missing delimiter, any trailing bit, and every position
outside the exact grouped-footprint list. Successful decoding is canonical and
retains the carrier, size, grouped-cell, atom, and payload evidence of the
underlying handle.

The length bound here is relative to the explicit grouped-family list. It does
not bound that list by circuit input size, prove polynomial enumeration or
runtime, encode atom or payload data, prove manuscript-level selector
faithfulness or compatibility, construct a realizer or route, derive the family,
complete PkgC, ZeroSlack, or PCCMin, put SAT in P, or prove P = NP.
-/

import PNP.ResidualTerminalPacketSelectorHandles
import PNP.Concrete.BitString

namespace PNP
namespace DirectWire

private theorem packetSelectorDecodeLength_shape
    (bits : Concrete.BitString) (index : Nat)
    (suffix : Concrete.BitString)
    (decoded : Concrete.BitString.decodeLength bits = some (index, suffix)) :
    bits = List.replicate index true ++ false :: suffix := by
  induction bits generalizing index suffix with
  | nil => simp [Concrete.BitString.decodeLength] at decoded
  | cons bit rest ih =>
      cases bit with
      | false =>
          simp only [Concrete.BitString.decodeLength] at decoded
          cases decoded
          rfl
      | true =>
          simp only [Concrete.BitString.decodeLength] at decoded
          cases restDecoded : Concrete.BitString.decodeLength rest with
          | none => simp [restDecoded] at decoded
          | some result =>
              cases result with
              | mk restIndex restSuffix =>
                  simp [restDecoded] at decoded
                  rcases decoded with ⟨rfl, rfl⟩
                  have restShape := ih restIndex restSuffix restDecoded
                  rw [restShape]
                  simp only [List.replicate_succ, List.cons_append]

/-! ## Canonical total codec -/

/-- Encode one exact input-relative selector handle as a canonical unary
    bitstring. -/
def TerminalBN6GroupedFamily.encodePacketSelectorHandle
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) : Concrete.BitString :=
  List.replicate handle.val true ++ [false]

/-- Decode every bitstring, rejecting malformed, trailing, and out-of-range
    selector positions. -/
def TerminalBN6GroupedFamily.decodePacketSelectorHandle
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (bits : Concrete.BitString) : Option family.PacketSelectorHandle :=
  match Concrete.BitString.decodeLength bits with
  | some (index, []) =>
      if inRange : index < family.packetPayloadSelectorUniverse.length then
        some ⟨index, inRange⟩
      else
        none
  | _ => none

/-- Encoding followed by total decoding is an exact round trip. -/
theorem TerminalBN6GroupedFamily.decodePacketSelectorHandle_encode
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    family.decodePacketSelectorHandle
      (family.encodePacketSelectorHandle handle) = some handle := by
  unfold TerminalBN6GroupedFamily.decodePacketSelectorHandle
    TerminalBN6GroupedFamily.encodePacketSelectorHandle
  rw [Concrete.BitString.decodeLength_frameHeader handle.val []]
  simp [handle.isLt]

/-- Exact decoding makes the canonical bit encoding injective. -/
theorem TerminalBN6GroupedFamily.encodePacketSelectorHandle_injective
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) :
    Function.Injective family.encodePacketSelectorHandle := by
  intro left right equal
  have decoded := congrArg family.decodePacketSelectorHandle equal
  rw [family.decodePacketSelectorHandle_encode,
    family.decodePacketSelectorHandle_encode] at decoded
  exact Option.some.inj decoded

/-- The canonical unary code has exactly position-plus-one bits. -/
theorem TerminalBN6GroupedFamily.encodePacketSelectorHandle_length
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    (family.encodePacketSelectorHandle handle).length = handle.val + 1 := by
  unfold TerminalBN6GroupedFamily.encodePacketSelectorHandle
  rw [Concrete.BitString.length_append_constructive,
    Concrete.BitString.length_replicate_constructive]
  rfl

/-- Code length is bounded by the exact explicit grouped-family universe. -/
theorem TerminalBN6GroupedFamily.encodePacketSelectorHandle_length_le_universe
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    (family.encodePacketSelectorHandle handle).length ≤
      family.packetPayloadSelectorUniverse.length := by
  rw [family.encodePacketSelectorHandle_length handle]
  exact handle.isLt

/-- Every accepted bitstring is the canonical encoding of its decoded handle. -/
theorem TerminalBN6GroupedFamily.decodePacketSelectorHandle_canonical
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (bits : Concrete.BitString) (handle : family.PacketSelectorHandle)
    (decoded : family.decodePacketSelectorHandle bits = some handle) :
    family.encodePacketSelectorHandle handle = bits := by
  unfold TerminalBN6GroupedFamily.decodePacketSelectorHandle at decoded
  cases lengthDecoded : Concrete.BitString.decodeLength bits with
  | none => simp [lengthDecoded] at decoded
  | some result =>
      cases result with
      | mk index suffix =>
          cases suffix with
          | nil =>
              simp only [lengthDecoded] at decoded
              split at decoded
              next inRange =>
                have handleEquation :
                    (⟨index, inRange⟩ : family.PacketSelectorHandle) = handle :=
                  Option.some.inj decoded
                subst handle
                unfold TerminalBN6GroupedFamily.encodePacketSelectorHandle
                exact (packetSelectorDecodeLength_shape bits index []
                  lengthDecoded).symm
              next notInRange => simp at decoded
          | cons bit tail => simp [lengthDecoded] at decoded

/-- Successful decoding retains the exact payload selector and all existing
    footprint evidence. -/
theorem TerminalBN6GroupedFamily.decodePacketSelectorHandle_payloadEvidence
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (bits : Concrete.BitString) (handle : family.PacketSelectorHandle)
    (_decoded : family.decodePacketSelectorHandle bits = some handle) :
    family.HasPacketPayloadSelectorAt
        (family.packetSelectorFootprint handle) ∧
      (family.packetSelectorFootprint handle).Sublist family.carrier ∧
      2 ≤ (family.packetSelectorFootprint handle).length ∧
      family.HasPayloadAt (family.packetSelectorFootprint handle) :=
  ⟨family.packetSelectorFootprint_hasPacketPayloadSelectorAt handle,
    family.packetSelectorFootprint_sublist_carrier handle,
    family.packetSelectorFootprint_large handle,
    family.packetSelectorFootprint_hasPayloadAt handle⟩

/-! ## Exact encoded selectors -/

/-- One accepted canonical code decodes to the exact requested footprint. -/
def TerminalBN6GroupedFamily.IsEncodedPacketSelectorAt
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (bits : Concrete.BitString) (footprint : List Atom) : Prop :=
  ∃ handle : family.PacketSelectorHandle,
    family.decodePacketSelectorHandle bits = some handle ∧
      family.packetSelectorFootprint handle = footprint

/-- Existence of an accepted canonical code for the requested footprint. -/
def TerminalBN6GroupedFamily.HasEncodedPacketSelectorAt
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom) : Prop :=
  ∃ bits : Concrete.BitString,
    family.IsEncodedPacketSelectorAt bits footprint

/-- Encoded selectors and the exact finite payload selectors describe the same
    footprints. -/
theorem TerminalBN6GroupedFamily.hasEncodedPacketSelectorAt_iff_payloadSelector
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom) :
    family.HasEncodedPacketSelectorAt footprint ↔
      family.HasPacketPayloadSelectorAt footprint := by
  constructor
  · rintro ⟨bits, handle, _decoded, footprintEquation⟩
    apply (family.hasFinitePacketSelectorHandleAt_iff_payloadSelector
      footprint).1
    exact ⟨handle, footprintEquation⟩
  · intro selector
    obtain ⟨handle, footprintEquation⟩ :=
      (family.hasFinitePacketSelectorHandleAt_iff_payloadSelector
        footprint).2 selector
    exact ⟨family.encodePacketSelectorHandle handle, handle,
      family.decodePacketSelectorHandle_encode handle, footprintEquation⟩

/-- A payload selector has exactly one accepted canonical bitstring. -/
theorem TerminalBN6GroupedFamily.existsUnique_encodedPacketSelector_iff_payloadSelector
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom) :
    (∃ bits : Concrete.BitString,
      family.IsEncodedPacketSelectorAt bits footprint ∧
        ∀ other : Concrete.BitString,
          family.IsEncodedPacketSelectorAt other footprint -> other = bits) ↔
      family.HasPacketPayloadSelectorAt footprint := by
  constructor
  · rintro ⟨bits, encoded, _unique⟩
    exact (family.hasEncodedPacketSelectorAt_iff_payloadSelector footprint).1
      ⟨bits, encoded⟩
  · intro selector
    obtain ⟨handle, footprintEquation, handleUnique⟩ :=
      (family.existsUnique_packetSelectorHandle_iff_payloadSelector
        footprint).2 selector
    refine ⟨family.encodePacketSelectorHandle handle,
      ⟨handle, family.decodePacketSelectorHandle_encode handle,
        footprintEquation⟩, ?_⟩
    intro other
    rintro ⟨otherHandle, otherDecoded, otherFootprintEquation⟩
    have otherHandleEquation : otherHandle = handle :=
      handleUnique otherHandle otherFootprintEquation
    have otherCanonical :=
      family.decodePacketSelectorHandle_canonical other otherHandle
        otherDecoded
    rw [otherHandleEquation] at otherCanonical
    exact otherCanonical.symm

/-! ## Exhaustive encoded Packet outcome -/

/-- The exact accepted selector-code information available in every Packet
    branch. -/
inductive TerminalPacketEncodedSelectorConclusion
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) : Prop where
  | pair
      (carrierLength : family.carrier.length = 2)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (selector : family.HasEncodedPacketSelectorAt family.carrier) :
      TerminalPacketEncodedSelectorConclusion family
  | balancedTriple
      (carrierLength : family.carrier.length = 3)
      (pairMass : Nat)
      (pairPositive : 0 < pairMass)
      (everyPair : ∀ footprint, footprint.Sublist family.carrier ->
        footprint.length = 2 ->
          family.hypergraph.footprintWeight footprint = pairMass)
      (selectors : ∀ footprint, footprint.Sublist family.carrier ->
        footprint.length = 2 ->
          family.HasEncodedPacketSelectorAt footprint) :
      TerminalPacketEncodedSelectorConclusion family
  | fullSpan
      (carrierLength : 3 ≤ family.carrier.length)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (selector : family.HasEncodedPacketSelectorAt family.carrier) :
      TerminalPacketEncodedSelectorConclusion family

/-- Upgrade every payload-selector branch to an accepted canonical bitstring
    without changing its alternatives. -/
theorem TerminalPacketPayloadSelectorConclusion.selectorCodes
    {Atom Payload : Type} [DecidableEq Atom]
    {family : TerminalBN6GroupedFamily Atom Payload}
    (conclusion : TerminalPacketPayloadSelectorConclusion family) :
    TerminalPacketEncodedSelectorConclusion family := by
  cases conclusion with
  | pair carrierLength fullPositive selector =>
      exact TerminalPacketEncodedSelectorConclusion.pair carrierLength
        fullPositive
        ((family.hasEncodedPacketSelectorAt_iff_payloadSelector
          family.carrier).2 selector)
  | balancedTriple carrierLength pairMass pairPositive everyPair selectors =>
      apply TerminalPacketEncodedSelectorConclusion.balancedTriple
        carrierLength pairMass pairPositive everyPair
      intro footprint footprintSublist footprintLength
      exact (family.hasEncodedPacketSelectorAt_iff_payloadSelector
        footprint).2 (selectors footprint footprintSublist footprintLength)
  | fullSpan carrierLength fullPositive selector =>
      exact TerminalPacketEncodedSelectorConclusion.fullSpan carrierLength
        fullPositive
        ((family.hasEncodedPacketSelectorAt_iff_payloadSelector
          family.carrier).2 selector)

/-- Every exact BN6 packet conclusion has an accepted canonical selector code
    in the same explicit grouped family. -/
theorem TerminalBN6PacketConclusion.selectorCodes
    {Atom Payload : Type} [DecidableEq Atom]
    {family : TerminalBN6GroupedFamily Atom Payload}
    (conclusion : TerminalBN6PacketConclusion family) :
    TerminalPacketEncodedSelectorConclusion family :=
  conclusion.payloadSelectors.selectorCodes

/-- BN6 followed by seed extraction, exact finite membership, canonical handle
    construction, and total fail-closed selector encoding. -/
theorem terminalBN6_packet_selector_codes
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (carrierAtLeastTwo : 2 ≤ family.carrier.length)
    (constant : family.ConstantActivation) :
    TerminalPacketEncodedSelectorConclusion family :=
  (terminalBN6_hypergraph_packet family carrierAtLeastTwo constant)
    |>.selectorCodes

end DirectWire
end PNP
