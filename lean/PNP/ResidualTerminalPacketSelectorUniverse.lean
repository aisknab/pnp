/-
Copyright (c) 2026 PNP Labs.

Finite payload-selector universe membership after Packet seed extraction.  The
universe is the duplicate-free list of exact grouped BN6 footprints already
present in the input family.  A payload selector records membership in that
finite list together with the existing carrier-containment, footprint-size,
and original cell-and-atom payload witness.

This is deliberately narrower than the manuscript's selector universe.  It
does not define an encoded selector handle, prove manuscript-level
faithfulness or compatibility, construct a realizer or route, or establish a
polynomial enumeration or size bound.  The grouped family remains explicit
input data.
-/

import PNP.ResidualTerminalPacketSelectorSeeds

namespace PNP
namespace DirectWire

/-! ## Canonical finite payload-selector universe -/

/-- The finite Packet payload-selector universe supplied by the exact grouped
    BN6 input: one selector footprint for each grouped cell. -/
def TerminalBN6GroupedFamily.packetPayloadSelectorUniverse
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) : List (List Atom) :=
  family.groups.map TerminalBN6GroupedCell.footprint

/-- Exact grouping makes the finite payload-selector universe duplicate-free. -/
theorem TerminalBN6GroupedFamily.packetPayloadSelectorUniverse_nodup
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) :
    family.packetPayloadSelectorUniverse.Nodup :=
  family.groupFootprintsNodup

/-- Membership is exactly the existence of an original grouped cell at the
    same footprint. -/
theorem TerminalBN6GroupedFamily.mem_packetPayloadSelectorUniverse_iff
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom) :
    footprint ∈ family.packetPayloadSelectorUniverse ↔
      ∃ cell, cell ∈ family.groups ∧ cell.footprint = footprint := by
  constructor
  · intro footprintMember
    rcases List.mem_map.1 footprintMember with
      ⟨cell, cellMember, footprintEquation⟩
    exact ⟨cell, cellMember, footprintEquation⟩
  · rintro ⟨cell, cellMember, footprintEquation⟩
    exact List.mem_map.2 ⟨cell, cellMember, footprintEquation⟩

/-- A finite payload selector is a raw Packet seed whose exact footprint is a
    member of the grouped family's canonical finite universe.  "Payload" here
    means only retention of the original grouped cell and atom witness. -/
def TerminalBN6GroupedFamily.HasPacketPayloadSelectorAt
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom) : Prop :=
  footprint ∈ family.packetPayloadSelectorUniverse ∧
    family.HasPacketSelectorSeedAt footprint

/-- Every raw payload-backed seed is automatically represented in the exact
    finite universe because its payload witness names a grouped cell at that
    footprint. -/
theorem TerminalBN6GroupedFamily.hasPacketPayloadSelectorAt_of_seed
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom)
    (seed : family.HasPacketSelectorSeedAt footprint) :
    family.HasPacketPayloadSelectorAt footprint := by
  rcases seed with
    ⟨footprintSublist, footprintLarge, cell, cellMember,
      cellFootprint, atom, atomMember⟩
  constructor
  · exact (family.mem_packetPayloadSelectorUniverse_iff footprint).2
      ⟨cell, cellMember, cellFootprint⟩
  · exact ⟨footprintSublist, footprintLarge, cell, cellMember,
      cellFootprint, atom, atomMember⟩

/-! ## Exhaustive finite-universe outcome -/

/-- The exact finite payload-selector information available in every Packet
    branch.  The branch structure and positivity facts are retained unchanged
    from the seed conclusion. -/
inductive TerminalPacketPayloadSelectorConclusion
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) : Prop where
  | pair
      (carrierLength : family.carrier.length = 2)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (selector : family.HasPacketPayloadSelectorAt family.carrier) :
      TerminalPacketPayloadSelectorConclusion family
  | balancedTriple
      (carrierLength : family.carrier.length = 3)
      (pairMass : Nat)
      (pairPositive : 0 < pairMass)
      (everyPair : ∀ footprint, footprint.Sublist family.carrier ->
        footprint.length = 2 ->
          family.hypergraph.footprintWeight footprint = pairMass)
      (selectors : ∀ footprint, footprint.Sublist family.carrier ->
        footprint.length = 2 ->
          family.HasPacketPayloadSelectorAt footprint) :
      TerminalPacketPayloadSelectorConclusion family
  | fullSpan
      (carrierLength : 3 ≤ family.carrier.length)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (selector : family.HasPacketPayloadSelectorAt family.carrier) :
      TerminalPacketPayloadSelectorConclusion family

/-- Seed extraction followed by exact finite-universe membership. -/
theorem TerminalPacketSelectorSeedConclusion.payloadSelectors
    {Atom Payload : Type} [DecidableEq Atom]
    {family : TerminalBN6GroupedFamily Atom Payload}
    (conclusion : TerminalPacketSelectorSeedConclusion family) :
    TerminalPacketPayloadSelectorConclusion family := by
  cases conclusion with
  | pair carrierLength fullPositive seed =>
      exact TerminalPacketPayloadSelectorConclusion.pair carrierLength
        fullPositive
        (family.hasPacketPayloadSelectorAt_of_seed family.carrier seed)
  | balancedTriple carrierLength pairMass pairPositive everyPair seeds =>
      apply TerminalPacketPayloadSelectorConclusion.balancedTriple
        carrierLength pairMass pairPositive everyPair
      intro footprint footprintSublist footprintLength
      exact family.hasPacketPayloadSelectorAt_of_seed footprint
        (seeds footprint footprintSublist footprintLength)
  | fullSpan carrierLength fullPositive seed =>
      exact TerminalPacketPayloadSelectorConclusion.fullSpan carrierLength
        fullPositive
        (family.hasPacketPayloadSelectorAt_of_seed family.carrier seed)

/-- Every exact BN6 packet conclusion has an exhaustive payload selector in
    the canonical finite universe of the same grouped family. -/
theorem TerminalBN6PacketConclusion.payloadSelectors
    {Atom Payload : Type} [DecidableEq Atom]
    {family : TerminalBN6GroupedFamily Atom Payload}
    (conclusion : TerminalBN6PacketConclusion family) :
    TerminalPacketPayloadSelectorConclusion family :=
  conclusion.selectorSeeds.payloadSelectors

/-- BN6 followed by seed extraction and exact finite payload-selector universe
    membership, still over arbitrary explicit grouped input data. -/
theorem terminalBN6_packet_payload_selectors
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (carrierAtLeastTwo : 2 ≤ family.carrier.length)
    (constant : family.ConstantActivation) :
    TerminalPacketPayloadSelectorConclusion family :=
  (terminalBN6_hypergraph_packet family carrierAtLeastTwo constant)
    |>.payloadSelectors

end DirectWire
end PNP
