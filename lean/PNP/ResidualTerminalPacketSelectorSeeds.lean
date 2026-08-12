/-
Copyright (c) 2026 PNP Labs.

Finite Packet selector-seed extraction from the exact BN6 packet conclusion.
The input family and its anchor carrier remain arbitrary and finite.  A seed is
not a bare footprint: it records that the footprint lies in the carrier, has
selector-relevant size, and retains an original grouped cell and positive atom
payload through `HasPayloadAt`.

The named theorem consumes any proved BN6 conclusion.  It returns a seed at the
full pair footprint, seeds at every pair footprint of a positive balanced
triple, or a seed at the positive full-span footprint.  In the mixed
three-anchor branch it follows the supplied positive alternative without
silently asserting that both alternatives are positive.

These are raw payload-backed seed inputs only.  This module does not prove that
a seed belongs to the manuscript's selector universe, construct a faithful or
compatible selector, construct realizers or routes, establish enumeration or
polynomial runtime, complete PkgC, ZeroSlack, or PCCMin, put SAT in P, or prove
P = NP.
-/

import PNP.ResidualTerminalBN6HypergraphPacket

namespace PNP
namespace DirectWire

/-! ## Payload-backed selector seeds -/

/-- A raw Packet selector seed is a supported nontrivial BN6 footprint that
    still carries an original grouped cell and positive atom payload. -/
def TerminalBN6GroupedFamily.HasPacketSelectorSeedAt
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom) : Prop :=
  footprint.Sublist family.carrier ∧
    2 ≤ footprint.length ∧
      family.HasPayloadAt footprint

/-- Exact payload retention plus the footprint side conditions constructs a
    raw Packet selector seed without choosing a fixed carrier. -/
theorem TerminalBN6GroupedFamily.hasPacketSelectorSeedAt_of_hasPayloadAt
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (footprint : List Atom)
    (footprintSublist : footprint.Sublist family.carrier)
    (footprintLarge : 2 ≤ footprint.length)
    (payload : family.HasPayloadAt footprint) :
    family.HasPacketSelectorSeedAt footprint :=
  ⟨footprintSublist, footprintLarge, payload⟩

/-! ## Exhaustive seed outcome -/

/-- The raw selector-seed information mechanically available from every BN6
    packet branch.  The balanced-triple constructor covers every supported pair
    footprint.  The full-span constructor covers both the positive full-span
    side of a three-anchor mixed packet and the four-or-more-anchor branch. -/
inductive TerminalPacketSelectorSeedConclusion
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) : Prop where
  | pair
      (carrierLength : family.carrier.length = 2)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (seed : family.HasPacketSelectorSeedAt family.carrier) :
      TerminalPacketSelectorSeedConclusion family
  | balancedTriple
      (carrierLength : family.carrier.length = 3)
      (pairMass : Nat)
      (pairPositive : 0 < pairMass)
      (everyPair : ∀ footprint, footprint.Sublist family.carrier ->
        footprint.length = 2 ->
          family.hypergraph.footprintWeight footprint = pairMass)
      (seeds : ∀ footprint, footprint.Sublist family.carrier ->
        footprint.length = 2 ->
          family.HasPacketSelectorSeedAt footprint) :
      TerminalPacketSelectorSeedConclusion family
  | fullSpan
      (carrierLength : 3 ≤ family.carrier.length)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (seed : family.HasPacketSelectorSeedAt family.carrier) :
      TerminalPacketSelectorSeedConclusion family

/-- Every exact BN6 packet conclusion yields the corresponding payload-backed
    raw selector seed outcome over the same arbitrary finite family. -/
theorem TerminalBN6PacketConclusion.selectorSeeds
    {Atom Payload : Type} [DecidableEq Atom]
    {family : TerminalBN6GroupedFamily Atom Payload}
    (conclusion : TerminalBN6PacketConclusion family) :
    TerminalPacketSelectorSeedConclusion family := by
  cases conclusion with
  | pair carrierLength _fullWeight fullPositive payload =>
      apply TerminalPacketSelectorSeedConclusion.pair carrierLength fullPositive
      exact family.hasPacketSelectorSeedAt_of_hasPayloadAt family.carrier
        (List.Sublist.refl family.carrier) (by omega) payload
  | balancedTripleOrFullSpan carrierLength pairMass everyPair _massEquation
      positiveAlternative balancedPayloads fullSpanPayload =>
      cases positiveAlternative with
      | inl pairPositive =>
          apply TerminalPacketSelectorSeedConclusion.balancedTriple
            carrierLength pairMass pairPositive everyPair
          intro footprint footprintSublist footprintLength
          exact family.hasPacketSelectorSeedAt_of_hasPayloadAt footprint
            footprintSublist (by omega)
            (balancedPayloads pairPositive footprint footprintSublist
              footprintLength)
      | inr fullPositive =>
          apply TerminalPacketSelectorSeedConclusion.fullSpan (by omega)
            fullPositive
          exact family.hasPacketSelectorSeedAt_of_hasPayloadAt family.carrier
            (List.Sublist.refl family.carrier) (by omega)
            (fullSpanPayload fullPositive)
  | fullSpan carrierLarge _properFootprintsZero _fullWeight fullPositive payload =>
      apply TerminalPacketSelectorSeedConclusion.fullSpan (by omega)
        fullPositive
      exact family.hasPacketSelectorSeedAt_of_hasPayloadAt family.carrier
        (List.Sublist.refl family.carrier) (by omega) payload

/-- BN6 followed by Packet seed extraction, still parameterized by an arbitrary
    finite grouped family and the explicit BCEL constant-cut premise. -/
theorem terminalBN6_packet_selector_seeds
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (carrierAtLeastTwo : 2 ≤ family.carrier.length)
    (constant : family.ConstantActivation) :
    TerminalPacketSelectorSeedConclusion family :=
  (terminalBN6_hypergraph_packet family carrierAtLeastTwo constant).selectorSeeds

end DirectWire
end PNP
