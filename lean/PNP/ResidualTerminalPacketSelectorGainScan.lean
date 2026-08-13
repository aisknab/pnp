/-
Copyright (c) 2026 PNP Labs.

Checked candidate-gain scanning for one exact Packet selector source cell.  A
canonical selector code is decoded fail closed, its original grouped cell is
selected, and every candidate implementation carried by that cell is scanned
with the existing executable strict-equivalent-gain checker.  The only local
outcomes are an original payload atom carrying a genuine `StrictEquivalentGain`
or proof that no candidate payload in that selected cell is such a gain.

The candidate implementations and grouped family remain explicit input data.
A local no-gain outcome is not a manuscript HN, budget, or lower-rank blocker
and does not imply global minimality or ZeroSlack.  This module does not build
replacement candidates, establish selector faithfulness or compatibility,
connect payload mass to charge surplus, derive the grouped family, establish an
encoded-size or polynomial-runtime bound, complete PkgC, ZeroSlack, or PCCMin,
put SAT in P, or prove P = NP.
-/

import PNP.ResidualTerminalPacketSelectorPayloadRealization
import PNP.ResidualRoutes

namespace PNP
namespace DirectWire

/-! ## Exact source-cell candidate list -/

/-- Candidate implementations are exactly the payloads of all original atoms
    in the cell selected by this canonical handle. -/
def TerminalBN6GroupedFamily.packetSelectorCandidateImplementations
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (handle : family.PacketSelectorHandle) :
    List (Implementation inputs outputs) :=
  (family.packetSelectorCell handle).atoms.map
    TerminalBN6PayloadAtom.payload

/-- Candidate-list membership is exactly membership of an original source-cell
    payload atom carrying that implementation. -/
theorem TerminalBN6GroupedFamily.mem_packetSelectorCandidateImplementations_iff
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (handle : family.PacketSelectorHandle)
    (candidate : Implementation inputs outputs) :
    candidate ∈ family.packetSelectorCandidateImplementations handle ↔
      ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          atom.payload = candidate := by
  constructor
  · intro member
    rcases List.mem_map.1 member with ⟨atom, atomMember, payloadEquation⟩
    exact ⟨atom, atomMember, payloadEquation⟩
  · rintro ⟨atom, atomMember, payloadEquation⟩
    exact List.mem_map.2 ⟨atom, atomMember, payloadEquation⟩

/-! ## Proof-bearing local gain scan -/

/-- Exact outcome of scanning every candidate payload atom in one explicit
    source list.  `unresolved` is deliberately local to that list. -/
inductive TerminalPacketCandidateGainOutcome
    {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (atoms : List (TerminalBN6PayloadAtom
      (Implementation inputs outputs))) : Type where
  | gain
      (atom : TerminalBN6PayloadAtom (Implementation inputs outputs))
      (atomMember : atom ∈ atoms)
      (verified : StrictEquivalentGain current atom.payload) :
      TerminalPacketCandidateGainOutcome current atoms
  | unresolved
      (noGain : ∀ atom, atom ∈ atoms →
        ¬StrictEquivalentGain current atom.payload) :
      TerminalPacketCandidateGainOutcome current atoms

/-- Execute the strict-equivalent-gain checker over every atom in one explicit
    source list while retaining exact original membership. -/
def scanTerminalPacketCandidateGains
    {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (atoms : List (TerminalBN6PayloadAtom
      (Implementation inputs outputs))) →
      TerminalPacketCandidateGainOutcome current atoms
  | [] => .unresolved (by simp)
  | head :: tail =>
      if checked : strictEquivalentGainBool current head.payload = true then
        .gain head (List.Mem.head tail) (strictEquivalentGainBool_sound checked)
      else
        match scanTerminalPacketCandidateGains current tail with
        | .gain atom atomMember verified =>
            .gain atom (List.Mem.tail head atomMember) verified
        | .unresolved noTailGain =>
            .unresolved (by
              intro atom atomMember verified
              rcases List.mem_cons.mp atomMember with headEquation | tailMember
              · subst atom
                exact checked (strictEquivalentGainBool_complete verified)
              · exact noTailGain atom tailMember verified)

/-- Execute the exact finite candidate scan for one decoded selector handle. -/
def TerminalBN6GroupedFamily.packetSelectorGainOutcome
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (handle : family.PacketSelectorHandle) :
    TerminalPacketCandidateGainOutcome current
      (family.packetSelectorCell handle).atoms :=
  scanTerminalPacketCandidateGains current
    (family.packetSelectorCell handle).atoms

/-- Every local outcome is exactly a verified original-atom gain or exact
    absence of such a gain among the selected cell's original atoms. -/
theorem TerminalPacketCandidateGainOutcome.sound
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {atoms : List (TerminalBN6PayloadAtom
      (Implementation inputs outputs))}
    (outcome : TerminalPacketCandidateGainOutcome current atoms) :
    (∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
      atom ∈ atoms ∧
        StrictEquivalentGain current atom.payload) ∨
      (∀ atom, atom ∈ atoms →
        ¬StrictEquivalentGain current atom.payload) := by
  cases outcome with
  | gain atom atomMember verified =>
      exact Or.inl ⟨atom, atomMember, verified⟩
  | unresolved noGain => exact Or.inr noGain

/-- Every gain exposed by the selector scan strictly descends in the same
    residual slack used by the global gain-chain interface. -/
theorem TerminalPacketCandidateGainOutcome.gain_strictResidualDescent
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (atom : TerminalBN6PayloadAtom (Implementation inputs outputs))
    (verified : StrictEquivalentGain current atom.payload) :
    residualSlack atom.payload < residualSlack current :=
  verified.strictResidualDescent

/-! ## Total fail-closed decoded scan -/

/-- Proof-bearing scan attached to the exact handle accepted from one input
    bitstring. -/
structure TerminalPacketSelectorGainScan
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs) where
  handle : family.PacketSelectorHandle
  outcome : TerminalPacketCandidateGainOutcome current
    (family.packetSelectorCell handle).atoms

/-- Decode a canonical Packet selector and scan every candidate implementation
    in its exact original source cell; malformed codes fail closed. -/
def TerminalBN6GroupedFamily.scanPacketSelectorGains
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (bits : Concrete.BitString) :
    Option (TerminalPacketSelectorGainScan family current) :=
  match family.decodePacketSelectorHandle bits with
  | none => none
  | some handle => some
      { handle := handle
        outcome := family.packetSelectorGainOutcome current handle }

/-- The checked scan rejects exactly when the canonical selector decoder
    rejects. Local no-gain is represented inside an accepted scan. -/
theorem TerminalBN6GroupedFamily.scanPacketSelectorGains_eq_none_iff
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (bits : Concrete.BitString) :
    family.scanPacketSelectorGains current bits = none ↔
      family.decodePacketSelectorHandle bits = none := by
  unfold TerminalBN6GroupedFamily.scanPacketSelectorGains
  split <;> simp_all

/-- A scan exists exactly when the total canonical decoder accepts one
    handle. -/
theorem TerminalBN6GroupedFamily.exists_scanPacketSelectorGains_iff
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (bits : Concrete.BitString) :
    (∃ scan, family.scanPacketSelectorGains current bits = some scan) ↔
      ∃ handle, family.decodePacketSelectorHandle bits = some handle := by
  constructor
  · rintro ⟨scan, scanned⟩
    unfold TerminalBN6GroupedFamily.scanPacketSelectorGains at scanned
    split at scanned
    next rejected => simp at scanned
    next handle accepted =>
      cases scanned
      exact ⟨handle, accepted⟩
  · rintro ⟨handle, decoded⟩
    refine ⟨
      { handle := handle
        outcome := family.packetSelectorGainOutcome current handle }, ?_⟩
    unfold TerminalBN6GroupedFamily.scanPacketSelectorGains
    rw [decoded]

/-- A returned scan carries exactly the handle accepted by the decoder. -/
theorem TerminalBN6GroupedFamily.decodePacketSelectorHandle_eq_some_of_gainScan
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (bits : Concrete.BitString)
    (scan : TerminalPacketSelectorGainScan family current)
    (scanned : family.scanPacketSelectorGains current bits = some scan) :
    family.decodePacketSelectorHandle bits = some scan.handle := by
  unfold TerminalBN6GroupedFamily.scanPacketSelectorGains at scanned
  split at scanned
  next rejected => simp at scanned
  next handle accepted =>
    cases scanned
    exact accepted

/-- Every successful checked scan recovers the exact canonical input and exact
    original source cell before exposing its local gain outcome. -/
theorem TerminalBN6GroupedFamily.scanPacketSelectorGains_sound
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (bits : Concrete.BitString)
    (scan : TerminalPacketSelectorGainScan family current)
    (scanned : family.scanPacketSelectorGains current bits = some scan) :
    family.encodePacketSelectorHandle scan.handle = bits ∧
      family.packetSelectorCell scan.handle ∈ family.groups ∧
      (family.packetSelectorCell scan.handle).footprint =
        family.packetSelectorFootprint scan.handle ∧
      ((∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
        atom ∈ (family.packetSelectorCell scan.handle).atoms ∧
          StrictEquivalentGain current atom.payload) ∨
        (∀ atom, atom ∈ (family.packetSelectorCell scan.handle).atoms →
          ¬StrictEquivalentGain current atom.payload)) :=
  ⟨family.decodePacketSelectorHandle_canonical bits scan.handle
      (family.decodePacketSelectorHandle_eq_some_of_gainScan current bits
        scan scanned),
    family.packetSelectorCell_mem_groups scan.handle,
    family.packetSelectorCell_footprint scan.handle,
    scan.outcome.sound⟩

/-- Every canonical handle code has one successful exact local gain scan. -/
theorem TerminalBN6GroupedFamily.exists_scanPacketSelectorGains_encode
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (handle : family.PacketSelectorHandle) :
    ∃ scan,
      family.scanPacketSelectorGains current
        (family.encodePacketSelectorHandle handle) = some scan ∧
      scan.handle = handle := by
  let scan : TerminalPacketSelectorGainScan family current
      :=
    { handle := handle
      outcome := family.packetSelectorGainOutcome current handle }
  exact ⟨scan, by
    unfold TerminalBN6GroupedFamily.scanPacketSelectorGains
    rw [family.decodePacketSelectorHandle_encode handle], rfl⟩

/-! ## Exact scanned selectors and Packet alternatives -/

/-- Existence of one produced checked scan at the requested footprint. -/
def TerminalBN6GroupedFamily.HasPacketSelectorGainScanAt
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (footprint : List Atom) : Prop :=
  ∃ bits : Concrete.BitString,
    ∃ scan : TerminalPacketSelectorGainScan family current,
      family.scanPacketSelectorGains current bits = some scan ∧
        family.packetSelectorFootprint scan.handle = footprint

/-- Produced checked scans exist at exactly the already encoded selector
    footprints; the scan adds no selector-universe assumption. -/
theorem TerminalBN6GroupedFamily.hasPacketSelectorGainScanAt_iff_encoded
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (footprint : List Atom) :
    family.HasPacketSelectorGainScanAt current footprint ↔
      family.HasEncodedPacketSelectorAt footprint := by
  constructor
  · rintro ⟨bits, scan, _scanned, footprintEquation⟩
    exact ⟨bits, scan.handle,
      family.decodePacketSelectorHandle_eq_some_of_gainScan current bits
        scan _scanned,
      footprintEquation⟩
  · rintro ⟨bits, handle, decoded, footprintEquation⟩
    obtain ⟨scan, scanned⟩ :=
      (family.exists_scanPacketSelectorGains_iff current bits).2
        ⟨handle, decoded⟩
    have scanDecoded :=
      family.decodePacketSelectorHandle_eq_some_of_gainScan current bits
        scan scanned
    rw [decoded] at scanDecoded
    have handleEquation : scan.handle = handle :=
      (Option.some.inj scanDecoded).symm
    exact ⟨bits, scan, scanned, by
      rw [handleEquation]
      exact footprintEquation⟩

/-- The exact local gain-scan information available in every finite Packet
    branch. -/
inductive TerminalPacketGainScanConclusion
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs) : Prop where
  | pair
      (carrierLength : family.carrier.length = 2)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (scan : family.HasPacketSelectorGainScanAt current family.carrier) :
      TerminalPacketGainScanConclusion family current
  | balancedTriple
      (carrierLength : family.carrier.length = 3)
      (pairMass : Nat)
      (pairPositive : 0 < pairMass)
      (everyPair : ∀ footprint, footprint.Sublist family.carrier →
        footprint.length = 2 →
          family.hypergraph.footprintWeight footprint = pairMass)
      (scans : ∀ footprint, footprint.Sublist family.carrier →
        footprint.length = 2 →
          family.HasPacketSelectorGainScanAt current footprint) :
      TerminalPacketGainScanConclusion family current
  | fullSpan
      (carrierLength : 3 ≤ family.carrier.length)
      (fullPositive : 0 <
        family.hypergraph.footprintWeight family.carrier)
      (scan : family.HasPacketSelectorGainScanAt current family.carrier) :
      TerminalPacketGainScanConclusion family current

/-- Upgrade every encoded Packet selector branch to one exact checked local
    gain scan without changing its alternatives. -/
theorem TerminalPacketEncodedSelectorConclusion.gainScans
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    (current : Implementation inputs outputs)
    (conclusion : TerminalPacketEncodedSelectorConclusion family) :
    TerminalPacketGainScanConclusion family current := by
  cases conclusion with
  | pair carrierLength fullPositive selector =>
      exact TerminalPacketGainScanConclusion.pair carrierLength fullPositive
        ((family.hasPacketSelectorGainScanAt_iff_encoded current
          family.carrier).2 selector)
  | balancedTriple carrierLength pairMass pairPositive everyPair selectors =>
      apply TerminalPacketGainScanConclusion.balancedTriple carrierLength
        pairMass pairPositive everyPair
      intro footprint footprintSublist footprintLength
      exact (family.hasPacketSelectorGainScanAt_iff_encoded current
        footprint).2 (selectors footprint footprintSublist footprintLength)
  | fullSpan carrierLength fullPositive selector =>
      exact TerminalPacketGainScanConclusion.fullSpan carrierLength
        fullPositive
        ((family.hasPacketSelectorGainScanAt_iff_encoded current
          family.carrier).2 selector)

/-- Every exact BN6 Packet conclusion admits the corresponding exact checked
    local candidate-gain scans. -/
theorem TerminalBN6PacketConclusion.gainScans
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    (current : Implementation inputs outputs)
    (conclusion : TerminalBN6PacketConclusion family) :
    TerminalPacketGainScanConclusion family current :=
  conclusion.selectorCodes.gainScans current

/-- BN6 followed by canonical selector coding, exact source selection, and
    checked local candidate-gain scanning across every Packet branch. -/
theorem terminalBN6_packet_selector_gain_scans
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (carrierAtLeastTwo : 2 ≤ family.carrier.length)
    (constant : family.ConstantActivation) :
    TerminalPacketGainScanConclusion family current :=
  (terminalBN6_packet_selector_codes family carrierAtLeastTwo constant)
    |>.gainScans current

end DirectWire
end PNP
