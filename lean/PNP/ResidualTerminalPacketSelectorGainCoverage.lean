/-
Copyright (c) 2026 PNP Labs.

Proof-bearing gain coverage for the exhaustive Packet selector-universe scan.
An explicit certificate states that every strict equivalent gain from the
current implementation occurs as an original payload atom in one canonical
source cell of the supplied grouped family.  Under exactly that premise, the
existing exhaustive scan returns either a genuine source-atom gain or a
kernel-checked ZeroSlack result.

The coverage certificate, grouped family, and candidate implementations remain
explicit inputs.  In particular, this module does not construct the
certificate from terminal data, prove selector faithfulness or compatibility,
construct replacement candidates, establish an encoded-size or polynomial
runtime bound, produce typed blockers or HB closure, complete PkgC, ZeroSlack,
or PCCMin globally, put SAT in P, remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPacketSelectorUniverseGainScan
import PNP.ResidualGainStopping

namespace PNP
namespace DirectWire

/-! ## Explicit coverage certificate -/

/-- A proof-bearing certificate that the supplied Packet selector universe
    contains every strict equivalent gain from `current`.  Coverage records the
    exact canonical handle, original source atom, and payload identity; it is a
    premise, not something inferred from finite scan failure. -/
structure TerminalPacketSelectorGainCoverage
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs) : Prop where
  covers : ∀ next : Implementation inputs outputs,
    StrictEquivalentGain current next ->
      ∃ handle : family.PacketSelectorHandle,
        ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
          atom ∈ (family.packetSelectorCell handle).atoms ∧
            atom.payload = next

/-- Certified coverage turns family-wide source-atom no-gain into global
    absence of a strict equivalent gain. -/
theorem TerminalPacketSelectorGainCoverage.noStrictEquivalentGain
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    {current : Implementation inputs outputs}
    (coverage : TerminalPacketSelectorGainCoverage family current)
    (noGain : ∀ handle : family.PacketSelectorHandle,
      ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
        ¬StrictEquivalentGain current atom.payload) :
    ∀ next : Implementation inputs outputs,
      ¬StrictEquivalentGain current next := by
  intro next verified
  obtain ⟨handle, atom, atomMember, payloadEquation⟩ :=
    coverage.covers next verified
  exact noGain handle atom atomMember (by
    simpa [payloadEquation] using verified)

/-- An unresolved exhaustive scan plus the explicit coverage certificate gives
    a proof-bearing semantic minimum. -/
def TerminalPacketSelectorGainCoverage.zeroSlackResult
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    {current : Implementation inputs outputs}
    (coverage : TerminalPacketSelectorGainCoverage family current)
    (noGain : ∀ handle : family.PacketSelectorHandle,
      ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
        ¬StrictEquivalentGain current atom.payload) :
    ZeroSlackResult current :=
  { minimum :=
      (isSemanticallyMinimum_iff_forall_not_strictEquivalentGain current).2
        (coverage.noStrictEquivalentGain noGain) }

/-- The certified no-gain result has exactly zero reference residual slack. -/
theorem TerminalPacketSelectorGainCoverage.residualSlack_eq_zero_of_noGain
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    {current : Implementation inputs outputs}
    (coverage : TerminalPacketSelectorGainCoverage family current)
    (noGain : ∀ handle : family.PacketSelectorHandle,
      ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
        ¬StrictEquivalentGain current atom.payload) :
    residualSlack current = 0 :=
  (coverage.zeroSlackResult noGain).sound

/-! ## Certified executable outcome -/

/-- Exact result of combining the exhaustive finite scan with an explicit
    certificate that its source payloads cover every possible gain. -/
inductive TerminalPacketSelectorCoveredGainOutcome
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs) : Type where
  | gain
      (handle : family.PacketSelectorHandle)
      (atom : TerminalBN6PayloadAtom (Implementation inputs outputs))
      (atomMember : atom ∈ (family.packetSelectorCell handle).atoms)
      (verified : StrictEquivalentGain current atom.payload) :
      TerminalPacketSelectorCoveredGainOutcome family current
  | zeroSlack (result : ZeroSlackResult current) :
      TerminalPacketSelectorCoveredGainOutcome family current

/-- Run the existing exhaustive scan and discharge its unresolved branch only
    through the separately supplied global gain-coverage certificate. -/
def TerminalBN6GroupedFamily.scanCoveredPacketSelectorGains
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (coverage : TerminalPacketSelectorGainCoverage family current) :
    TerminalPacketSelectorCoveredGainOutcome family current :=
  match family.scanPacketSelectorUniverseGains current with
  | .gain handle atom atomMember verified =>
      .gain handle atom atomMember verified
  | .unresolved noGain => .zeroSlack (coverage.zeroSlackResult noGain)

/-- The certified scan returns exactly an original source-atom gain or a
    proof-bearing ZeroSlack result for the current implementation. -/
theorem TerminalPacketSelectorCoveredGainOutcome.sound
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    {current : Implementation inputs outputs}
    (outcome : TerminalPacketSelectorCoveredGainOutcome family current) :
    (∃ handle : family.PacketSelectorHandle,
      ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          StrictEquivalentGain current atom.payload) ∨
      ZeroSlackResult current := by
  cases outcome with
  | gain handle atom atomMember verified =>
      exact Or.inl ⟨handle, atom, atomMember, verified⟩
  | zeroSlack result => exact Or.inr result

/-- Every certified outcome either strictly decreases residual slack through
    its disclosed source atom or proves the current residual slack is zero. -/
theorem TerminalPacketSelectorCoveredGainOutcome.residualSlack_spec
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    {current : Implementation inputs outputs}
    (outcome : TerminalPacketSelectorCoveredGainOutcome family current) :
    (∃ handle : family.PacketSelectorHandle,
      ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          residualSlack atom.payload < residualSlack current) ∨
      residualSlack current = 0 := by
  cases outcome with
  | gain handle atom atomMember verified =>
      exact Or.inl
        ⟨handle, atom, atomMember, verified.strictResidualDescent⟩
  | zeroSlack result => exact Or.inr result.sound

/-- The executable complete scan satisfies the certified gain-or-ZeroSlack
    interface. -/
theorem TerminalBN6GroupedFamily.scanCoveredPacketSelectorGains_sound
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (coverage : TerminalPacketSelectorGainCoverage family current) :
    (∃ handle : family.PacketSelectorHandle,
      ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          StrictEquivalentGain current atom.payload) ∨
      ZeroSlackResult current :=
  (family.scanCoveredPacketSelectorGains current coverage).sound

/-! ## Packet alternatives with one certified scan -/

/-- Every encoded Packet branch is retained literally while carrying the
    certified gain-or-ZeroSlack outcome. -/
structure TerminalPacketSelectorGainCoverageConclusion
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs) : Type where
  packet : TerminalPacketEncodedSelectorConclusion family
  coveredScan : TerminalPacketSelectorCoveredGainOutcome family current

/-- Upgrade an existing encoded Packet conclusion with a certified scan. -/
def TerminalPacketEncodedSelectorConclusion.coveredGainScan
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    (current : Implementation inputs outputs)
    (coverage : TerminalPacketSelectorGainCoverage family current)
    (conclusion : TerminalPacketEncodedSelectorConclusion family) :
    TerminalPacketSelectorGainCoverageConclusion family current :=
  { packet := conclusion
    coveredScan := family.scanCoveredPacketSelectorGains current coverage }

/-- The coverage upgrade preserves the complete original Packet conclusion. -/
theorem TerminalPacketEncodedSelectorConclusion.coveredGainScan_packet
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    (current : Implementation inputs outputs)
    (coverage : TerminalPacketSelectorGainCoverage family current)
    (conclusion : TerminalPacketEncodedSelectorConclusion family) :
    (conclusion.coveredGainScan current coverage).packet = conclusion :=
  rfl

/-- BN6 followed by canonical selector coding, exhaustive scanning, and the
    explicit gain-coverage certificate. -/
def terminalBN6_packet_selector_covered_gain_scan
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (carrierAtLeastTwo : 2 ≤ family.carrier.length)
    (constant : family.ConstantActivation)
    (coverage : TerminalPacketSelectorGainCoverage family current) :
    TerminalPacketSelectorGainCoverageConclusion family current :=
  (terminalBN6_packet_selector_codes family carrierAtLeastTwo constant)
    |>.coveredGainScan current coverage

/-- The composed interface preserves every Packet alternative and returns
    either one exact source-cell gain or proof-bearing ZeroSlack. -/
theorem terminalBN6_packet_selector_covered_gain_scan_sound
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (carrierAtLeastTwo : 2 ≤ family.carrier.length)
    (constant : family.ConstantActivation)
    (coverage : TerminalPacketSelectorGainCoverage family current) :
    TerminalPacketEncodedSelectorConclusion family ∧
      ((∃ handle : family.PacketSelectorHandle,
        ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
          atom ∈ (family.packetSelectorCell handle).atoms ∧
            StrictEquivalentGain current atom.payload) ∨
        ZeroSlackResult current) :=
  ⟨terminalBN6_packet_selector_codes family carrierAtLeastTwo constant,
    family.scanCoveredPacketSelectorGains_sound current coverage⟩

end DirectWire
end PNP
