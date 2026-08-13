/-
Copyright (c) 2026 PNP Labs.

Exhaustive checked gain scanning over every canonical selector in one arbitrary
finite explicit grouped BN6 family. Every input-relative handle is enumerated,
and every original candidate payload in its exact source cell is checked with
the existing executable strict-equivalent-gain checker. The only outcomes are
one source atom carrying a genuine `StrictEquivalentGain`, or exact absence of
such a gain throughout that supplied finite selector universe.

The grouped family and its candidate implementations remain explicit inputs.
Family-wide no-gain is not a manuscript HN, budget, or lower-rank blocker and
does not imply global minimality or ZeroSlack. This module does not establish
selector faithfulness or compatibility, construct replacement candidates,
connect payload mass to charge surplus, derive the grouped family, establish an
encoded-size or polynomial-runtime bound, complete PkgC, ZeroSlack, or PCCMin,
put SAT in P, or prove P = NP.
-/

import PNP.ResidualTerminalPacketSelectorGainScan

namespace PNP
namespace DirectWire

/-! ## Complete canonical handle enumeration -/

/-- The exact finite list of all canonical handles for this input-relative
    selector universe. -/
def TerminalBN6GroupedFamily.packetSelectorHandles
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) :
    List family.PacketSelectorHandle :=
  allFin family.packetPayloadSelectorUniverse.length

/-- Every canonical handle occurs in the exhaustive handle list. -/
theorem TerminalBN6GroupedFamily.mem_packetSelectorHandles
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload)
    (handle : family.PacketSelectorHandle) :
    handle ∈ family.packetSelectorHandles :=
  mem_allFin handle

/-- The handle enumeration has exactly one position for every grouped
    footprint in the input-relative universe. -/
theorem TerminalBN6GroupedFamily.packetSelectorHandles_length
    {Atom Payload : Type} [DecidableEq Atom]
    (family : TerminalBN6GroupedFamily Atom Payload) :
    family.packetSelectorHandles.length =
      family.packetPayloadSelectorUniverse.length :=
  allFin_length family.packetPayloadSelectorUniverse.length

/-! ## Proof-bearing scan over an arbitrary handle list -/

/-- Exact outcome of scanning every source-cell payload behind a supplied list
    of canonical handles. The unresolved proof is restricted exactly to that
    handle list. -/
inductive TerminalPacketSelectorHandleListGainOutcome
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (handles : List family.PacketSelectorHandle) : Type where
  | gain
      (handle : family.PacketSelectorHandle)
      (handleMember : handle ∈ handles)
      (atom : TerminalBN6PayloadAtom (Implementation inputs outputs))
      (atomMember : atom ∈ (family.packetSelectorCell handle).atoms)
      (verified : StrictEquivalentGain current atom.payload) :
      TerminalPacketSelectorHandleListGainOutcome family current handles
  | unresolved
      (noGain : ∀ handle, handle ∈ handles ->
        ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
          ¬StrictEquivalentGain current atom.payload) :
      TerminalPacketSelectorHandleListGainOutcome family current handles

/-- Scan each supplied handle's complete source-cell candidate list, stopping
    only on a proof-bearing strict equivalent gain. -/
def scanTerminalPacketSelectorHandleGains
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs) :
    (handles : List family.PacketSelectorHandle) ->
      TerminalPacketSelectorHandleListGainOutcome family current handles
  | [] => .unresolved (by simp)
  | head :: tail =>
      match family.packetSelectorGainOutcome current head with
      | .gain atom atomMember verified =>
          .gain head (List.Mem.head tail) atom atomMember verified
      | .unresolved noHeadGain =>
          match scanTerminalPacketSelectorHandleGains family current tail with
          | .gain handle handleMember atom atomMember verified =>
              .gain handle (List.Mem.tail head handleMember)
                atom atomMember verified
          | .unresolved noTailGain =>
              .unresolved (by
                intro handle handleMember atom atomMember verified
                rcases List.mem_cons.mp handleMember with headEquation |
                  tailMember
                · subst handle
                  exact noHeadGain atom atomMember verified
                · exact noTailGain handle tailMember atom atomMember verified)

/-- A handle-list scan is exactly either one original source-cell gain or
    absence of every such gain behind the supplied handles. -/
theorem TerminalPacketSelectorHandleListGainOutcome.sound
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    {current : Implementation inputs outputs}
    {handles : List family.PacketSelectorHandle}
    (outcome : TerminalPacketSelectorHandleListGainOutcome
      family current handles) :
    (∃ handle, handle ∈ handles ∧
      ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          StrictEquivalentGain current atom.payload) ∨
      (∀ handle, handle ∈ handles ->
        ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
          ¬StrictEquivalentGain current atom.payload) := by
  cases outcome with
  | gain handle handleMember atom atomMember verified =>
      exact Or.inl
        ⟨handle, handleMember, atom, atomMember, verified⟩
  | unresolved noGain => exact Or.inr noGain

/-! ## Exhaustive input-relative selector-universe scan -/

/-- Exact result for the complete canonical selector universe of one explicit
    grouped family. -/
inductive TerminalPacketSelectorUniverseGainOutcome
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs) : Type where
  | gain
      (handle : family.PacketSelectorHandle)
      (atom : TerminalBN6PayloadAtom (Implementation inputs outputs))
      (atomMember : atom ∈ (family.packetSelectorCell handle).atoms)
      (verified : StrictEquivalentGain current atom.payload) :
      TerminalPacketSelectorUniverseGainOutcome family current
  | unresolved
      (noGain : ∀ handle,
        ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
          ¬StrictEquivalentGain current atom.payload) :
      TerminalPacketSelectorUniverseGainOutcome family current

/-- Execute the checked gain scan at every canonical selector handle in the
    supplied explicit family. -/
def TerminalBN6GroupedFamily.scanPacketSelectorUniverseGains
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs) :
    TerminalPacketSelectorUniverseGainOutcome family current :=
  match scanTerminalPacketSelectorHandleGains family current
      family.packetSelectorHandles with
  | .gain handle _handleMember atom atomMember verified =>
      .gain handle atom atomMember verified
  | .unresolved noGain =>
      .unresolved (fun handle =>
        noGain handle (family.mem_packetSelectorHandles handle))

/-- The complete universe scan is exactly either one canonical source-cell
    gain or proof of no gain behind any canonical selector in the family. -/
theorem TerminalPacketSelectorUniverseGainOutcome.sound
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    {current : Implementation inputs outputs}
    (outcome : TerminalPacketSelectorUniverseGainOutcome family current) :
    (∃ handle : family.PacketSelectorHandle,
      ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          StrictEquivalentGain current atom.payload) ∨
      (∀ handle : family.PacketSelectorHandle,
        ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
          ¬StrictEquivalentGain current atom.payload) := by
  cases outcome with
  | gain handle atom atomMember verified =>
      exact Or.inl ⟨handle, atom, atomMember, verified⟩
  | unresolved noGain => exact Or.inr noGain

/-- The executable complete scan satisfies the exact universe-wide outcome. -/
theorem TerminalBN6GroupedFamily.scanPacketSelectorUniverseGains_sound
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs) :
    (∃ handle : family.PacketSelectorHandle,
      ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          StrictEquivalentGain current atom.payload) ∨
      (∀ handle : family.PacketSelectorHandle,
        ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
          ¬StrictEquivalentGain current atom.payload) :=
  (family.scanPacketSelectorUniverseGains current).sound

/-- A gain returned from the universe scan always strictly decreases the same
    residual slack used by the global gain-chain interface. -/
theorem TerminalPacketSelectorUniverseGainOutcome.gain_strictResidualDescent
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    {current : Implementation inputs outputs}
    (handle : family.PacketSelectorHandle)
    (atom : TerminalBN6PayloadAtom (Implementation inputs outputs))
    (_atomMember : atom ∈ (family.packetSelectorCell handle).atoms)
    (verified : StrictEquivalentGain current atom.payload) :
    residualSlack atom.payload < residualSlack current :=
  verified.strictResidualDescent

/-- Every gain witness from the exhaustive scan has a canonical accepted code,
    an original source cell, and its exact decoded footprint. -/
theorem TerminalBN6GroupedFamily.universeGain_source_and_code
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (handle : family.PacketSelectorHandle)
    (atom : TerminalBN6PayloadAtom (Implementation inputs outputs))
    (atomMember : atom ∈ (family.packetSelectorCell handle).atoms)
    (verified : StrictEquivalentGain current atom.payload) :
    family.decodePacketSelectorHandle
        (family.encodePacketSelectorHandle handle) = some handle ∧
      family.packetSelectorCell handle ∈ family.groups ∧
      (family.packetSelectorCell handle).footprint =
        family.packetSelectorFootprint handle ∧
      atom ∈ (family.packetSelectorCell handle).atoms ∧
      StrictEquivalentGain current atom.payload :=
  ⟨family.decodePacketSelectorHandle_encode handle,
    family.packetSelectorCell_mem_groups handle,
    family.packetSelectorCell_footprint handle,
    atomMember,
    verified⟩

/-- Universe-wide unresolved evidence rules out a gain in every successfully
    decoded source-cell scan, without turning that finite-family fact into a
    global blocker or minimum. -/
theorem TerminalBN6GroupedFamily.universeNoGain_of_gainScan
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (noGain : ∀ handle : family.PacketSelectorHandle,
      ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
        ¬StrictEquivalentGain current atom.payload)
    (bits : Concrete.BitString)
    (scan : TerminalPacketSelectorGainScan family current)
    (_scanned : family.scanPacketSelectorGains current bits = some scan)
    (atom : TerminalBN6PayloadAtom (Implementation inputs outputs))
    (atomMember : atom ∈
      (family.packetSelectorCell scan.handle).atoms) :
    ¬StrictEquivalentGain current atom.payload :=
  noGain scan.handle atom atomMember

/-! ## Packet alternatives with one shared exhaustive scan -/

/-- Every Packet conclusion is retained unchanged while carrying one
    exhaustive scan over the whole supplied selector universe. Keeping the
    existing proposition as a field avoids reconstructing or weakening any of
    its pair, balanced-triple, or full-span alternatives. -/
structure TerminalPacketSelectorUniverseGainScanConclusion
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs) : Type where
  packet : TerminalPacketEncodedSelectorConclusion family
  universeScan : TerminalPacketSelectorUniverseGainOutcome family current

/-- Upgrade every encoded Packet branch with the same exhaustive selector-
    universe scan, without changing its existing alternatives. -/
def TerminalPacketEncodedSelectorConclusion.universeGainScan
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    (current : Implementation inputs outputs)
    (conclusion : TerminalPacketEncodedSelectorConclusion family) :
    TerminalPacketSelectorUniverseGainScanConclusion family current :=
  { packet := conclusion
    universeScan := family.scanPacketSelectorUniverseGains current }

/-- The universe-scan upgrade preserves the complete original Packet
    conclusion literally. -/
theorem TerminalPacketEncodedSelectorConclusion.universeGainScan_packet
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    (current : Implementation inputs outputs)
    (conclusion : TerminalPacketEncodedSelectorConclusion family) :
    (conclusion.universeGainScan current).packet = conclusion :=
  rfl

/-- Every exact finite BN6 Packet conclusion admits one exhaustive checked
    gain scan over all canonical selectors in its explicit family. -/
def TerminalBN6PacketConclusion.universeGainScan
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    (current : Implementation inputs outputs)
    (conclusion : TerminalBN6PacketConclusion family) :
    TerminalPacketSelectorUniverseGainScanConclusion family current :=
  conclusion.selectorCodes.universeGainScan current

/-- BN6 followed by canonical selector coding and one exhaustive checked scan
    across the entire supplied finite selector universe. -/
def terminalBN6_packet_selector_universe_gain_scan
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (carrierAtLeastTwo : 2 ≤ family.carrier.length)
    (constant : family.ConstantActivation) :
    TerminalPacketSelectorUniverseGainScanConclusion family current :=
  (terminalBN6_packet_selector_codes family carrierAtLeastTwo constant)
    |>.universeGainScan current

/-- The composed BN6 interface preserves its complete Packet conclusion and
    exposes the exact exhaustive gain-or-family-local-no-gain disjunction. -/
theorem terminalBN6_packet_selector_universe_gain_scan_sound
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs))
    (current : Implementation inputs outputs)
    (carrierAtLeastTwo : 2 ≤ family.carrier.length)
    (constant : family.ConstantActivation) :
    TerminalPacketEncodedSelectorConclusion family ∧
      ((∃ handle : family.PacketSelectorHandle,
        ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
          atom ∈ (family.packetSelectorCell handle).atoms ∧
            StrictEquivalentGain current atom.payload) ∨
        (∀ handle : family.PacketSelectorHandle,
          ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
            ¬StrictEquivalentGain current atom.payload)) :=
  ⟨terminalBN6_packet_selector_codes family carrierAtLeastTwo constant,
    family.scanPacketSelectorUniverseGains_sound current⟩

end DirectWire
end PNP
