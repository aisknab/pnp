import PNP.ResidualTerminalPacketUnitChargeBlueprintRealizer

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

/-! ## Concrete accepted and rejected blueprints -/

def unitChargeZeroGateIdentity : Implementation 1 1 :=
  ⟨0, Candidate.ofDirectWireWord identityProgram identityWord⟩

def unitChargeNotImplementation : Implementation 1 1 :=
  ⟨1, Candidate.ofDirectWireWord notProgram notWord⟩

/-- The one current gate is unmatched and the zero-gate replacement preserves
    the identity semantics. -/
def acceptedUnitChargeBlueprint :
    TerminalPacketUnitChargeBlueprint redundantIdentityImplementation where
  next := unitChargeZeroGateIdentity
  pairing := []
  unmatched := [0]

example : acceptedUnitChargeBlueprint.check = true := by
  rfl

def acceptedUnitChargeBlueprintValid : acceptedUnitChargeBlueprint.Valid :=
  (acceptedUnitChargeBlueprint.check_eq_true_iff).1 (by rfl)

example :
    TerminalPacketChargeSurplus
      (List.range redundantIdentityImplementation.gateCount)
      (List.range acceptedUnitChargeBlueprint.next.gateCount)
      (fun _ : Nat => 1) (fun _ : Nat => 1) :=
  acceptedUnitChargeBlueprintValid.chargeSurplus

example : StrictEquivalentGain redundantIdentityImplementation
    acceptedUnitChargeBlueprint.next :=
  acceptedUnitChargeBlueprint.strictEquivalentGain_of_check (by rfl)

example : residualSlack acceptedUnitChargeBlueprint.next <
    residualSlack redundantIdentityImplementation :=
  acceptedUnitChargeBlueprint.strictResidualDescent_of_check (by rfl)

/-- Reusing the single support occurrence both in a match and in the unmatched
    remainder fails exact multiplicity validation. -/
def duplicateSupportUnitChargeBlueprint :
    TerminalPacketUnitChargeBlueprint redundantIdentityImplementation where
  next := redundantIdentityImplementation
  pairing := [(0, 0)]
  unmatched := [0]

example : duplicateSupportUnitChargeBlueprint.check = false := by
  rfl

/-- Exact one-to-one pairing with no unmatched gate cannot claim strict
    surplus. -/
def emptyUnmatchedUnitChargeBlueprint :
    TerminalPacketUnitChargeBlueprint redundantIdentityImplementation where
  next := redundantIdentityImplementation
  pairing := [(0, 0)]
  unmatched := []

example : emptyUnmatchedUnitChargeBlueprint.check = false := by
  rfl

/-- Correct occurrence accounting cannot replace Boolean NOT by identity. -/
def semanticMismatchUnitChargeBlueprint :
    TerminalPacketUnitChargeBlueprint unitChargeNotImplementation where
  next := unitChargeZeroGateIdentity
  pairing := []
  unmatched := [0]

example : semanticMismatchUnitChargeBlueprint.check = false := by
  rfl

/-! ## The source-list and selector-family scans retain exact membership -/

def rejectedUnitChargeAtom : TerminalBN6PayloadAtom
    (TerminalPacketUnitChargeBlueprint redundantIdentityImplementation) where
  mass := 1
  massPositive := by simp
  payload := duplicateSupportUnitChargeBlueprint

def acceptedUnitChargeAtom : TerminalBN6PayloadAtom
    (TerminalPacketUnitChargeBlueprint redundantIdentityImplementation) where
  mass := 1
  massPositive := by simp
  payload := acceptedUnitChargeBlueprint

theorem unitChargeBlueprintAtomScan_findsAccepted :
    ∃ atom,
      atom ∈ [rejectedUnitChargeAtom, acceptedUnitChargeAtom] ∧
        atom.payload.Valid ∧
        StrictEquivalentGain redundantIdentityImplementation
          atom.payload.next := by
  have exactOutcome :=
    (scanTerminalPacketUnitChargeBlueprintAtoms
      redundantIdentityImplementation
      [rejectedUnitChargeAtom, acceptedUnitChargeAtom]).sound
  rcases exactOutcome with found | noValid
  · exact found
  · exact False.elim
      (noValid acceptedUnitChargeAtom (by simp)
        acceptedUnitChargeBlueprintValid)

variable {Atom : Type} [DecidableEq Atom]
variable {inputs outputs : Nat}
variable {current : Implementation inputs outputs}
variable {family : TerminalBN6GroupedFamily Atom
  (TerminalPacketUnitChargeBlueprint current)}

example :
    (∃ handle : family.PacketSelectorHandle,
      ∃ atom : TerminalBN6PayloadAtom
        (TerminalPacketUnitChargeBlueprint current),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          atom.payload.Valid ∧
          StrictEquivalentGain current atom.payload.next) ∨
      (∀ handle : family.PacketSelectorHandle,
        ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms →
          ¬atom.payload.Valid) :=
  (family.realizeUnitChargeBlueprints current).sound

example (handle : family.PacketSelectorHandle)
    (atom : TerminalBN6PayloadAtom
      (TerminalPacketUnitChargeBlueprint current))
    (atomMember : atom ∈ (family.packetSelectorCell handle).atoms)
    (valid : atom.payload.Valid) :
    residualSlack atom.payload.next < residualSlack current :=
  TerminalPacketUnitChargeBlueprintRealizerOutcome.gain_descent
    handle atom atomMember valid

example (conclusion : TerminalPacketEncodedSelectorConclusion family) :
    conclusion.unitChargeBlueprintRealizer.packet = conclusion :=
  conclusion.unitChargeBlueprintRealizer_packet

example
    (carrierAtLeastTwo : 2 ≤ family.carrier.length)
    (constant : family.ConstantActivation) :
    TerminalPacketEncodedSelectorConclusion family ∧
      ((∃ handle : family.PacketSelectorHandle,
        ∃ atom : TerminalBN6PayloadAtom
          (TerminalPacketUnitChargeBlueprint current),
          atom ∈ (family.packetSelectorCell handle).atoms ∧
            atom.payload.Valid ∧
            StrictEquivalentGain current atom.payload.next) ∨
        (∀ handle : family.PacketSelectorHandle,
          ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms →
            ¬atom.payload.Valid)) :=
  terminalBN6_packet_unit_charge_blueprint_realizer_sound current family
    carrierAtLeastTwo constant

end DirectWire
end PNP
