/-
Copyright (c) 2026 PNP Labs.

Executable realization of finite Packet replacement blueprints through the
unit-charge specialization of `R-ChargeSurplus`.  A blueprint contains only a
replacement implementation and occurrence-level pairing data.  The validator
derives both charge ledgers canonically from the two NAND gate counts, checks
exact multiplicity, requires a nonempty unmatched support remainder, and
checks semantic equivalence.  Acceptance constructs the existing generic
charge-surplus realization, a genuine strict equivalent gain, and strict
residual descent without accepting any strict inequality as an input.

The complete finite-family scan is relative to one supplied explicit grouped
BN6 family.  Its unresolved branch means only that no supplied blueprint
passed this validator.  This module does not construct blueprints from
terminal data, establish manuscript selector faithfulness or compatibility,
produce typed HN, budget, or lower-rank blockers, close HB/rank routing,
establish polynomial bounds, prove unconditional ZeroSlack or PCCMin, put SAT
in P, remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPacketChargeSurplus

namespace PNP
namespace DirectWire

/-! ## Constructive occurrence-permutation checker -/

/-- Remove the first occurrence of one natural number without invoking a
    classical permutation decider. -/
def eraseFirstNat (needle : Nat) : List Nat → Option (List Nat)
  | [] => none
  | head :: tail =>
      if head = needle then
        some tail
      else
        (eraseFirstNat needle tail).map (fun remaining => head :: remaining)

/-- Successful removal is an exact occurrence permutation: reinserting the
    removed value yields the original list up to `List.Perm`. -/
theorem eraseFirstNat_sound
    {needle : Nat} {source remaining : List Nat}
    (erased : eraseFirstNat needle source = some remaining) :
    (needle :: remaining).Perm source := by
  induction source generalizing remaining with
  | nil => simp [eraseFirstNat] at erased
  | cons head tail inductionHypothesis =>
      by_cases equal : head = needle
      · subst head
        simp [eraseFirstNat] at erased
        subst remaining
        exact List.Perm.refl _
      · cases recursiveEquation : eraseFirstNat needle tail with
        | none => simp [eraseFirstNat, equal, recursiveEquation] at erased
        | some rest =>
            simp [eraseFirstNat, equal, recursiveEquation] at erased
            subst remaining
            exact (List.Perm.swap head needle rest).trans
              (List.Perm.cons head
                (inductionHypothesis recursiveEquation))

/-- Every present occurrence can be removed by the executable remover. -/
theorem eraseFirstNat_exists_of_mem
    {needle : Nat} {source : List Nat}
    (member : needle ∈ source) :
    ∃ remaining, eraseFirstNat needle source = some remaining := by
  induction source with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      by_cases equal : head = needle
      · subst head
        exact ⟨tail, by simp [eraseFirstNat]⟩
      · have tailMember : needle ∈ tail := by
          have needleNeHead : needle ≠ head := Ne.symm equal
          simpa [needleNeHead] using member
        obtain ⟨remaining, erased⟩ := inductionHypothesis tailMember
        exact ⟨head :: remaining, by
          simp [eraseFirstNat, equal, erased]⟩

/-- Executable exact-multiplicity comparison for natural-number occurrence
    lists.  The recursive removal algorithm is constructive and avoids the
    generic classical `Decidable (List.Perm ...)` instance. -/
def natOccurrencePermBool : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | head :: tail, right =>
      match eraseFirstNat head right with
      | none => false
      | some remaining => natOccurrencePermBool tail remaining

/-- The constructive occurrence checker never accepts non-permutations. -/
theorem natOccurrencePermBool_sound
    {left right : List Nat}
    (checked : natOccurrencePermBool left right = true) :
    left.Perm right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact List.Perm.refl []
      | cons head tail =>
          simp [natOccurrencePermBool] at checked
  | cons head tail inductionHypothesis =>
      cases erasedEquation : eraseFirstNat head right with
      | none =>
          simp [natOccurrencePermBool, erasedEquation] at checked
      | some remaining =>
          have tailPerm : tail.Perm remaining :=
            inductionHypothesis (by
              simpa [natOccurrencePermBool, erasedEquation] using checked)
          exact (List.Perm.cons head tailPerm).trans
            (eraseFirstNat_sound erasedEquation)

/-- Every exact occurrence permutation is accepted by the constructive
    checker. -/
theorem natOccurrencePermBool_complete
    {left right : List Nat}
    (permuted : left.Perm right) :
    natOccurrencePermBool left right = true := by
  induction left generalizing right with
  | nil =>
      have rightEmpty : right = [] := permuted.nil_eq.symm
      subst right
      rfl
  | cons head tail inductionHypothesis =>
      have headMember : head ∈ right :=
        permuted.mem_iff.mp (by simp)
      obtain ⟨remaining, erasedEquation⟩ :=
        eraseFirstNat_exists_of_mem headMember
      have reinserted : (head :: remaining).Perm right :=
        eraseFirstNat_sound erasedEquation
      have tailPerm : tail.Perm remaining :=
        (permuted.trans reinserted.symm).cons_inv
      simp [natOccurrencePermBool, erasedEquation,
        inductionHypothesis tailPerm]

/-- The constructive Boolean checker recognizes exactly `List.Perm` for Nat
    occurrence ledgers. -/
theorem natOccurrencePermBool_eq_true_iff (left right : List Nat) :
    natOccurrencePermBool left right = true ↔ left.Perm right :=
  ⟨natOccurrencePermBool_sound, natOccurrencePermBool_complete⟩

/-! ## Canonical unit-charge replacement blueprints -/

/-- Finite replacement data whose occurrence ledgers are interpreted
    canonically as the NAND gate positions of `current` and `next`.

    No gate-count inequality, charge inequality, semantic proof, or gain proof
    is stored in the blueprint. -/
structure TerminalPacketUnitChargeBlueprint
    {inputs outputs : Nat}
    (current : Implementation inputs outputs) where
  next : Implementation inputs outputs
  pairing : List (Nat × Nat)
  unmatched : List Nat

/-- Exact proposition checked by the executable blueprint validator.  Each
    gate occurrence is represented once by its index in `List.range`; the two
    permutation identities therefore enforce multiplicity rather than mere
    value membership. -/
def TerminalPacketUnitChargeBlueprint.Valid
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (blueprint : TerminalPacketUnitChargeBlueprint current) : Prop :=
  (List.range current.gateCount).Perm
      (blueprint.pairing.map Prod.fst ++ blueprint.unmatched) ∧
    (List.range blueprint.next.gateCount).Perm
      (blueprint.pairing.map Prod.snd) ∧
    blueprint.unmatched ≠ [] ∧
    Equivalent blueprint.next.candidate.program
      blueprint.next.candidate.directWireWord
      current.candidate.program current.candidate.directWireWord

/-- Executable, fail-closed validator for one finite replacement blueprint. -/
def TerminalPacketUnitChargeBlueprint.check
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (blueprint : TerminalPacketUnitChargeBlueprint current) : Bool :=
  natOccurrencePermBool (List.range current.gateCount)
      (blueprint.pairing.map Prod.fst ++ blueprint.unmatched) &&
    natOccurrencePermBool (List.range blueprint.next.gateCount)
      (blueprint.pairing.map Prod.snd) &&
    decide (blueprint.unmatched ≠ []) &&
    equivalentBool blueprint.next.candidate current.candidate

/-- The Boolean validator recognizes exactly the proof-bearing validity
    proposition. -/
theorem TerminalPacketUnitChargeBlueprint.check_eq_true_iff
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (blueprint : TerminalPacketUnitChargeBlueprint current) :
    blueprint.check = true ↔ blueprint.Valid := by
  simp only [TerminalPacketUnitChargeBlueprint.check,
    TerminalPacketUnitChargeBlueprint.Valid,
    Bool.and_eq_true, natOccurrencePermBool_eq_true_iff,
    decide_eq_true_eq, equivalentBool_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨supportExact, replacementExact⟩, unmatchedNonempty⟩,
      semanticsPreserved⟩
    exact ⟨supportExact, replacementExact, unmatchedNonempty,
      semanticsPreserved⟩
  · rintro ⟨supportExact, replacementExact, unmatchedNonempty,
      semanticsPreserved⟩
    exact ⟨⟨⟨supportExact, replacementExact⟩, unmatchedNonempty⟩,
      semanticsPreserved⟩

/-- A valid blueprint canonically instantiates the generic charge-surplus
    kernel with the two gate-occurrence ranges and unit weights. -/
def TerminalPacketUnitChargeBlueprint.Valid.chargeSurplus
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {blueprint : TerminalPacketUnitChargeBlueprint current}
    (valid : blueprint.Valid) :
    TerminalPacketChargeSurplus
      (List.range current.gateCount)
      (List.range blueprint.next.gateCount)
      (fun _ : Nat => 1) (fun _ : Nat => 1) :=
  {
    pairing := blueprint.pairing
    unmatched := blueprint.unmatched
    supportExact := valid.1
    replacementExact := valid.2.1
    weightPreserved := by
      intro entry _member
      rfl
    positiveUnmatched := by
      cases unmatchedEquation : blueprint.unmatched with
      | nil => exact False.elim (valid.2.2.1 unmatchedEquation)
      | cons head tail =>
          exact ⟨head, by simp, by simp⟩
  }

/-- Canonical ranges with unit charge account exactly for NAND gate count. -/
theorem unitChargeRange_sum (count : Nat) :
    ((List.range count).map (fun _ : Nat => 1)).sum = count := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp [List.range_succ, inductionHypothesis]

/-- A valid blueprint constructs the complete generic charge-surplus
    realization.  Gate accounting and positive unit weight are derived rather
    than caller-provided. -/
def TerminalPacketUnitChargeBlueprint.Valid.chargeSurplusRealization
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {blueprint : TerminalPacketUnitChargeBlueprint current}
    (valid : blueprint.Valid) :
    TerminalPacketChargeSurplusRealization current blueprint.next
      (List.range current.gateCount)
      (List.range blueprint.next.gateCount)
      (fun _ : Nat => 1) (fun _ : Nat => 1) :=
  {
    surplus := valid.chargeSurplus
    supportAccountsCurrent := unitChargeRange_sum current.gateCount
    replacementAccountsNext := unitChargeRange_sum blueprint.next.gateCount
    semanticsPreserved := valid.2.2.2
  }

/-- Validator acceptance produces a genuine strict equivalent gain without
    consulting the existing gate-count gain checker. -/
theorem TerminalPacketUnitChargeBlueprint.strictEquivalentGain_of_check
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (blueprint : TerminalPacketUnitChargeBlueprint current)
    (checked : blueprint.check = true) :
    StrictEquivalentGain current blueprint.next :=
  ((blueprint.check_eq_true_iff).1 checked).chargeSurplusRealization
    |>.strictEquivalentGain

/-- Validator acceptance strictly decreases reference residual slack. -/
theorem TerminalPacketUnitChargeBlueprint.strictResidualDescent_of_check
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (blueprint : TerminalPacketUnitChargeBlueprint current)
    (checked : blueprint.check = true) :
    residualSlack blueprint.next < residualSlack current :=
  (blueprint.strictEquivalentGain_of_check checked).strictResidualDescent

/-! ## Exact scan of original source atoms -/

/-- Result of validating every blueprint atom in one exact source list. -/
inductive TerminalPacketUnitChargeBlueprintAtomOutcome
    {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (atoms : List (TerminalBN6PayloadAtom
      (TerminalPacketUnitChargeBlueprint current))) : Type where
  | gain
      (atom : TerminalBN6PayloadAtom
        (TerminalPacketUnitChargeBlueprint current))
      (atomMember : atom ∈ atoms)
      (valid : atom.payload.Valid) :
      TerminalPacketUnitChargeBlueprintAtomOutcome current atoms
  | unresolved
      (noValid : ∀ atom, atom ∈ atoms → ¬atom.payload.Valid) :
      TerminalPacketUnitChargeBlueprintAtomOutcome current atoms

/-- Validate all original blueprint payloads in one source list. -/
def scanTerminalPacketUnitChargeBlueprintAtoms
    {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (atoms : List (TerminalBN6PayloadAtom
      (TerminalPacketUnitChargeBlueprint current))) →
      TerminalPacketUnitChargeBlueprintAtomOutcome current atoms
  | [] => .unresolved (by simp)
  | head :: tail =>
      if checked : head.payload.check = true then
        .gain head (List.Mem.head tail)
          ((head.payload.check_eq_true_iff).1 checked)
      else
        match scanTerminalPacketUnitChargeBlueprintAtoms current tail with
        | .gain atom atomMember valid =>
            .gain atom (List.Mem.tail head atomMember) valid
        | .unresolved noTailValid =>
            .unresolved (by
              intro atom atomMember valid
              rcases List.mem_cons.mp atomMember with headEquation | tailMember
              · subst atom
                exact checked ((head.payload.check_eq_true_iff).2 valid)
              · exact noTailValid atom tailMember valid)

/-- The source-list scan returns either one exact valid original atom or proof
    that no original atom in that list is a valid blueprint. -/
theorem TerminalPacketUnitChargeBlueprintAtomOutcome.sound
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {atoms : List (TerminalBN6PayloadAtom
      (TerminalPacketUnitChargeBlueprint current))}
    (outcome : TerminalPacketUnitChargeBlueprintAtomOutcome current atoms) :
    (∃ atom, atom ∈ atoms ∧ atom.payload.Valid ∧
      StrictEquivalentGain current atom.payload.next) ∨
      (∀ atom, atom ∈ atoms → ¬atom.payload.Valid) := by
  cases outcome with
  | gain atom atomMember valid =>
      exact Or.inl ⟨atom, atomMember, valid,
        valid.chargeSurplusRealization.strictEquivalentGain⟩
  | unresolved noValid => exact Or.inr noValid

/-! ## Exhaustive canonical selector-family realizer -/

/-- Scan result behind an arbitrary list of canonical selector handles. -/
inductive TerminalPacketUnitChargeBlueprintHandleListOutcome
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketUnitChargeBlueprint current))
    (handles : List family.PacketSelectorHandle) : Type where
  | gain
      (handle : family.PacketSelectorHandle)
      (handleMember : handle ∈ handles)
      (atom : TerminalBN6PayloadAtom
        (TerminalPacketUnitChargeBlueprint current))
      (atomMember : atom ∈ (family.packetSelectorCell handle).atoms)
      (valid : atom.payload.Valid) :
      TerminalPacketUnitChargeBlueprintHandleListOutcome current family handles
  | unresolved
      (noValid : ∀ handle, handle ∈ handles →
        ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms →
          ¬atom.payload.Valid) :
      TerminalPacketUnitChargeBlueprintHandleListOutcome current family handles

/-- Validate every source atom behind every supplied canonical handle. -/
def scanTerminalPacketUnitChargeBlueprintHandles
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketUnitChargeBlueprint current)) :
    (handles : List family.PacketSelectorHandle) →
      TerminalPacketUnitChargeBlueprintHandleListOutcome
        current family handles
  | [] => .unresolved (by simp)
  | head :: tail =>
      match scanTerminalPacketUnitChargeBlueprintAtoms current
          (family.packetSelectorCell head).atoms with
      | .gain atom atomMember valid =>
          .gain head (List.Mem.head tail) atom atomMember valid
      | .unresolved noHeadValid =>
          match scanTerminalPacketUnitChargeBlueprintHandles current family
              tail with
          | .gain handle handleMember atom atomMember valid =>
              .gain handle (List.Mem.tail head handleMember)
                atom atomMember valid
          | .unresolved noTailValid =>
              .unresolved (by
                intro handle handleMember atom atomMember valid
                rcases List.mem_cons.mp handleMember with headEquation |
                  tailMember
                · subst handle
                  exact noHeadValid atom atomMember valid
                · exact noTailValid handle tailMember atom atomMember valid)

/-- Exact outcome for every canonical handle in one supplied explicit Packet
    selector family.  `unresolved` is deliberately family-local. -/
inductive TerminalPacketUnitChargeBlueprintRealizerOutcome
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketUnitChargeBlueprint current)) : Type where
  | gain
      (handle : family.PacketSelectorHandle)
      (atom : TerminalBN6PayloadAtom
        (TerminalPacketUnitChargeBlueprint current))
      (atomMember : atom ∈ (family.packetSelectorCell handle).atoms)
      (valid : atom.payload.Valid) :
      TerminalPacketUnitChargeBlueprintRealizerOutcome current family
  | unresolved
      (noValid : ∀ handle,
        ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms →
          ¬atom.payload.Valid) :
      TerminalPacketUnitChargeBlueprintRealizerOutcome current family

/-- Execute the validator over every original blueprint atom behind every
    canonical handle in the supplied family. -/
def TerminalBN6GroupedFamily.realizeUnitChargeBlueprints
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketUnitChargeBlueprint current)) :
    TerminalPacketUnitChargeBlueprintRealizerOutcome current family :=
  match scanTerminalPacketUnitChargeBlueprintHandles current family
      family.packetSelectorHandles with
  | .gain handle _handleMember atom atomMember valid =>
      .gain handle atom atomMember valid
  | .unresolved noValid =>
      .unresolved (fun handle =>
        noValid handle (family.mem_packetSelectorHandles handle))

/-- The exhaustive realizer returns only an exact source atom with a
    charge-derived gain, or exact absence of a valid blueprint throughout the
    supplied family. -/
theorem TerminalPacketUnitChargeBlueprintRealizerOutcome.sound
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketUnitChargeBlueprint current)}
    (outcome : TerminalPacketUnitChargeBlueprintRealizerOutcome
      current family) :
    (∃ handle : family.PacketSelectorHandle,
      ∃ atom : TerminalBN6PayloadAtom
        (TerminalPacketUnitChargeBlueprint current),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          atom.payload.Valid ∧
          StrictEquivalentGain current atom.payload.next) ∨
      (∀ handle : family.PacketSelectorHandle,
        ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms →
          ¬atom.payload.Valid) := by
  cases outcome with
  | gain handle atom atomMember valid =>
      exact Or.inl ⟨handle, atom, atomMember, valid,
        valid.chargeSurplusRealization.strictEquivalentGain⟩
  | unresolved noValid => exact Or.inr noValid

/-- Every returned source atom carries strict residual descent. -/
theorem TerminalPacketUnitChargeBlueprintRealizerOutcome.gain_descent
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketUnitChargeBlueprint current)}
    (handle : family.PacketSelectorHandle)
    (atom : TerminalBN6PayloadAtom
      (TerminalPacketUnitChargeBlueprint current))
    (_atomMember : atom ∈ (family.packetSelectorCell handle).atoms)
    (valid : atom.payload.Valid) :
    residualSlack atom.payload.next < residualSlack current :=
  valid.chargeSurplusRealization.strictResidualDescent

/-! ## Packet-preserving composition -/

/-- Preserve the complete encoded Packet alternatives while attaching the one
    exhaustive unit-charge blueprint realizer outcome. -/
structure TerminalPacketUnitChargeBlueprintRealizerConclusion
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketUnitChargeBlueprint current)) : Type where
  packet : TerminalPacketEncodedSelectorConclusion family
  realizer : TerminalPacketUnitChargeBlueprintRealizerOutcome current family

/-- Add the exhaustive checked realizer without changing the Packet
    conclusion. -/
def TerminalPacketEncodedSelectorConclusion.unitChargeBlueprintRealizer
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketUnitChargeBlueprint current)}
    (conclusion : TerminalPacketEncodedSelectorConclusion family) :
    TerminalPacketUnitChargeBlueprintRealizerConclusion current family :=
  {
    packet := conclusion
    realizer := family.realizeUnitChargeBlueprints current
  }

/-- The realizer upgrade preserves the existing Packet conclusion literally. -/
theorem TerminalPacketEncodedSelectorConclusion.unitChargeBlueprintRealizer_packet
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketUnitChargeBlueprint current)}
    (conclusion : TerminalPacketEncodedSelectorConclusion family) :
    conclusion.unitChargeBlueprintRealizer.packet = conclusion :=
  rfl

/-- BN6 followed by canonical selector coding and exhaustive checked
    unit-charge blueprint realization over the supplied finite family. -/
def terminalBN6_packet_unit_charge_blueprint_realizer
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketUnitChargeBlueprint current))
    (carrierAtLeastTwo : 2 ≤ family.carrier.length)
    (constant : family.ConstantActivation) :
    TerminalPacketUnitChargeBlueprintRealizerConclusion current family :=
  (terminalBN6_packet_selector_codes family carrierAtLeastTwo constant)
    |>.unitChargeBlueprintRealizer

/-- The composed interface preserves every Packet alternative and exposes
    exactly a source blueprint with a charge-derived gain or supplied-family
    validator silence. -/
theorem terminalBN6_packet_unit_charge_blueprint_realizer_sound
    {Atom : Type} [DecidableEq Atom] {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketUnitChargeBlueprint current))
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
  ⟨terminalBN6_packet_selector_codes family carrierAtLeastTwo constant,
    (family.realizeUnitChargeBlueprints current).sound⟩

end DirectWire
end PNP
