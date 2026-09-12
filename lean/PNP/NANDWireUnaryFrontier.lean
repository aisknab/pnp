/-
Copyright (c) 2026 PNP Labs.

Derive a constant or unary replacement for the completed frontier of the actual
visible predecessor cone, then compile it into the original exterior. All
ordinary outputs and computational field wires retain their full values.

This manuscript R7 component is not arbitrary-support minimization, complete
Package E, unconditional ZeroSlack or a polynomial-time PCCMin theorem.
-/

import PNP.NANDWireFrontierLift
import PNP.NANDWireUnaryRealization

namespace PNP.DirectWire.WireUnaryFrontier

variable {inputs outputs fields width : Nat}

/-- The sole valuation of a zero-input word determines every output constant. -/
def constantWord (original : Implementation 0 width) : Implementation 0 width :=
  (Candidate.ofDirectWireWord (.empty : Program 0 0)
    ⟨fun output => .constant (original.candidate.semantics Fin.elim0 output)⟩).toImplementation

theorem constantWord_value (original : Implementation 0 width)
    (valuation : Valuation 0) (output : Fin width) :
    (constantWord original).candidate.semantics valuation output =
      original.candidate.semantics valuation output := by
  unfold constantWord
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_semantics]
  change original.candidate.semantics Fin.elim0 output =
    original.candidate.semantics valuation output
  have same : (Fin.elim0 : Valuation 0) = valuation := by
    funext index
    exact Fin.elim0 index
  rw [same]

theorem constantWord_gateCount (original : Implementation 0 width) :
    (constantWord original).gateCount = 0 := rfl

/-- Regard the entire local frontier as an ordered output word, with no omitted fields. -/
def unaryCarrier (original : Implementation 1 width) : WireCarrier 1 width 0 :=
  WireCarrier.unpack original

def unaryWord (original : Implementation 1 width) : Implementation 1 width :=
  (WireUnaryRealization.realize (unaryCarrier original)).implementation

theorem unaryWord_value (original : Implementation 1 width)
    (valuation : Valuation 1) (output : Fin width) :
    (unaryWord original).candidate.semantics valuation output =
      original.candidate.semantics valuation output :=
  (WireUnaryRealization.realize_output (unaryCarrier original) valuation output).trans
    (WireCarrier.unpack_output (fields := 0) original valuation output)

theorem unaryWord_minimal (original other : Implementation 1 width)
    (sameOpen : Equivalent other.candidate.program other.candidate.directWireWord
      original.candidate.program original.candidate.directWireWord) :
    (unaryWord original).gateCount ≤ other.gateCount := by
  have sameFull : Equivalent (unaryCarrier other).exposed.candidate.program
      (unaryCarrier other).exposed.candidate.directWireWord
      (unaryCarrier original).exposed.candidate.program
      (unaryCarrier original).exposed.candidate.directWireWord := by
    unfold unaryCarrier
    rw [WireCarrier.exposed_unpack, WireCarrier.exposed_unpack]
    exact sameOpen
  exact WireUnaryRealization.realize_minimal
    (unaryCarrier original) (unaryCarrier other) sameFull

theorem unaryWord_gate_bound (original : Implementation 1 width) :
    (unaryWord original).gateCount ≤ 1 :=
  WireUnaryRealization.realize_gate_bound (unaryCarrier original)

/-- Dimension transport is checked by the input index, never by a supplied wire map. -/
def localWord : {inputs : Nat} → Implementation inputs width →
    inputs ≤ 1 → Implementation inputs width
  | 0, original, _small => constantWord original
  | 1, original, _small => unaryWord original
  | _ + 2, _original, impossible => False.elim (by omega)

theorem localWord_value (original : Implementation inputs width) (small : inputs ≤ 1)
    (valuation : Valuation inputs) (output : Fin width) :
    (localWord original small).candidate.semantics valuation output =
      original.candidate.semantics valuation output := by
  cases inputs with
  | zero => exact constantWord_value original valuation output
  | succ inputs =>
    cases inputs with
    | zero => exact unaryWord_value original valuation output
    | succ inputs => omega

/-- Minimum among every implementation of the complete local open function. -/
theorem localWord_minimal (original other : Implementation inputs width)
    (small : inputs ≤ 1)
    (sameOpen : Equivalent other.candidate.program other.candidate.directWireWord
      original.candidate.program original.candidate.directWireWord) :
    (localWord original small).gateCount ≤ other.gateCount := by
  cases inputs with
  | zero => exact Nat.zero_le _
  | succ inputs =>
    cases inputs with
    | zero => exact unaryWord_minimal original other sameOpen
    | succ inputs => omega

theorem localWord_nonincrease (original : Implementation inputs width)
    (small : inputs ≤ 1) :
    (localWord original small).gateCount ≤ original.gateCount :=
  localWord_minimal original original small
    (Equivalent.refl original.candidate.program original.candidate.directWireWord)

theorem localWord_gate_bound (original : Implementation inputs width)
    (small : inputs ≤ 1) :
    (localWord original small).gateCount ≤ 1 := by
  cases inputs with
  | zero => exact Nat.zero_le _
  | succ inputs =>
    cases inputs with
    | zero => exact unaryWord_gate_bound original
    | succ inputs => omega

/-- Derive the entire completed frontier word from the actual pulled source. -/
def replacement (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) :
    Implementation (WireFrontierLift.pulled carrier keep).boundary.length
      (WireFrontierLift.pulled carrier keep).interface.length :=
  localWord (WireFrontierLift.pulled carrier keep).extractedCandidate.toImplementation small

/-- Every local valuation and complete frontier port agrees, not only induced inputs. -/
theorem replacement_agreement (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) :
    (replacement carrier keep small).candidate.semantics =
      (WireFrontierLift.pulled carrier keep).extractedCandidate.semantics :=
  funext fun valuation => funext fun output =>
    localWord_value _ small valuation output

theorem replacement_minimal (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1)
    (other : Implementation (WireFrontierLift.pulled carrier keep).boundary.length
      (WireFrontierLift.pulled carrier keep).interface.length)
    (sameOpen : other.candidate.semantics =
      (WireFrontierLift.pulled carrier keep).extractedCandidate.semantics) :
    (replacement carrier keep small).gateCount ≤ other.gateCount := by
  apply localWord_minimal _ other small
  intro valuation output
  exact congrFun (congrFun sameOpen valuation) output

theorem replacement_nonincrease (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) :
    (replacement carrier keep small).gateCount ≤
      (WireFrontierLift.pulled carrier keep).gateCount :=
  localWord_nonincrease _ small

theorem replacement_gate_bound (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) :
    (replacement carrier keep small).gateCount ≤ 1 :=
  localWord_gate_bound _ small

private theorem localWord_zero (original : Implementation inputs width)
    (small : inputs ≤ 1) (zero : inputs = 0) :
    (localWord original small).gateCount = 0 := by
  subst inputs
  rfl

theorem replacement_zero_gateCount (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1)
    (zero : (WireFrontierLift.pulled carrier keep).boundary.length = 0) :
    (replacement carrier keep small).gateCount = 0 :=
  localWord_zero _ small zero

/-- Run the actual primary-boundary compiler; there is no compiler-result input. -/
def expanded (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) :
    WireCarrier inputs outputs fields :=
  WireFrontierLift.expanded carrier keep (replacement carrier keep small).candidate

theorem expanded_output (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (expanded carrier keep small).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  WireFrontierLift.expanded_output carrier keep _
    (replacement_agreement carrier keep small) valuation output

theorem expanded_field (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1)
    (valuation : Valuation inputs) (field : Fin fields) :
    (expanded carrier keep small).fieldValue valuation field =
      carrier.fieldValue valuation field :=
  WireFrontierLift.expanded_field carrier keep _
    (replacement_agreement carrier keep small) valuation field

theorem expanded_equivalent (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) :
    Equivalent (expanded carrier keep small).implementation.candidate.program
      (expanded carrier keep small).implementation.candidate.directWireWord
      carrier.implementation.candidate.program carrier.implementation.candidate.directWireWord :=
  expanded_output carrier keep small

/-- Exactly one copy of the actual original exterior remains. -/
theorem expanded_charge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) :
    (expanded carrier keep small).implementation.gateCount =
      (replacement carrier keep small).gateCount +
        WireFrontierLift.exteriorCharge carrier keep :=
  WireFrontierLift.expanded_charge carrier keep _

theorem expanded_nonincrease (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) :
    (expanded carrier keep small).implementation.gateCount ≤ carrier.implementation.gateCount := by
  rw [expanded_charge, WireFrontierLift.original_charge]
  exact Nat.add_le_add_right (replacement_nonincrease carrier keep small) _

theorem expanded_gain_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) :
    (expanded carrier keep small).implementation.gateCount < carrier.implementation.gateCount ↔
      (replacement carrier keep small).gateCount <
        (WireFrontierLift.pulled carrier keep).gateCount :=
  WireFrontierLift.original_gain_iff carrier keep _

/-- Recognize the actual boundary and derive the complete replacement, without a certificate. -/
def attempt (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) :
    Option (WireCarrier inputs outputs fields) :=
  if small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1 then
    some (expanded carrier keep small)
  else none

/-- Every zero/unary frontier succeeds; larger boundaries are outside this rule. -/
theorem attempt_isSome_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (attempt carrier keep).isSome = true ↔
      (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1 := by
  unfold attempt
  split
  next small => exact ⟨fun _accepted => small, fun _small => rfl⟩
  next notSmall =>
    constructor
    · intro impossible
      cases impossible
    · intro small
      exact (notSmall small).elim

private theorem attempt_result (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (result : WireCarrier inputs outputs fields)
    (accepted : attempt carrier keep = some result) :
    ∃ small, result = expanded carrier keep small := by
  unfold attempt at accepted
  split at accepted
  next small => exact ⟨small, (Option.some.inj accepted).symm⟩
  next notSmall => cases accepted

theorem attempt_output (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (result : WireCarrier inputs outputs fields)
    (accepted : attempt carrier keep = some result)
    (valuation : Valuation inputs) (output : Fin outputs) :
    result.implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output := by
  obtain ⟨small, rfl⟩ := attempt_result carrier keep result accepted
  exact expanded_output carrier keep small valuation output

/-- No replacement, agreement or supplied success witness occurs in this interface. -/
theorem attempt_field (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (result : WireCarrier inputs outputs fields)
    (accepted : attempt carrier keep = some result)
    (valuation : Valuation inputs) (field : Fin fields) :
    result.fieldValue valuation field = carrier.fieldValue valuation field := by
  obtain ⟨small, rfl⟩ := attempt_result carrier keep result accepted
  exact expanded_field carrier keep small valuation field

theorem attempt_nonincrease (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (result : WireCarrier inputs outputs fields)
    (accepted : attempt carrier keep = some result) :
    result.implementation.gateCount ≤ carrier.implementation.gateCount := by
  obtain ⟨small, rfl⟩ := attempt_result carrier keep result accepted
  exact expanded_nonincrease carrier keep small

theorem attempt_charge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (result : WireCarrier inputs outputs fields)
    (accepted : attempt carrier keep = some result) :
    ∃ small, result.implementation.gateCount =
      (replacement carrier keep small).gateCount +
        WireFrontierLift.exteriorCharge carrier keep := by
  obtain ⟨small, rfl⟩ := attempt_result carrier keep result accepted
  exact ⟨small, expanded_charge carrier keep small⟩

/-- R7 binds the old R5 identity to its actual source in the computed expanded program. -/
def dischargeR7 (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    WireFrontierLift.ExpandedDischarge carrier keep
      (replacement carrier keep small).candidate creation :=
  WireFrontierLift.discharge carrier keep _ (replacement_agreement carrier keep small) creation

theorem dischargeR7_source_exact (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    (dischargeR7 carrier keep small creation).actualSource =
      (expanded carrier keep small).source creation.coordinate := rfl

theorem dischargeR7_full_value (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1)
    (creation : WireObligationRestoration.R5Creation carrier keep)
    (valuation : Valuation inputs) :
    (dischargeR7 carrier keep small creation).actualSource.eval valuation
        ((expanded carrier keep small).implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate :=
  WireFrontierLift.discharge_full_value carrier keep _
    (replacement_agreement carrier keep small) creation valuation

/-- Proper exterior and strict local saving are independent, physically checked facts. -/
structure ProperGain (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Type where
  small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1
  proper : 0 < WireFrontierLift.exteriorCharge carrier keep
  smaller : (replacement carrier keep small).gateCount <
    (WireFrontierLift.pulled carrier keep).gateCount

def checkedProperGain (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Option (ProperGain carrier keep) :=
  if small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1 then
    if proper : 0 < WireFrontierLift.exteriorCharge carrier keep then
      if smaller : (replacement carrier keep small).gateCount <
          (WireFrontierLift.pulled carrier keep).gateCount then
        some ⟨small, proper, smaller⟩
      else none
    else none
  else none

theorem checkedProperGain_isSome_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (checkedProperGain carrier keep).isSome = true ↔
      ∃ small, 0 < WireFrontierLift.exteriorCharge carrier keep ∧
        (replacement carrier keep small).gateCount <
          (WireFrontierLift.pulled carrier keep).gateCount := by
  unfold checkedProperGain
  split
  next small =>
    split
    next proper =>
      split
      next smaller => exact ⟨fun _accepted => ⟨small, proper, smaller⟩, fun _valid => rfl⟩
      next notSmaller =>
        constructor
        · intro impossible
          cases impossible
        · rintro ⟨_small, _proper, smaller⟩
          exact (notSmaller smaller).elim
    next notProper =>
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨_small, proper, _smaller⟩
        exact (notProper proper).elim
  next notSmall =>
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨small, _proper, _smaller⟩
      exact (notSmall small).elim

/-- Any smaller complete local realization implies acceptance on a proper recognized cone. -/
theorem checkedProperGain_complete (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1)
    (proper : 0 < WireFrontierLift.exteriorCharge carrier keep)
    (other : Implementation (WireFrontierLift.pulled carrier keep).boundary.length
      (WireFrontierLift.pulled carrier keep).interface.length)
    (sameOpen : other.candidate.semantics =
      (WireFrontierLift.pulled carrier keep).extractedCandidate.semantics)
    (smaller : other.gateCount < (WireFrontierLift.pulled carrier keep).gateCount) :
    (checkedProperGain carrier keep).isSome = true :=
  (checkedProperGain_isSome_iff carrier keep).2
    ⟨small, proper,
      Nat.lt_of_le_of_lt (replacement_minimal carrier keep small other sameOpen) smaller⟩

def ProperGain.strictGain {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} (gain : ProperGain carrier keep) :
    StrictEquivalentGain carrier.implementation
      (expanded carrier keep gain.small).implementation where
  smaller := (expanded_gain_iff carrier keep gain.small).2 gain.smaller
  equivalent := expanded_equivalent carrier keep gain.small

theorem ProperGain.checked {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} (gain : ProperGain carrier keep) :
    (WireFrontierLift.pulled carrier keep).gateCount < carrier.implementation.gateCount ∧
      StrictEquivalentGain carrier.implementation (expanded carrier keep gain.small).implementation ∧
      (∀ valuation field, (expanded carrier keep gain.small).fieldValue valuation field =
        carrier.fieldValue valuation field) ∧
      (expanded carrier keep gain.small).implementation.gateCount =
        (replacement carrier keep gain.small).gateCount +
          WireFrontierLift.exteriorCharge carrier keep :=
  ⟨(WireFrontierLift.proper_iff_exterior_positive carrier keep).2 gain.proper,
    gain.strictGain, expanded_field carrier keep gain.small, expanded_charge carrier keep gain.small⟩

end PNP.DirectWire.WireUnaryFrontier
