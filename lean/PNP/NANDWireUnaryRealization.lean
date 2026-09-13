/-
Copyright (c) 2026 PNP Labs.

Compute a full computational unary word from its actual two input valuations.
Ordered outputs and computational fields share one physical NOT gate when any
of them requires negation; otherwise constants and the input cost zero gates.

This is a source-derived unary realization component for manuscript R7, not a
complete ambient-support calculus, Package E or general polynomial PCCMin.
-/

import PNP.NANDWireObligationRestoration

namespace PNP.DirectWire.WireUnaryRealization

variable {outputs fields : Nat}

/-- The actual value of a complete original observation at a unary input. -/
def bit (carrier : WireCarrier 1 outputs fields) (value : Bool)
    (observation : Fin (outputs + fields)) : Bool :=
  carrier.exposed.candidate.semantics (fun _ => value) observation

private theorem unary_valuation (valuation : Valuation 1) :
    valuation = fun _ => valuation fin1Zero := by
  funext index
  have same : index = fin1Zero := by
    apply Fin.ext
    have bound := index.isLt
    change index.val = 0
    omega
  exact congrArg valuation same

/-- The two actual unary values determine every input valuation. -/
theorem observation_value (carrier : WireCarrier 1 outputs fields)
    (valuation : Valuation 1) (observation : Fin (outputs + fields)) :
    carrier.exposed.candidate.semantics valuation observation =
      if valuation fin1Zero then bit carrier true observation else bit carrier false observation := by
  calc
    carrier.exposed.candidate.semantics valuation observation =
        carrier.exposed.candidate.semantics (fun _ => valuation fin1Zero) observation :=
      congrArg (fun input => carrier.exposed.candidate.semantics input observation)
        (unary_valuation valuation)
    _ = _ := by cases valuation fin1Zero <;> rfl

/-- Whether this complete observation is the negation of the unary boundary. -/
def negatedAt (carrier : WireCarrier 1 outputs fields)
    (observation : Fin (outputs + fields)) : Bool :=
  bit carrier false observation && !(bit carrier true observation)

/-- Include every computational field, not only the ordinary output tuple. -/
def needsNegation (carrier : WireCarrier 1 outputs fields) : Bool :=
  (allFin (outputs + fields)).any (negatedAt carrier)

theorem needsNegation_iff (carrier : WireCarrier 1 outputs fields) :
    needsNegation carrier = true ↔
      ∃ observation, bit carrier false observation = true ∧
        bit carrier true observation = false := by
  constructor
  · intro needed
    obtain ⟨observation, _member, result⟩ := List.any_eq_true.mp needed
    refine ⟨observation, ?_⟩
    unfold negatedAt at result
    have parts := result
    simp only [Bool.and_eq_true] at parts
    refine ⟨parts.1, ?_⟩
    cases high : bit carrier true observation with
    | false => rfl
    | true =>
        have impossible := parts.2
        rw [high] at impossible
        cases impossible
  · rintro ⟨observation, low, high⟩
    apply List.any_eq_true.mpr
    refine ⟨observation, mem_allFin observation, ?_⟩
    unfold negatedAt
    rw [low, high]
    rfl

private theorem not_negated (carrier : WireCarrier 1 outputs fields)
    (noneNeeded : needsNegation carrier = false) (observation : Fin (outputs + fields)) :
    negatedAt carrier observation = false := by
  cases result : negatedAt carrier observation with
  | false => rfl
  | true =>
      have needed : needsNegation carrier = true :=
        List.any_eq_true.mpr ⟨observation, mem_allFin observation, result⟩
      rw [noneNeeded] at needed
      cases needed

/-- Literal zero-gate sources; the negation case is forbidden by the computed no-negation branch. -/
def zeroSource : Bool → Bool → Source 1 0
  | false, false => .constant false
  | false, true => .input fin1Zero
  | true, false => .constant false
  | true, true => .constant true

/-- All negated observations refer to the same actual physical NOT gate. -/
def oneSource : Bool → Bool → Source 1 1
  | false, false => .constant false
  | false, true => .input fin1Zero
  | true, false => .gate fin1Zero
  | true, true => .constant true

private theorem zeroSource_value (low high : Bool) (valuation : Valuation 1)
    (notNegated : (low && (!high)) = false) :
    (zeroSource low high).eval valuation Fin.elim0 =
      if valuation fin1Zero then high else low := by
  cases low <;> cases high
  · change false = if valuation fin1Zero then false else false
    cases valuation fin1Zero <;> rfl
  · change valuation fin1Zero = if valuation fin1Zero then true else false
    cases valuation fin1Zero <;> rfl
  · cases notNegated
  · change true = if valuation fin1Zero then true else true
    cases valuation fin1Zero <;> rfl

private theorem oneSource_value (low high : Bool) (valuation : Valuation 1) :
    (oneSource low high).eval valuation (notProgram.eval valuation) =
      if valuation fin1Zero then high else low := by
  cases low <;> cases high
  · change false = if valuation fin1Zero then false else false
    cases valuation fin1Zero <;> rfl
  · change valuation fin1Zero = if valuation fin1Zero then true else false
    cases valuation fin1Zero <;> rfl
  · change notProgram.eval valuation fin1Zero =
      if valuation fin1Zero then false else true
    have negative := notCircuit_spec valuation
    change notProgram.eval valuation fin1Zero = !valuation fin1Zero at negative
    rw [negative]
    cases valuation fin1Zero <;> rfl
  · change true = if valuation fin1Zero then true else true
    cases valuation fin1Zero <;> rfl

def zeroImplementation (carrier : WireCarrier 1 outputs fields) :
    Implementation 1 (outputs + fields) :=
  (Candidate.ofDirectWireWord (.empty : Program 1 0)
    ⟨fun observation => zeroSource (bit carrier false observation)
      (bit carrier true observation)⟩).toImplementation

def oneImplementation (carrier : WireCarrier 1 outputs fields) :
    Implementation 1 (outputs + fields) :=
  (Candidate.ofDirectWireWord notProgram
    ⟨fun observation => oneSource (bit carrier false observation)
      (bit carrier true observation)⟩).toImplementation

/-- Compute the actual word, without an input replacement or agreement certificate. -/
def implementation (carrier : WireCarrier 1 outputs fields) :
    Implementation 1 (outputs + fields) :=
  if needsNegation carrier then oneImplementation carrier else zeroImplementation carrier

def realize (carrier : WireCarrier 1 outputs fields) : WireCarrier 1 outputs fields :=
  WireCarrier.unpack (implementation carrier)


/-- The computed actual full word agrees with every original observation. -/
theorem implementation_value (carrier : WireCarrier 1 outputs fields)
    (valuation : Valuation 1) (observation : Fin (outputs + fields)) :
    (implementation carrier).candidate.semantics valuation observation =
      carrier.exposed.candidate.semantics valuation observation := by
  rw [observation_value]
  cases needed : needsNegation carrier with
  | false =>
      unfold implementation
      rw [needed]
      change (zeroImplementation carrier).candidate.semantics valuation observation = _
      unfold zeroImplementation
      dsimp only [Candidate.toImplementation]
      rw [Candidate.ofDirectWireWord_semantics]
      exact zeroSource_value _ _ valuation (not_negated carrier needed observation)
  | true =>
      unfold implementation
      rw [needed]
      change (oneImplementation carrier).candidate.semantics valuation observation = _
      unfold oneImplementation
      dsimp only [Candidate.toImplementation]
      rw [Candidate.ofDirectWireWord_semantics]
      exact oneSource_value _ _ valuation

theorem realize_output (carrier : WireCarrier 1 outputs fields)
    (valuation : Valuation 1) (output : Fin outputs) :
    (realize carrier).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  (WireCarrier.unpack_output _ valuation output).trans
    ((implementation_value carrier valuation (Fin.castAdd fields output)).trans
      (carrier.exposed_output valuation output))

/-- Includes every original computational field, with no agreement premise. -/
theorem realize_field (carrier : WireCarrier 1 outputs fields)
    (valuation : Valuation 1) (field : Fin fields) :
    (realize carrier).fieldValue valuation field = carrier.fieldValue valuation field :=
  (WireCarrier.unpack_field _ valuation field).trans
    ((implementation_value carrier valuation (Fin.natAdd outputs field)).trans
      (carrier.exposed_field valuation field))

theorem realize_equivalent (carrier : WireCarrier 1 outputs fields) :
    Equivalent (realize carrier).implementation.candidate.program
      (realize carrier).implementation.candidate.directWireWord
      carrier.implementation.candidate.program
      carrier.implementation.candidate.directWireWord :=
  realize_output carrier

theorem realize_full_equivalent (carrier : WireCarrier 1 outputs fields) :
    Equivalent (realize carrier).exposed.candidate.program
      (realize carrier).exposed.candidate.directWireWord
      carrier.exposed.candidate.program carrier.exposed.candidate.directWireWord := by
  unfold realize
  rw [WireCarrier.exposed_unpack]
  exact implementation_value carrier

/-- All negated fields and outputs share one gate; an empty full word costs zero. -/
theorem realize_gateCount (carrier : WireCarrier 1 outputs fields) :
    (realize carrier).implementation.gateCount = if needsNegation carrier then 1 else 0 := by
  unfold realize
  rw [WireCarrier.unpack_gateCount]
  unfold implementation
  cases needsNegation carrier <;> rfl

private theorem zero_candidate_not_negated {width : Nat}
    (candidate : Candidate 1 0 width) (observation : Fin width) :
    ¬ (candidate.semantics (fun _ => false) observation = true ∧
       candidate.semantics (fun _ => true) observation = false) := by
  rintro ⟨low, high⟩
  change (candidate.directWireWord.source observation).eval
    (fun _ => false) (candidate.program.eval (fun _ => false)) = true at low
  change (candidate.directWireWord.source observation).eval
    (fun _ => true) (candidate.program.eval (fun _ => true)) = false at high
  cases sourceAt : candidate.directWireWord.source observation with
  | input input =>
      rw [sourceAt] at low
      cases low
  | constant value =>
      rw [sourceAt] at low high
      have impossible : true = false := low.symm.trans high
      cases impossible
  | gate gate => exact Fin.elim0 gate

/-- A zero-gate source cannot negate its only input, whatever the output width. -/
theorem negation_requires_gate {width : Nat}
    (other : Implementation 1 width) (observation : Fin width)
    (low : other.candidate.semantics (fun _ => false) observation = true)
    (high : other.candidate.semantics (fun _ => true) observation = false) :
    1 ≤ other.gateCount := by
  cases other with
  | mk gates candidate =>
      cases gates with
      | zero => exact (zero_candidate_not_negated candidate observation ⟨low, high⟩).elim
      | succ gates => exact Nat.succ_le_succ (Nat.zero_le gates)

/-- Minimum among every equivalent complete computational carrier, not merely
among implementations matching the ordinary outputs. -/
theorem realize_minimal (carrier other : WireCarrier 1 outputs fields)
    (sameFull : Equivalent other.exposed.candidate.program
      other.exposed.candidate.directWireWord carrier.exposed.candidate.program
      carrier.exposed.candidate.directWireWord) :
    (realize carrier).implementation.gateCount ≤ other.implementation.gateCount := by
  rw [realize_gateCount]
  cases needed : needsNegation carrier with
  | false => exact Nat.zero_le _
  | true =>
      obtain ⟨observation, low, high⟩ := (needsNegation_iff carrier).mp needed
      exact negation_requires_gate other.exposed observation
        ((sameFull (fun _ => false) observation).trans low)
        ((sameFull (fun _ => true) observation).trans high)

theorem realize_nonincrease (carrier : WireCarrier 1 outputs fields) :
    (realize carrier).implementation.gateCount ≤ carrier.implementation.gateCount :=
  realize_minimal carrier carrier
    (Equivalent.refl carrier.exposed.candidate.program carrier.exposed.candidate.directWireWord)

theorem realize_gate_bound (carrier : WireCarrier 1 outputs fields) :
    (realize carrier).implementation.gateCount ≤ 1 := by
  rw [realize_gateCount]
  cases needsNegation carrier <;> decide


/-- A source-exact R7 witness for the actual computed unary realization.
The original R5 identity is retained; no masked value substitutes for its full value. -/
structure R7Discharge (carrier : WireCarrier 1 outputs fields)
    (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep) where
  actualSource : Source 1 (realize carrier).implementation.gateCount
  sourceExact : actualSource = (realize carrier).source creation.coordinate
  fullWitness : ∀ valuation,
    actualSource.eval valuation
        ((realize carrier).implementation.candidate.program.eval valuation) =
      creation.originalSource.eval valuation
        (carrier.implementation.candidate.program.eval valuation)

/-- Derive the replacement and full witness from the original carrier itself. -/
def dischargeR7 (carrier : WireCarrier 1 outputs fields)
    (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    R7Discharge carrier keep creation :=
  { actualSource := (realize carrier).source creation.coordinate
    sourceExact := rfl
    fullWitness := by
      intro valuation
      rw [creation.sourceExact]
      exact realize_field carrier valuation creation.coordinate }

theorem R7Discharge.full_value {carrier : WireCarrier 1 outputs fields}
    {keep : Fin fields → Bool}
    {creation : WireObligationRestoration.R5Creation carrier keep}
    (witness : R7Discharge carrier keep creation) (valuation : Valuation 1) :
    witness.actualSource.eval valuation
        ((realize carrier).implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate := by
  have value := witness.fullWitness valuation
  rw [creation.sourceExact] at value
  exact value

theorem dischargeR7_source_exact (carrier : WireCarrier 1 outputs fields)
    (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    (dischargeR7 carrier keep creation).actualSource =
      (realize carrier).source creation.coordinate := rfl

theorem dischargeR7_full_value (carrier : WireCarrier 1 outputs fields)
    (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep)
    (valuation : Valuation 1) :
    (dischargeR7 carrier keep creation).actualSource.eval valuation
        ((realize carrier).implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate :=
  (dischargeR7 carrier keep creation).full_value valuation

/-- A computed complete-word gain, not a proper-support Package E certificate. -/
structure CheckedGain (carrier : WireCarrier 1 outputs fields) : Type where
  smaller : (realize carrier).implementation.gateCount < carrier.implementation.gateCount

def checkedGain (carrier : WireCarrier 1 outputs fields) : Option (CheckedGain carrier) :=
  if smaller : (realize carrier).implementation.gateCount < carrier.implementation.gateCount
    then some ⟨smaller⟩ else none

theorem checkedGain_isSome_iff (carrier : WireCarrier 1 outputs fields) :
    (checkedGain carrier).isSome = true ↔
      (realize carrier).implementation.gateCount < carrier.implementation.gateCount := by
  unfold checkedGain
  split
  next smaller =>
    constructor
    · intro _accepted
      exact smaller
    · intro _smaller
      rfl
  next notSmaller =>
    constructor
    · intro impossible
      cases impossible
    · intro smaller
      exact (notSmaller smaller).elim

/-- If any complete unary realization is smaller, this computed query succeeds. -/
theorem checkedGain_complete (carrier other : WireCarrier 1 outputs fields)
    (sameFull : Equivalent other.exposed.candidate.program
      other.exposed.candidate.directWireWord carrier.exposed.candidate.program
      carrier.exposed.candidate.directWireWord)
    (smaller : other.implementation.gateCount < carrier.implementation.gateCount) :
    (checkedGain carrier).isSome = true :=
  (checkedGain_isSome_iff carrier).mpr
    (Nat.lt_of_le_of_lt (realize_minimal carrier other sameFull) smaller)

def CheckedGain.strictGain {carrier : WireCarrier 1 outputs fields}
    (gain : CheckedGain carrier) :
    StrictEquivalentGain carrier.implementation (realize carrier).implementation where
  smaller := gain.smaller
  equivalent := realize_equivalent carrier

theorem CheckedGain.checked {carrier : WireCarrier 1 outputs fields}
    (gain : CheckedGain carrier) :
    StrictEquivalentGain carrier.implementation (realize carrier).implementation ∧
      (∀ valuation field, (realize carrier).fieldValue valuation field =
        carrier.fieldValue valuation field) ∧
      (realize carrier).implementation.gateCount = (if needsNegation carrier then 1 else 0) :=
  ⟨gain.strictGain, realize_field carrier, realize_gateCount carrier⟩

end PNP.DirectWire.WireUnaryRealization
