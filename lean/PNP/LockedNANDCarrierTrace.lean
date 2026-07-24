/-
Copyright (c) 2026 PNP Labs.

Global carrier geometry and trace equivalence for the locked-NAND construction
in Section 17 of the pinned legacy manuscript
`final-pnp-proof-report-hardened-7072f8d`.

Unlike the historical package records, every object below is derived from an
intrinsically topological `DirectWire.Program`.  No occurrence table, carrier
separation certificate, coherent trace, satisfiability bit, or package verdict
is supplied by a caller.

This file proves the manuscript's carrier-separation and trace-equivalence
layer for arbitrary finite NAND circuits.  It does not yet assemble the exposed
global direct-wire baseline, prove `BaselineDistinct`, instantiate the
conditional threshold boundary, construct a polynomial bitstring-level
reduction, or prove P = NP.
-/

import PNP.LockedNANDBaseline
import PNP.LockedNANDLocalBaseline

namespace PNP
namespace DirectWire
namespace LockedNANDTrace

/-! ## Intrinsic Boolean NAND circuits -/

/-- A Boolean NAND circuit has an intrinsically topological program and a
declared gate output.  The output field makes the zero-gate case uninhabited;
the later CNF-to-NAND normalization is responsible for installing a final
output gate. -/
structure Circuit (inputs : Nat) where
  gateCount : Nat
  program : Program inputs gateCount
  outputGate : Fin gateCount

/-- Satisfaction of the declared Boolean output. -/
def Circuit.Satisfiable {inputs : Nat} (circuit : Circuit inputs) : Prop :=
  ∃ input : Valuation inputs,
    circuit.program.eval input circuit.outputGate = true

/-! ## Tagged carrier layout -/

/-- The two ordered source occurrences belonging to one NAND gate. -/
inductive OccurrenceSide where
  | left
  | right
  deriving Repr, DecidableEq

def OccurrenceSide.offset : OccurrenceSide → Nat
  | .left => 0
  | .right => 1

/-- Exact number of carrier coordinates in
`X ⊔ T ⊔ O ⊔ R ⊔ L ⊔ {z}`. -/
def carrierWidth (inputs gates : Nat) : Nat :=
  inputs + 6 * gates + 1

/-- One typed member of the six disjoint carrier families. -/
inductive CarrierSlot (inputs gates : Nat) where
  | primary : Fin inputs → CarrierSlot inputs gates
  | trace : Fin gates → CarrierSlot inputs gates
  | occurrence : Fin (2 * gates) → CarrierSlot inputs gates
  | sourceLock : Fin (2 * gates) → CarrierSlot inputs gates
  | traceLock : Fin gates → CarrierSlot inputs gates
  | finalLock : CarrierSlot inputs gates
  deriving Repr, DecidableEq

/-- Pair one gate coordinate with its left or right occurrence coordinate. -/
def occurrenceCoordinate {gates : Nat} (gate : Fin gates)
    (side : OccurrenceSide) : Fin (2 * gates) :=
  match side with
  | .left =>
      ⟨2 * gate.val, by
        simpa only [Nat.two_mul] using
          Nat.add_lt_add gate.isLt gate.isLt⟩
  | .right =>
      ⟨2 * gate.val + 1, by
        simpa only [Nat.two_mul, Nat.add_assoc] using
          Nat.add_lt_add_of_lt_of_le gate.isLt
            (Nat.succ_le_of_lt gate.isLt)⟩

@[simp] theorem occurrenceCoordinate_left_val {gates : Nat}
    (gate : Fin gates) :
    (occurrenceCoordinate gate .left).val = 2 * gate.val := by
  rfl

@[simp] theorem occurrenceCoordinate_right_val {gates : Nat}
    (gate : Fin gates) :
    (occurrenceCoordinate gate .right).val = 2 * gate.val + 1 := by
  rfl

theorem occurrenceCoordinate_injective {gates : Nat}
    {leftGate rightGate : Fin gates}
    {leftSide rightSide : OccurrenceSide}
    (equal : occurrenceCoordinate leftGate leftSide =
      occurrenceCoordinate rightGate rightSide) :
    leftGate = rightGate ∧ leftSide = rightSide := by
  have valueEqual := congrArg Fin.val equal
  cases leftSide <;> cases rightSide
  · constructor
    · apply Fin.ext
      change 2 * leftGate.val = 2 * rightGate.val at valueEqual
      omega
    · rfl
  · change 2 * leftGate.val = 2 * rightGate.val + 1 at valueEqual
    omega
  · change 2 * leftGate.val + 1 = 2 * rightGate.val at valueEqual
    omega
  · constructor
    · apply Fin.ext
      change 2 * leftGate.val + 1 = 2 * rightGate.val + 1 at valueEqual
      omega
    · rfl

theorem occurrenceCoordinate_left_ne_right {gates : Nat}
    (gate : Fin gates) :
    occurrenceCoordinate gate .left ≠ occurrenceCoordinate gate .right := by
  intro equal
  exact OccurrenceSide.noConfusion
    (occurrenceCoordinate_injective equal).2

def primarySlot {inputs gates : Nat} (index : Fin inputs) :
    Fin (carrierWidth inputs gates) :=
  ⟨index.val, by
    unfold carrierWidth
    omega⟩

def traceSlot {inputs gates : Nat} (index : Fin gates) :
    Fin (carrierWidth inputs gates) :=
  ⟨inputs + index.val, by
    unfold carrierWidth
    omega⟩

def occurrenceSlot {inputs gates : Nat} (index : Fin (2 * gates)) :
    Fin (carrierWidth inputs gates) :=
  ⟨inputs + gates + index.val, by
    unfold carrierWidth
    omega⟩

def sourceLockSlot {inputs gates : Nat} (index : Fin (2 * gates)) :
    Fin (carrierWidth inputs gates) :=
  ⟨inputs + 3 * gates + index.val, by
    unfold carrierWidth
    omega⟩

def traceLockSlot {inputs gates : Nat} (index : Fin gates) :
    Fin (carrierWidth inputs gates) :=
  ⟨inputs + 5 * gates + index.val, by
    unfold carrierWidth
    omega⟩

def finalLockSlot (inputs gates : Nat) : Fin (carrierWidth inputs gates) :=
  ⟨inputs + 6 * gates, by
    unfold carrierWidth
    omega⟩

/-- Encode one tagged carrier member into the contiguous `Fin` layout used by
the later direct-wire builder. -/
def CarrierSlot.encode {inputs gates : Nat} :
    CarrierSlot inputs gates → Fin (carrierWidth inputs gates)
  | .primary index => primarySlot index
  | .trace index => traceSlot index
  | .occurrence index => occurrenceSlot index
  | .sourceLock index => sourceLockSlot index
  | .traceLock index => traceLockSlot index
  | .finalLock => finalLockSlot inputs gates

/-- Decode every numeric carrier coordinate into exactly one tagged family. -/
def decodeCarrierSlot {inputs gates : Nat}
    (slot : Fin (carrierWidth inputs gates)) : CarrierSlot inputs gates :=
  if hPrimary : slot.val < inputs then
    .primary ⟨slot.val, hPrimary⟩
  else if hTrace : slot.val < inputs + gates then
    .trace ⟨slot.val - inputs, by omega⟩
  else if hOccurrence : slot.val < inputs + 3 * gates then
    .occurrence ⟨slot.val - (inputs + gates), by omega⟩
  else if hSourceLock : slot.val < inputs + 5 * gates then
    .sourceLock ⟨slot.val - (inputs + 3 * gates), by omega⟩
  else if hTraceLock : slot.val < inputs + 6 * gates then
    .traceLock ⟨slot.val - (inputs + 5 * gates), by omega⟩
  else
    .finalLock

@[simp] theorem decodeCarrierSlot_primary {inputs gates : Nat}
    (index : Fin inputs) :
    decodeCarrierSlot (primarySlot (gates := gates) index) =
      CarrierSlot.primary index := by
  unfold decodeCarrierSlot primarySlot
  split
  · congr 1
  · rename_i hNotPrimary
    exact False.elim (hNotPrimary index.isLt)

@[simp] theorem decodeCarrierSlot_trace {inputs gates : Nat}
    (index : Fin gates) :
    decodeCarrierSlot (traceSlot (inputs := inputs) index) =
      CarrierSlot.trace index := by
  unfold decodeCarrierSlot traceSlot
  simp only
  split
  · omega
  · split
    · congr 1
      apply Fin.ext
      simp
    · omega

@[simp] theorem decodeCarrierSlot_occurrence {inputs gates : Nat}
    (index : Fin (2 * gates)) :
    decodeCarrierSlot (occurrenceSlot (inputs := inputs) index) =
      CarrierSlot.occurrence index := by
  unfold decodeCarrierSlot occurrenceSlot
  simp only
  split
  · omega
  · split
    · omega
    · split
      · congr 1
        apply Fin.ext
        simp
      · omega

@[simp] theorem decodeCarrierSlot_sourceLock {inputs gates : Nat}
    (index : Fin (2 * gates)) :
    decodeCarrierSlot (sourceLockSlot (inputs := inputs) index) =
      CarrierSlot.sourceLock index := by
  unfold decodeCarrierSlot sourceLockSlot
  simp only
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split
        · congr 1
          apply Fin.ext
          simp
        · omega

@[simp] theorem decodeCarrierSlot_traceLock {inputs gates : Nat}
    (index : Fin gates) :
    decodeCarrierSlot (traceLockSlot (inputs := inputs) index) =
      CarrierSlot.traceLock index := by
  unfold decodeCarrierSlot traceLockSlot
  simp only
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split
        · omega
        · split
          · congr 1
            apply Fin.ext
            simp
          · omega

@[simp] theorem decodeCarrierSlot_finalLock (inputs gates : Nat) :
    decodeCarrierSlot (finalLockSlot inputs gates) =
      (CarrierSlot.finalLock : CarrierSlot inputs gates) := by
  unfold decodeCarrierSlot finalLockSlot carrierWidth
  simp only
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split
        · omega
        · split
          · omega
          · rfl

@[simp] theorem decode_encode {inputs gates : Nat}
    (slot : CarrierSlot inputs gates) :
    decodeCarrierSlot slot.encode = slot := by
  cases slot <;> simp [CarrierSlot.encode]

theorem encode_decode {inputs gates : Nat}
    (slot : Fin (carrierWidth inputs gates)) :
    (decodeCarrierSlot slot).encode = slot := by
  unfold decodeCarrierSlot
  split
  · apply Fin.ext
    rfl
  · split
    · apply Fin.ext
      simp [CarrierSlot.encode, traceSlot]
      omega
    · split
      · apply Fin.ext
        simp [CarrierSlot.encode, occurrenceSlot]
        omega
      · split
        · apply Fin.ext
          simp [CarrierSlot.encode, sourceLockSlot]
          omega
        · split
          · apply Fin.ext
            simp [CarrierSlot.encode, traceLockSlot]
            omega
          · apply Fin.ext
            simp [CarrierSlot.encode, finalLockSlot, carrierWidth]
            have hUpper := slot.isLt
            unfold carrierWidth at hUpper
            omega

theorem CarrierSlot.encode_injective {inputs gates : Nat} :
    Function.Injective
      (CarrierSlot.encode :
        CarrierSlot inputs gates → Fin (carrierWidth inputs gates)) := by
  intro left right equal
  have := congrArg decodeCarrierSlot equal
  simpa using this

/-- The numeric carrier is an exact partition: encoding and decoding are
mutual inverses, so no two families collide and no coordinate is omitted. -/
structure CarrierSeparation (inputs gates : Nat) : Prop where
  decodeEncode : ∀ slot : CarrierSlot inputs gates,
    decodeCarrierSlot slot.encode = slot
  encodeDecode : ∀ slot : Fin (carrierWidth inputs gates),
    (decodeCarrierSlot slot).encode = slot
  encodeInjective : Function.Injective
    (CarrierSlot.encode :
      CarrierSlot inputs gates → Fin (carrierWidth inputs gates))

theorem carrierSeparation (inputs gates : Nat) :
    CarrierSeparation inputs gates :=
  { decodeEncode := decode_encode
    encodeDecode := encode_decode
    encodeInjective := CarrierSlot.encode_injective }

theorem finalLock_fresh {inputs gates : Nat}
    (slot : CarrierSlot inputs gates)
    (notFinal : slot ≠ .finalLock) :
    slot.encode ≠ finalLockSlot inputs gates := by
  intro equal
  apply notFinal
  apply CarrierSlot.encode_injective
  simpa [CarrierSlot.encode] using equal

/-! ## Semantic carrier valuations -/

/-- Values assigned independently to every tagged carrier family. -/
structure CarrierValuation (inputs gates : Nat) where
  primary : Valuation inputs
  trace : Valuation gates
  occurrence : Valuation (2 * gates)
  sourceLock : Valuation (2 * gates)
  traceLock : Valuation gates
  finalLock : Bool

def CarrierValuation.occurrenceAt {inputs gates : Nat}
    (valuation : CarrierValuation inputs gates)
    (gate : Fin gates) (side : OccurrenceSide) : Bool :=
  valuation.occurrence (occurrenceCoordinate gate side)

def CarrierValuation.sourceLockAt {inputs gates : Nat}
    (valuation : CarrierValuation inputs gates)
    (gate : Fin gates) (side : OccurrenceSide) : Bool :=
  valuation.sourceLock (occurrenceCoordinate gate side)

def liftOccurrenceCoordinate {gates : Nat} (index : Fin (2 * gates)) :
    Fin (2 * (gates + 1)) :=
  ⟨index.val, by omega⟩

/-- Restrict a carrier assignment to the prefix ending before its last gate. -/
def CarrierValuation.restrict {inputs gates : Nat}
    (valuation : CarrierValuation inputs (gates + 1)) :
    CarrierValuation inputs gates :=
  { primary := valuation.primary
    trace := fun index => valuation.trace index.castSucc
    occurrence := fun index =>
      valuation.occurrence (liftOccurrenceCoordinate index)
    sourceLock := fun index =>
      valuation.sourceLock (liftOccurrenceCoordinate index)
    traceLock := fun index => valuation.traceLock index.castSucc
    finalLock := valuation.finalLock }

@[simp] theorem CarrierValuation.restrict_primary {inputs gates : Nat}
    (valuation : CarrierValuation inputs (gates + 1)) :
    valuation.restrict.primary = valuation.primary := rfl

@[simp] theorem CarrierValuation.restrict_trace {inputs gates : Nat}
    (valuation : CarrierValuation inputs (gates + 1)) (index : Fin gates) :
    valuation.restrict.trace index = valuation.trace index.castSucc := rfl

@[simp] theorem CarrierValuation.restrict_occurrenceAt
    {inputs gates : Nat}
    (valuation : CarrierValuation inputs (gates + 1))
    (gate : Fin gates) (side : OccurrenceSide) :
    valuation.restrict.occurrenceAt gate side =
      valuation.occurrenceAt gate.castSucc side := by
  unfold CarrierValuation.occurrenceAt CarrierValuation.restrict
    liftOccurrenceCoordinate occurrenceCoordinate
  apply congrArg valuation.occurrence
  apply Fin.ext
  cases side <;> rfl

@[simp] theorem CarrierValuation.restrict_sourceLockAt
    {inputs gates : Nat}
    (valuation : CarrierValuation inputs (gates + 1))
    (gate : Fin gates) (side : OccurrenceSide) :
    valuation.restrict.sourceLockAt gate side =
      valuation.sourceLockAt gate.castSucc side := by
  unfold CarrierValuation.sourceLockAt CarrierValuation.restrict
    liftOccurrenceCoordinate occurrenceCoordinate
  apply congrArg valuation.sourceLock
  apply Fin.ext
  cases side <;> rfl

/-! ## Distinguished locked checks -/

/-- Distinguished source check selected by the actual source constructor. -/
def sourceCheck {inputs gates : Nat} (source : Source inputs gates)
    (lock occurrence : Bool) (input : Valuation inputs)
    (trace : Valuation gates) : Bool :=
  match source with
  | .input index =>
      (equalityMacro lock occurrence (input index)).a8
  | .constant false =>
      (constantZeroMacro lock occurrence).d3
  | .constant true =>
      (constantOneMacro lock occurrence).b2
  | .gate index =>
      (equalityMacro lock occurrence (trace index)).a8

/-- Distinguished trace equation for one NAND gate. -/
def traceCheck (lock trace left right : Bool) : Bool :=
  (traceMacro lock trace left right).q16

theorem boolEq_eq_true_iff (left right : Bool) :
    boolEq left right = true ↔ left = right := by
  cases left <;> cases right <;> decide

theorem sourceCheck_self {inputs gates : Nat}
    (source : Source inputs gates) (input : Valuation inputs)
    (trace : Valuation gates) :
    sourceCheck source true (source.eval input trace) input trace = true := by
  cases source with
  | input index =>
      rw [sourceCheck, equalityMacro_distinguished_spec]
      simp [Source.eval, boolEq_eq_true_iff]
  | constant value =>
      cases value with
      | false =>
          rw [sourceCheck, constantZeroMacro_distinguished_spec]
          rfl
      | true =>
          rw [sourceCheck, constantOneMacro_distinguished_spec]
          rfl
  | gate index =>
      rw [sourceCheck, equalityMacro_distinguished_spec]
      simp [Source.eval, boolEq_eq_true_iff]

theorem sourceCheck_true_value {inputs gates : Nat}
    (source : Source inputs gates) (lock occurrence : Bool)
    (input : Valuation inputs) (trace : Valuation gates)
    (accepted : sourceCheck source lock occurrence input trace = true) :
    occurrence = source.eval input trace := by
  cases source with
  | input index =>
      rw [sourceCheck, equalityMacro_distinguished_spec] at accepted
      have parts :
          lock = true ∧ boolEq occurrence (input index) = true := by
        simpa using accepted
      exact (boolEq_eq_true_iff occurrence (input index)).mp parts.2
  | constant value =>
      cases value with
      | false =>
          rw [sourceCheck, constantZeroMacro_distinguished_spec] at accepted
          cases lock <;> cases occurrence <;>
            simp [Source.eval] at accepted ⊢
      | true =>
          rw [sourceCheck, constantOneMacro_distinguished_spec] at accepted
          cases lock <;> cases occurrence <;>
            simp [Source.eval] at accepted ⊢
  | gate index =>
      rw [sourceCheck, equalityMacro_distinguished_spec] at accepted
      have parts :
          lock = true ∧ boolEq occurrence (trace index) = true := by
        simpa using accepted
      exact (boolEq_eq_true_iff occurrence (trace index)).mp parts.2

theorem traceCheck_self (left right : Bool) :
    traceCheck true (boolNand left right) left right = true := by
  rw [traceCheck, traceMacro_distinguished_spec]
  simp [boolEq_eq_true_iff]

theorem traceCheck_true_value (lock trace left right : Bool)
    (accepted : traceCheck lock trace left right = true) :
    trace = boolNand left right := by
  rw [traceCheck, traceMacro_distinguished_spec] at accepted
  have parts :
      lock = true ∧ boolEq trace (boolNand left right) = true := by
    simpa using accepted
  exact (boolEq_eq_true_iff trace (boolNand left right)).mp parts.2

/-- The exact three checks belonging to the newest topological gate. -/
def gateChecks {inputs gates : Nat} (gate : Gate inputs gates)
    (valuation : CarrierValuation inputs (gates + 1)) : List Bool :=
  let coordinate := Fin.last gates
  let earlierTrace : Valuation gates :=
    fun index => valuation.trace index.castSucc
  let leftOccurrence := valuation.occurrenceAt coordinate .left
  let rightOccurrence := valuation.occurrenceAt coordinate .right
  [sourceCheck gate.left
      (valuation.sourceLockAt coordinate .left)
      leftOccurrence valuation.primary earlierTrace,
   sourceCheck gate.right
      (valuation.sourceLockAt coordinate .right)
      rightOccurrence valuation.primary earlierTrace,
   traceCheck (valuation.traceLock coordinate)
      (valuation.trace coordinate) leftOccurrence rightOccurrence]

@[simp] theorem gateChecks_length {inputs gates : Nat}
    (gate : Gate inputs gates)
    (valuation : CarrierValuation inputs (gates + 1)) :
    (gateChecks gate valuation).length = 3 := rfl

/-- All distinguished checks in topological gate order. -/
def distinguishedChecks {inputs : Nat} :
    {gates : Nat} → Program inputs gates →
      CarrierValuation inputs gates → List Bool
  | 0, .empty, _ => []
  | _ + 1, .snoc initial gate, valuation =>
      distinguishedChecks initial valuation.restrict ++
        gateChecks gate valuation

@[simp] theorem distinguishedChecks_length {inputs gates : Nat}
    (program : Program inputs gates)
    (valuation : CarrierValuation inputs gates) :
    (distinguishedChecks program valuation).length = 3 * gates := by
  induction program with
  | empty => rfl
  | @snoc gates initial gate ih =>
      simp [distinguishedChecks, ih, gateChecks_length]
      omega

/-- Prefix-conjunction value of exactly the distinguished check list. -/
def tracePredicate {inputs gates : Nat} (program : Program inputs gates)
    (valuation : CarrierValuation inputs gates) : Bool :=
  prefixConjunction (distinguishedChecks program valuation)

/-! ## Canonical coherent extension -/

/-- The value of every ordered source occurrence under genuine topological
evaluation. -/
def coherentOccurrences {inputs : Nat} :
    {gates : Nat} → Program inputs gates → Valuation inputs →
      Valuation (2 * gates)
  | 0, .empty, _, index => Fin.elim0 index
  | gates + 1, .snoc initial gate, input, index =>
      if hEarlier : index.val < 2 * gates then
        coherentOccurrences initial input ⟨index.val, hEarlier⟩
      else if index.val = 2 * gates then
        gate.left.eval input (initial.eval input)
      else
        gate.right.eval input (initial.eval input)

@[simp] theorem coherentOccurrences_snoc_earlier
    {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates) (input : Valuation inputs)
    (index : Fin (2 * gates)) :
    coherentOccurrences (.snoc initial gate) input
        (liftOccurrenceCoordinate index) =
      coherentOccurrences initial input index := by
  change
    (if hEarlier : index.val < 2 * gates then
        coherentOccurrences initial input ⟨index.val, hEarlier⟩
      else if index.val = 2 * gates then
        gate.left.eval input (initial.eval input)
      else
        gate.right.eval input (initial.eval input)) =
      coherentOccurrences initial input index
  rw [dif_pos index.isLt]

@[simp] theorem coherentOccurrences_snoc_left
    {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates) (input : Valuation inputs) :
    coherentOccurrences (.snoc initial gate) input
        (occurrenceCoordinate (Fin.last gates) .left) =
      gate.left.eval input (initial.eval input) := by
  change
    (if hEarlier : 2 * gates < 2 * gates then
        coherentOccurrences initial input ⟨2 * gates, hEarlier⟩
      else if 2 * gates = 2 * gates then
        gate.left.eval input (initial.eval input)
      else
        gate.right.eval input (initial.eval input)) =
      gate.left.eval input (initial.eval input)
  simp

@[simp] theorem coherentOccurrences_snoc_right
    {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates) (input : Valuation inputs) :
    coherentOccurrences (.snoc initial gate) input
        (occurrenceCoordinate (Fin.last gates) .right) =
      gate.right.eval input (initial.eval input) := by
  change
    (if hEarlier : 2 * gates + 1 < 2 * gates then
        coherentOccurrences initial input ⟨2 * gates + 1, hEarlier⟩
      else if 2 * gates + 1 = 2 * gates then
        gate.left.eval input (initial.eval input)
      else
        gate.right.eval input (initial.eval input)) =
      gate.right.eval input (initial.eval input)
  split
  · omega
  · split
    · omega
    · rfl

/-- Canonical extension: genuine gate values, genuine source occurrences, all
check locks active, and a fresh active final lock. -/
def coherentExtension {inputs gates : Nat}
    (program : Program inputs gates) (input : Valuation inputs) :
    CarrierValuation inputs gates :=
  { primary := input
    trace := program.eval input
    occurrence := coherentOccurrences program input
    sourceLock := fun _ => true
    traceLock := fun _ => true
    finalLock := true }

@[ext] theorem CarrierValuation.ext {inputs gates : Nat}
    (left right : CarrierValuation inputs gates)
    (primary : left.primary = right.primary)
    (trace : left.trace = right.trace)
    (occurrence : left.occurrence = right.occurrence)
    (sourceLock : left.sourceLock = right.sourceLock)
    (traceLock : left.traceLock = right.traceLock)
    (finalLock : left.finalLock = right.finalLock) :
    left = right := by
  cases left
  cases right
  simp_all

@[simp] theorem coherentExtension_primary {inputs gates : Nat}
    (program : Program inputs gates) (input : Valuation inputs) :
    (coherentExtension program input).primary = input := rfl

@[simp] theorem coherentExtension_trace {inputs gates : Nat}
    (program : Program inputs gates) (input : Valuation inputs)
    (gate : Fin gates) :
    (coherentExtension program input).trace gate =
      program.eval input gate := rfl

@[simp] theorem coherentExtension_sourceLockAt {inputs gates : Nat}
    (program : Program inputs gates) (input : Valuation inputs)
    (gate : Fin gates) (side : OccurrenceSide) :
    (coherentExtension program input).sourceLockAt gate side = true := rfl

@[simp] theorem coherentExtension_traceLock {inputs gates : Nat}
    (program : Program inputs gates) (input : Valuation inputs)
    (gate : Fin gates) :
    (coherentExtension program input).traceLock gate = true := rfl

@[simp] theorem coherentExtension_finalLock {inputs gates : Nat}
    (program : Program inputs gates) (input : Valuation inputs) :
    (coherentExtension program input).finalLock = true := rfl

@[simp] theorem coherentExtension_snoc_restrict
    {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates) (input : Valuation inputs) :
    (coherentExtension (.snoc initial gate) input).restrict =
      coherentExtension initial input := by
  apply CarrierValuation.ext
  · rfl
  · funext index
    exact Program.eval_snoc_castSucc initial gate input index
  · funext index
    exact coherentOccurrences_snoc_earlier initial gate input index
  · funext index
    rfl
  · funext index
    rfl
  · rfl

theorem gateChecks_coherent
    {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates) (input : Valuation inputs) :
    gateChecks gate (coherentExtension (.snoc initial gate) input) =
      [true, true, true] := by
  simp [gateChecks, coherentExtension, CarrierValuation.occurrenceAt,
    CarrierValuation.sourceLockAt, coherentOccurrences_snoc_left,
    coherentOccurrences_snoc_right, sourceCheck_self, traceCheck_self,
    Gate.eval, Program.eval_snoc_last]

theorem distinguishedChecks_coherentExtension
    {inputs gates : Nat} (program : Program inputs gates)
    (input : Valuation inputs) :
    distinguishedChecks program (coherentExtension program input) =
      List.replicate (3 * gates) true := by
  induction program with
  | empty => rfl
  | @snoc gates initial gate ih =>
      rw [distinguishedChecks, coherentExtension_snoc_restrict,
        ih, gateChecks_coherent]
      change
        List.replicate (3 * gates) true ++ List.replicate 3 true =
          List.replicate (3 * (gates + 1)) true
      rw [List.replicate_append_replicate]
      congr 1

theorem tracePredicate_coherentExtension
    {inputs gates : Nat} (program : Program inputs gates)
    (input : Valuation inputs) :
    tracePredicate program (coherentExtension program input) = true := by
  unfold tracePredicate
  rw [distinguishedChecks_coherentExtension]
  apply (prefixConjunction_eq_true_iff _).mpr
  intro check member
  simpa using (List.eq_of_mem_replicate member)

/-! ## Reverse trace soundness -/

private theorem acceptedEarlierChecks
    {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates)
    (valuation : CarrierValuation inputs (gates + 1))
    (accepted :
      tracePredicate (.snoc initial gate) valuation = true) :
    tracePredicate initial valuation.restrict = true := by
  apply (prefixConjunction_eq_true_iff _).mpr
  intro check member
  have allAccepted :=
    (prefixConjunction_eq_true_iff
      (distinguishedChecks (.snoc initial gate) valuation)).mp accepted
  apply allAccepted check
  unfold distinguishedChecks
  exact List.mem_append_left _ member

private theorem acceptedCurrentCheck
    {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates)
    (valuation : CarrierValuation inputs (gates + 1))
    (accepted :
      tracePredicate (.snoc initial gate) valuation = true)
    (check : Bool) (member : check ∈ gateChecks gate valuation) :
    check = true := by
  have allAccepted :=
    (prefixConjunction_eq_true_iff
      (distinguishedChecks (.snoc initial gate) valuation)).mp accepted
  apply allAccepted check
  unfold distinguishedChecks
  exact List.mem_append_right _ member

/-- If every distinguished check is true, every trace coordinate equals the
actual topological evaluation of the circuit under the primary carrier
assignment. -/
theorem trace_sound_of_predicate_true
    {inputs gates : Nat} (program : Program inputs gates)
    (valuation : CarrierValuation inputs gates)
    (accepted : tracePredicate program valuation = true)
    (index : Fin gates) :
    valuation.trace index =
      program.eval valuation.primary index := by
  induction program with
  | empty => exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      by_cases hEarlier : index.val < gates
      · let earlierIndex : Fin gates := ⟨index.val, hEarlier⟩
        have indexEqual : index = earlierIndex.castSucc := by
          apply Fin.ext
          rfl
        rw [indexEqual, Program.eval_snoc_castSucc]
        exact ih valuation.restrict
          (acceptedEarlierChecks initial gate valuation accepted)
          earlierIndex
      · have indexValue : index.val = gates := by
          have indexBound := index.isLt
          omega
        have indexEqual : index = Fin.last gates := by
          apply Fin.ext
          exact indexValue
        rw [indexEqual]
        let coordinate := Fin.last gates
        let earlierTrace : Valuation gates :=
          fun earlier => valuation.trace earlier.castSucc
        let leftOccurrence := valuation.occurrenceAt coordinate .left
        let rightOccurrence := valuation.occurrenceAt coordinate .right
        have leftAccepted : sourceCheck gate.left
            (valuation.sourceLockAt coordinate .left)
            leftOccurrence valuation.primary earlierTrace = true := by
          apply acceptedCurrentCheck initial gate valuation accepted
          exact List.Mem.head _
        have rightAccepted : sourceCheck gate.right
            (valuation.sourceLockAt coordinate .right)
            rightOccurrence valuation.primary earlierTrace = true := by
          apply acceptedCurrentCheck initial gate valuation accepted
          exact List.Mem.tail _ (List.Mem.head _)
        have traceAccepted : traceCheck
            (valuation.traceLock coordinate)
            (valuation.trace coordinate)
            leftOccurrence rightOccurrence = true := by
          apply acceptedCurrentCheck initial gate valuation accepted
          exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
        have leftValue :
            leftOccurrence =
              gate.left.eval valuation.primary earlierTrace :=
          sourceCheck_true_value gate.left
            (valuation.sourceLockAt coordinate .left)
            leftOccurrence valuation.primary earlierTrace leftAccepted
        have rightValue :
            rightOccurrence =
              gate.right.eval valuation.primary earlierTrace :=
          sourceCheck_true_value gate.right
            (valuation.sourceLockAt coordinate .right)
            rightOccurrence valuation.primary earlierTrace rightAccepted
        have currentValue :
            valuation.trace coordinate =
              boolNand leftOccurrence rightOccurrence :=
          traceCheck_true_value
            (valuation.traceLock coordinate)
            (valuation.trace coordinate)
            leftOccurrence rightOccurrence traceAccepted
        have earlierSound : ∀ earlier : Fin gates,
            earlierTrace earlier =
              initial.eval valuation.primary earlier := by
          intro earlier
          exact ih valuation.restrict
            (acceptedEarlierChecks initial gate valuation accepted) earlier
        have leftSemantic :
            gate.left.eval valuation.primary earlierTrace =
              gate.left.eval valuation.primary
                (initial.eval valuation.primary) :=
          gate.left.eval_congr (fun _ => rfl) earlierSound
        have rightSemantic :
            gate.right.eval valuation.primary earlierTrace =
              gate.right.eval valuation.primary
                (initial.eval valuation.primary) :=
          gate.right.eval_congr (fun _ => rfl) earlierSound
        rw [Program.eval_snoc_last]
        calc
          valuation.trace coordinate =
              boolNand leftOccurrence rightOccurrence := currentValue
          _ = boolNand
              (gate.left.eval valuation.primary earlierTrace)
              (gate.right.eval valuation.primary earlierTrace) := by
                rw [leftValue, rightValue]
          _ = boolNand
              (gate.left.eval valuation.primary
                (initial.eval valuation.primary))
              (gate.right.eval valuation.primary
                (initial.eval valuation.primary)) := by
                rw [leftSemantic, rightSemantic]

/-- Fixed-input form of the legacy manuscript's `TraceEquivalence` lemma. -/
theorem traceEquivalence
    {inputs : Nat} (circuit : Circuit inputs)
    (input : Valuation inputs) :
    (∃ valuation : CarrierValuation inputs circuit.gateCount,
        valuation.primary = input ∧
        tracePredicate circuit.program valuation = true ∧
        valuation.trace circuit.outputGate = true) ↔
      circuit.program.eval input circuit.outputGate = true := by
  constructor
  · rintro ⟨valuation, primary, accepted, outputTrue⟩
    have traceSound :=
      trace_sound_of_predicate_true circuit.program valuation
        accepted circuit.outputGate
    rw [primary] at traceSound
    exact traceSound ▸ outputTrue
  · intro outputTrue
    exact ⟨coherentExtension circuit.program input, rfl,
      tracePredicate_coherentExtension circuit.program input, outputTrue⟩

/-- Global satisfiability form: the locked trace predicate and declared output
have a joint carrier assignment exactly when the source NAND circuit is
satisfiable. -/
theorem satisfiable_iff_trace_extension
    {inputs : Nat} (circuit : Circuit inputs) :
    circuit.Satisfiable ↔
      ∃ valuation : CarrierValuation inputs circuit.gateCount,
        tracePredicate circuit.program valuation = true ∧
        valuation.trace circuit.outputGate = true := by
  constructor
  · rintro ⟨input, outputTrue⟩
    exact ⟨coherentExtension circuit.program input,
      tracePredicate_coherentExtension circuit.program input, outputTrue⟩
  · rintro ⟨valuation, accepted, outputTrue⟩
    refine ⟨valuation.primary, ?_⟩
    have traceSound :=
      trace_sound_of_predicate_true circuit.program valuation
        accepted circuit.outputGate
    exact traceSound ▸ outputTrue

/-- Constructive `G-Coh`: every primary assignment has an extension making all
distinguished trace checks true, independently of whether the declared output
is true. -/
theorem exists_coherent_trace
    {inputs : Nat} (circuit : Circuit inputs)
    (input : Valuation inputs) :
    ∃ valuation : CarrierValuation inputs circuit.gateCount,
      valuation.primary = input ∧
      tracePredicate circuit.program valuation = true :=
  ⟨coherentExtension circuit.program input, rfl,
    tracePredicate_coherentExtension circuit.program input⟩

end LockedNANDTrace
end DirectWire
end PNP
