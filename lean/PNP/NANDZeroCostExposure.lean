/-
Copyright (c) 2026 PNP Labs.

Source-derived zero-cost exposure of inputs, constants and existing outputs.
The extension and projection are literal output-word constructions. Their
two-way transfer of arbitrary realizations proves equality of semantic minima;
no minimum is executed by the constructor.

This is not arbitrary internal-wire exposure, forced positive materializer
cost, a full profile model, Package E, global saturation or polynomial PCCMin.
-/

import PNP.NANDMinimum
import PNP.NANDComposition

namespace PNP.DirectWire.ZeroCostExposure

/-- References with a zero-gate interpretation in every realization of the
original open function, not only in its current physical implementation. -/
inductive Reference (inputs outputs : Nat) where
  | input : Fin inputs → Reference inputs outputs
  | constant : Bool → Reference inputs outputs
  | output : Fin outputs → Reference inputs outputs
  deriving Repr, DecidableEq

variable {inputs outputs added : Nat}

def Reference.value (reference : Reference inputs outputs)
    (valuation : Valuation inputs) (result : Valuation outputs) : Bool :=
  match reference with
  | .input index => valuation index
  | .constant value => value
  | .output index => result index

def Reference.toSource (reference : Reference inputs outputs)
    (current : Implementation inputs outputs) :
    Source inputs current.gateCount :=
  match reference with
  | .input index => .input index
  | .constant value => .constant value
  | .output index => current.candidate.directWireWord.source index

theorem Reference.toSource_eval (reference : Reference inputs outputs)
    (current : Implementation inputs outputs) (valuation : Valuation inputs) :
    (reference.toSource current).eval valuation (current.candidate.program.eval valuation) =
      reference.value valuation (current.candidate.semantics valuation) := by
  cases reference <;> rfl

theorem Reference.value_congr (reference : Reference inputs outputs)
    (valuation : Valuation inputs) (left right : Valuation outputs)
    (same : ∀ output, left output = right output) :
    reference.value valuation left = reference.value valuation right := by
  cases reference with
  | input index => rfl
  | constant value => rfl
  | output index => exact same index

/-- Keep the program and append only selected free references to its output word. -/
def extend (current : Implementation inputs outputs)
    (layout : Fin added → Reference inputs outputs) :
    Implementation inputs (outputs + added) :=
  ⟨current.gateCount, Candidate.ofDirectWireWord current.candidate.program
    ⟨splitFin current.candidate.directWireWord.source
      (fun field => (layout field).toSource current)⟩⟩

/-- Forget the extra outputs of any realization, without changing its program. -/
def project (current : Implementation inputs (outputs + added)) :
    Implementation inputs outputs :=
  ⟨current.gateCount, Candidate.ofDirectWireWord current.candidate.program
    ⟨fun output => current.candidate.directWireWord.source
      (Fin.castAdd added output)⟩⟩

theorem extend_gateCount (current : Implementation inputs outputs)
    (layout : Fin added → Reference inputs outputs) :
    (extend current layout).gateCount = current.gateCount := rfl

theorem project_gateCount (current : Implementation inputs (outputs + added)) :
    (project (outputs := outputs) (added := added) current).gateCount =
      current.gateCount := rfl

theorem extend_original (current : Implementation inputs outputs)
    (layout : Fin added → Reference inputs outputs)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (extend current layout).candidate.semantics valuation (Fin.castAdd added output) =
      current.candidate.semantics valuation output := by
  unfold extend
  dsimp only
  rw [Candidate.ofDirectWireWord_semantics]
  change ((splitFin current.candidate.directWireWord.source
    (fun field => (layout field).toSource current)) (Fin.castAdd added output)).eval
      valuation (current.candidate.program.eval valuation) = _
  rw [splitFin_left]
  rfl

theorem extend_field (current : Implementation inputs outputs)
    (layout : Fin added → Reference inputs outputs)
    (valuation : Valuation inputs) (field : Fin added) :
    (extend current layout).candidate.semantics valuation (Fin.natAdd outputs field) =
      (layout field).value valuation (current.candidate.semantics valuation) := by
  unfold extend
  dsimp only
  rw [Candidate.ofDirectWireWord_semantics]
  change ((splitFin current.candidate.directWireWord.source
    (fun field => (layout field).toSource current)) (Fin.natAdd outputs field)).eval
      valuation (current.candidate.program.eval valuation) = _
  rw [splitFin_right]
  exact Reference.toSource_eval (layout field) current valuation

theorem project_semantics (current : Implementation inputs (outputs + added))
    (valuation : Valuation inputs) (output : Fin outputs) :
    (project (outputs := outputs) (added := added) current).candidate.semantics
        valuation output =
      current.candidate.semantics valuation (Fin.castAdd added output) := by
  unfold project
  dsimp only
  rw [Candidate.ofDirectWireWord_semantics]
  rfl

/-- The same syntactic layout extends every equivalent realization. -/
theorem extend_equivalent (left right : Implementation inputs outputs)
    (layout : Fin added → Reference inputs outputs)
    (same : Equivalent left.candidate.program left.candidate.directWireWord
      right.candidate.program right.candidate.directWireWord) :
    Equivalent (extend left layout).candidate.program
      (extend left layout).candidate.directWireWord
      (extend right layout).candidate.program
      (extend right layout).candidate.directWireWord := by
  intro valuation coordinate
  change (extend left layout).candidate.semantics valuation coordinate =
    (extend right layout).candidate.semantics valuation coordinate
  rcases finSum_decompose coordinate with ⟨output, rfl⟩ | ⟨field, rfl⟩
  · rw [extend_original, extend_original]
    exact same valuation output
  · rw [extend_field, extend_field]
    exact Reference.value_congr (layout field) valuation _ _
      (fun output => same valuation output)

theorem project_equivalent (left right : Implementation inputs (outputs + added))
    (same : Equivalent left.candidate.program left.candidate.directWireWord
      right.candidate.program right.candidate.directWireWord) :
    Equivalent (project (outputs := outputs) (added := added) left).candidate.program
      (project (outputs := outputs) (added := added) left).candidate.directWireWord
      (project (outputs := outputs) (added := added) right).candidate.program
      (project (outputs := outputs) (added := added) right).candidate.directWireWord := by
  intro valuation output
  change (project (outputs := outputs) (added := added) left).candidate.semantics
    valuation output =
    (project (outputs := outputs) (added := added) right).candidate.semantics
      valuation output
  rw [project_semantics, project_semantics]
  exact same valuation (Fin.castAdd added output)

theorem project_extend_equivalent (current : Implementation inputs outputs)
    (layout : Fin added → Reference inputs outputs) :
    Equivalent (project (outputs := outputs) (added := added)
      (extend current layout)).candidate.program
      (project (outputs := outputs) (added := added)
        (extend current layout)).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord := by
  intro valuation output
  change (project (outputs := outputs) (added := added)
    (extend current layout)).candidate.semantics valuation output =
      current.candidate.semantics valuation output
  rw [project_semantics, extend_original]

/-- Zero-cost exposure preserves the minimum over all equivalent circuits.
The proof transports arbitrary realizations in both directions; it does not
infer a minimum-size fact merely from the current program's gate count. -/
theorem referenceMinimum_extend (current : Implementation inputs outputs)
    (layout : Fin added → Reference inputs outputs) :
    referenceMinimum (extend current layout) = referenceMinimum current := by
  apply Nat.le_antisymm
  · have same := equivalentBool_sound (referenceMinimumWitness_equivalent current)
    have transferred := extend_equivalent (referenceMinimumImplementation current)
      current layout same
    exact referenceMinimum_le_of_equivalent (extend current layout)
      (extend (referenceMinimumImplementation current) layout).candidate transferred
  · have same := equivalentBool_sound
      (referenceMinimumWitness_equivalent (extend current layout))
    have transferred := project_equivalent (outputs := outputs) (added := added)
      (referenceMinimumImplementation (extend current layout))
      (extend current layout) same
    have original := Equivalent.trans transferred
      (project_extend_equivalent current layout)
    exact referenceMinimum_le_of_equivalent current
      (project (outputs := outputs) (added := added)
        (referenceMinimumImplementation (extend current layout))).candidate original

theorem residualSlack_extend (current : Implementation inputs outputs)
    (layout : Fin added → Reference inputs outputs) :
    residualSlack (extend current layout) = residualSlack current := by
  unfold residualSlack
  rw [extend_gateCount, referenceMinimum_extend]


/-- A literal source match, constructed by the recognizer rather than requested
as correctness authority from a caller. -/
structure Recognition (current : Implementation inputs outputs)
    (field : Source inputs current.gateCount) : Type where
  reference : Reference inputs outputs
  source_eq : reference.toSource current = field

private def findOutput (current : Implementation inputs outputs)
    (field : Source inputs current.gateCount) :
    List (Fin outputs) →
      Option { output : Fin outputs // current.candidate.directWireWord.source output = field }
  | [] => none
  | output :: rest =>
      if matched : current.candidate.directWireWord.source output = field then
        some ⟨output, matched⟩
      else findOutput current field rest

/-- Internal gate wires are accepted only when already exposed as an output.
No truth-table or minimum-size search runs in this recognizer. -/
def recognize (current : Implementation inputs outputs)
    (field : Source inputs current.gateCount) : Option (Recognition current field) :=
  match field with
  | .input index => some ⟨.input index, rfl⟩
  | .constant value => some ⟨.constant value, rfl⟩
  | .gate index =>
      match findOutput current (.gate index) (allFin outputs) with
      | none => none
      | some output => some ⟨.output output.val, output.property⟩

private def chosenReference (current : Implementation inputs outputs)
    (field : Source inputs current.gateCount) : Reference inputs outputs :=
  match recognize current field with
  | none => .constant false
  | some receipt => receipt.reference

private theorem chosenReference_matches (current : Implementation inputs outputs)
    (field : Source inputs current.gateCount)
    (accepted : (recognize current field).isSome = true) :
    (chosenReference current field).toSource current = field := by
  cases found : recognize current field with
  | none =>
      rw [found] at accepted
      cases accepted
  | some receipt =>
      unfold chosenReference
      rw [found]
      exact receipt.source_eq

def checkLayout (current : Implementation inputs outputs)
    (fields : Fin added → Source inputs current.gateCount) : Bool :=
  allTrue (allFin added) fun field => (recognize current (fields field)).isSome

/-- A source-derived layout for an entire ordered tuple of actual field wires. -/
structure LayoutRecognition (current : Implementation inputs outputs)
    (fields : Fin added → Source inputs current.gateCount) : Type where
  layout : Fin added → Reference inputs outputs
  source_eq : ∀ field, (layout field).toSource current = fields field

def compileLayout (current : Implementation inputs outputs)
    (fields : Fin added → Source inputs current.gateCount) :
    Option (LayoutRecognition current fields) :=
  if checked : checkLayout current fields = true then
    some
      { layout := fun field => chosenReference current (fields field)
        source_eq := by
          intro field
          exact chosenReference_matches current (fields field)
            (allTrue_sound checked (mem_allFin field)) }
  else none

theorem compileLayout_success_iff (current : Implementation inputs outputs)
    (fields : Fin added → Source inputs current.gateCount) :
    (∃ receipt, compileLayout current fields = some receipt) ↔
      checkLayout current fields = true := by
  constructor
  · rintro ⟨receipt, found⟩
    unfold compileLayout at found
    split at found
    · assumption
    · cases found
  · intro checked
    unfold compileLayout
    rw [dif_pos checked]
    exact ⟨_, rfl⟩

/-- Every successfully recognized tuple has its actual wire values, unchanged
gate count and unchanged semantic minimum. Refusal makes no claim of a gain,
a complete Package E route, or semantic impossibility of another encoding. -/
theorem compileLayout_sound (current : Implementation inputs outputs)
    (fields : Fin added → Source inputs current.gateCount)
    (receipt : LayoutRecognition current fields)
    (_accepted : compileLayout current fields = some receipt) :
    (extend current receipt.layout).gateCount = current.gateCount ∧
      referenceMinimum (extend current receipt.layout) = referenceMinimum current ∧
      ∀ valuation field,
        (extend current receipt.layout).candidate.semantics valuation
            (Fin.natAdd outputs field) =
          (fields field).eval valuation (current.candidate.program.eval valuation) := by
  refine ⟨extend_gateCount current receipt.layout,
    referenceMinimum_extend current receipt.layout, ?_⟩
  intro valuation field
  rw [extend_field]
  exact (Reference.toSource_eval (receipt.layout field) current valuation).symm.trans
    (congrArg (fun source => source.eval valuation (current.candidate.program.eval valuation))
      (receipt.source_eq field))

private theorem findOutput_exists_of_mem (current : Implementation inputs outputs)
    (field : Source inputs current.gateCount) (output : Fin outputs)
    {candidates : List (Fin outputs)} (member : output ∈ candidates)
    (same : current.candidate.directWireWord.source output = field) :
    ∃ result, findOutput current field candidates = some result := by
  induction member with
  | head =>
      unfold findOutput
      rw [dif_pos same]
      exact ⟨_, rfl⟩
  | tail head _ ih =>
      unfold findOutput
      split
      · exact ⟨_, rfl⟩
      · exact ih

/-- Exact completeness for literal input, constant and old-output aliases.
This is not completeness for all semantic identities between gate wires. -/
theorem recognize_success_iff (current : Implementation inputs outputs)
    (field : Source inputs current.gateCount) :
    (∃ receipt, recognize current field = some receipt) ↔
      ∃ reference : Reference inputs outputs, reference.toSource current = field := by
  constructor
  · rintro ⟨receipt, _⟩
    exact ⟨receipt.reference, receipt.source_eq⟩
  · intro available
    cases field with
    | input index => exact ⟨_, rfl⟩
    | constant value => exact ⟨_, rfl⟩
    | gate index =>
        rcases available with ⟨reference, same⟩
        cases reference with
        | input _ => cases same
        | constant _ => cases same
        | output output =>
            obtain ⟨found, foundAt⟩ := findOutput_exists_of_mem current (.gate index)
              output (mem_allFin output) same
            dsimp only [recognize]
            rw [foundAt]
            exact ⟨_, rfl⟩

theorem recognize_isSome_iff (current : Implementation inputs outputs)
    (field : Source inputs current.gateCount) :
    (recognize current field).isSome = true ↔
      ∃ reference : Reference inputs outputs, reference.toSource current = field := by
  constructor
  · intro accepted
    cases found : recognize current field with
    | none =>
        rw [found] at accepted
        cases accepted
    | some receipt => exact ⟨receipt.reference, receipt.source_eq⟩
  · intro available
    obtain ⟨receipt, found⟩ := (recognize_success_iff current field).2 available
    rw [found]
    rfl

theorem recognize_none_iff (current : Implementation inputs outputs)
    (field : Source inputs current.gateCount) :
    recognize current field = none ↔
      ¬ ∃ reference : Reference inputs outputs, reference.toSource current = field := by
  constructor
  · intro refused available
    obtain ⟨receipt, found⟩ := (recognize_success_iff current field).2 available
    rw [refused] at found
    cases found
  · intro unavailable
    cases found : recognize current field with
    | none => rfl
    | some receipt =>
        exact False.elim (unavailable ⟨receipt.reference, receipt.source_eq⟩)

/-- A gate wire is refused exactly when no ordinary output names that wire.
Refusal neither proves a gain nor excludes another semantic encoding. -/
theorem recognize_gate_none_iff (current : Implementation inputs outputs)
    (gate : Fin current.gateCount) :
    recognize current (.gate gate) = none ↔
      ∀ output, current.candidate.directWireWord.source output ≠ .gate gate := by
  rw [recognize_none_iff]
  constructor
  · intro unavailable output same
    exact unavailable ⟨.output output, same⟩
  · intro notOutput
    rintro ⟨reference, same⟩
    cases reference with
    | input _ => cases same
    | constant _ => cases same
    | output output => exact notOutput output same

theorem checkLayout_iff (current : Implementation inputs outputs)
    (fields : Fin added → Source inputs current.gateCount) :
    checkLayout current fields = true ↔
      ∀ field, ∃ reference : Reference inputs outputs,
        reference.toSource current = fields field := by
  constructor
  · intro checked field
    exact (recognize_isSome_iff current (fields field)).1
      (allTrue_sound checked (mem_allFin field))
  · intro available
    exact allTrue_complete (allFin added) _ (fun field _ =>
      (recognize_isSome_iff current (fields field)).2 (available field))

/-- The executable tuple compiler accepts exactly the layouts constructible
from the current input, constant and ordinary-output wire sources. -/
theorem compileLayout_available_iff (current : Implementation inputs outputs)
    (fields : Fin added → Source inputs current.gateCount) :
    (∃ receipt, compileLayout current fields = some receipt) ↔
      ∀ field, ∃ reference : Reference inputs outputs,
        reference.toSource current = fields field :=
  (compileLayout_success_iff current fields).trans (checkLayout_iff current fields)

end PNP.DirectWire.ZeroCostExposure
