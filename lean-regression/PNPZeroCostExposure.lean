import PNP

namespace PNP.DirectWire.ZeroCostExposureRegression

open ZeroCostExposure

-- General contracts, not finite-fixture substitutes.
example {inputs outputs added : Nat} (current : Implementation inputs outputs)
    (layout : Fin added → Reference inputs outputs) :
    referenceMinimum (extend current layout) = referenceMinimum current :=
  referenceMinimum_extend current layout

example {inputs outputs added : Nat} (current : Implementation inputs outputs)
    (layout : Fin added → Reference inputs outputs) :
    residualSlack (extend current layout) = residualSlack current :=
  residualSlack_extend current layout

example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (field : Source inputs current.gateCount) :
    (∃ receipt, recognize current field = some receipt) ↔
      ∃ reference : Reference inputs outputs, reference.toSource current = field :=
  recognize_success_iff current field

example {inputs outputs : Nat} (current : Implementation inputs outputs)
    (gate : Fin current.gateCount) :
    recognize current (.gate gate) = none ↔
      ∀ output, current.candidate.directWireWord.source output ≠ .gate gate :=
  recognize_gate_none_iff current gate

example {inputs outputs added : Nat} (current : Implementation inputs outputs)
    (fields : Fin added → Source inputs current.gateCount) :
    (∃ receipt, compileLayout current fields = some receipt) ↔
      ∀ field, ∃ reference : Reference inputs outputs,
        reference.toSource current = fields field :=
  compileLayout_available_iff current fields

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (checked : checkLayout carrier.implementation carrier.source = true) :
    carrier.exposed.gateCount = carrier.implementation.gateCount ∧
      referenceMinimum carrier.exposed = referenceMinimum carrier.implementation ∧
      residualSlack carrier.exposed = residualSlack carrier.implementation :=
  carrier.checked_exposure_preserves_problem checked

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    checkLayout current (added := 0) Fin.elim0 = true := rfl

private def notProgram : Program 1 1 :=
  .snoc .empty ⟨.input 0, .input 0⟩

private def notOnly : Implementation 1 1 :=
  (Candidate.ofDirectWireWord notProgram ⟨fun _ => .gate ⟨0, by decide⟩⟩).toImplementation

private def identityOnly : Implementation 1 1 :=
  (Candidate.ofDirectWireWord .empty ⟨fun _ => .input 0⟩).toImplementation

/-- The physical NOT gate is hidden from the ordinary output. -/
private def hiddenNot : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord notProgram ⟨fun _ => .input 0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

/-- Two separately allocated gates compute the same NOT; both are exposed. -/
private def separatelyChargedDuplicate : Implementation 1 2 :=
  (Candidate.ofDirectWireWord
    (.snoc notProgram ⟨.input 0, .input 0⟩)
    ⟨fun output => if output.val = 0 then .gate ⟨0, by decide⟩ else .gate ⟨1, by decide⟩⟩).toImplementation

private def duplicateAlias : Fin 1 → Reference 1 1 := fun _ => .output 0

private theorem duplicate_equivalent_alias :
    Equivalent separatelyChargedDuplicate.candidate.program
      separatelyChargedDuplicate.candidate.directWireWord
      (extend notOnly duplicateAlias).candidate.program
      (extend notOnly duplicateAlias).candidate.directWireWord :=
  equivalentBool_sound (by decide)

/-- An extra physical charge does not force any extra semantic minimum. -/
theorem duplicate_minimum_unchanged :
    referenceMinimum separatelyChargedDuplicate = referenceMinimum notOnly :=
  (referenceMinimum_invariant separatelyChargedDuplicate (extend notOnly duplicateAlias)
    duplicate_equivalent_alias).trans (referenceMinimum_extend notOnly duplicateAlias)

example : separatelyChargedDuplicate.gateCount = notOnly.gateCount + 1 := rfl

-- The duplicated producers are distinct physical indices, despite equal values.
example : (⟨0, by decide⟩ : Fin separatelyChargedDuplicate.gateCount) ≠
    ⟨1, by decide⟩ := by decide

private theorem hidden_minimum_zero : referenceMinimum hiddenNot.implementation = 0 := by
  apply Nat.le_zero.mp
  exact referenceMinimum_le_of_equivalent hiddenNot.implementation identityOnly.candidate
    (equivalentBool_sound (by decide))

-- The only exhaustive reductions here have one input and at most one gate.
-- They are kernel-checked counterexamples, never polynomial-time claims.
private theorem not_minimum_one : referenceMinimum notOnly = 1 := by decide +kernel

private theorem exposed_hidden_minimum_one : referenceMinimum hiddenNot.exposed = 1 := by
  decide +kernel

theorem hidden_exposure_changes_minimum_without_new_gates :
    hiddenNot.exposed.gateCount = hiddenNot.implementation.gateCount ∧
      referenceMinimum hiddenNot.implementation = 0 ∧
      referenceMinimum hiddenNot.exposed = 1 :=
  ⟨rfl, hidden_minimum_zero, exposed_hidden_minimum_one⟩

theorem hidden_exposure_destroys_slack :
    residualSlack hiddenNot.implementation = 1 ∧ residualSlack hiddenNot.exposed = 0 := by
  unfold residualSlack
  rw [hidden_minimum_zero, exposed_hidden_minimum_one]
  exact ⟨rfl, rfl⟩

example : referenceMinimum separatelyChargedDuplicate = 1 := by
  rw [duplicate_minimum_unchanged, not_minimum_one]

example : recognize hiddenNot.implementation (.gate ⟨0, by decide⟩) = none := rfl
example : checkLayout hiddenNot.implementation hiddenNot.source = false := by decide
example : compileLayout hiddenNot.implementation hiddenNot.source = none := rfl

/-- Inputs, both constants, an old output and its repetition are all admissible. -/
private def mixedAliases : WireCarrier 1 1 5 :=
  { implementation := notOnly
    source := fun field =>
      match field.val with
      | 0 => .input 0
      | 1 => .constant false
      | 2 => .constant true
      | _ => .gate ⟨0, by decide⟩ }

example : checkLayout mixedAliases.implementation mixedAliases.source = true := by decide
example : (compileLayout mixedAliases.implementation mixedAliases.source).isSome = true := by
  decide

example : referenceMinimum mixedAliases.exposed = referenceMinimum notOnly :=
  mixedAliases.exposed_referenceMinimum_of_checkLayout (by decide)

example : residualSlack mixedAliases.exposed = residualSlack notOnly :=
  mixedAliases.exposed_residualSlack_of_checkLayout (by decide)

/-- No ordinary outputs are required for input/constant aliases. -/
private def fieldsOnly : WireCarrier 1 0 2 :=
  { implementation := (Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩).toImplementation
    source := fun field => if field.val = 0 then .input 0 else .constant true }

private def allEmpty : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

example : checkLayout fieldsOnly.implementation fieldsOnly.source = true := by decide
example : checkLayout allEmpty.implementation allEmpty.source = true := rfl

/-- Semantic redundancy alone does not make a different physical wire an alias.
The source checker deliberately refuses it rather than claiming completeness. -/
private def semanticallyDuplicate : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord
      separatelyChargedDuplicate.candidate.program ⟨fun _ => .gate ⟨0, by decide⟩⟩).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

example : checkLayout semanticallyDuplicate.implementation semanticallyDuplicate.source = false := by
  decide

example (valuation : Valuation 1) :
    semanticallyDuplicate.fieldValue valuation 0 =
      semanticallyDuplicate.implementation.candidate.semantics valuation 0 := rfl

-- Invalid references cannot be formed: a one-gate circuit has no gate 1.
example : ¬ (1 < hiddenNot.implementation.gateCount) := by decide

end PNP.DirectWire.ZeroCostExposureRegression
