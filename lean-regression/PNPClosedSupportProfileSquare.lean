import PNP

/- General type contracts, kernel guards and runtime checks retained from the
   individually checked research fixtures. One root import covers the bundle. -/

namespace PNP.DirectWire.ClosedSupportObservationRegression

open ClosedSupportObservation

/- The contracts use arbitrary dimensions and ordinary seed data, not a
   supplied observer, source-closure certificate or field-preservation premise. -/
example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
        (implementation target keep seed) field = true ↔
      ∃ source, source ∈ matchingSources target field ∧
        retained target keep seed source = true :=
  available_iff_retained_source target keep seed field

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (implementation target keep seed) field = tableAvailable target keep seed field :=
  available_eq_tableAvailable target keep seed field

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (gate : Fin target.implementation.gateCount)
    (selected : terminalGateSelected (records target keep seed) gate = true)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (implementation target keep seed).candidate.program.eval valuation
        (terminalExtractionGateIndex target.implementation.candidate
          (records target keep seed) gate selected) =
      target.implementation.candidate.program.eval
        (fun index => valuation (Fin.castAdd target.implementation.gateCount index)) gate :=
  gate_value target keep seed gate selected valuation

private def notProgram : Program 1 1 :=
  .snoc .empty ⟨.input 0, .input 0⟩

private def hiddenNot : WireCarrier 1 0 1 :=
  { implementation := (Candidate.ofDirectWireWord notProgram ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def doubleNot : WireCarrier 1 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.snoc notProgram ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩)
        ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

private def nandProgram : Program 2 1 :=
  .snoc .empty ⟨.input 0, .input 1⟩

private def andProgram : Program 2 2 :=
  .snoc nandProgram ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩

private def bufferedNand : WireCarrier 2 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.snoc andProgram ⟨.gate ⟨1, by decide⟩, .gate ⟨1, by decide⟩⟩)
        ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨2, by decide⟩ }

private def andTarget : WireCarrier 2 0 1 :=
  { implementation := (Candidate.ofDirectWireWord andProgram ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

private def rawAndRecords : List (TerminalPrimitiveRecord 2 2 0 1) := [.gate ⟨1, by decide⟩]

private def rawAndImplementation : Implementation 4 2 :=
  terminalAmbientSupportImplementation andTarget.implementation.candidate rawAndRecords

private def rawAndTable : Bool :=
  (matchingSources andTarget 0).any fun source =>
    match source with
    | .constant _ => true
    | .input _ => true
    | .gate gate => terminalGateSelected rawAndRecords gate

private def constantTarget : WireCarrier 0 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .constant true }

private def emptyTarget : WireCarrier 0 0 0 :=
  { implementation := constantTarget.implementation
    source := Fin.elim0 }

theorem empty_support_does_not_invent_field :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget hiddenNot)
      (implementation hiddenNot (fun _ => false) []) 0 = false := by decide +kernel

theorem input_equivalent_field_needs_no_original_gate :
    tableAvailable doubleNot (fun _ => true) [] 0 = true ∧
      (implementation doubleNot (fun _ => true) []).gateCount = 0 := by decide +kernel

theorem unclosed_support_is_not_covered_by_table_theorem :
    rawAndTable = true ∧
      WireProfileAvailability.available (WireProfileAmbient.ambientTarget andTarget)
        rawAndImplementation 0 = false := by decide +kernel

theorem empty_dimensions :
    (implementation emptyTarget Fin.elim0 []).gateCount = 0 := by decide +kernel

private def checks : List (String × Bool) :=
  [ ("empty support rejects nontrivial field",
      !(tableAvailable hiddenNot (fun _ => false) [] 0) &&
        !(WireProfileAvailability.available (WireProfileAmbient.ambientTarget hiddenNot)
          (implementation hiddenNot (fun _ => false) []) 0))
  , ("gate seed derives a genuine field source",
      tableAvailable hiddenNot (fun _ => true) [.gate ⟨0, by decide⟩] 0 &&
        WireProfileAvailability.available (WireProfileAmbient.ambientTarget hiddenNot)
          (implementation hiddenNot (fun _ => true) [.gate ⟨0, by decide⟩]) 0)
  , ("a profile seed derives rather than assumes a matching gate",
      tableAvailable hiddenNot (fun _ => true) [.profile 0] 0 &&
        terminalGateSelected (records hiddenNot (fun _ => true) [.profile 0]) ⟨0, by decide⟩)
  , ("input-equivalent gate field survives with no selected gate",
      tableAvailable doubleNot (fun _ => true) [] 0 &&
        decide ((implementation doubleNot (fun _ => true) []).gateCount = 0))
  , ("semantically equal original gate supplies the field without its literal final gate",
      tableAvailable bufferedNand (fun _ => true) [.gate ⟨0, by decide⟩] 0 &&
        terminalGateSelected (records bufferedNand (fun _ => true) [.gate ⟨0, by decide⟩]) ⟨0, by decide⟩ &&
        !(terminalGateSelected (records bufferedNand (fun _ => true) [.gate ⟨0, by decide⟩]) ⟨2, by decide⟩) &&
        WireProfileAvailability.available (WireProfileAmbient.ambientTarget bufferedNand)
          (implementation bufferedNand (fun _ => true) [.gate ⟨0, by decide⟩]) 0)
  , ("raw unclosed gate table would falsely accept",
      rawAndTable &&
        !(WireProfileAvailability.available (WireProfileAmbient.ambientTarget andTarget)
          rawAndImplementation 0))
  , ("computed closure repairs the raw missing predecessor",
      terminalGateSelected (records andTarget (fun _ => true) [.gate ⟨1, by decide⟩]) ⟨0, by decide⟩ &&
        tableAvailable andTarget (fun _ => true) [.gate ⟨1, by decide⟩] 0 &&
        WireProfileAvailability.available (WireProfileAmbient.ambientTarget andTarget)
          (implementation andTarget (fun _ => true) [.gate ⟨1, by decide⟩]) 0)
  , ("zero-input constant needs no physical gate",
      tableAvailable constantTarget (fun _ => true) [] 0 &&
        decide ((implementation constantTarget (fun _ => true) []).gateCount = 0))
  , ("empty dimensions", decide ((implementation emptyTarget Fin.elim0 []).gateCount = 0))
  , ("forgetting is not silently treated as field preservation",
      !(tableAvailable hiddenNot (fun _ => false) [] 0) &&
        tableAvailable hiddenNot (fun _ => false) [.gate ⟨0, by decide⟩] 0)
  ]

def run : IO Unit := do
  for (name, passed) in checks do
    if passed then
      IO.println ("closed-observation-check-passed: " ++ name)
    else
      throw (IO.userError ("closed-observation-check-failed: " ++ name))
  IO.println "closed-observation-regressions-complete: 10 runtime checks; 3 general type contracts; 4 kernel guards"

end PNP.DirectWire.ClosedSupportObservationRegression

#print axioms PNP.DirectWire.ClosedSupportObservationRegression.empty_support_does_not_invent_field
#print axioms PNP.DirectWire.ClosedSupportObservationRegression.input_equivalent_field_needs_no_original_gate
#print axioms PNP.DirectWire.ClosedSupportObservationRegression.unclosed_support_is_not_covered_by_table_theorem
#print axioms PNP.DirectWire.ClosedSupportObservationRegression.empty_dimensions

namespace PNP.DirectWire.ClosedSupportUnionRegression

open ClosedSupportObservation ClosedSupportUnion

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
        (implementation target keep (left ++ right)) field =
      (WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
          (implementation target keep left) field ||
        WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
          (implementation target keep right) field) :=
  available_append target keep left right field

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (family : List (List
      (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)))
    (field : Fin fields) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
        (implementation target keep family.flatten) field =
      family.foldr (fun seed remaining =>
        WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
          (implementation target keep seed) field || remaining)
        (WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
          (implementation target keep []) field) :=
  available_flatten target keep family field

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (within : ∀ record, record ∈ left → record ∈ right)
    (field : Fin fields)
    (present : WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (implementation target keep left) field = true) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (implementation target keep right) field = true :=
  available_mono target keep left right within field present

private def first : Fin 2 := ⟨0, by decide⟩
private def second : Fin 2 := ⟨1, by decide⟩

private def andProgram : Program 2 2 :=
  .snoc (.snoc .empty ⟨.input 0, .input 1⟩)
    ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩

private def andTarget : WireCarrier 2 0 1 :=
  { implementation := (Candidate.ofDirectWireWord andProgram ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate second }

private def rawObserved (seed : List (TerminalPrimitiveRecord 2 2 0 1)) : Bool :=
  WireProfileAvailability.available (WireProfileAmbient.ambientTarget andTarget)
    (terminalAmbientSupportImplementation andTarget.implementation.candidate seed) 0

theorem raw_union_is_not_the_union_of_raw_observations :
    rawObserved [.gate first, .gate second] = true ∧
      rawObserved [.gate first] = false ∧
      rawObserved [.gate second] = false := by decide +kernel

theorem computed_right_side_already_contains_the_required_predecessor :
    terminalGateSelected (records andTarget (fun _ => true) [.gate second]) first = true ∧
      WireProfileAvailability.available (WireProfileAmbient.ambientTarget andTarget)
        (implementation andTarget (fun _ => true) [.gate second]) 0 = true := by decide +kernel

private def constantTarget : WireCarrier 0 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .constant true }

theorem an_empty_family_can_still_observe_a_constant :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget constantTarget)
      (implementation constantTarget (fun _ => true) ([] :
        List (List (TerminalPrimitiveRecord 0 0 0 1))).flatten) 0 = true := by decide +kernel

theorem a_finite_family_with_empty_and_repeated_seeds_keeps_its_field :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget andTarget)
      (implementation andTarget (fun _ => true)
        ([[], [.gate second], [.gate first], [.gate second]] :
          List (List (TerminalPrimitiveRecord 2 2 0 1))).flatten) 0 = true := by decide +kernel

end PNP.DirectWire.ClosedSupportUnionRegression

#print axioms PNP.DirectWire.ClosedSupportUnionRegression.raw_union_is_not_the_union_of_raw_observations
#print axioms PNP.DirectWire.ClosedSupportUnionRegression.computed_right_side_already_contains_the_required_predecessor
#print axioms PNP.DirectWire.ClosedSupportUnionRegression.an_empty_family_can_still_observe_a_constant
#print axioms PNP.DirectWire.ClosedSupportUnionRegression.a_finite_family_with_empty_and_repeated_seeds_keeps_its_field

namespace PNP.DirectWire.ClosedSupportProfileRegression

open ClosedSupportObservation ClosedSupportProfile

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields)
    (profileMember : TerminalPrimitiveRecord.profile field ∈ records target keep seed) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (implementation target keep seed) field = true :=
  profile_available target keep seed field profileMember

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) (kept : keep field = true) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (projectedImplementation target keep seed) field = true :=
  projected_available target keep seed field kept

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) (kept : keep field = true) :
    tableAvailable target keep (seed ++ keptFieldSeed target keep) field = true :=
  projected_tableAvailable target keep seed field kept

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) (kept : keep field = true)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (WireProfileAvailability.bind (WireProfileAmbient.ambientTarget target)
        (projectedImplementation target keep seed)).fieldValue valuation field =
      target.fieldValue
        (fun index => valuation (Fin.castAdd target.implementation.gateCount index)) field :=
  projected_fieldValue target keep seed field kept valuation

private def nandProgram : Program 2 1 :=
  .snoc .empty ⟨.input 0, .input 1⟩

private def andProgram : Program 2 2 :=
  .snoc nandProgram ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩

private def bufferedNand : WireCarrier 2 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (.snoc andProgram ⟨.gate ⟨1, by decide⟩, .gate ⟨1, by decide⟩⟩)
        ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨2, by decide⟩ }

theorem requested_field_does_not_force_its_literal_buffer_gates :
    (projectedImplementation bufferedNand (fun _ => true) []).gateCount = 1 ∧
      terminalGateSelected
        (records bufferedNand (fun _ => true) (keptFieldSeed bufferedNand (fun _ => true)))
        ⟨2, by decide⟩ = false := by decide +kernel

private def notProgram : Program 1 1 :=
  .snoc .empty ⟨.input 0, .input 0⟩

private def hiddenNot : WireCarrier 1 0 1 :=
  { implementation := (Candidate.ofDirectWireWord notProgram ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

theorem a_forgotten_field_is_not_claimed_preserved :
    (projectedImplementation hiddenNot (fun _ => false) []).gateCount = 0 ∧
      WireProfileAvailability.available (WireProfileAmbient.ambientTarget hiddenNot)
        (projectedImplementation hiddenNot (fun _ => false) []) 0 = false := by decide +kernel

private def constantTarget : WireCarrier 0 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .constant true }

theorem a_requested_constant_has_no_physical_gate :
    (projectedImplementation constantTarget (fun _ => true) []).gateCount = 0 ∧
      WireProfileAvailability.available (WireProfileAmbient.ambientTarget constantTarget)
        (projectedImplementation constantTarget (fun _ => true) []) 0 = true := by decide +kernel

private def doubleNot : WireCarrier 1 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (.snoc notProgram ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩)
        ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

theorem a_requested_input_equivalent_field_has_no_physical_gate :
    (projectedImplementation doubleNot (fun _ => true) []).gateCount = 0 ∧
      WireProfileAvailability.available (WireProfileAmbient.ambientTarget doubleNot)
        (projectedImplementation doubleNot (fun _ => true) []) 0 = true := by decide +kernel

private def emptyTarget : WireCarrier 0 0 0 :=
  { implementation := constantTarget.implementation
    source := Fin.elim0 }

theorem empty_dimensions_need_no_seed_or_gate :
    keptFieldSeed emptyTarget Fin.elim0 = [] ∧
      (projectedImplementation emptyTarget Fin.elim0 []).gateCount = 0 := by decide +kernel

private def outputNot : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord notProgram ⟨fun _ => .gate ⟨0, by decide⟩⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

theorem field_preservation_is_not_ordinary_output_equivalence :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget outputNot)
        (projectedImplementation outputNot (fun _ => true) []) 0 = true ∧
      (projectedImplementation outputNot (fun _ => true) []).candidate.semantics
          (fun _ => false) ⟨0, by decide⟩ ≠
        (WireProfileAmbient.ambientTarget outputNot).implementation.candidate.semantics
          (fun _ => false) ⟨0, by decide⟩ := by decide +kernel

end PNP.DirectWire.ClosedSupportProfileRegression

#print axioms PNP.DirectWire.ClosedSupportProfileRegression.requested_field_does_not_force_its_literal_buffer_gates
#print axioms PNP.DirectWire.ClosedSupportProfileRegression.a_forgotten_field_is_not_claimed_preserved
#print axioms PNP.DirectWire.ClosedSupportProfileRegression.a_requested_constant_has_no_physical_gate
#print axioms PNP.DirectWire.ClosedSupportProfileRegression.a_requested_input_equivalent_field_has_no_physical_gate
#print axioms PNP.DirectWire.ClosedSupportProfileRegression.empty_dimensions_need_no_seed_or_gate
#print axioms PNP.DirectWire.ClosedSupportProfileRegression.field_preservation_is_not_ordinary_output_equivalence

namespace PNP.DirectWire.ClosedSupportSquareRegression

open ClosedSupportSquare

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (corner : TerminalSupportSquareCorner) (field : Fin fields) (kept : keep field = true) :
    TerminalPrimitiveRecord.profile field ∈ (square target keep left right).records corner :=
  corner_profileMember target keep left right corner field kept

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (corner : TerminalSupportSquareCorner) (field : Fin fields) (kept : keep field = true) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (cornerImplementation target keep left right corner) field = true :=
  corner_available target keep left right corner field kept

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (corner : TerminalSupportSquareCorner) (field : Fin fields) (kept : keep field = true)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (WireProfileAvailability.bind (WireProfileAmbient.ambientTarget target)
        (cornerImplementation target keep left right corner)).fieldValue valuation field =
      target.fieldValue
        (fun index => valuation (Fin.castAdd target.implementation.gateCount index)) field :=
  corner_fieldValue target keep left right corner field kept valuation

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (first second : TerminalSupportSquareCorner)
    (field : Fin fields) (kept : keep field = true)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (WireProfileAvailability.bind (WireProfileAmbient.ambientTarget target)
        (cornerImplementation target keep left right first)).fieldValue valuation field =
      (WireProfileAvailability.bind (WireProfileAmbient.ambientTarget target)
        (cornerImplementation target keep left right second)).fieldValue valuation field :=
  corners_fieldValue_equal target keep left right first second field kept valuation

private def nandProgram : Program 2 1 :=
  .snoc .empty ⟨.input 0, .input 1⟩

private def bufferedNand : WireCarrier 2 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (.snoc (.snoc nandProgram
          ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩)
          ⟨.gate ⟨1, by decide⟩, .gate ⟨1, by decide⟩⟩)
        ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨2, by decide⟩ }

private def bufferedCorner (corner : TerminalSupportSquareCorner) :=
  cornerImplementation bufferedNand (fun _ => true) [] [.gate ⟨2, by decide⟩] corner

theorem compatible_corners_can_have_different_physical_sizes :
    (bufferedCorner .meet).gateCount = 1 ∧
      (bufferedCorner .left).gateCount = 1 ∧
      (bufferedCorner .right).gateCount = 3 ∧
      (bufferedCorner .join).gateCount = 3 := by decide +kernel

private def singleNand : WireCarrier 2 0 1 :=
  { implementation := (Candidate.ofDirectWireWord nandProgram ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

theorem a_requested_field_can_force_the_entire_physical_support :
    (cornerImplementation singleNand (fun _ => true) [] [] .meet).gateCount =
      singleNand.implementation.gateCount ∧
      0 < (cornerImplementation singleNand (fun _ => true) [] [] .meet).gateCount := by
  decide +kernel

private def hiddenNot : WireCarrier 1 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (.snoc .empty ⟨.input 0, .input 0⟩ : Program 1 1) ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

theorem forgotten_fields_need_not_agree_between_corners :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget hiddenNot)
        (cornerImplementation hiddenNot (fun _ => false)
          [.gate ⟨0, by decide⟩] [] .left) 0 = true ∧
      WireProfileAvailability.available (WireProfileAmbient.ambientTarget hiddenNot)
        (cornerImplementation hiddenNot (fun _ => false)
          [.gate ⟨0, by decide⟩] [] .meet) 0 = false := by decide +kernel

private def constantTarget : WireCarrier 0 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .constant true }

theorem constants_agree_at_every_zero_gate_corner (corner : TerminalSupportSquareCorner) :
    (cornerImplementation constantTarget (fun _ => true) [] [] corner).gateCount = 0 ∧
      WireProfileAvailability.available (WireProfileAmbient.ambientTarget constantTarget)
        (cornerImplementation constantTarget (fun _ => true) [] [] corner) 0 = true := by
  cases corner <;> decide +kernel

private def emptyTarget : WireCarrier 0 0 0 :=
  { implementation := constantTarget.implementation
    source := Fin.elim0 }

theorem empty_dimensions_have_no_physical_gate (corner : TerminalSupportSquareCorner) :
    (cornerImplementation emptyTarget Fin.elim0 [] [] corner).gateCount = 0 := by
  cases corner <;> decide +kernel

end PNP.DirectWire.ClosedSupportSquareRegression

#print axioms PNP.DirectWire.ClosedSupportSquareRegression.compatible_corners_can_have_different_physical_sizes
#print axioms PNP.DirectWire.ClosedSupportSquareRegression.a_requested_field_can_force_the_entire_physical_support
#print axioms PNP.DirectWire.ClosedSupportSquareRegression.forgotten_fields_need_not_agree_between_corners
#print axioms PNP.DirectWire.ClosedSupportSquareRegression.constants_agree_at_every_zero_gate_corner
#print axioms PNP.DirectWire.ClosedSupportSquareRegression.empty_dimensions_have_no_physical_gate

/-!
Candidate-level obstruction for the actual computed wire-profile model:
a positive full-profile slack does not guarantee any proper saturated support.
This is a guard against widening the new preservation theorem. It is not a
counterexample to a manuscript theorem with additional terminal/admissibility
hypotheses, and it does not rule out whole-circuit gains or other routes.
-/

namespace PNP.DirectWire.ClosedSupportPositiveObstruction

private def first : Fin 2 := ⟨0, by decide⟩
private def second : Fin 2 := ⟨1, by decide⟩

private def singleProgram : Program 2 1 :=
  .snoc .empty ⟨.input 0, .input 1⟩

private def duplicated : WireCarrier 2 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (.snoc singleProgram ⟨.input 0, .input 1⟩)
        ⟨fun _ => .gate first⟩).toImplementation
    source := fun _ => .gate second }

private def smaller : WireCarrier 2 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord singleProgram
        ⟨fun _ => .gate ⟨0, by decide⟩⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def system : TerminalSaturationSystem 2 2 1 1 :=
  terminalCandidateSaturationSystem duplicated.implementation.candidate
    (WireProfileAmbient.model duplicated (fun _ => true))

private theorem smaller_full_equivalent : WireProfile.FullEquivalent duplicated smaller := by
  apply (WireProfile.full_iff duplicated smaller).mpr
  constructor
  · intro valuation output
    have outputZero : output = (⟨0, by decide⟩ : Fin 1) := Fin.ext (by omega)
    subst output
    rfl
  · intro valuation field
    rfl

theorem positive_full_slack : 0 < WireProfile.fullSlack duplicated := by
  have upper : WireProfile.fullMinimum duplicated ≤ 1 :=
    referenceMinimum_le_of_equivalent duplicated.exposed smaller.exposed.candidate
      smaller_full_equivalent
  change 0 < 2 - WireProfile.fullMinimum duplicated
  omega

private theorem first_to_profile :
    system.requires .gateSource (.gate first) (.profile 0) = true := by decide +kernel

private theorem second_to_profile :
    system.requires .gateSource (.gate second) (.profile 0) = true := by decide +kernel

private theorem profile_to_first :
    system.requires .gateSource (.profile 0) (.gate first) = true := by decide +kernel

private theorem profile_to_second :
    system.requires .gateSource (.profile 0) (.gate second) = true := by decide +kernel

private theorem gate_membership_iff
    (seed : List (TerminalPrimitiveRecord 2 2 1 1)) :
    TerminalPrimitiveRecord.gate first ∈ terminalSaturateRecords system seed ↔
      TerminalPrimitiveRecord.gate second ∈ terminalSaturateRecords system seed := by
  constructor
  · intro member
    exact terminalSaturateRecords_closed system seed .gateSource (.profile 0) (.gate second)
      (terminalSaturateRecords_closed system seed .gateSource (.gate first) (.profile 0)
        member first_to_profile) profile_to_second
  · intro member
    exact terminalSaturateRecords_closed system seed .gateSource (.profile 0) (.gate first)
      (terminalSaturateRecords_closed system seed .gateSource (.gate second) (.profile 0)
        member second_to_profile) profile_to_first

private theorem bool_eq_of_true_iff (left right : Bool)
    (same : left = true ↔ right = true) : left = right := by
  cases left <;> cases right
  · rfl
  · have impossible := same.mpr rfl
    cases impossible
  · have impossible := same.mp rfl
    cases impossible
  · rfl

private theorem selected_equal
    (seed : List (TerminalPrimitiveRecord 2 2 1 1)) :
    terminalGateSelected (terminalSaturateRecords system seed) first =
      terminalGateSelected (terminalSaturateRecords system seed) second := by
  apply bool_eq_of_true_iff
  exact (terminalGateSelected_eq_true_iff _ first).trans
    ((gate_membership_iff seed).trans
      (terminalGateSelected_eq_true_iff _ second).symm)

private theorem gateCount_cases
    (seed : List (TerminalPrimitiveRecord 2 2 1 1)) :
    (extractSaturatedTerminalSupport duplicated.implementation.candidate system seed).gateCount = 0 ∨
      (extractSaturatedTerminalSupport duplicated.implementation.candidate system seed).gateCount = 2 := by
  rw [extractSaturatedTerminalSupport_gateCount]
  let selected := terminalGateSelected (terminalSaturateRecords system seed)
  have equal : selected first = selected second := selected_equal seed
  cases firstValue : selected first with
  | false =>
      have secondValue : selected second = false := equal.symm.trans firstValue
      have allFalse : selected = fun _ => false :=
        funext (Fin.cases firstValue (Fin.cases secondValue (fun index => Fin.elim0 index)))
      apply Or.inl
      change (terminalSelectedGateIndices selected).length = 0
      rw [allFalse]
      rfl
  | true =>
      have secondValue : selected second = true := equal.symm.trans firstValue
      have allTrue : selected = fun _ => true :=
        funext (Fin.cases firstValue (Fin.cases secondValue (fun index => Fin.elim0 index)))
      apply Or.inr
      change (terminalSelectedGateIndices selected).length = 2
      rw [allTrue]
      rfl

theorem no_proper_seed (seed : List (TerminalPrimitiveRecord 2 2 1 1)) :
    ¬ TerminalSupportProper duplicated.implementation.candidate system seed := by
  intro proper
  change 0 <
      (extractSaturatedTerminalSupport duplicated.implementation.candidate system seed).gateCount ∧
    (extractSaturatedTerminalSupport duplicated.implementation.candidate system seed).gateCount < 2
    at proper
  rcases gateCount_cases seed with empty | full
  · rw [empty] at proper
    omega
  · rw [full] at proper
    omega

theorem no_proper_positive_seed :
    ¬ ∃ seed : List (TerminalPrimitiveRecord 2 2 1 1),
      TerminalSupportProper duplicated.implementation.candidate system seed ∧
        TerminalSupportPositive duplicated.implementation.candidate system seed := by
  rintro ⟨seed, proper, _positive⟩
  exact no_proper_seed seed proper

/-- The candidate is rejected before a three-pass-normalized terminal state:
the existing sharing pass already removes its syntactic duplicate. -/
theorem sharing_saves_one :
    physicalNormalizationPassSavings .sharing duplicated.exposed = 1 := by decide +kernel

theorem not_normalization_quiescent :
    ¬ PhysicalNormalizationQuiescent duplicated.exposed := by
  intro quiet
  have zero := quiet .sharing
  rw [sharing_saves_one] at zero
  cases zero

theorem normalized_gateCount :
    duplicated.normalize.implementation.gateCount = 1 := by decide +kernel

end PNP.DirectWire.ClosedSupportPositiveObstruction

#print axioms PNP.DirectWire.ClosedSupportPositiveObstruction.positive_full_slack
#print axioms PNP.DirectWire.ClosedSupportPositiveObstruction.no_proper_seed
#print axioms PNP.DirectWire.ClosedSupportPositiveObstruction.no_proper_positive_seed

#print axioms PNP.DirectWire.ClosedSupportPositiveObstruction.sharing_saves_one
#print axioms PNP.DirectWire.ClosedSupportPositiveObstruction.not_normalization_quiescent
#print axioms PNP.DirectWire.ClosedSupportPositiveObstruction.normalized_gateCount

def main : IO Unit := do
  PNP.DirectWire.ClosedSupportObservationRegression.run
  IO.println "closed-support-profile-square-regressions-complete: 14 general type contracts; 25 kernel guards; 10 runtime checks"
