import PNP.NANDClosedSupportObservation
import PNP.ResidualTerminalSupportSquareClosure

/-!
Exact computational-field observation under unions of computed closed supports.
The existing support-square closure law supplies the structural union fact.
This derives observations, not positivity, minimum cost, all-role compatibility,
global routing, or a polynomial construction. The original matching table and
profile-dependency computation still use finite exhaustive semantics.
-/

namespace PNP.DirectWire.ClosedSupportUnion

open ClosedSupportObservation

variable {inputs outputs fields : Nat}

theorem records_mono (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (within : ∀ record, record ∈ left → record ∈ right)
    (record : TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)
    (member : record ∈ records target keep left) :
    record ∈ records target keep right := by
  let system := terminalCandidateSaturationSystem target.implementation.candidate
    (WireProfileAmbient.model target keep)
  apply (mem_terminalSaturateRecords_iff system right record).mpr
  exact terminalSaturate_monotone system
    (fun item => item ∈ left) (fun item => item ∈ right) within record
    ((mem_terminalSaturateRecords_iff system left record).mp member)

theorem mem_records_append (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (record : TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields) :
    record ∈ records target keep (left ++ right) ↔
      record ∈ records target keep left ∨ record ∈ records target keep right := by
  let system := terminalCandidateSaturationSystem target.implementation.candidate
    (WireProfileAmbient.model target keep)
  let square := terminalSaturatedSupportSquare system left right
  constructor
  · intro member
    apply (square.mem_joinRecords_iff record).mp
    apply records_mono target keep (left ++ right)
      (records target keep left ++ records target keep right) ?_ record member
    intro item itemMember
    cases List.mem_append.mp itemMember with
    | inl fromLeft =>
        exact List.mem_append_left _
          (terminalSaturateRecords_extensive system left item fromLeft)
    | inr fromRight =>
        exact List.mem_append_right _
          (terminalSaturateRecords_extensive system right item fromRight)
  · intro member
    cases member with
    | inl fromLeft =>
        exact records_mono target keep left (left ++ right)
          (fun _ found => List.mem_append_left right found) record fromLeft
    | inr fromRight =>
        exact records_mono target keep right (left ++ right)
          (fun _ found => List.mem_append_right left found) record fromRight

private theorem bool_eq_of_true_iff (left right : Bool)
    (same : left = true ↔ right = true) : left = right := by
  cases left <;> cases right
  · rfl
  · have impossible := same.mpr rfl
    cases impossible
  · have impossible := same.mp rfl
    cases impossible
  · rfl

theorem retained_append (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (source : Source inputs target.implementation.gateCount) :
    retained target keep (left ++ right) source =
      (retained target keep left source || retained target keep right source) := by
  cases source with
  | constant _ => rfl
  | input _ => rfl
  | gate gate =>
      change terminalGateSelected (records target keep (left ++ right)) gate =
        (terminalGateSelected (records target keep left) gate ||
          terminalGateSelected (records target keep right) gate)
      apply bool_eq_of_true_iff
      rw [Bool.or_eq_true, terminalGateSelected_eq_true_iff,
        terminalGateSelected_eq_true_iff, terminalGateSelected_eq_true_iff]
      exact mem_records_append target keep left right (.gate gate)

theorem tableAvailable_append (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) :
    tableAvailable target keep (left ++ right) field =
      (tableAvailable target keep left field || tableAvailable target keep right field) := by
  apply bool_eq_of_true_iff
  rw [Bool.or_eq_true, tableAvailable_iff, tableAvailable_iff, tableAvailable_iff]
  constructor
  · rintro ⟨source, matched, present⟩
    rw [retained_append, Bool.or_eq_true] at present
    cases present with
    | inl fromLeft => exact Or.inl ⟨source, matched, fromLeft⟩
    | inr fromRight => exact Or.inr ⟨source, matched, fromRight⟩
  · intro present
    cases present with
    | inl fromLeft =>
        obtain ⟨source, matched, present⟩ := fromLeft
        refine ⟨source, matched, ?_⟩
        rw [retained_append, Bool.or_eq_true]
        exact Or.inl present
    | inr fromRight =>
        obtain ⟨source, matched, present⟩ := fromRight
        refine ⟨source, matched, ?_⟩
        rw [retained_append, Bool.or_eq_true]
        exact Or.inr present

theorem available_append (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
        (implementation target keep (left ++ right)) field =
      (WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
          (implementation target keep left) field ||
        WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
          (implementation target keep right) field) := by
  rw [available_eq_tableAvailable, available_eq_tableAvailable, available_eq_tableAvailable]
  exact tableAvailable_append target keep left right field

theorem available_flatten (target : WireCarrier inputs outputs fields)
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
          (implementation target keep []) field) := by
  induction family with
  | nil => rfl
  | cons seed family ih =>
      change WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
          (implementation target keep (seed ++ family.flatten)) field =
        (WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
            (implementation target keep seed) field ||
          family.foldr (fun part remaining =>
            WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
              (implementation target keep part) field || remaining)
            (WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
              (implementation target keep []) field))
      rw [available_append, ih]

theorem available_mono (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (within : ∀ record, record ∈ left → record ∈ right)
    (field : Fin fields)
    (present : WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (implementation target keep left) field = true) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (implementation target keep right) field = true := by
  obtain ⟨source, matched, selected⟩ :=
    (available_iff_retained_source target keep left field).mp present
  apply available_of_retained_source target keep right field source matched
  cases source with
  | constant _ => rfl
  | input _ => rfl
  | gate gate =>
      apply (terminalGateSelected_eq_true_iff _ gate).mpr
      exact records_mono target keep left right within (.gate gate)
        ((terminalGateSelected_eq_true_iff _ gate).mp selected)

end PNP.DirectWire.ClosedSupportUnion
