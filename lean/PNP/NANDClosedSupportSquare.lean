import PNP.NANDClosedSupportProfile
import PNP.ResidualTerminalSupportSquareClosure

/-!
Compute a support square from two seeds and the requested computational
profile fields. Every corner preserves those actual field values. The square,
its records, physical supports, observer and field bindings are all derived.

This is not the full manuscript profile frontier or a proof of ordinary-output
equivalence, positivity, properness, optimality, forced-cost transparency,
global routing, unconditional ZeroSlack, or polynomial construction.
-/

namespace PNP.DirectWire.ClosedSupportSquare

open ClosedSupportObservation ClosedSupportProfile

variable {inputs outputs fields : Nat}

def square (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)) :
    TerminalSaturatedSupportSquare
      (terminalCandidateSaturationSystem target.implementation.candidate
        (WireProfileAmbient.model target keep)) :=
  terminalSaturatedSupportSquare
    (terminalCandidateSaturationSystem target.implementation.candidate
      (WireProfileAmbient.model target keep))
    (left ++ keptFieldSeed target keep) (right ++ keptFieldSeed target keep)

def cornerImplementation (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (corner : TerminalSupportSquareCorner) :
    Implementation (inputs + target.implementation.gateCount) target.implementation.gateCount :=
  terminalAmbientSupportImplementation target.implementation.candidate
    ((square target keep left right).records corner)

theorem corner_profileMember (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (corner : TerminalSupportSquareCorner) (field : Fin fields) (kept : keep field = true) :
    TerminalPrimitiveRecord.profile field ∈ (square target keep left right).records corner := by
  have seeded (seed : List
      (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)) :
      TerminalPrimitiveRecord.profile field ∈
        records target keep (seed ++ keptFieldSeed target keep) := by
    apply terminalSaturateRecords_extensive
      (terminalCandidateSaturationSystem target.implementation.candidate
        (WireProfileAmbient.model target keep))
      (seed ++ keptFieldSeed target keep) (.profile field)
    apply List.mem_append_right
    exact List.mem_map.mpr
      ⟨field, List.mem_filter.mpr ⟨mem_allFin field, kept⟩, rfl⟩
  cases corner with
  | left => exact seeded left
  | right => exact seeded right
  | meet =>
      exact ((square target keep left right).mem_meetRecords_iff _).mpr
        ⟨seeded left, seeded right⟩
  | join =>
      exact ((square target keep left right).mem_joinRecords_iff _).mpr
        (Or.inl (seeded left))

private theorem resaturate_eq (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (closed : TerminalRawSupport.Closed (fun record => record ∈ seed)
      (terminalCandidateSaturationSystem target.implementation.candidate
        (WireProfileAmbient.model target keep))) :
    implementation target keep seed =
      terminalAmbientSupportImplementation target.implementation.candidate seed := by
  let system := terminalCandidateSaturationSystem target.implementation.candidate
    (WireProfileAmbient.model target keep)
  have members (record : TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields) :
      record ∈ records target keep seed ↔ record ∈ seed := by
    constructor
    · intro member
      exact terminalSaturate_least system (fun item => item ∈ seed)
        (fun item => item ∈ seed) (fun _ found => found) closed record
        ((mem_terminalSaturateRecords_iff system seed record).mp member)
    · exact terminalSaturateRecords_extensive system seed record
  apply terminalAmbientSupportImplementation_eq_of_gateSelected_eq
    target.implementation.candidate (records target keep seed) seed
  funext gate
  simp only [terminalGateSelected, members]

theorem corner_available (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (corner : TerminalSupportSquareCorner) (field : Fin fields) (kept : keep field = true) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (cornerImplementation target keep left right corner) field = true := by
  let support := (square target keep left right).records corner
  have member : TerminalPrimitiveRecord.profile field ∈ records target keep support :=
    terminalSaturateRecords_extensive
      (terminalCandidateSaturationSystem target.implementation.candidate
        (WireProfileAmbient.model target keep)) support (.profile field)
      (corner_profileMember target keep left right corner field kept)
  have present := profile_available target keep support field member
  rw [resaturate_eq target keep support
    ((square target keep left right).records_closed corner)] at present
  exact present

theorem corner_fieldValue (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (corner : TerminalSupportSquareCorner) (field : Fin fields) (kept : keep field = true)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (WireProfileAvailability.bind (WireProfileAmbient.ambientTarget target)
        (cornerImplementation target keep left right corner)).fieldValue valuation field =
      target.fieldValue
        (fun index => valuation (Fin.castAdd target.implementation.gateCount index)) field :=
  (WireProfileAvailability.bind_fieldValue (WireProfileAmbient.ambientTarget target)
    (cornerImplementation target keep left right corner) field
      (corner_available target keep left right corner field kept) valuation).trans
    (WireProfileFieldClosed.ambient_fieldValue target valuation field)

theorem corners_fieldValue_equal (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (left right : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (first second : TerminalSupportSquareCorner)
    (field : Fin fields) (kept : keep field = true)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (WireProfileAvailability.bind (WireProfileAmbient.ambientTarget target)
        (cornerImplementation target keep left right first)).fieldValue valuation field =
      (WireProfileAvailability.bind (WireProfileAmbient.ambientTarget target)
        (cornerImplementation target keep left right second)).fieldValue valuation field :=
  (corner_fieldValue target keep left right first field kept valuation).trans
    (corner_fieldValue target keep left right second field kept valuation).symm

end PNP.DirectWire.ClosedSupportSquare
