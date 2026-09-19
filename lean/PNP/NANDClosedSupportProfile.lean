import PNP.NANDClosedSupportObservation
import PNP.ResidualTerminalProfileLocality

/-!
Concrete computational-field preservation from profile-record seeds. The
existing exact influence-locality theorem is reused with the computed
wire-profile observer. No literal field gate is injected into the seed.

This does not supply the other manuscript profile roles, guarantee a proper
or minimum support, establish ordinary-output equivalence, prove positivity,
or give polynomial construction bounds. Semantic matching and influence are
still finite exhaustive reference computations.
-/

namespace PNP.DirectWire.ClosedSupportProfile

open ClosedSupportObservation

variable {inputs outputs fields : Nat}

private theorem full_records_selected (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (gate : Fin target.implementation.gateCount) :
    terminalGateSelected (records target keep
      (allTerminalPrimitiveRecords inputs target.implementation.gateCount outputs fields))
      gate = true := by
  apply (terminalGateSelected_eq_true_iff _ gate).mpr
  exact terminalSaturateRecords_extensive
    (terminalCandidateSaturationSystem target.implementation.candidate
      (WireProfileAmbient.model target keep))
    (allTerminalPrimitiveRecords inputs target.implementation.gateCount outputs fields)
    (.gate gate) (mem_allTerminalPrimitiveRecords (.gate gate))

private theorem full_ambient_available (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (terminalAmbientSupportImplementation target.implementation.candidate
        (allTerminalPrimitiveRecords inputs target.implementation.gateCount outputs fields))
      field = true := by
  let full := allTerminalPrimitiveRecords inputs target.implementation.gateCount outputs fields
  have selectedEqual : terminalGateSelected full =
      terminalGateSelected (records target keep full) := by
    funext gate
    exact ((terminalGateSelected_eq_true_iff full gate).mpr
      (mem_allTerminalPrimitiveRecords (.gate gate))).trans
        (full_records_selected target keep gate).symm
  rw [terminalAmbientSupportImplementation_eq_of_gateSelected_eq
    target.implementation.candidate full (records target keep full) selectedEqual]
  apply available_of_retained_source target keep full field (target.source field)
  · apply (mem_matchingSources target field (target.source field)).mpr
    apply (WireProfileAvailability.sourceMatches_iff target target.implementation
      field (target.source field)).mpr
    intro valuation
    rfl
  · cases binding : target.source field with
    | constant _ => rfl
    | input _ => rfl
    | gate gate => exact full_records_selected target keep gate

theorem profile_available (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields)
    (profileMember : TerminalPrimitiveRecord.profile field ∈ records target keep seed) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (implementation target keep seed) field = true :=
  (terminalCandidateSaturate_profile_preserved target.implementation.candidate
    (WireProfileAmbient.model target keep) seed field profileMember).trans
      (full_ambient_available target keep field)

def keptFieldSeed (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) :
    List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields) :=
  ((allFin fields).filter keep).map TerminalPrimitiveRecord.profile

def projectedImplementation (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)) :
    Implementation (inputs + target.implementation.gateCount) target.implementation.gateCount :=
  implementation target keep (seed ++ keptFieldSeed target keep)

theorem projected_available (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) (kept : keep field = true) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (projectedImplementation target keep seed) field = true := by
  apply profile_available target keep (seed ++ keptFieldSeed target keep) field
  apply terminalSaturateRecords_extensive
    (terminalCandidateSaturationSystem target.implementation.candidate
      (WireProfileAmbient.model target keep))
    (seed ++ keptFieldSeed target keep) (.profile field)
  apply List.mem_append_right
  exact List.mem_map.mpr
    ⟨field, List.mem_filter.mpr ⟨mem_allFin field, kept⟩, rfl⟩

theorem projected_tableAvailable (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) (kept : keep field = true) :
    tableAvailable target keep (seed ++ keptFieldSeed target keep) field = true :=
  (available_eq_tableAvailable target keep (seed ++ keptFieldSeed target keep) field).symm.trans
    (projected_available target keep seed field kept)

theorem projected_fieldValue (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) (kept : keep field = true)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (WireProfileAvailability.bind (WireProfileAmbient.ambientTarget target)
        (projectedImplementation target keep seed)).fieldValue valuation field =
      target.fieldValue
        (fun index => valuation (Fin.castAdd target.implementation.gateCount index)) field :=
  (WireProfileAvailability.bind_fieldValue (WireProfileAmbient.ambientTarget target)
    (projectedImplementation target keep seed) field
      (projected_available target keep seed field kept) valuation).trans
    (WireProfileFieldClosed.ambient_fieldValue target valuation field)

end PNP.DirectWire.ClosedSupportProfile
