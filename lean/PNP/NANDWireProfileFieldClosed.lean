import PNP.NANDWireProfileAmbient
import PNP.ResidualTerminalSaturatedSupportContext

/-!
Research: obtain an actual extracted support preserving every computational
field by seeding the existing candidate-derived saturation with actual field
gate sources. This constructs the support and its observer, not a supplied
correctness certificate. It need not be proper, smaller, optimal or polynomial.
It is not a whole-circuit replacement or a proof of forced-cost transparency.
-/

namespace PNP.DirectWire.WireProfileFieldClosed

open WireProfileAvailability WireProfileAmbient

variable {inputs outputs fields : Nat}

def fieldGateSeed (target : WireCarrier inputs outputs fields) :
    List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields) :=
  (allFin fields).flatMap fun field =>
    match target.source field with
    | .gate gate => [.gate gate]
    | .input _ => []
    | .constant _ => []

def records (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)) :
    List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields) :=
  terminalSaturateRecords
    (terminalCandidateSaturationSystem target.implementation.candidate (model target keep))
    (seed ++ fieldGateSeed target)

def implementation (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)) :
    Implementation (inputs + target.implementation.gateCount) target.implementation.gateCount :=
  terminalAmbientSupportImplementation target.implementation.candidate (records target keep seed)

theorem source_selected (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) (gate : Fin target.implementation.gateCount)
    (binding : target.source field = .gate gate) :
    terminalGateSelected (records target keep seed) gate = true := by
  apply (terminalGateSelected_eq_true_iff _ gate).mpr
  apply terminalSaturateRecords_extensive
    (terminalCandidateSaturationSystem target.implementation.candidate (model target keep))
    (seed ++ fieldGateSeed target) (.gate gate)
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨field, mem_allFin field, ?_⟩
  rw [binding]
  exact List.Mem.head []

theorem boundary_isInput (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (wire : TerminalSupportWire inputs target.implementation.gateCount)
    (member : wire ∈ (extractTerminalSupport target.implementation.candidate
      (records target keep seed)).boundary) :
    ∃ input : Fin inputs, wire = .input input :=
  terminalCandidateSaturate_boundary_isInput target.implementation.candidate
    (model target keep) (seed ++ fieldGateSeed target) wire member

theorem gate_value (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (gate : Fin target.implementation.gateCount)
    (selected : terminalGateSelected (records target keep seed) gate = true)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (implementation target keep seed).candidate.program.eval valuation
        (terminalExtractionGateIndex target.implementation.candidate
          (records target keep seed) gate selected) =
      target.implementation.candidate.program.eval
        (fun index => valuation (Fin.castAdd target.implementation.gateCount index)) gate := by
  let support := extractTerminalSupport target.implementation.candidate (records target keep seed)
  let original : Valuation inputs :=
    fun index => valuation (Fin.castAdd target.implementation.gateCount index)
  have boundaryEqual :
      (fun index => valuation ((support.boundary.get index).ambientIndex)) =
        terminalInducedBoundaryValuation target.implementation.candidate
          (records target keep seed) original := by
    funext index
    obtain ⟨input, equal⟩ := boundary_isInput target keep seed
      (support.boundary.get index) (List.get_mem support.boundary index)
    change valuation ((support.boundary.get index).ambientIndex) =
      (support.boundary.get index).candidateValue target.implementation.candidate original
    rw [equal]
    rfl
  change (support.extractedCandidate.program.renameInputs
      (fun index => (support.boundary.get index).ambientIndex)).eval valuation _ = _
  rw [Program.eval_renameInputs, boundaryEqual]
  exact extractTerminalSupport_gate_induced target.implementation.candidate
    (records target keep seed) original gate selected

theorem ambient_fieldValue (target : WireCarrier inputs outputs fields)
    (valuation : Valuation (inputs + target.implementation.gateCount)) (field : Fin fields) :
    (ambientTarget target).fieldValue valuation field =
      target.fieldValue
        (fun index => valuation (Fin.castAdd target.implementation.gateCount index)) field :=
  pad_fieldValue target target.implementation.gateCount valuation field

theorem available (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) :
    (model target keep).observe (implementation target keep seed) field = true := by
  change WireProfileAvailability.available (ambientTarget target)
    (implementation target keep seed) field = true
  cases binding : target.source field with
  | input index =>
      apply available_of_source (ambientTarget target) (implementation target keep seed)
        field (.input (Fin.castAdd target.implementation.gateCount index))
      intro valuation
      rw [ambient_fieldValue]
      change valuation (Fin.castAdd target.implementation.gateCount index) =
        (target.source field).eval _ _
      rw [binding]
      rfl
  | constant value =>
      apply available_of_source (ambientTarget target) (implementation target keep seed)
        field (.constant value)
      intro valuation
      rw [ambient_fieldValue]
      change value = (target.source field).eval _ _
      rw [binding]
      rfl
  | gate gate =>
      have selected := source_selected target keep seed field gate binding
      apply available_of_source (ambientTarget target) (implementation target keep seed)
        field (.gate (terminalExtractionGateIndex target.implementation.candidate
          (records target keep seed) gate selected))
      intro valuation
      rw [ambient_fieldValue]
      change (implementation target keep seed).candidate.program.eval valuation _ =
        (target.source field).eval _ _
      rw [binding]
      exact gate_value target keep seed gate selected valuation

end PNP.DirectWire.WireProfileFieldClosed
