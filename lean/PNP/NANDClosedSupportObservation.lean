import PNP.NANDWireProfileFieldClosed

/-!
Research: exact source-table observation of every support produced by the
computed wire-profile saturation model. No field-source seed is injected:
availability may be true or false. The table and the support are both computed.

Uniform source matching still enumerates input valuations. This does not
replace the full manuscript profile grammar, prove polynomial construction,
find an optimal or proper support, or establish global route completeness.
-/

namespace PNP.DirectWire.ClosedSupportObservation

variable {inputs outputs fields : Nat}

def records (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields) :=
  terminalSaturateRecords
    (terminalCandidateSaturationSystem target.implementation.candidate
      (WireProfileAmbient.model target keep)) seed

def implementation (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    Implementation (inputs + target.implementation.gateCount)
      target.implementation.gateCount :=
  terminalAmbientSupportImplementation target.implementation.candidate
    (records target keep seed)

def matchingSources (target : WireCarrier inputs outputs fields) (field : Fin fields) :
    List (Source inputs target.implementation.gateCount) :=
  (allSources inputs target.implementation.gateCount).filter
    (WireProfileAvailability.sourceMatches target target.implementation field)

def retained (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) : Source inputs target.implementation.gateCount → Bool
  | .constant _ => true
  | .input _ => true
  | .gate gate => terminalGateSelected (records target keep seed) gate

def tableAvailable (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (field : Fin fields) : Bool :=
  (matchingSources target field).any (retained target keep seed)

theorem mem_matchingSources (target : WireCarrier inputs outputs fields)
    (field : Fin fields) (source : Source inputs target.implementation.gateCount) :
    source ∈ matchingSources target field ↔
      WireProfileAvailability.sourceMatches target target.implementation field source = true := by
  constructor
  · intro member
    exact (List.mem_filter.mp member).2
  · intro matched
    exact List.mem_filter.mpr ⟨mem_allSources source, matched⟩

theorem boundary_isInput (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields))
    (wire : TerminalSupportWire inputs target.implementation.gateCount)
    (member : wire ∈ (extractTerminalSupport target.implementation.candidate
      (records target keep seed)).boundary) :
    ∃ input : Fin inputs, wire = .input input :=
  terminalCandidateSaturate_boundary_isInput target.implementation.candidate
    (WireProfileAmbient.model target keep) seed wire member

theorem gate_value (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields))
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

theorem lift_retained_source (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields))
    (source : Source inputs target.implementation.gateCount)
    (present : retained target keep seed source = true) :
    ∃ lifted : Source (inputs + target.implementation.gateCount)
        (implementation target keep seed).gateCount,
      ∀ valuation, lifted.eval valuation
          ((implementation target keep seed).candidate.program.eval valuation) =
        source.eval
          (fun index => valuation (Fin.castAdd target.implementation.gateCount index))
          (target.implementation.candidate.program.eval
            (fun index => valuation (Fin.castAdd target.implementation.gateCount index))) := by
  cases source with
  | constant value => exact ⟨.constant value, fun _ => rfl⟩
  | input index => exact ⟨.input (Fin.castAdd target.implementation.gateCount index), fun _ => rfl⟩
  | gate gate =>
      refine ⟨.gate (terminalExtractionGateIndex target.implementation.candidate
        (records target keep seed) gate present), ?_⟩
      intro valuation
      exact gate_value target keep seed gate present valuation

theorem available_of_retained_source (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (field : Fin fields)
    (source : Source inputs target.implementation.gateCount)
    (matched : source ∈ matchingSources target field)
    (present : retained target keep seed source = true) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (implementation target keep seed) field = true := by
  obtain ⟨lifted, same⟩ := lift_retained_source target keep seed source present
  have matchValue := (WireProfileAvailability.sourceMatches_iff
    target target.implementation field source).mp
      ((mem_matchingSources target field source).mp matched)
  apply WireProfileAvailability.available_of_source
    (WireProfileAmbient.ambientTarget target) (implementation target keep seed) field lifted
  intro valuation
  exact (same valuation).trans
    ((matchValue _).trans
      (WireProfileFieldClosed.ambient_fieldValue target valuation field).symm)

private def extendZero (extra : Nat) (valuation : Valuation inputs) :
    Valuation (inputs + extra) :=
  splitFin valuation (fun _ : Fin extra => false)

private theorem restrict_extendZero (extra : Nat) (valuation : Valuation inputs) :
    (fun index => extendZero extra valuation (Fin.castAdd extra index)) = valuation :=
  funext (splitFin_left valuation (fun _ : Fin extra => false))

theorem retract_support_source (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields))
    (offered : Source (inputs + target.implementation.gateCount)
      (implementation target keep seed).gateCount) :
    ∃ source : Source inputs target.implementation.gateCount,
      retained target keep seed source = true ∧
      ∀ valuation, offered.eval (extendZero target.implementation.gateCount valuation)
          ((implementation target keep seed).candidate.program.eval
            (extendZero target.implementation.gateCount valuation)) =
        source.eval valuation (target.implementation.candidate.program.eval valuation) := by
  cases offered with
  | constant value => exact ⟨.constant value, rfl, fun _ => rfl⟩
  | input index =>
      rcases finSum_decompose index with ⟨left, rfl⟩ | ⟨right, rfl⟩
      · exact ⟨.input left, rfl, fun valuation =>
          splitFin_left valuation (fun _ : Fin target.implementation.gateCount => false) left⟩
      · exact ⟨.constant false, rfl, fun valuation =>
          splitFin_right valuation (fun _ : Fin target.implementation.gateCount => false) right⟩
  | gate index =>
      let original := terminalExtractionOrigin target.implementation.candidate
        (records target keep seed) index
      have selected := terminalExtractionOrigin_selected target.implementation.candidate
        (records target keep seed) index
      refine ⟨.gate original, selected, ?_⟩
      intro valuation
      have equal := gate_value target keep seed original selected
        (extendZero target.implementation.gateCount valuation)
      have origin := terminalExtractionGateIndex_origin target.implementation.candidate
        (records target keep seed) index
      rw [origin] at equal
      rw [restrict_extendZero] at equal
      exact equal

theorem available_iff_retained_source (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (field : Fin fields) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
        (implementation target keep seed) field = true ↔
      ∃ source, source ∈ matchingSources target field ∧
        retained target keep seed source = true := by
  constructor
  · intro available
    obtain ⟨offered, same⟩ :=
      (WireProfileAmbient.available_iff_exists (WireProfileAmbient.ambientTarget target)
        (implementation target keep seed) field).mp available
    obtain ⟨source, present, retracted⟩ :=
      retract_support_source target keep seed offered
    refine ⟨source, ?_, present⟩
    apply (mem_matchingSources target field source).mpr
    apply (WireProfileAvailability.sourceMatches_iff
      target target.implementation field source).mpr
    intro valuation
    calc
      source.eval valuation (target.implementation.candidate.program.eval valuation) =
          offered.eval (extendZero target.implementation.gateCount valuation)
            ((implementation target keep seed).candidate.program.eval
              (extendZero target.implementation.gateCount valuation)) :=
        (retracted valuation).symm
      _ = (WireProfileAmbient.ambientTarget target).fieldValue
          (extendZero target.implementation.gateCount valuation) field := same _
      _ = target.fieldValue valuation field := by
        rw [WireProfileFieldClosed.ambient_fieldValue, restrict_extendZero]
  · rintro ⟨source, matched, present⟩
    exact available_of_retained_source target keep seed field source matched present

theorem tableAvailable_iff (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (field : Fin fields) :
    tableAvailable target keep seed field = true ↔
      ∃ source, source ∈ matchingSources target field ∧
        retained target keep seed source = true := by
  exact List.any_eq_true

private theorem bool_eq_of_true_iff (left right : Bool)
    (same : left = true ↔ right = true) : left = right := by
  cases left <;> cases right
  · rfl
  · have impossible := same.mpr rfl
    cases impossible
  · have impossible := same.mp rfl
    cases impossible
  · rfl

theorem available_eq_tableAvailable (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (field : Fin fields) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (implementation target keep seed) field =
        tableAvailable target keep seed field :=
  bool_eq_of_true_iff _ _
    ((available_iff_retained_source target keep seed field).trans
      (tableAvailable_iff target keep seed field).symm)

end PNP.DirectWire.ClosedSupportObservation
