import PNP.NANDClosedSupportObservation
import PNP.ResidualTerminalSaturationCostBalance
import PNP.NANDComposition

/-!
Specialize the computed full-profile minimum of a computed closed support to
the original primary inputs. The reference minimum and matching sources are
computed, not supplied. Whole-circuit reconstruction and strict descent are
proved in NANDClosedSupportFullGain. The finite searches are exhaustive, with
no polynomial-time claim or positive-support discovery result.
-/

namespace PNP.DirectWire.ClosedSupportFullGain

variable {inputs outputs fields : Nat}

def fullRealization (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :=
  terminalFullProfileMinimumRealization
    (WireProfileAmbient.model target keep).ambientProfileSystem
    (ClosedSupportObservation.implementation target keep seed)

def offered (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :=
  (fullRealization target keep seed).realization.implementation

def extendZero (extra : Nat) (valuation : Valuation inputs) : Valuation (inputs + extra) :=
  splitFin valuation (fun _ : Fin extra => false)

theorem restrict_extendZero (extra : Nat) (valuation : Valuation inputs) :
    (fun index => extendZero extra valuation (Fin.castAdd extra index)) = valuation :=
  funext (splitFin_left valuation (fun _ : Fin extra => false))

def inputBinding (extra : Nat) : Fin (inputs + extra) → Source inputs 0 :=
  splitFin (fun index => .input index) (fun _ : Fin extra => .constant false)

theorem inputBinding_eval (extra : Nat) (valuation : Valuation inputs)
    (gateValues : Valuation 0) (index : Fin (inputs + extra)) :
    (inputBinding extra index).eval valuation gateValues = extendZero extra valuation index := by
  rcases finSum_decompose index with ⟨left, rfl⟩ | ⟨right, rfl⟩
  · simp only [inputBinding, extendZero, splitFin_left, Source.eval]
  · simp only [inputBinding, extendZero, splitFin_right, Source.eval]

def prefixProgram (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    Program inputs (0 + (offered target keep seed).gateCount) :=
  Program.empty.appendSubstituted (inputBinding target.implementation.gateCount)
    (offered target keep seed).candidate.program

def prefixSource (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields))
    (source : Source (inputs + target.implementation.gateCount)
      (offered target keep seed).gateCount) :
    Source inputs (0 + (offered target keep seed).gateCount) :=
  source.substituteInputs (inputBinding target.implementation.gateCount)

theorem prefixSource_value (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields))
    (source : Source (inputs + target.implementation.gateCount)
      (offered target keep seed).gateCount)
    (valuation : Valuation inputs) :
    (prefixSource target keep seed source).eval valuation
        ((prefixProgram target keep seed).eval valuation) =
      source.eval (extendZero target.implementation.gateCount valuation)
        ((offered target keep seed).candidate.program.eval
          (extendZero target.implementation.gateCount valuation)) := by
  unfold prefixSource
  rw [Source.eval_substituteInputs]
  apply source.eval_congr
  · intro index
    exact inputBinding_eval _ _ _ index
  · intro gate
    unfold prefixProgram
    rw [Program.eval_appendSubstituted_suffix]
    have inputEqual :
        (fun index => (inputBinding target.implementation.gateCount index).eval
          valuation (Program.empty.eval valuation)) =
          extendZero target.implementation.gateCount valuation :=
      funext (inputBinding_eval _ _ _)
    rw [inputEqual]

theorem offered_available (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (field : Fin fields)
    (present : WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (ClosedSupportObservation.implementation target keep seed) field = true) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (offered target keep seed) field = true :=
  ((fullRealization target keep seed).profileEqual field).trans present

def prefixField (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (field : Fin fields) :
    Source inputs (0 + (offered target keep seed).gateCount) :=
  prefixSource target keep seed
    ((WireProfileAvailability.bind (WireProfileAmbient.ambientTarget target)
      (offered target keep seed)).source field)

theorem prefixField_value (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (field : Fin fields)
    (present : ClosedSupportObservation.retained target keep seed (target.source field) = true)
    (valuation : Valuation inputs) :
    (prefixField target keep seed field).eval valuation
        ((prefixProgram target keep seed).eval valuation) =
      target.fieldValue valuation field := by
  have matched : target.source field ∈ ClosedSupportObservation.matchingSources target field :=
    (ClosedSupportObservation.mem_matchingSources target field (target.source field)).mpr
      ((WireProfileAvailability.sourceMatches_iff target target.implementation field
        (target.source field)).mpr (fun _ => rfl))
  have available := offered_available target keep seed field
    (ClosedSupportObservation.available_of_retained_source target keep seed field
      (target.source field) matched present)
  unfold prefixField
  rw [prefixSource_value]
  have same := WireProfileAvailability.bind_fieldValue
    (WireProfileAmbient.ambientTarget target) (offered target keep seed) field available
    (extendZero target.implementation.gateCount valuation)
  change (WireProfileAvailability.bind (WireProfileAmbient.ambientTarget target)
    (offered target keep seed)).fieldValue
      (extendZero target.implementation.gateCount valuation) field = _
  rw [same, WireProfileFieldClosed.ambient_fieldValue, restrict_extendZero]

theorem interface_index_sound
    {gates profileWidth : Nat} {candidate : Candidate inputs gates outputs}
    (support : TerminalExtractedSupport (profileWidth := profileWidth) candidate)
    (producer : Fin gates) (index : Fin support.interface.length)
    (found : support.interfaceIndex? producer = some index) :
    support.interface.get index = producer := by
  unfold TerminalExtractedSupport.interfaceIndex? at found
  split at found
  · cases found
    exact Subtype.property (p := fun i : Fin support.interface.length =>
      support.interface.get i = producer) _
  · cases found

theorem interface_index_exists
    {gates profileWidth : Nat} {candidate : Candidate inputs gates outputs}
    (support : TerminalExtractedSupport (profileWidth := profileWidth) candidate)
    (producer : Fin gates) (member : producer ∈ support.interface) :
    ∃ index, support.interfaceIndex? producer = some index := by
  unfold TerminalExtractedSupport.interfaceIndex?
  rw [dif_pos member]
  exact ⟨_, rfl⟩

theorem ambient_output (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields))
    (producer : Fin target.implementation.gateCount)
    (member : producer ∈ (extractTerminalSupport target.implementation.candidate
      (ClosedSupportObservation.records target keep seed)).interface)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (ClosedSupportObservation.implementation target keep seed).candidate.semantics
        valuation producer =
      target.implementation.candidate.program.eval
        (fun input => valuation (Fin.castAdd target.implementation.gateCount input)) producer := by
  let support := extractTerminalSupport target.implementation.candidate
    (ClosedSupportObservation.records target keep seed)
  let rename := fun index : Fin support.boundary.length =>
    (support.boundary.get index).ambientIndex
  let original : Valuation inputs :=
    fun input => valuation (Fin.castAdd target.implementation.gateCount input)
  obtain ⟨index, found⟩ := interface_index_exists support producer member
  have sameIndex := interface_index_sound support producer index found
  have boundaryEqual : (fun index => valuation (rename index)) =
      terminalInducedBoundaryValuation target.implementation.candidate
        (ClosedSupportObservation.records target keep seed) original := by
    funext index
    obtain ⟨input, equal⟩ := ClosedSupportObservation.boundary_isInput target keep seed
      (support.boundary.get index) (List.get_mem support.boundary index)
    change valuation ((support.boundary.get index).ambientIndex) =
      (support.boundary.get index).candidateValue target.implementation.candidate original
    rw [equal]
    rfl
  change (terminalAmbientSupportCandidate target.implementation.candidate
    (ClosedSupportObservation.records target keep seed)).semantics valuation producer = _
  unfold terminalAmbientSupportCandidate
  rw [Candidate.ofDirectWireWord_semantics]
  simp only [DirectWire.semantics, DirectWireWord.eval]
  rw [found]
  change (support.extractedCandidate.renameInputs rename).semantics valuation index = _
  rw [Candidate.renameInputs_semantics, boundaryEqual]
  exact (extractTerminalSupport_induced target.implementation.candidate
    (ClosedSupportObservation.records target keep seed) original index).trans
      (congrArg (target.implementation.candidate.program.eval original) sameIndex)

def prefixOutput (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (producer : Fin target.implementation.gateCount) :
    Source inputs (0 + (offered target keep seed).gateCount) :=
  prefixSource target keep seed ((offered target keep seed).candidate.directWireWord.source producer)

theorem prefixOutput_value (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields))
    (producer : Fin target.implementation.gateCount)
    (member : producer ∈ (extractTerminalSupport target.implementation.candidate
      (ClosedSupportObservation.records target keep seed)).interface)
    (valuation : Valuation inputs) :
    (prefixOutput target keep seed producer).eval valuation
        ((prefixProgram target keep seed).eval valuation) =
      target.implementation.candidate.program.eval valuation producer := by
  unfold prefixOutput
  rw [prefixSource_value]
  change (offered target keep seed).candidate.semantics
    (extendZero target.implementation.gateCount valuation) producer = _
  have same := (fullRealization target keep seed).realization.equivalent
    (extendZero target.implementation.gateCount valuation) producer
  change (offered target keep seed).candidate.semantics
    (extendZero target.implementation.gateCount valuation) producer =
      (ClosedSupportObservation.implementation target keep seed).candidate.semantics
        (extendZero target.implementation.gateCount valuation) producer at same
  rw [same, ambient_output target keep seed producer member, restrict_extendZero]

theorem offered_gateCount (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    (offered target keep seed).gateCount =
      (terminalSaturationCostSnapshot target.implementation.candidate
        (WireProfileAmbient.model target keep)
        (ClosedSupportObservation.records target keep seed)).fullMinimum := rfl

theorem offered_gateCount_le (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    (offered target keep seed).gateCount ≤
      (extractTerminalSupport target.implementation.candidate
        (ClosedSupportObservation.records target keep seed)).gateCount :=
  terminalFullProfileMinimum_le
    (terminalCurrentFullCarrierRealization
      (WireProfileAmbient.model target keep).ambientProfileSystem
      (ClosedSupportObservation.implementation target keep seed))

end PNP.DirectWire.ClosedSupportFullGain
