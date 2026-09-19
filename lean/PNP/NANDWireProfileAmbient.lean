import PNP.NANDWireProfileAvailability
import PNP.ResidualTerminalCandidateSaturation

/-!
Research: derive coherent computational-field observers at the base and ambient
input shapes. Extra inputs are genuine independent Boolean inputs, not supplied
correctness data. Reference availability remains an exhaustive computation.
This does not define the manuscript's noncomputational profile roles or prove
global route completeness, forced-cost transparency, or polynomial bounds.
-/

namespace PNP.DirectWire.WireProfileAmbient

open WireProfileAvailability

variable {inputs outputs fields : Nat}

theorem available_iff_exists (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) (field : Fin fields) :
    available target offered field = true ↔
      ∃ source : Source inputs offered.gateCount,
        ∀ valuation, source.eval valuation (offered.candidate.program.eval valuation) =
          target.fieldValue valuation field := by
  constructor
  · intro present
    obtain ⟨source, _member, checked⟩ := List.find?_isSome.mp present
    exact ⟨source, (sourceMatches_iff target offered field source).mp checked⟩
  · rintro ⟨source, same⟩
    exact available_of_source target offered field source same

def padImplementation (offered : Implementation inputs outputs) (extra : Nat) :
    Implementation (inputs + extra) outputs :=
  (offered.candidate.renameInputs (Fin.castAdd extra)).toImplementation

def padCarrier (target : WireCarrier inputs outputs fields) (extra : Nat) :
    WireCarrier (inputs + extra) outputs fields :=
  { implementation := padImplementation target.implementation extra
    source := fun field => (target.source field).renameInputs (Fin.castAdd extra) }

theorem pad_gateCount (offered : Implementation inputs outputs) (extra : Nat) :
    (padImplementation offered extra).gateCount = offered.gateCount := rfl

theorem eval_paddedSource (offered : Implementation inputs outputs) (extra : Nat)
    (source : Source inputs offered.gateCount) (valuation : Valuation (inputs + extra)) :
    (source.renameInputs (Fin.castAdd extra)).eval valuation
        ((padImplementation offered extra).candidate.program.eval valuation) =
      source.eval (fun index => valuation (Fin.castAdd extra index))
        (offered.candidate.program.eval (fun index => valuation (Fin.castAdd extra index))) := by
  change (source.renameInputs (Fin.castAdd extra)).eval valuation
      ((offered.candidate.program.renameInputs (Fin.castAdd extra)).eval valuation) = _
  rw [Source.eval_renameInputs]
  exact source.eval_congr (fun _ => rfl)
    (fun gate => Program.eval_renameInputs _ _ _ gate)

theorem pad_fieldValue (target : WireCarrier inputs outputs fields) (extra : Nat)
    (valuation : Valuation (inputs + extra)) (field : Fin fields) :
    (padCarrier target extra).fieldValue valuation field =
      target.fieldValue (fun index => valuation (Fin.castAdd extra index)) field :=
  eval_paddedSource target.implementation extra (target.source field) valuation

def retractSource {gates extra : Nat} : Source (inputs + extra) gates → Source inputs gates
  | .input index => splitFin (fun left => .input left)
      (fun _ : Fin extra => .constant false) index
  | .constant value => .constant value
  | .gate gate => .gate gate

theorem eval_retractSource {gates extra : Nat}
    (source : Source (inputs + extra) gates) (valuation : Valuation inputs)
    (gateValues : Valuation gates) :
    (retractSource source).eval valuation gateValues =
      source.eval (splitFin valuation (fun _ : Fin extra => false)) gateValues := by
  cases source with
  | input index =>
      rcases finSum_decompose index with ⟨left, rfl⟩ | ⟨right, rfl⟩
      · simp only [retractSource, splitFin_left, Source.eval]
      · simp only [retractSource, splitFin_right, Source.eval]
  | constant value => rfl
  | gate gate => rfl

private theorem restrict_extended (extra : Nat) (valuation : Valuation inputs) :
    (fun index => splitFin valuation (fun _ : Fin extra => false)
      (Fin.castAdd extra index)) = valuation :=
  funext (splitFin_left valuation (fun _ : Fin extra => false))

theorem available_pad_iff (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) (extra : Nat) (field : Fin fields) :
    available (padCarrier target extra) (padImplementation offered extra) field = true ↔
      available target offered field = true := by
  constructor
  · intro present
    obtain ⟨source, same⟩ :=
      (available_iff_exists (padCarrier target extra)
        (padImplementation offered extra) field).mp present
    apply available_of_source target offered field (retractSource source)
    intro valuation
    let extended : Valuation (inputs + extra) :=
      splitFin valuation (fun _ : Fin extra => false)
    have gateEqual : ∀ gate,
        (padImplementation offered extra).candidate.program.eval extended gate =
          offered.candidate.program.eval valuation gate := by
      intro gate
      change (offered.candidate.program.renameInputs (Fin.castAdd extra)).eval extended gate = _
      rw [Program.eval_renameInputs]
      change offered.candidate.program.eval
        (fun index => splitFin valuation (fun _ : Fin extra => false)
          (Fin.castAdd extra index)) gate = _
      rw [restrict_extended]
    calc
      (retractSource source).eval valuation (offered.candidate.program.eval valuation) =
          source.eval extended (offered.candidate.program.eval valuation) :=
        eval_retractSource source valuation _
      _ = source.eval extended
          ((padImplementation offered extra).candidate.program.eval extended) :=
        source.eval_congr (fun _ => rfl) (fun gate => (gateEqual gate).symm)
      _ = (padCarrier target extra).fieldValue extended field := same extended
      _ = target.fieldValue valuation field := by
        rw [pad_fieldValue]
        change target.fieldValue
          (fun index => splitFin valuation (fun _ : Fin extra => false)
            (Fin.castAdd extra index)) field = _
        rw [restrict_extended]
  · intro present
    obtain ⟨source, same⟩ := (available_iff_exists target offered field).mp present
    apply available_of_source (padCarrier target extra) (padImplementation offered extra)
      field (source.renameInputs (Fin.castAdd extra))
    intro valuation
    exact (eval_paddedSource offered extra source valuation).trans
      ((same _).trans (pad_fieldValue target extra valuation field).symm)

private theorem bool_eq_of_true_iff (left right : Bool)
    (same : left = true ↔ right = true) : left = right := by
  cases left <;> cases right
  · rfl
  · have impossible := same.mpr rfl
    cases impossible
  · have impossible := same.mp rfl
    cases impossible
  · rfl

theorem available_pad (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) (extra : Nat) (field : Fin fields) :
    available (padCarrier target extra) (padImplementation offered extra) field =
      available target offered field :=
  bool_eq_of_true_iff _ _ (available_pad_iff target offered extra field)

def rewordImplementation {newOutputs : Nat} (offered : Implementation inputs outputs)
    (word : DirectWireWord inputs offered.gateCount newOutputs) :
    Implementation inputs newOutputs :=
  (Candidate.ofDirectWireWord offered.candidate.program word).toImplementation

def rewordCarrier {newOutputs : Nat} (target : WireCarrier inputs outputs fields)
    (word : DirectWireWord inputs target.implementation.gateCount newOutputs) :
    WireCarrier inputs newOutputs fields :=
  { implementation := rewordImplementation target.implementation word
    source := target.source }

theorem available_reword {newOutputs : Nat} (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs)
    (targetWord : DirectWireWord inputs target.implementation.gateCount newOutputs)
    (offeredWord : DirectWireWord inputs offered.gateCount newOutputs) (field : Fin fields) :
    available (rewordCarrier target targetWord)
      (rewordImplementation offered offeredWord) field = available target offered field := rfl

def ambientTarget (target : WireCarrier inputs outputs fields) :
    WireCarrier (inputs + target.implementation.gateCount)
      target.implementation.gateCount fields :=
  rewordCarrier (padCarrier target target.implementation.gateCount)
    ⟨fun _ => .constant false⟩

def ambientImplementation (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) :
    Implementation (inputs + target.implementation.gateCount) target.implementation.gateCount :=
  rewordImplementation (padImplementation offered target.implementation.gateCount)
    ⟨fun _ => .constant false⟩

def model (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) :
    TerminalCandidateSaturationModel (profileWidth := fields) target.implementation.candidate :=
  { profileSystem := system target
    projection := ⟨keep⟩
    observe := available (ambientTarget target) }

theorem model_observe_coherent (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (offered : Implementation inputs outputs) (field : Fin fields) :
    (model target keep).observe (ambientImplementation target offered) field =
      (model target keep).profileSystem.observe offered field := by
  change available (ambientTarget target) (ambientImplementation target offered) field =
    available target offered field
  unfold ambientTarget ambientImplementation
  rw [available_reword, available_pad]

end PNP.DirectWire.WireProfileAmbient
