/-
Copyright (c) 2026 PNP Labs.

Dependency bounds for actual wire-backed carrier operations. The constructions
are the existing expose/unpack, physical normalization, mask, materializer and
common-input literal join. No Boolean-equivalence premise supplies a wiring
bound. These are prerequisites for the complete history and literal-splice
theorem, not complete Package E, global ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDNormalizationCausalBounds
import PNP.NANDWireObligationRestoration

namespace PNP.DirectWire
namespace WireCarrier

variable {inputs outputs fields : Nat}

/-- Syntactic dependency level of an actual computational field source. -/
def fieldLevel (carrier : WireCarrier inputs outputs fields)
    (labels : Fin inputs → Nat) (field : Fin fields) : Nat :=
  CausalBound.source (carrier.source field) labels
    (CausalBound.levels carrier.implementation.candidate.program labels)

/-- Pointwise bounds for all ordinary outputs and all literal field wires. -/
def CausalBounds (carrier : WireCarrier inputs outputs fields)
    (labels : Fin inputs → Nat) (outputCaps : Fin outputs → Nat)
    (fieldCaps : Fin fields → Nat) : Prop :=
  (∀ output, CausalBound.outputLevel carrier.implementation.candidate labels output ≤
    outputCaps output) ∧
  (∀ field, carrier.fieldLevel labels field ≤ fieldCaps field)

theorem exposed_output_level (carrier : WireCarrier inputs outputs fields)
    (labels : Fin inputs → Nat) (output : Fin outputs) :
    CausalBound.outputLevel carrier.exposed.candidate labels (Fin.castAdd fields output) =
      CausalBound.outputLevel carrier.implementation.candidate labels output := by
  change CausalBound.source
    (carrier.exposed.candidate.directWireWord.source (Fin.castAdd fields output))
    labels (CausalBound.levels carrier.implementation.candidate.program labels) = _
  rw [exposed_output_source]
  rfl

theorem exposed_field_level (carrier : WireCarrier inputs outputs fields)
    (labels : Fin inputs → Nat) (field : Fin fields) :
    CausalBound.outputLevel carrier.exposed.candidate labels (Fin.natAdd outputs field) =
      carrier.fieldLevel labels field := by
  change CausalBound.source
    (carrier.exposed.candidate.directWireWord.source (Fin.natAdd outputs field))
    labels (CausalBound.levels carrier.implementation.candidate.program labels) = _
  rw [exposed_field_source]
  rfl

theorem exposed_level (carrier : WireCarrier inputs outputs fields)
    (labels : Fin inputs → Nat) (observation : Fin (outputs + fields)) :
    CausalBound.outputLevel carrier.exposed.candidate labels observation =
      splitFin (CausalBound.outputLevel carrier.implementation.candidate labels)
        (carrier.fieldLevel labels) observation := by
  rcases finSum_decompose observation with ⟨output, rfl⟩ | ⟨field, rfl⟩
  · rw [exposed_output_level, splitFin_left]
  · rw [exposed_field_level, splitFin_right]

theorem causalBounds_exposed_le (carrier : WireCarrier inputs outputs fields)
    (labels : Fin inputs → Nat) (outputCaps : Fin outputs → Nat)
    (fieldCaps : Fin fields → Nat)
    (bounded : carrier.CausalBounds labels outputCaps fieldCaps)
    (observation : Fin (outputs + fields)) :
    CausalBound.outputLevel carrier.exposed.candidate labels observation ≤
      splitFin outputCaps fieldCaps observation := by
  rcases finSum_decompose observation with ⟨output, rfl⟩ | ⟨field, rfl⟩
  · rw [exposed_output_level, splitFin_left]
    exact bounded.1 output
  · rw [exposed_field_level, splitFin_right]
    exact bounded.2 field

theorem causalBounds_self (carrier : WireCarrier inputs outputs fields)
    (labels : Fin inputs → Nat) :
    carrier.CausalBounds labels
      (CausalBound.outputLevel carrier.implementation.candidate labels)
      (carrier.fieldLevel labels) :=
  ⟨fun _ => Nat.le_refl _, fun _ => Nat.le_refl _⟩

/-- The constructed normalizer bounds the entire actual exposed word. -/
theorem normalize_exposed_level (carrier : WireCarrier inputs outputs fields)
    (labels : Fin inputs → Nat) (observation : Fin (outputs + fields)) :
    CausalBound.outputLevel carrier.normalize.exposed.candidate labels observation ≤
      CausalBound.outputLevel carrier.exposed.candidate labels observation := by
  unfold normalize
  rw [exposed_unpack]
  exact CausalBound.physical_normalization_output_bound carrier.exposed labels observation

theorem normalize_output_level (carrier : WireCarrier inputs outputs fields)
    (labels : Fin inputs → Nat) (output : Fin outputs) :
    CausalBound.outputLevel carrier.normalize.implementation.candidate labels output ≤
      CausalBound.outputLevel carrier.implementation.candidate labels output := by
  simpa only [exposed_output_level] using
    normalize_exposed_level carrier labels (Fin.castAdd fields output)

theorem normalize_field_level (carrier : WireCarrier inputs outputs fields)
    (labels : Fin inputs → Nat) (field : Fin fields) :
    carrier.normalize.fieldLevel labels field ≤ carrier.fieldLevel labels field := by
  simpa only [exposed_field_level] using
    normalize_exposed_level carrier labels (Fin.natAdd outputs field)

theorem normalize_causalBounds (carrier : WireCarrier inputs outputs fields)
    (labels : Fin inputs → Nat) (outputCaps : Fin outputs → Nat)
    (fieldCaps : Fin fields → Nat)
    (bounded : carrier.CausalBounds labels outputCaps fieldCaps) :
    carrier.normalize.CausalBounds labels outputCaps fieldCaps :=
  ⟨fun output => Nat.le_trans (normalize_output_level carrier labels output)
      (bounded.1 output),
    fun field => Nat.le_trans (normalize_field_level carrier labels field)
      (bounded.2 field)⟩

end WireCarrier

namespace WireObligationRestoration

variable {inputs outputs fields : Nat}

theorem masked_causalBounds (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (labels : Fin inputs → Nat)
    (outputCaps : Fin outputs → Nat) (fieldCaps : Fin fields → Nat)
    (bounded : carrier.CausalBounds labels outputCaps fieldCaps) :
    (masked carrier keep).CausalBounds labels outputCaps fieldCaps := by
  constructor
  · exact bounded.1
  · intro field
    change CausalBound.source (if keep field then carrier.source field else .constant false)
      labels (CausalBound.levels carrier.implementation.candidate.program labels) ≤ fieldCaps field
    split
    · exact bounded.2 field
    · exact Nat.zero_le _

theorem hidden_causalBounds (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (labels : Fin inputs → Nat)
    (fieldCaps : Fin fields → Nat)
    (bounded : ∀ field, carrier.fieldLevel labels field ≤ fieldCaps field) :
    (hidden carrier keep).CausalBounds labels Fin.elim0 fieldCaps := by
  constructor
  · intro output
    exact Fin.elim0 output
  · intro field
    change CausalBound.source (if keep field then .constant false else carrier.source field)
      labels (CausalBound.levels carrier.implementation.candidate.program labels) ≤ fieldCaps field
    split
    · exact Nat.zero_le _
    · exact bounded field

theorem materializer_causalBounds (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (labels : Fin inputs → Nat)
    (fieldCaps : Fin fields → Nat)
    (bounded : ∀ field, carrier.fieldLevel labels field ≤ fieldCaps field) :
    (materializer carrier keep).CausalBounds labels Fin.elim0 fieldCaps :=
  WireCarrier.normalize_causalBounds (hidden carrier keep) labels Fin.elim0 fieldCaps
    (hidden_causalBounds carrier keep labels fieldCaps bounded)

private theorem prefix_level {leftGates rightGates : Nat}
    (left : Program inputs leftGates) (right : Program inputs rightGates)
    (wire : Source inputs leftGates) (labels : Fin inputs → Nat) :
    CausalBound.source (wire.weakenGates rightGates) labels
        (CausalBound.levels (left.appendSubstituted (fun input => .input input) right) labels) =
      CausalBound.source wire labels (CausalBound.levels left labels) := by
  rw [CausalBound.source_weaken]
  exact CausalBound.source_congr wire (fun _ => rfl)
    (CausalBound.levels_append_prefix left (fun input => .input input) right labels)

private theorem suffix_level {leftGates rightGates : Nat}
    (left : Program inputs leftGates) (right : Program inputs rightGates)
    (wire : Source inputs rightGates) (labels : Fin inputs → Nat) :
    CausalBound.source
        (wire.substituteInputs (fun input => Source.input (gates := leftGates) input)) labels
        (CausalBound.levels (left.appendSubstituted (fun input => .input input) right) labels) =
      CausalBound.source wire labels (CausalBound.levels right labels) :=
  CausalBound.substituted_source_level left (fun input => .input input) right wire labels

theorem join_output_level (visible : WireCarrier inputs outputs fields)
    (missing : WireCarrier inputs 0 fields) (keep : Fin fields → Bool)
    (labels : Fin inputs → Nat) (output : Fin outputs) :
    CausalBound.outputLevel (join visible missing keep).implementation.candidate labels output =
      CausalBound.outputLevel visible.implementation.candidate labels output := by
  unfold join CausalBound.outputLevel
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_pointwise]
  exact prefix_level visible.implementation.candidate.program
    missing.implementation.candidate.program
    (visible.implementation.candidate.directWireWord.source output) labels

theorem join_field_level (visible : WireCarrier inputs outputs fields)
    (missing : WireCarrier inputs 0 fields) (keep : Fin fields → Bool)
    (labels : Fin inputs → Nat) (field : Fin fields) :
    (join visible missing keep).fieldLevel labels field =
      if keep field then visible.fieldLevel labels field else missing.fieldLevel labels field := by
  unfold join WireCarrier.fieldLevel
  dsimp only [Candidate.toImplementation]
  cases kept : keep field
  · simp only [Bool.false_eq_true, if_false]
    exact suffix_level visible.implementation.candidate.program
      missing.implementation.candidate.program (missing.source field) labels
  · simp only [if_true]
    exact prefix_level visible.implementation.candidate.program
      missing.implementation.candidate.program (visible.source field) labels

theorem join_causalBounds (visible : WireCarrier inputs outputs fields)
    (missing : WireCarrier inputs 0 fields) (keep : Fin fields → Bool)
    (labels : Fin inputs → Nat) (outputCaps : Fin outputs → Nat)
    (fieldCaps : Fin fields → Nat)
    (visibleBound : visible.CausalBounds labels outputCaps fieldCaps)
    (missingBound : missing.CausalBounds labels Fin.elim0 fieldCaps) :
    (join visible missing keep).CausalBounds labels outputCaps fieldCaps := by
  constructor
  · intro output
    rw [join_output_level]
    exact visibleBound.1 output
  · intro field
    rw [join_field_level]
    split
    · exact visibleBound.2 field
    · exact missingBound.2 field

end WireObligationRestoration
end PNP.DirectWire
