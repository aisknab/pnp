/-
Copyright (c) 2026 PNP Labs.

Literal zero/unary realization and its one-copy splice preserve observation
dependency bounds. The minimum constructor is computed from the original full
unary function, and its compiler caps are derived from actual source programs.
This does not establish complete rewrite histories, a global route, or
polynomial-time PCCMin.
-/

import PNP.NANDWireUnaryArbitrarySupport
import PNP.NANDWireCausalBounds

namespace PNP.DirectWire.WireUnaryCausalBound

variable {outputs fields : Nat}

private theorem only_index (index : Fin 1) : index = fin1Zero := by
  apply Fin.ext
  have bound := index.isLt
  change index.val = 0
  omega

theorem input_label_le_of_bit_ne (carrier : WireCarrier 1 outputs fields)
    (labels : Fin 1 → Nat) (observation : Fin (outputs + fields))
    (different : WireUnaryRealization.bit carrier false observation ≠
      WireUnaryRealization.bit carrier true observation) :
    labels fin1Zero ≤ CausalBound.outputLevel carrier.exposed.candidate labels observation := by
  by_cases bounded : labels fin1Zero ≤
      CausalBound.outputLevel carrier.exposed.candidate labels observation
  · exact bounded
  · have inputSame : ∀ index, labels index ≤
        CausalBound.outputLevel carrier.exposed.candidate labels observation →
        (fun _ : Fin 1 => false) index = (fun _ : Fin 1 => true) index := by
      intro index below
      rw [only_index index] at below
      exact False.elim (bounded below)
    have same := CausalBound.source_sound carrier.exposed.candidate.program
      (carrier.exposed.candidate.directWireWord.source observation) labels
      (CausalBound.outputLevel carrier.exposed.candidate labels observation)
      (fun _ => false) (fun _ => true) inputSame (Nat.le_refl _)
    exact False.elim (different same)

theorem zero_implementation_bound (carrier : WireCarrier 1 outputs fields)
    (labels : Fin 1 → Nat) (observation : Fin (outputs + fields)) :
    CausalBound.outputLevel
        (WireUnaryRealization.zeroImplementation carrier).candidate labels observation ≤
      CausalBound.outputLevel carrier.exposed.candidate labels observation := by
  unfold CausalBound.outputLevel WireUnaryRealization.zeroImplementation
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_pointwise]
  change CausalBound.source
    (WireUnaryRealization.zeroSource (WireUnaryRealization.bit carrier false observation)
      (WireUnaryRealization.bit carrier true observation)) labels
    (CausalBound.levels (.empty : Program 1 0) labels) ≤ _
  cases low : WireUnaryRealization.bit carrier false observation <;>
    cases high : WireUnaryRealization.bit carrier true observation
  · exact Nat.zero_le _
  · apply input_label_le_of_bit_ne carrier labels observation
    rw [low, high]
    decide
  · exact Nat.zero_le _
  · exact Nat.zero_le _

theorem one_implementation_bound (carrier : WireCarrier 1 outputs fields)
    (labels : Fin 1 → Nat) (observation : Fin (outputs + fields)) :
    CausalBound.outputLevel
        (WireUnaryRealization.oneImplementation carrier).candidate labels observation ≤
      CausalBound.outputLevel carrier.exposed.candidate labels observation := by
  unfold CausalBound.outputLevel WireUnaryRealization.oneImplementation
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_pointwise]
  change CausalBound.source
    (WireUnaryRealization.oneSource (WireUnaryRealization.bit carrier false observation)
      (WireUnaryRealization.bit carrier true observation)) labels
    (CausalBound.levels notProgram labels) ≤ _
  cases low : WireUnaryRealization.bit carrier false observation <;>
    cases high : WireUnaryRealization.bit carrier true observation
  · exact Nat.zero_le _
  · apply input_label_le_of_bit_ne carrier labels observation
    rw [low, high]
    decide
  · change max (labels fin1Zero) (labels fin1Zero) ≤ _
    rw [Nat.max_self]
    apply input_label_le_of_bit_ne carrier labels observation
    rw [low, high]
    decide
  · exact Nat.zero_le _

theorem implementation_output_bound (carrier : WireCarrier 1 outputs fields)
    (labels : Fin 1 → Nat) (observation : Fin (outputs + fields)) :
    CausalBound.outputLevel
        (WireUnaryRealization.implementation carrier).candidate labels observation ≤
      CausalBound.outputLevel carrier.exposed.candidate labels observation := by
  cases needed : WireUnaryRealization.needsNegation carrier with
  | false =>
      unfold WireUnaryRealization.implementation
      rw [needed]
      exact zero_implementation_bound carrier labels observation
  | true =>
      unfold WireUnaryRealization.implementation
      rw [needed]
      exact one_implementation_bound carrier labels observation

theorem realize_causalBounds (carrier : WireCarrier 1 outputs fields)
    (labels : Fin 1 → Nat) :
    (WireUnaryRealization.realize carrier).CausalBounds labels
      (CausalBound.outputLevel carrier.implementation.candidate labels)
      (carrier.fieldLevel labels) := by
  have exposedBound (observation : Fin (outputs + fields)) :
      CausalBound.outputLevel (WireUnaryRealization.realize carrier).exposed.candidate
          labels observation ≤
        CausalBound.outputLevel carrier.exposed.candidate labels observation := by
    unfold WireUnaryRealization.realize
    rw [WireCarrier.exposed_unpack]
    exact implementation_output_bound carrier labels observation
  constructor
  · intro output
    simpa only [WireCarrier.exposed_output_level] using
      exposedBound (Fin.castAdd fields output)
  · intro field
    simpa only [WireCarrier.exposed_field_level] using
      exposedBound (Fin.natAdd outputs field)

variable {inputs width : Nat}

theorem constantWord_output_bound (original : Implementation 0 width)
    (labels : Fin 0 → Nat) (output : Fin width) :
    CausalBound.outputLevel (WireUnaryFrontier.constantWord original).candidate labels output ≤
      CausalBound.outputLevel original.candidate labels output := by
  unfold WireUnaryFrontier.constantWord CausalBound.outputLevel
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_pointwise]
  exact Nat.zero_le _

theorem unaryCarrier_output_level (original : Implementation 1 width)
    (labels : Fin 1 → Nat) (output : Fin width) :
    CausalBound.outputLevel (WireUnaryFrontier.unaryCarrier original).implementation.candidate
        labels output =
      CausalBound.outputLevel original.candidate labels output := by
  unfold WireUnaryFrontier.unaryCarrier WireCarrier.unpack CausalBound.outputLevel
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_pointwise]
  rfl

theorem unaryWord_output_bound (original : Implementation 1 width)
    (labels : Fin 1 → Nat) (output : Fin width) :
    CausalBound.outputLevel (WireUnaryFrontier.unaryWord original).candidate labels output ≤
      CausalBound.outputLevel original.candidate labels output := by
  simpa only [WireUnaryFrontier.unaryWord, unaryCarrier_output_level] using
    (realize_causalBounds (WireUnaryFrontier.unaryCarrier original) labels).1 output

theorem localWord_output_bound (original : Implementation inputs width)
    (small : inputs ≤ 1) (labels : Fin inputs → Nat) (output : Fin width) :
    CausalBound.outputLevel (WireUnaryFrontier.localWord original small).candidate
        labels output ≤
      CausalBound.outputLevel original.candidate labels output := by
  cases inputs with
  | zero => exact constantWord_output_bound original labels output
  | succ inputs =>
      cases inputs with
      | zero => exact unaryWord_output_bound original labels output
      | succ inputs => omega

theorem arbitrary_replacement_output_bound (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1)
    (labels : Fin (WireUnaryArbitrarySupport.pulled carrier records).boundary.length → Nat)
    (output : Fin (WireUnaryArbitrarySupport.pulled carrier records).interface.length) :
    CausalBound.outputLevel
        (WireUnaryArbitrarySupport.replacement carrier records small).candidate labels output ≤
      CausalBound.outputLevel
        (WireUnaryArbitrarySupport.pulled carrier records).extractedCandidate labels output :=
  localWord_output_bound
    (WireUnaryArbitrarySupport.pulled carrier records).extractedCandidate.toImplementation
    small labels output

variable (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))

private theorem option_get_spec {alpha : Type} (value : Option alpha)
    (present : value.isSome = true) : value = some (value.get present) := by
  cases value with
  | none => cases present
  | some item => rfl

/-- The R7 record is precisely the computed compiler output. -/
theorem compiled_spec
    (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1) :
    ArbitrarySupportSplice.compile carrier.exposed.candidate records
        (WireUnaryArbitrarySupport.replacement carrier records small).candidate =
      some (WireUnaryArbitrarySupport.compiled carrier records small) :=
  option_get_spec _ (WireUnaryArbitrarySupport.compile_isSome carrier records small)

/-- Extraction and the literal unary constructor derive every interface cap. -/
theorem replacement_dependency_bound
    (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1)
    (labels : Fin inputs → Nat) :
    ArbitrarySupportSplice.DependencyInterfaceBound carrier.exposed.candidate records
      (WireUnaryArbitrarySupport.replacement carrier records small).candidate labels := by
  intro port
  have localBound := arbitrary_replacement_output_bound carrier records small
    (ArbitrarySupportSplice.dependencyBoundaryLabels carrier.exposed.candidate records labels) port
  have originalBound := extractTerminalSupport_causal_levels carrier.exposed.candidate
    records labels port
  exact Nat.le_trans localBound originalBound

/-- The actual one-copy R7 splice cannot add any observation dependency. -/
theorem expanded_exposed_bound
    (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1)
    (labels : Fin inputs → Nat) (observation : Fin (outputs + fields)) :
    CausalBound.outputLevel (WireUnaryArbitrarySupport.expanded carrier records small).exposed.candidate
        labels observation ≤
      CausalBound.outputLevel carrier.exposed.candidate labels observation := by
  unfold WireUnaryArbitrarySupport.expanded WireCarrier.spliceResult
  rw [WireCarrier.exposed_unpack]
  exact ArbitrarySupportSplice.result_output_dependency_bound carrier.exposed.candidate records
    (WireUnaryArbitrarySupport.replacement carrier records small).candidate labels
    (replacement_dependency_bound carrier records small labels)
    (WireUnaryArbitrarySupport.compiled carrier records small)
    (compiled_spec carrier records small) observation

/-- Whole-carrier bounds are derived from source data and boundary recognition alone. -/
theorem expanded_causalBounds
    (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1)
    (labels : Fin inputs → Nat) :
    (WireUnaryArbitrarySupport.expanded carrier records small).CausalBounds labels
      (CausalBound.outputLevel carrier.implementation.candidate labels)
      (carrier.fieldLevel labels) := by
  constructor
  · intro output
    simpa only [WireCarrier.exposed_output_level] using
      expanded_exposed_bound carrier records small labels (Fin.castAdd fields output)
  · intro field
    simpa only [WireCarrier.exposed_field_level] using
      expanded_exposed_bound carrier records small labels (Fin.natAdd outputs field)

/-- A successful executable R7 attempt preserves all original dependency bounds. -/
theorem attempt_causalBounds (realized : WireCarrier inputs outputs fields)
    (accepted : WireUnaryArbitrarySupport.attempt carrier records = some realized)
    (labels : Fin inputs → Nat) :
    realized.CausalBounds labels
      (CausalBound.outputLevel carrier.implementation.candidate labels)
      (carrier.fieldLevel labels) := by
  unfold WireUnaryArbitrarySupport.attempt at accepted
  split at accepted
  · rename_i small
    cases accepted
    exact expanded_causalBounds carrier records small labels
  · cases accepted


end PNP.DirectWire.WireUnaryCausalBound
