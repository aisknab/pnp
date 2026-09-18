/-
Copyright (c) 2026 PNP Labs.

Finite carrier recoding uses two actual NAND programs. Their two-way inverse
equations are checked over complete finite input tuples, never supplied as
observer functions. Encoding and decoding allocate their real gates; physical
normalization supplies the two deletion counts.

This computational construction is not the full manuscript profile, an
arbitrary-support causal or ownership transport, complete R2/N3, a globally
successful strategy, or a polynomial-time checker. The inverse check enumerates
all field valuations and earns no polynomial-runtime credit.
-/

import PNP.NANDWireCarrier

namespace PNP.DirectWire.WireCarrierRecoding

variable {inputs outputs fields mappedFields : Nat}

/-- A single inverse equation, checked at every input tuple and field. -/
def roundTripCheck (encoder decoder : Implementation fields fields) : Bool :=
  allTrue (allBoolTuples fields) fun input =>
    allTrue (allFin fields) fun field =>
      boolEqual
        (decoder.candidate.semantics
          (encoder.candidate.semantics input.toValuation) field)
        (input.toValuation field)

theorem roundTripCheck_iff (encoder decoder : Implementation fields fields) :
    roundTripCheck encoder decoder = true ↔
      ∀ valuation field,
        decoder.candidate.semantics
          (encoder.candidate.semantics valuation) field = valuation field := by
  constructor
  · intro checked valuation field
    have tupleChecked := allTrue_sound checked
      (mem_allBoolTuples (BoolTuple.ofFn valuation))
    have fieldChecked := allTrue_sound tupleChecked (mem_allFin field)
    have same : (BoolTuple.ofFn valuation).toValuation = valuation :=
      funext (BoolTuple.toValuation_ofFn valuation)
    simpa only [same] using (boolEqual_eq_true_iff _ _).1 fieldChecked
  · intro inverse
    apply allTrue_complete
    intro tuple _member
    apply allTrue_complete
    intro field _member
    exact (boolEqual_eq_true_iff _ _).2 (inverse tuple.toValuation field)

/-- Both directions are checked; no quotient-only agreement is accepted. -/
def check (encoder decoder : Implementation fields fields) : Bool :=
  roundTripCheck encoder decoder && roundTripCheck decoder encoder

theorem check_iff (encoder decoder : Implementation fields fields) :
    check encoder decoder = true ↔
      (∀ valuation field, decoder.candidate.semantics
        (encoder.candidate.semantics valuation) field = valuation field) ∧
      (∀ valuation field, encoder.candidate.semantics
        (decoder.candidate.semantics valuation) field = valuation field) := by
  simp only [check, Bool.and_eq_true, roundTripCheck_iff]

/-- Evidence computed from the literal encoder and decoder, not a raw input. -/
structure Checked (encoder decoder : Implementation fields fields) : Type where
  decode_encode : ∀ valuation field, decoder.candidate.semantics
    (encoder.candidate.semantics valuation) field = valuation field
  encode_decode : ∀ valuation field, encoder.candidate.semantics
    (decoder.candidate.semantics valuation) field = valuation field

def compile (encoder decoder : Implementation fields fields) :
    Option (Checked encoder decoder) :=
  if accepted : check encoder decoder = true then
    some ⟨((check_iff encoder decoder).1 accepted).1,
      ((check_iff encoder decoder).1 accepted).2⟩
  else none

theorem compile_success_iff (encoder decoder : Implementation fields fields) :
    (∃ checked, compile encoder decoder = some checked) ↔
      check encoder decoder = true := by
  constructor
  · rintro ⟨checked, _found⟩
    exact (check_iff encoder decoder).2
      ⟨checked.decode_encode, checked.encode_decode⟩
  · intro accepted
    refine ⟨⟨((check_iff encoder decoder).1 accepted).1,
      ((check_iff encoder decoder).1 accepted).2⟩, ?_⟩
    simp only [compile, dif_pos accepted]

/-- Append a real NAND map, binding its inputs to the actual ordered fields. -/
def appendMap (carrier : WireCarrier inputs outputs fields)
    (mapping : Implementation fields mappedFields) :
    WireCarrier inputs outputs mappedFields :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (carrier.implementation.candidate.program.appendSubstituted
          carrier.source mapping.candidate.program)
        ⟨fun output =>
          (carrier.implementation.candidate.directWireWord.source output).weakenGates
            mapping.gateCount⟩).toImplementation
    source := fun field =>
      (mapping.candidate.directWireWord.source field).substituteInputs carrier.source }

theorem appendMap_gateCount (carrier : WireCarrier inputs outputs fields)
    (mapping : Implementation fields mappedFields) :
    (appendMap carrier mapping).implementation.gateCount =
      carrier.implementation.gateCount + mapping.gateCount := rfl

theorem appendMap_output (carrier : WireCarrier inputs outputs fields)
    (mapping : Implementation fields mappedFields)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (appendMap carrier mapping).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output := by
  unfold appendMap
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_semantics]
  unfold semantics DirectWireWord.eval
  rw [Source.eval_weakenGates]
  exact (carrier.implementation.candidate.directWireWord.source output).eval_congr
    (fun _ => rfl)
    (fun gate => Program.eval_appendSubstituted_prefix
      carrier.implementation.candidate.program carrier.source
      mapping.candidate.program valuation gate)

theorem appendMap_field (carrier : WireCarrier inputs outputs fields)
    (mapping : Implementation fields mappedFields)
    (valuation : Valuation inputs) (field : Fin mappedFields) :
    (appendMap carrier mapping).fieldValue valuation field =
      mapping.candidate.semantics (carrier.fieldValue valuation) field := by
  unfold appendMap WireCarrier.fieldValue
  dsimp only [Candidate.toImplementation]
  rw [Source.eval_substituteInputs]
  apply (mapping.candidate.directWireWord.source field).eval_congr
  · intro index
    exact (carrier.source index).eval_congr (fun _ => rfl)
      (fun gate => Program.eval_appendSubstituted_prefix
        carrier.implementation.candidate.program carrier.source
        mapping.candidate.program valuation gate)
  · intro gate
    exact Program.eval_appendSubstituted_suffix
      carrier.implementation.candidate.program carrier.source
      mapping.candidate.program valuation gate

/-- Normalize with every encoded field visible, not just ordinary outputs. -/
def encoded (carrier : WireCarrier inputs outputs fields)
    (encoder : Implementation fields fields) : WireCarrier inputs outputs fields :=
  (appendMap carrier encoder).normalize

theorem encoded_output (carrier : WireCarrier inputs outputs fields)
    (encoder : Implementation fields fields)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (encoded carrier encoder).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  ((appendMap carrier encoder).normalize_output valuation output).trans
    (appendMap_output carrier encoder valuation output)

theorem encoded_field (carrier : WireCarrier inputs outputs fields)
    (encoder : Implementation fields fields)
    (valuation : Valuation inputs) (field : Fin fields) :
    (encoded carrier encoder).fieldValue valuation field =
      encoder.candidate.semantics (carrier.fieldValue valuation) field :=
  ((appendMap carrier encoder).normalize_field valuation field).trans
    (appendMap_field carrier encoder valuation field)

/-- The decoder is physically appended after the actual normalized encoding. -/
def expanded (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) : WireCarrier inputs outputs fields :=
  appendMap (encoded carrier encoder) decoder

/-- Re-establish the original field representation and normalize its real word. -/
def result (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) : WireCarrier inputs outputs fields :=
  (expanded carrier encoder decoder).normalize

/-- Actual deletion counts of the two physical normalization runs. -/
def removed (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) : Nat :=
  (runPhysicalNormalization (appendMap carrier encoder).exposed).trace.savedGates +
    (runPhysicalNormalization (expanded carrier encoder decoder).exposed).trace.savedGates

theorem result_output (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (result carrier encoder decoder).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  ((expanded carrier encoder decoder).normalize_output valuation output).trans
    ((appendMap_output (encoded carrier encoder) decoder valuation output).trans
      (encoded_output carrier encoder valuation output))

theorem result_field (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) (checked : Checked encoder decoder)
    (valuation : Valuation inputs) (field : Fin fields) :
    (result carrier encoder decoder).fieldValue valuation field =
      carrier.fieldValue valuation field := by
  apply ((expanded carrier encoder decoder).normalize_field valuation field).trans
  apply (appendMap_field (encoded carrier encoder) decoder valuation field).trans
  apply (decoder.candidate.semantics_input_congr
    (fun coordinate => encoded_field carrier encoder valuation coordinate) field).trans
  exact checked.decode_encode (carrier.fieldValue valuation) field

/-- Every appended gate is charged; both deletion counts come from execution. -/
theorem result_gate_balance (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) :
    (result carrier encoder decoder).implementation.gateCount +
        removed carrier encoder decoder =
      carrier.implementation.gateCount + encoder.gateCount + decoder.gateCount := by
  have first := (appendMap carrier encoder).normalize_exact_accounting
  have second := (expanded carrier encoder decoder).normalize_exact_accounting
  have encodeSize := appendMap_gateCount carrier encoder
  have decodeSize : (expanded carrier encoder decoder).implementation.gateCount =
      (encoded carrier encoder).implementation.gateCount + decoder.gateCount := rfl
  change (encoded carrier encoder).implementation.gateCount +
      (runPhysicalNormalization (appendMap carrier encoder).exposed).trace.savedGates =
        (appendMap carrier encoder).implementation.gateCount at first
  change (result carrier encoder decoder).implementation.gateCount +
      (runPhysicalNormalization (expanded carrier encoder decoder).exposed).trace.savedGates =
        (expanded carrier encoder decoder).implementation.gateCount at second
  unfold removed
  omega

end PNP.DirectWire.WireCarrierRecoding
