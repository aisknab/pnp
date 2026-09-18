import PNP.NANDWireRecodingInput

namespace PNP.DirectWire.WireRecodingInput.Regression

open Concrete.LockedNAND (RawCandidate)

def identity (width : Nat) : Implementation width width :=
  (Candidate.ofDirectWireWord (.empty : Program width 0)
    ⟨fun field => .input field⟩).toImplementation

def negation : Implementation 1 1 :=
  (Candidate.ofDirectWireWord
    ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
    (⟨fun _ => .gate 0⟩ : DirectWireWord 1 1 1)).toImplementation

def direct : WireCarrier 1 1 1 :=
  { implementation := identity 1, source := fun index => .input index }

def empty : WireCarrier 0 0 0 :=
  { implementation := identity 0, source := Fin.elim0 }

def rawIdentity : RawCandidate := RawCandidate.ofCandidate (identity 1).candidate
def rawNegation : RawCandidate := RawCandidate.ofCandidate negation.candidate

example {fields : Nat} (implementation : Implementation fields fields) :
    decode fields (RawCandidate.ofCandidate implementation.candidate) = some implementation :=
  decode_encode implementation

example {fields : Nat} (raw : RawCandidate) :
    (∃ implementation, decode fields raw = some implementation) ↔
      ∃ packed, raw.elaborate = some packed ∧
        packed.inputCount = fields ∧ packed.outputCount = fields :=
  decode_success_iff raw

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {before : WireObligationHistory.State source} {encoder decoder : RawCandidate}
    (receipt : Receipt before encoder decoder) :
    receipt.next.pending = before.pending := receipt.pending

#print axioms PNP.DirectWire.WireRecodingInput.decode_encode
#print axioms PNP.DirectWire.WireRecodingInput.decode_elaboration_none
#print axioms PNP.DirectWire.WireRecodingInput.decode_success_iff
#print axioms PNP.DirectWire.WireRecodingInput.execute_success_iff
#print axioms PNP.DirectWire.WireRecodingInput.execute_encoder_none
#print axioms PNP.DirectWire.WireRecodingInput.execute_decoder_none
#print axioms PNP.DirectWire.WireRecodingInput.Receipt.pending
#print axioms PNP.DirectWire.WireRecodingInput.Receipt.charged_eq
#print axioms PNP.DirectWire.WireRecodingInput.Receipt.removed_eq
#print axioms PNP.DirectWire.WireRecodingInput.Receipt.causalInvariant

-- These executions test the raw boundary; the general equalities above are proof authority.
#eval show IO Unit from do
  let before := WireObligationHistory.State.initial direct
  let malformed : List RawCandidate :=
    [ { rawIdentity with inputCount := 2 }
    , { rawIdentity with outputs := [.input 0, .input 0] }
    , { rawIdentity with outputs := [] }
    , { rawIdentity with outputs := [.input 1] }
    , { rawIdentity with outputs := [.gate 0] }
    , { rawNegation with gates := [⟨.gate 0, .input 0⟩] }
    , { rawNegation with gates := [⟨.input 0, .gate 1⟩] }
    , { rawNegation with gates := rawNegation.gates ++ [⟨.gate 8, .input 0⟩] } ]
  for bad in malformed do
    if (decode 1 bad).isSome then
      throw (IO.userError "a malformed or wrong-width raw recoder decoded")
    if (execute before bad rawIdentity).isSome ||
        (execute before rawIdentity bad).isSome then
      throw (IO.userError "a malformed raw pair escaped full decoding")
  match decode 1 rawNegation with
  | none => throw (IO.userError "the existing raw format failed valid elaboration")
  | some decoded =>
      if decoded.gateCount != 1 then
        throw (IO.userError "raw elaboration changed the literal gate count")
      for tuple in allBoolTuples 1 do
        if decoded.candidate.semantics tuple.toValuation 0 !=
            negation.candidate.semantics tuple.toValuation 0 then
          throw (IO.userError "raw elaboration changed the candidate")
  if (execute before rawIdentity rawNegation).isSome then
    throw (IO.userError "raw decoding bypassed the actual inverse check")
  match execute before rawNegation rawNegation with
  | none => throw (IO.userError "a valid raw reversible pair was rejected")
  | some receipt =>
      if receipt.charged != 2 then
        throw (IO.userError "raw receipt did not charge both literal programs")
      if receipt.next.current.fieldValue (fun _ => true) 0 != true ||
          receipt.next.current.fieldValue (fun _ => false) 0 != false then
        throw (IO.userError "raw recoding failed the original field representation")
  let pending := before.create 2718 (0 : Fin 1) rfl
  match execute pending rawIdentity rawIdentity with
  | none => throw (IO.userError "a raw identity pair rejected an open snapshot")
  | some receipt =>
      let creationID := (receipt.next.pending (0 : Fin 1)).map (fun snapshot => snapshot.identity)
      if creationID != some 2718 then
        throw (IO.userError "raw recoding changed the pending snapshot identity")
  let rawEmpty := RawCandidate.ofCandidate (identity 0).candidate
  if !(execute (WireObligationHistory.State.initial empty) rawEmpty rawEmpty).isSome then
    throw (IO.userError "raw empty dimensions failed")
  IO.println "RECODING_RAW_INPUT_RUNTIME_PASSED"

end PNP.DirectWire.WireRecodingInput.Regression
