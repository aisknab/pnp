/-
Copyright (c) 2026 PNP Labs.

Raw recoding reuses the existing multi-output NAND candidate codec. Width
checks and the existing elaborator establish both actual programs; the recoding
executor then computes inverse and causal evidence. No new circuit format,
correctness premise, ownership map or charge total is supplied by the caller.

This input boundary does not establish global successful search, full
manuscript profiles or polynomial runtime/certificate-size bounds.
-/

import PNP.Concrete.LockedNANDEncoding
import PNP.NANDWireRecodingState

namespace PNP.DirectWire.WireRecodingInput

open Concrete.LockedNAND (RawCandidate PackedCandidate)
open WireObligationHistory (State)

variable {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}

/-- Reindex only after both dimensions have been checked. -/
def atWidth (fields : Nat) (packed : PackedCandidate)
    (inputAt : packed.inputCount = fields) (outputAt : packed.outputCount = fields) :
    Implementation fields fields := by
  rcases packed with ⟨inputCount, gateCount, outputCount, candidate⟩
  dsimp only at inputAt outputAt
  cases inputAt
  cases outputAt
  exact ⟨gateCount, candidate⟩

/-- The established elaborator rejects all bad coordinates and forward references. -/
def decode (fields : Nat) (raw : RawCandidate) : Option (Implementation fields fields) :=
  match raw.elaborate with
  | none => none
  | some packed =>
      if inputAt : packed.inputCount = fields then
        if outputAt : packed.outputCount = fields then
          some (atWidth fields packed inputAt outputAt)
        else none
      else none

theorem decode_encode (implementation : Implementation fields fields) :
    decode fields (RawCandidate.ofCandidate implementation.candidate) = some implementation := by
  unfold decode
  rw [RawCandidate.elaborate_ofCandidate]
  simp only
  rfl

theorem decode_elaboration_none (raw : RawCandidate) (invalid : raw.elaborate = none) :
    decode fields raw = none := by
  unfold decode
  rw [invalid]

theorem decode_success_iff (raw : RawCandidate) :
    (∃ implementation, decode fields raw = some implementation) ↔
      ∃ packed, raw.elaborate = some packed ∧
        packed.inputCount = fields ∧ packed.outputCount = fields := by
  constructor
  · rintro ⟨implementation, accepted⟩
    unfold decode at accepted
    split at accepted
    · cases accepted
    · rename_i packed elaborated
      split at accepted
      · rename_i inputAt
        split at accepted
        · rename_i outputAt
          exact ⟨packed, elaborated, inputAt, outputAt⟩
        · cases accepted
      · cases accepted
  · rintro ⟨packed, elaborated, inputAt, outputAt⟩
    refine ⟨atWidth fields packed inputAt outputAt, ?_⟩
    unfold decode
    rw [elaborated]
    simp only [dif_pos inputAt, dif_pos outputAt]

/-- Bind the literal input to both elaborated programs and the actual checked run. -/
structure Receipt (before : State source) (rawEncoder rawDecoder : RawCandidate) : Type where
  encoder : Implementation fields fields
  decoder : Implementation fields fields
  encoderAt : decode fields rawEncoder = some encoder
  decoderAt : decode fields rawDecoder = some decoder
  checked : WireRecodingState.Receipt before encoder decoder

def Receipt.next {before : State source} {rawEncoder rawDecoder : RawCandidate}
    (receipt : Receipt before rawEncoder rawDecoder) : State source :=
  receipt.checked.next

def Receipt.charged {before : State source} {rawEncoder rawDecoder : RawCandidate}
    (receipt : Receipt before rawEncoder rawDecoder) : Nat :=
  receipt.encoder.gateCount + receipt.decoder.gateCount

def Receipt.removed {before : State source} {rawEncoder rawDecoder : RawCandidate}
    (receipt : Receipt before rawEncoder rawDecoder) : Nat :=
  WireCarrierRecoding.removed before.current receipt.encoder receipt.decoder

def execute (before : State source) (rawEncoder rawDecoder : RawCandidate) :
    Option (Receipt before rawEncoder rawDecoder) :=
  match encoderAt : decode fields rawEncoder with
  | none => none
  | some encoder =>
      match decoderAt : decode fields rawDecoder with
      | none => none
      | some decoder =>
          match WireRecodingState.execute before encoder decoder with
          | none => none
          | some checked => some ⟨encoder, decoder, encoderAt, decoderAt, checked⟩

theorem execute_success_iff (before : State source) (rawEncoder rawDecoder : RawCandidate) :
    (∃ receipt, execute before rawEncoder rawDecoder = some receipt) ↔
      ∃ encoder decoder, decode fields rawEncoder = some encoder ∧
        decode fields rawDecoder = some decoder ∧
        WireCarrierRecoding.check encoder decoder = true ∧
        before.current.dependencyGuard
          (WireCarrierRecoding.result before.current encoder decoder) = true := by
  constructor
  · rintro ⟨receipt, _accepted⟩
    exact ⟨receipt.encoder, receipt.decoder, receipt.encoderAt, receipt.decoderAt,
      (WireCarrierRecoding.check_iff _ _).2
        ⟨receipt.checked.inverse.decode_encode, receipt.checked.inverse.encode_decode⟩,
      receipt.checked.causal⟩
  · rintro ⟨encoder, decoder, encoderAt, decoderAt, inverse, causal⟩
    obtain ⟨checked, checkedAt⟩ :=
      (WireRecodingState.execute_success_iff before encoder decoder).2 ⟨inverse, causal⟩
    refine ⟨⟨encoder, decoder, encoderAt, decoderAt, checked⟩, ?_⟩
    unfold execute
    split
    · rename_i rejected
      have impossible := rejected.symm.trans encoderAt
      cases impossible
    · rename_i actualEncoder actualEncoderAt
      have sameEncoder : actualEncoder = encoder :=
        Option.some.inj (actualEncoderAt.symm.trans encoderAt)
      cases sameEncoder
      split
      · rename_i rejected
        have impossible := rejected.symm.trans decoderAt
        cases impossible
      · rename_i actualDecoder actualDecoderAt
        have sameDecoder : actualDecoder = decoder :=
          Option.some.inj (actualDecoderAt.symm.trans decoderAt)
        cases sameDecoder
        rw [checkedAt]

theorem execute_encoder_none (before : State source) (rawEncoder rawDecoder : RawCandidate)
    (invalid : decode fields rawEncoder = none) :
    execute before rawEncoder rawDecoder = none := by
  unfold execute
  split
  · rfl
  · rename_i encoder encoderAt
    have impossible := invalid.symm.trans encoderAt
    cases impossible

theorem execute_decoder_none (before : State source) (rawEncoder rawDecoder : RawCandidate)
    (invalid : decode fields rawDecoder = none) :
    execute before rawEncoder rawDecoder = none := by
  unfold execute
  split
  · rfl
  · split
    · rfl
    · rename_i decoder decoderAt
      have impossible := invalid.symm.trans decoderAt
      cases impossible

theorem Receipt.pending {before : State source} {rawEncoder rawDecoder : RawCandidate}
    (receipt : Receipt before rawEncoder rawDecoder) :
    receipt.next.pending = before.pending := rfl

theorem Receipt.charged_eq {before : State source} {rawEncoder rawDecoder : RawCandidate}
    (receipt : Receipt before rawEncoder rawDecoder) :
    receipt.next.charged = before.charged + receipt.charged :=
  Nat.add_assoc before.charged receipt.encoder.gateCount receipt.decoder.gateCount

theorem Receipt.removed_eq {before : State source} {rawEncoder rawDecoder : RawCandidate}
    (receipt : Receipt before rawEncoder rawDecoder) :
    receipt.next.removed = before.removed + receipt.removed := rfl

theorem Receipt.causalInvariant {before : State source} {rawEncoder rawDecoder : RawCandidate}
    (receipt : Receipt before rawEncoder rawDecoder) (labels : Fin inputs → Nat)
    (bounded : before.CausalInvariant labels) : receipt.next.CausalInvariant labels :=
  receipt.checked.causalInvariant labels bounded

end PNP.DirectWire.WireRecodingInput
