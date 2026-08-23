/-
Copyright (c) 2026 PNP Labs.

The exact encoded source and target languages for the locked-NAND reduction.
This module first fixes the semantic transformation independently of its
finite work-machine implementation.  Malformed inputs map to the empty word,
which is not an encoded target instance.
-/

import PNP.Concrete.Complexity
import PNP.Concrete.LockedNANDEncoding

namespace PNP
namespace Concrete
namespace LockedNAND

open DirectWire
open DirectWire.LockedNANDTrace
open DirectWire.LockedNANDGlobalCandidates

/-- Decode, validate, normalize, and intrinsically elaborate one external
NAND circuit. -/
def decodeElaboratedCircuit (bits : BitString) : Option PackedCircuit :=
  match decodeCircuit bits with
  | none => none
  | some raw => raw.elaborate

theorem decodeElaboratedCircuit_encodeCircuit_ofCircuit
    {inputs : Nat} (circuit : Circuit inputs) :
    decodeElaboratedCircuit
        (encodeCircuit (RawCircuit.ofCircuit circuit)) =
      some { inputCount := inputs, circuit := circuit } := by
  simp [decodeElaboratedCircuit, decodeCircuit_encodeCircuit,
    RawCircuit.elaborate_ofCircuit]

/-- The concrete source language: exactly the valid external NAND circuits
whose normalized intrinsic circuit is satisfiable. -/
def EncodedNANDSAT : Language := fun bits =>
  match decodeElaboratedCircuit bits with
  | none => False
  | some packed => packed.circuit.Satisfiable

/-- Decode one complete direct-wire candidate and ask the already-defined
exhaustive semantic reference minimum whether it crosses the encoded
threshold.  The actual gate list is elaborated and measured; no descriptor or
caller-supplied semantic certificate is accepted.  This is a language
specification, not a claim that the exhaustive reference computation runs in
polynomial time. -/
def EncodedDirectWireMinimumThreshold : Language := fun bits =>
  match decodeLockedInstance bits with
  | none => False
  | some raw =>
      match raw.elaborate with
      | none => False
      | some packed =>
          packed.baseline + 1 ≤
            referenceMinimum
              (Implementation.mk packed.gateCount packed.candidate)

/-- The locked-NAND target uses the general encoded direct-wire exact-minimum
threshold query.  Locked-shape correctness belongs to the source builder, not
to a second target-language descriptor or premise. -/
def EncodedLockedNANDThreshold : Language :=
  EncodedDirectWireMinimumThreshold

/-- Canonical encoding and intrinsic elaboration expose the exact semantic
threshold for every finite typed direct-wire candidate. -/
theorem encodedDirectWireMinimumThreshold_ofCandidate_iff
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (threshold : Nat) :
    EncodedDirectWireMinimumThreshold
        (encodeLockedInstance
          (RawLockedInstance.ofCandidate candidate threshold)) ↔
      threshold + 1 ≤
        referenceMinimum (Implementation.mk gates candidate) := by
  simp [EncodedDirectWireMinimumThreshold,
    decodeLockedInstance_encodeLockedInstance,
    RawLockedInstance.elaborate_ofCandidate]

/-- The pure specification of the builder.  The successful branch emits the
complete full candidate and exact source-derived baseline. -/
def buildLockedNANDInstance (bits : BitString) : BitString :=
  match decodeElaboratedCircuit bits with
  | none => []
  | some packed =>
      encodeLockedInstance (lockedInstanceOfCircuit packed.circuit)

theorem buildLockedNANDInstance_of_decoded
    (bits : BitString) (packed : PackedCircuit)
    (decoded : decodeElaboratedCircuit bits = some packed) :
    buildLockedNANDInstance bits =
      encodeLockedInstance (lockedInstanceOfCircuit packed.circuit) := by
  simp [buildLockedNANDInstance, decoded]

theorem buildLockedNANDInstance_of_malformed
    (bits : BitString)
    (malformed : decodeElaboratedCircuit bits = none) :
    buildLockedNANDInstance bits = [] := by
  simp [buildLockedNANDInstance, malformed]

theorem empty_not_encodedLockedNANDThreshold :
    ¬ EncodedLockedNANDThreshold [] := by
  simp [EncodedLockedNANDThreshold, EncodedDirectWireMinimumThreshold,
    decodeLockedInstance, decodeTokens, decodeLockedInstanceTokens]

theorem encoded_fullCandidate_threshold_iff_satisfiable
    {inputs : Nat} (circuit : Circuit inputs) :
    EncodedLockedNANDThreshold
        (encodeLockedInstance (lockedInstanceOfCircuit circuit)) ↔
      circuit.Satisfiable := by
  rw [fullCandidate_satisfiable_iff_referenceMinimum_ge_succ]
  simp [EncodedLockedNANDThreshold, EncodedDirectWireMinimumThreshold,
    decodeLockedInstance_encodeLockedInstance,
    lockedInstanceOfCircuit,
    RawLockedInstance.elaborate_ofCandidate]

/-- Exact semantic correctness of the external transformation on every
bitstring, including fail-closed malformed inputs. -/
theorem buildLockedNANDInstance_correct (bits : BitString) :
    EncodedNANDSAT bits ↔
      EncodedLockedNANDThreshold (buildLockedNANDInstance bits) := by
  cases decoded : decodeElaboratedCircuit bits with
  | none =>
      simp [EncodedNANDSAT, decoded,
        buildLockedNANDInstance_of_malformed bits decoded,
        empty_not_encodedLockedNANDThreshold]
  | some packed =>
      rw [buildLockedNANDInstance_of_decoded bits packed decoded]
      simpa [EncodedNANDSAT, decoded] using
        (encoded_fullCandidate_threshold_iff_satisfiable packed.circuit).symm

end LockedNAND
end Concrete
end PNP
