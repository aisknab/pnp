import PNP.Concrete.ResidualReduction.SourceReplayEndpointGenerated
import PNP.Concrete.ResidualReduction.SourceReductionInputEncoding
import PNP.Concrete.ResidualReduction.SourceMatrixEncoding

/-! Original-source size accounting for the physical replay endpoint.
The request includes the complete generated history and a dimension-bounded
witness. Its byte length and the actual refined-machine fuel are bounded by
polynomials in the source-family encoding, or in the original normalizer input.
This does not construct a terminal model or package a new request-building
machine; it closes the size-substitution boundary for the replay machine. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointBudget
open PNP.Concrete PNP.Concrete.NativeNormalization
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceReplayEndpointGenerated (recoverRequest projectRequest)

theorem request_length (request : SourceReplayRequest.Request) :
    (SourceReplayRequest.codec.encode request).length =
      request.dimension + 2 * request.data.length + 2 * request.witness.length + 4 := by
  change ([request.recover] ++ (natural request.dimension ++
    ((natural request.data.length ++ encodeSeq bitCodec.encode request.data) ++
      (natural request.witness.length ++ encodeSeq bitCodec.encode request.witness)))).length = _
  rw [SourceReplayEndpointOutput.bit_sequence,SourceReplayEndpointOutput.bit_sequence]
  simp only [List.length_append,List.length_cons,List.length_nil,natural_length]
  omega

def requestPolynomial : NatPolynomial :=
  .add (.add (.mul (.constant 3) .variable)
    (.mul (.constant 2) (SourceEncoding.dataPolynomial .variable .variable))) (.constant 4)

theorem family_request_bound (n : Nat) (F : Family n) (recover : Bool) (witness : BitString)
    (width : witness.length ≤ n) :
    (SourceReplayRequest.codec.encode
      ⟨recover,n,SourceEncoding.dataCodec.encode (SourceEncoding.toData (reduce n F)),witness⟩).length ≤
        requestPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  have dimension := SourceMatrixEncoding.dimension_bound n F
  have rows := SourceMatrixEncoding.rowCount_bound n F
  have storage := Nat.le_trans (SourceEncoding.reduce_encoded_bound n F)
    (SourceEncoding.dataBound_mono dimension rows)
  rw [request_length]
  simp only [requestPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_mul,
    NatPolynomial.eval_constant,NatPolynomial.eval_variable,SourceEncoding.dataPolynomial_eval]
  omega

theorem recover_request_bound (n : Nat) (F : Family n) (z : Point (reduce n F).dimension) :
    (SourceReplayRequest.codec.encode (recoverRequest n F z)).length ≤
      requestPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  have accounting := reduce_dimension_accounting n F
  apply family_request_bound n F true
  rw [SourceEncoding.point_length]
  omega

theorem project_request_bound (n : Nat) (F : Family n) (x : Point n) :
    (SourceReplayRequest.codec.encode (projectRequest n F x)).length ≤
      requestPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  apply family_request_bound n F false
  exact Nat.le_of_eq (SourceEncoding.point_length x)

def nativeRequestPolynomial : NatPolynomial :=
  .add (.mul (.constant 5) SourceEncoding.sourceOutputPolynomial) (.constant 4)

theorem native_request_bound (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (packet : NativeSerializedNormalizer.packet input = .system c D)
    (recover : Bool) (witness : BitString) (width : witness.length ≤ 2 * c) :
    (SourceReplayRequest.codec.encode
      ⟨recover,2 * c,SourceEncoding.dataCodec.encode
        (SourceEncoding.toData (reduce (2 * c) (NativeSource.family D))),witness⟩).length ≤
      nativeRequestPolynomial.eval input.length := by
  have storage := SourceEncoding.source_encoded_bound input
  simp only [SourceEncoding.sourceEncode,packet,SourceEncoding.encodeNativePacket,
    List.length_append,List.length_cons,List.length_nil,natural_length] at storage
  rw [request_length]
  simp only [nativeRequestPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_mul,NatPolynomial.eval_constant]
  omega

theorem native_recover_request_bound (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (packet : NativeSerializedNormalizer.packet input = .system c D)
    (z : Point (reduce (2 * c) (NativeSource.family D)).dimension) :
    (SourceReplayRequest.codec.encode (recoverRequest (2 * c) (NativeSource.family D) z)).length ≤
      nativeRequestPolynomial.eval input.length := by
  have accounting := reduce_dimension_accounting (2 * c) (NativeSource.family D)
  apply native_request_bound input c D packet true
  rw [SourceEncoding.point_length]
  omega

theorem native_project_request_bound (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (packet : NativeSerializedNormalizer.packet input = .system c D) (x : Point (2 * c)) :
    (SourceReplayRequest.codec.encode (projectRequest (2 * c) (NativeSource.family D) x)).length ≤
      nativeRequestPolynomial.eval input.length := by
  apply native_request_bound input c D packet false
  exact Nat.le_of_eq (SourceEncoding.point_length x)

def runtimePolynomial : NatPolynomial :=
  NatPolynomial.substitute SourceReplayEndpointPolynomial.rawRefinement.timeBound requestPolynomial
def nativeRuntimePolynomial : NatPolynomial :=
  NatPolynomial.substitute SourceReplayEndpointPolynomial.rawRefinement.timeBound nativeRequestPolynomial

private theorem runtime_bound (request : BitString) (size : Nat) (bound : request.length ≤ requestPolynomial.eval size) :
    SourceReplayEndpointPolynomial.rawRefinement.timeBound.eval (BitString.size request) ≤
      runtimePolynomial.eval size := by
  rw [runtimePolynomial,NatPolynomial.eval_substitute]
  exact NatPolynomial.eval_mono _ bound
private theorem native_runtime_bound (request : BitString) (size : Nat)
    (bound : request.length ≤ nativeRequestPolynomial.eval size) :
    SourceReplayEndpointPolynomial.rawRefinement.timeBound.eval (BitString.size request) ≤
      nativeRuntimePolynomial.eval size := by
  rw [nativeRuntimePolynomial,NatPolynomial.eval_substitute]
  exact NatPolynomial.eval_mono _ bound

theorem recover_run (n : Nat) (F : Family n) (z : Point (reduce n F).dimension) :
    ∃ steps ≤ runtimePolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length,
      boundedDecide SourceReplayEndpointPolynomial.rawRefinement.machine steps
        (SourceReplayRequest.codec.encode (recoverRequest n F z)) ≠ .timeout ∧
      machineOutput SourceReplayEndpointPolynomial.rawRefinement.machine steps
        (SourceReplayRequest.codec.encode (recoverRequest n F z)) =
          SourceReplayEndpointOutput.codec.encode (some (NativeSource.pointBytes ((reduce n F).lift z))) := by
  refine ⟨_,runtime_bound _ _ (recover_request_bound n F z),?_,
    SourceReplayEndpointGenerated.machine_recover_generated n F z⟩
  exact SourceReplayEndpointPolynomial.rawRefinement.haltsWithin _
    (SourceReplayEndpointPolynomial.polynomial.haltsWithin _)

theorem project_run (n : Nat) (F : Family n) (x : Point n) :
    ∃ steps ≤ runtimePolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length,
      boundedDecide SourceReplayEndpointPolynomial.rawRefinement.machine steps
        (SourceReplayRequest.codec.encode (projectRequest n F x)) ≠ .timeout ∧
      machineOutput SourceReplayEndpointPolynomial.rawRefinement.machine steps
        (SourceReplayRequest.codec.encode (projectRequest n F x)) =
          SourceReplayEndpointOutput.codec.encode
            (some ((SourceEncoding.pointCodec (reduce n F).dimension).encode ((reduce n F).project x))) := by
  refine ⟨_,runtime_bound _ _ (project_request_bound n F x),?_,
    SourceReplayEndpointGenerated.machine_project_generated n F x⟩
  exact SourceReplayEndpointPolynomial.rawRefinement.haltsWithin _
    (SourceReplayEndpointPolynomial.polynomial.haltsWithin _)

theorem native_recover_run (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (packet : NativeSerializedNormalizer.packet input = .system c D)
    (z : Point (reduce (2 * c) (NativeSource.family D)).dimension) :
    ∃ steps ≤ nativeRuntimePolynomial.eval input.length,
      boundedDecide SourceReplayEndpointPolynomial.rawRefinement.machine steps
        (SourceReplayRequest.codec.encode (recoverRequest (2 * c) (NativeSource.family D) z)) ≠ .timeout ∧
      machineOutput SourceReplayEndpointPolynomial.rawRefinement.machine steps
        (SourceReplayRequest.codec.encode (recoverRequest (2 * c) (NativeSource.family D) z)) =
          SourceReplayEndpointOutput.codec.encode
            (some (NativeSource.pointBytes ((reduce (2 * c) (NativeSource.family D)).lift z))) := by
  refine ⟨_,native_runtime_bound _ _ (native_recover_request_bound input c D packet z),?_,
    SourceReplayEndpointGenerated.machine_recover_generated (2 * c) (NativeSource.family D) z⟩
  exact SourceReplayEndpointPolynomial.rawRefinement.haltsWithin _
    (SourceReplayEndpointPolynomial.polynomial.haltsWithin _)

theorem native_project_run (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (packet : NativeSerializedNormalizer.packet input = .system c D) (x : Point (2 * c)) :
    ∃ steps ≤ nativeRuntimePolynomial.eval input.length,
      boundedDecide SourceReplayEndpointPolynomial.rawRefinement.machine steps
        (SourceReplayRequest.codec.encode (projectRequest (2 * c) (NativeSource.family D) x)) ≠ .timeout ∧
      machineOutput SourceReplayEndpointPolynomial.rawRefinement.machine steps
        (SourceReplayRequest.codec.encode (projectRequest (2 * c) (NativeSource.family D) x)) =
          SourceReplayEndpointOutput.codec.encode
            (some ((SourceEncoding.pointCodec (reduce (2 * c) (NativeSource.family D)).dimension).encode
              ((reduce (2 * c) (NativeSource.family D)).project x))) := by
  refine ⟨_,native_runtime_bound _ _ (native_project_request_bound input c D packet x),?_,
    SourceReplayEndpointGenerated.machine_project_generated (2 * c) (NativeSource.family D) x⟩
  exact SourceReplayEndpointPolynomial.rawRefinement.haltsWithin _
    (SourceReplayEndpointPolynomial.polynomial.haltsWithin _)

end PNP.Concrete.ResidualReduction.SourceReplayEndpointBudget
