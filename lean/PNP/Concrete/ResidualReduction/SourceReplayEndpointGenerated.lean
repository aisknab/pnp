import PNP.Concrete.ResidualReduction.SourceReplayEndpointPolynomial

/-! Source-generated semantic linkage for the physical replay endpoint.
The history is constructed by reduce, never supplied as correctness authority.
A terminal model can be lifted and an original model survives project/recover.
These witness maps do not find a terminal model or solve a stopped core. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointGenerated
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceEncoding (pointCodec)

/-- Decode the actual machine-produced optional answer. This is an observation
of the compiled endpoint, not an executable callback in its finite program. -/
def readAnswer (request : SourceReplayRequest.Request) : Option BitString :=
  (SourceReplayEndpointOutput.codec.decode
    (SourceReplayEndpointPolynomial.polynomial.output (SourceReplayRequest.codec.encode request))).join

theorem readAnswer_eq (request : SourceReplayRequest.Request) :
    readAnswer request = SourceReplayRequest.evaluate request := by
  rw [readAnswer,SourceReplayEndpointPolynomial.polynomial_canonical,NativeNormalization.NativeBitCodec.decode_encode]
  rfl

def recoverRequest (n : Nat) (F : Family n) (z : Point (reduce n F).dimension) :
    SourceReplayRequest.Request :=
  ⟨true,n,SourceEncoding.dataCodec.encode (SourceEncoding.toData (reduce n F)),
    (pointCodec (reduce n F).dimension).encode z⟩
def projectRequest (n : Nat) (F : Family n) (x : Point n) : SourceReplayRequest.Request :=
  ⟨false,n,SourceEncoding.dataCodec.encode (SourceEncoding.toData (reduce n F)),(pointCodec n).encode x⟩

theorem recover_generated (n : Nat) (F : Family n) (z : Point (reduce n F).dimension) :
    SourceReplayEndpointPolynomial.polynomial.output (SourceReplayRequest.codec.encode (recoverRequest n F z)) =
      SourceReplayEndpointOutput.codec.encode (some (NativeSource.pointBytes ((reduce n F).lift z))) := by
  rw [SourceReplayEndpointPolynomial.polynomial_canonical]
  exact congrArg SourceReplayEndpointOutput.codec.encode (SourceEncoding.recover_reduce n F z)

theorem project_generated (n : Nat) (F : Family n) (x : Point n) :
    SourceReplayEndpointPolynomial.polynomial.output (SourceReplayRequest.codec.encode (projectRequest n F x)) =
      SourceReplayEndpointOutput.codec.encode
        (some ((pointCodec (reduce n F).dimension).encode ((reduce n F).project x))) := by
  rw [SourceReplayEndpointPolynomial.polynomial_canonical]
  exact congrArg SourceReplayEndpointOutput.codec.encode (SourceEncoding.project_reduce n F x)

theorem recover_generated_result (n : Nat) (F : Family n) (z : Point (reduce n F).dimension) :
    readAnswer (recoverRequest n F z) = some (NativeSource.pointBytes ((reduce n F).lift z)) := by
  rw [readAnswer_eq]
  exact SourceEncoding.recover_reduce n F z

theorem project_generated_result (n : Nat) (F : Family n) (x : Point n) :
    readAnswer (projectRequest n F x) =
      some ((pointCodec (reduce n F).dimension).encode ((reduce n F).project x)) := by
  rw [readAnswer_eq]
  exact SourceEncoding.project_reduce n F x

theorem recover_model (n : Nat) (F : Family n) (z : Point (reduce n F).dimension)
    (model : models (reduce n F).core z = true) :
    ∃ x : Point n,
      SourceReplayEndpointPolynomial.polynomial.output (SourceReplayRequest.codec.encode (recoverRequest n F z)) =
        SourceReplayEndpointOutput.codec.encode (some (NativeSource.pointBytes x)) ∧
      models F x = true := by
  exact ⟨(reduce n F).lift z,recover_generated n F z,(reduce_model_map n F z).symm.trans model⟩

theorem project_recover_model (n : Nat) (F : Family n) (x : Point n) (model : models F x = true) :
    (readAnswer (projectRequest n F x)).bind (fun witness =>
      readAnswer ⟨true,n,SourceEncoding.dataCodec.encode (SourceEncoding.toData (reduce n F)),witness⟩) =
        some (NativeSource.pointBytes x) := by
  simp only [readAnswer_eq,projectRequest,SourceReplayRequest.evaluate,Bool.false_eq_true,↓reduceIte]
  exact SourceEncoding.recover_project_model n F x model

theorem machine_recover_generated (n : Nat) (F : Family n) (z : Point (reduce n F).dimension) :
    machineOutput SourceReplayEndpointPolynomial.rawRefinement.machine
      (SourceReplayEndpointPolynomial.rawRefinement.timeBound.eval
        (BitString.size (SourceReplayRequest.codec.encode (recoverRequest n F z))))
      (SourceReplayRequest.codec.encode (recoverRequest n F z)) =
        SourceReplayEndpointOutput.codec.encode (some (NativeSource.pointBytes ((reduce n F).lift z))) :=
  (SourceReplayEndpointPolynomial.rawRefinement.output_eq _
    (SourceReplayEndpointPolynomial.polynomial.haltsWithin _)).trans (recover_generated n F z)

theorem machine_project_generated (n : Nat) (F : Family n) (x : Point n) :
    machineOutput SourceReplayEndpointPolynomial.rawRefinement.machine
      (SourceReplayEndpointPolynomial.rawRefinement.timeBound.eval
        (BitString.size (SourceReplayRequest.codec.encode (projectRequest n F x))))
      (SourceReplayRequest.codec.encode (projectRequest n F x)) =
        SourceReplayEndpointOutput.codec.encode
          (some ((pointCodec (reduce n F).dimension).encode ((reduce n F).project x))) :=
  (SourceReplayEndpointPolynomial.rawRefinement.output_eq _
    (SourceReplayEndpointPolynomial.polynomial.haltsWithin _)).trans (project_generated n F x)

end PNP.Concrete.ResidualReduction.SourceReplayEndpointGenerated
