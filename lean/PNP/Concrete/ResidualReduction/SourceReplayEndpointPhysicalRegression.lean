import PNP.Concrete.ResidualReduction.SourceReplayEndpointBudget
import Lean

/-! Focused physical-refinement, source-size and source-generated witness
contracts. The unchanged literal parsing/replay/serialization suites are not
imported or rerun. Kernel examples quantify over arbitrary raw inputs and
families; the complete new public theorem set is checked for unexpected axioms. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointPhysicalRegression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NativeNormalization
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceReplayEndpointPolynomial (program sourceFuel polynomial rawRefinement)
open PNP.Concrete.ResidualReduction.SourceReplayEndpointGenerated (readAnswer recoverRequest projectRequest)

example : polynomial.program =
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 40 sourceFuel) :=
  SourceReplayEndpointPolynomial.polynomial_program
example (input : BitString) :
    SourceReplayEndpointClosed.fuel input + 1 ≤ sourceFuel.eval input.length :=
  SourceReplayEndpointPolynomial.fuel_bound input
example (input : BitString) :
    CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted,SourceReplayEndpointClosed.result input⟩ :=
  SourceReplayEndpointPolynomial.source_result input
example : CompilerIO.AcceptsWithin program sourceFuel := SourceReplayEndpointPolynomial.acceptsWithin
example (input : BitString) :
    polynomial.output input = SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.answer input) :=
  SourceReplayEndpointPolynomial.polynomial_output input
example (input : BitString) :
    SourceReplayEndpointOutput.codec.decode (polynomial.output input) = some (SourceReplayRequest.answer input) :=
  SourceReplayEndpointPolynomial.polynomial_decoded input
example (input : BitString) : (polynomial.output input).length ≤ 2 * input.length + 2 :=
  SourceReplayEndpointPolynomial.output_length input
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 40 sourceFuel).eval input.length) input = .accept :=
  SourceReplayEndpointPolynomial.machine_accepts input
example (input : BitString) :
    machineOutput rawRefinement.machine (rawRefinement.timeBound.eval (BitString.size input)) input =
      SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.answer input) :=
  SourceReplayEndpointPolynomial.machine_output input
example (input : BitString) (bad : SourceReplayRequest.codec.decode input = none) :
    polynomial.output input = SourceReplayEndpointOutput.codec.encode none :=
  SourceReplayEndpointPolynomial.malformed input bad
example : polynomial.output [] = SourceReplayEndpointOutput.codec.encode none :=
  SourceReplayEndpointPolynomial.malformed [] rfl
example (request : SourceReplayRequest.Request) : readAnswer request = SourceReplayRequest.evaluate request :=
  SourceReplayEndpointGenerated.readAnswer_eq request
example (n : Nat) (F : Family n) (z : Point (reduce n F).dimension)
    (model : models (reduce n F).core z = true) :
    ∃ x : Point n, polynomial.output (SourceReplayRequest.codec.encode (recoverRequest n F z)) =
      SourceReplayEndpointOutput.codec.encode (some (NativeSource.pointBytes x)) ∧ models F x = true :=
  SourceReplayEndpointGenerated.recover_model n F z model
example (n : Nat) (F : Family n) (x : Point n) (model : models F x = true) :
    (readAnswer (projectRequest n F x)).bind (fun witness =>
      readAnswer ⟨true,n,SourceEncoding.dataCodec.encode (SourceEncoding.toData (reduce n F)),witness⟩) =
        some (NativeSource.pointBytes x) :=
  SourceReplayEndpointGenerated.project_recover_model n F x model
example (request : SourceReplayRequest.Request) :
    (SourceReplayRequest.codec.encode request).length =
      request.dimension + 2 * request.data.length + 2 * request.witness.length + 4 :=
  SourceReplayEndpointBudget.request_length request
example (n : Nat) (F : Family n) (z : Point (reduce n F).dimension) :
    ∃ steps ≤ SourceReplayEndpointBudget.runtimePolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length,
      boundedDecide rawRefinement.machine steps (SourceReplayRequest.codec.encode (recoverRequest n F z)) ≠ .timeout ∧
      machineOutput rawRefinement.machine steps (SourceReplayRequest.codec.encode (recoverRequest n F z)) =
        SourceReplayEndpointOutput.codec.encode (some (NativeSource.pointBytes ((reduce n F).lift z))) :=
  SourceReplayEndpointBudget.recover_run n F z
example (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (packet : NativeSerializedNormalizer.packet input = .system c D) (x : Point (2 * c)) :
    ∃ steps ≤ SourceReplayEndpointBudget.nativeRuntimePolynomial.eval input.length,
      boundedDecide rawRefinement.machine steps
        (SourceReplayRequest.codec.encode (projectRequest (2 * c) (NativeSource.family D) x)) ≠ .timeout ∧
      machineOutput rawRefinement.machine steps
        (SourceReplayRequest.codec.encode (projectRequest (2 * c) (NativeSource.family D) x)) =
          SourceReplayEndpointOutput.codec.encode
            (some ((SourceEncoding.pointCodec (reduce (2 * c) (NativeSource.family D)).dimension).encode
              ((reduce (2 * c) (NativeSource.family D)).project x))) :=
  SourceReplayEndpointBudget.native_project_run input c D packet x
example : sourceFuel.eval 0 = 381 := by decide
example : sourceFuel.eval 1 = 1782 := by decide
example : sourceFuel.eval 2 = 4485 := by decide

run_cmd do
  let names := [
    ``SourceReplayEndpointPolynomial.sourceFuel_eval,
    ``SourceReplayEndpointPolynomial.fuel_bound,
    ``SourceReplayEndpointPolynomial.source_result,
    ``SourceReplayEndpointPolynomial.acceptsWithin,
    ``SourceReplayEndpointPolynomial.source_output,
    ``SourceReplayEndpointPolynomial.polynomial_program,
    ``SourceReplayEndpointPolynomial.polynomial_output,
    ``SourceReplayEndpointPolynomial.polynomial_decoded,
    ``SourceReplayEndpointPolynomial.polynomial_canonical,
    ``SourceReplayEndpointPolynomial.malformed,
    ``SourceReplayEndpointPolynomial.output_length,
    ``SourceReplayEndpointPolynomial.machine_accepts,
    ``SourceReplayEndpointPolynomial.machine_output,
    ``SourceReplayEndpointPolynomial.machine_decoded,
    ``SourceReplayEndpointPolynomial.machine_output_length,
    ``SourceReplayEndpointGenerated.readAnswer_eq,
    ``SourceReplayEndpointGenerated.recover_generated,
    ``SourceReplayEndpointGenerated.project_generated,
    ``SourceReplayEndpointGenerated.recover_generated_result,
    ``SourceReplayEndpointGenerated.project_generated_result,
    ``SourceReplayEndpointGenerated.recover_model,
    ``SourceReplayEndpointGenerated.project_recover_model,
    ``SourceReplayEndpointGenerated.machine_recover_generated,
    ``SourceReplayEndpointGenerated.machine_project_generated,
    ``SourceReplayEndpointBudget.request_length,
    ``SourceReplayEndpointBudget.family_request_bound,
    ``SourceReplayEndpointBudget.recover_request_bound,
    ``SourceReplayEndpointBudget.project_request_bound,
    ``SourceReplayEndpointBudget.native_request_bound,
    ``SourceReplayEndpointBudget.native_recover_request_bound,
    ``SourceReplayEndpointBudget.native_project_request_bound,
    ``SourceReplayEndpointBudget.recover_run,
    ``SourceReplayEndpointBudget.project_run,
    ``SourceReplayEndpointBudget.native_recover_run,
    ``SourceReplayEndpointBudget.native_project_run]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"REPLAY_ENDPOINT_PHYSICAL_AXIOMS_GREEN: {names.length} declarations"

run_cmd Lean.logInfo "REPLAY_ENDPOINT_PHYSICAL_REGRESSIONS_GREEN: 20 kernel examples; all-input physical runtime, source-generated maps and original-source bounds; unchanged literal suites not rerun"

end PNP.Concrete.ResidualReduction.SourceReplayEndpointPhysicalRegression
