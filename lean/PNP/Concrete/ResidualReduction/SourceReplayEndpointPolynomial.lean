import PNP.Concrete.ResidualReduction.SourceReplayEndpointClosed
import PNP.Concrete.BitRegisterCompilerIOPolynomial
import PNP.Concrete.PipelineRefinement

/-! Physical polynomial-time implementation of the complete serialized replay
endpoint. The source budget includes the final accepting instruction; the
existing compiler charges register copies and both physical input/output
adapters. Machine acceptance means a returned encoded answer, not that replay
succeeded: the answer may be the canonical none tag. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointPolynomial
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec

private def historyFuel : NatPolynomial :=
  .add (.add (.mul (.mul (.constant 32) .variable) .variable)
    (.mul (.constant 153) .variable)) (.constant 387)
private def traversalFuel : NatPolynomial :=
  .add (.add (.add (.mul (.mul (.constant 50) .variable) .variable)
    (.mul (.constant 228) .variable)) (.mul (.constant 4) (.mul (.constant 2) .variable))) (.constant 411)
def sourceFuel : NatPolynomial :=
  .add (.add (.add (.add (.mul .variable (.add historyFuel traversalFuel))
    (.mul (.add (.mul (.constant 16) .variable) (.constant 36)) .variable))
    (.mul (.constant 80) .variable)) (.constant 380)) (.constant 1)

theorem sourceFuel_eval (length : Nat) :
    sourceFuel.eval length = length * (SourceReplayHistoryStack.allowance length +
      SourceReplayLoopMachine.allowance length (2 * length)) +
      (16 * length + 36) * length + 80 * length + 380 + 1 := rfl

theorem fuel_bound (input : BitString) :
    SourceReplayEndpointClosed.fuel input + 1 ≤ sourceFuel.eval input.length := by
  rw [sourceFuel_eval]
  have checked := SourceReplayEndpointClosed.fuel_bound input
  omega

def program : Program 40 := SourceReplayEndpointClosed.program
private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0,SourceReplayEndpointState.initial input⟩ := rfl

theorem source_result (input : BitString) :
    CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted,SourceReplayEndpointClosed.result input⟩ := by
  have run : BitRegister.run program (SourceReplayEndpointClosed.fuel input + 1)
      (BitRegister.initial program input) = ⟨.accepted,SourceReplayEndpointClosed.result input⟩ := by
    rw [initial_eq]
    exact (SourceReplayEndpointClosed.block_exec input).program_run 0 8
  have bound := fuel_bound input
  have slack : sourceFuel.eval input.length = (SourceReplayEndpointClosed.fuel input + 1) +
      (sourceFuel.eval input.length - (SourceReplayEndpointClosed.fuel input + 1)) := by omega
  unfold CompilerIO.sourceResult
  rw [slack,BitRegister.run_add,run,BitRegister.run_accepted]

theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  rw [source_result]

theorem source_output (input : BitString) :
    (CompilerIO.sourceResult program (sourceFuel.eval input.length) input).store.get 8 =
      SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.answer input) := by
  rw [source_result]
  exact SourceReplayEndpointClosed.output_eq input

def polynomial : PolynomialTimeFunction := CompilerIO.compilePolynomial program sourceFuel acceptsWithin
theorem polynomial_program : polynomial.program =
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 40 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem output_projection (input : BitString) : polynomial.output input =
    (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl

theorem polynomial_output (input : BitString) :
    polynomial.output input = SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.answer input) := by
  rw [output_projection,CompilerIO.compilePolynomial_output]
  exact source_output input

theorem polynomial_decoded (input : BitString) :
    SourceReplayEndpointOutput.codec.decode (polynomial.output input) = some (SourceReplayRequest.answer input) := by
  rw [polynomial_output]
  exact decode_encode _ _

theorem polynomial_canonical (request : SourceReplayRequest.Request) :
    polynomial.output (SourceReplayRequest.codec.encode request) =
      SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.evaluate request) := by
  rw [polynomial_output,SourceReplayRequest.answer_canonical]

theorem malformed (input : BitString) (bad : SourceReplayRequest.codec.decode input = none) :
    polynomial.output input = SourceReplayEndpointOutput.codec.encode none := by
  rw [polynomial_output,SourceReplayRequest.malformed input bad]

theorem output_length (input : BitString) :
    (polynomial.output input).length ≤ 2 * input.length + 2 := by
  rw [polynomial_output,← SourceReplayEndpointClosed.output_eq]
  exact SourceReplayEndpointClosed.output_size_bound input

theorem machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 40 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

def rawRefinement : FunctionProgram.RawRefinement polynomial.program := by
  rw [polynomial_program]
  exact FunctionProgram.RawRefinement.ofMachine (CompilerIO.rawMachine program)
    (CompilerIO.runtimePolynomial 40 sourceFuel)

theorem machine_output (input : BitString) :
    machineOutput rawRefinement.machine
      (rawRefinement.timeBound.eval (BitString.size input)) input =
        SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.answer input) :=
  (rawRefinement.output_eq input (polynomial.haltsWithin input)).trans (polynomial_output input)

theorem machine_decoded (input : BitString) :
    SourceReplayEndpointOutput.codec.decode
      (machineOutput rawRefinement.machine (rawRefinement.timeBound.eval (BitString.size input)) input) =
        some (SourceReplayRequest.answer input) := by
  rw [machine_output]
  exact decode_encode _ _

theorem machine_output_length (input : BitString) :
    (machineOutput rawRefinement.machine (rawRefinement.timeBound.eval (BitString.size input)) input).length ≤
      2 * input.length + 2 := by
  rw [machine_output,← SourceReplayEndpointClosed.output_eq]
  exact SourceReplayEndpointClosed.output_size_bound input

end PNP.Concrete.ResidualReduction.SourceReplayEndpointPolynomial
