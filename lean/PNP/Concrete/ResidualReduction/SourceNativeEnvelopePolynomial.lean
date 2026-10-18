import PNP.Concrete.ResidualReduction.SourceNativeEnvelopeInput
import PNP.Concrete.PipelineRefinement

/-! Physical finite-machine implementation of native-packet reduction.
The closed source bound is compiled with register copies and all input/output
adapters charged. Canonical packets retain their exact original dimension. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeEnvelopePolynomial
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NativeNormalization
open PNP.Concrete.ResidualReduction.SourceNativeEnvelopeInput (answer sourceFuel)

def program : Program 64 := SourceNativeEnvelopeInput.block.program 0 8
private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0,SourceNativeEnvelopeState.initial input⟩ := rfl

theorem source_result (input : BitString) :
    ∃ after : Store 64, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted,after⟩ ∧ after.get 8 = answer input := by
  obtain ⟨used,after,checked,bound,output⟩ := SourceNativeEnvelopeInput.block_exec input
  have run : BitRegister.run program (used + 1) (BitRegister.initial program input) = ⟨.accepted,after⟩ := by
    rw [initial_eq]
    exact checked.program_run 0 8
  have slack : sourceFuel.eval input.length = (used + 1) + (sourceFuel.eval input.length - (used + 1)) := by omega
  refine ⟨after,?_,output⟩
  unfold CompilerIO.sourceResult
  rw [slack,BitRegister.run_add,run,BitRegister.run_accepted]

theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  obtain ⟨after,run,_⟩ := source_result input
  rw [run]
theorem source_output (input : BitString) :
    (CompilerIO.sourceResult program (sourceFuel.eval input.length) input).store.get 8 = answer input := by
  obtain ⟨after,run,output⟩ := source_result input
  rw [run]
  exact output

def polynomial : PolynomialTimeFunction := CompilerIO.compilePolynomial program sourceFuel acceptsWithin
theorem polynomial_program : polynomial.program =
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 64 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem output_projection (input : BitString) : polynomial.output input =
    (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = answer input := by
  rw [output_projection,CompilerIO.compilePolynomial_output]
  exact source_output input
theorem polynomial_canonical (packet : NativeOutputPacket.Packet) :
    polynomial.output (NativeOutputPacket.encode packet) = SourceEncoding.encodeNativePacket packet := by
  rw [polynomial_output,SourceNativeEnvelopeInput.canonical_answer]
theorem output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input
theorem machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 64 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

def rawRefinement : FunctionProgram.RawRefinement polynomial.program := by
  rw [polynomial_program]
  exact FunctionProgram.RawRefinement.ofMachine (CompilerIO.rawMachine program)
    (CompilerIO.runtimePolynomial 64 sourceFuel)
theorem machine_output (input : BitString) :
    machineOutput rawRefinement.machine
      (rawRefinement.timeBound.eval (BitString.size input)) input = answer input :=
  (rawRefinement.output_eq input (polynomial.haltsWithin input)).trans (polynomial_output input)

end PNP.Concrete.ResidualReduction.SourceNativeEnvelopePolynomial
