import PNP.Concrete.ResidualReduction.SourceNativeSystemInput

/-! Physical polynomial-time compilation of the complete native-system
conversion. Literal parsing, counters, byte ordering, copying and output
packing are included. The surrounding native-packet variants and composition
with normalization and history reduction remain separate obligations. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemPolynomial
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceNativeSystemInput (answer sourceFuel)

def program : Program 24 := SourceNativeSystemInput.block.program 0 8
private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0,SourceNativeSystemState.initial input⟩ := rfl

theorem source_result (input : BitString) :
    ∃ after : Store 24, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted,after⟩ ∧ after.get 8 = answer input := by
  let after := SourceNativeSystemState.work (SourceNativeSystemParse.result input).stream
    (answer input) (SourceNativeSystemParse.result input)
  have run : BitRegister.run program (SourceNativeSystemInput.fuel input + 1)
      (BitRegister.initial program input) = ⟨.accepted,after⟩ := by
    rw [initial_eq]
    exact (SourceNativeSystemInput.block_exec input).program_run 0 8
  have enough : SourceNativeSystemInput.fuel input + 1 ≤ sourceFuel.eval input.length := by
    rw [SourceNativeSystemInput.sourceFuel_eval]
    exact Nat.add_le_add_right (SourceNativeSystemInput.fuel_bound input) 1
  have slack : sourceFuel.eval input.length =
      (SourceNativeSystemInput.fuel input + 1) +
        (sourceFuel.eval input.length - (SourceNativeSystemInput.fuel input + 1)) := by omega
  refine ⟨after,?_,rfl⟩
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
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 24 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem output_projection (input : BitString) : polynomial.output input =
    (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = answer input := by
  rw [output_projection,CompilerIO.compilePolynomial_output]
  exact source_output input

theorem polynomial_canonical {c : Nat} (D : NativeSparseSystem.System c) :
    polynomial.output (natural c ++ (NativeSystemCodec.systemCodec c).encode D) =
      SourceNativeEncoding.familyPacket D := by
  rw [polynomial_output,SourceNativeSystemInput.canonical_answer]

theorem history_input_canonical {c : Nat} (D : NativeSparseSystem.System c) :
    polynomial.output (natural c ++ (NativeSystemCodec.systemCodec c).encode D) =
      SourceHistoryEncoding.packet (NativeSource.family D) := by
  rw [polynomial_canonical,SourceNativeEncoding.family_packet]

theorem rejects_trailing {c : Nat} (D : NativeSparseSystem.System c)
    (suffix : BitString) (extra : suffix ≠ []) :
    polynomial.output (natural c ++ ((NativeSystemCodec.systemCodec c).encode D ++ suffix)) = [false] := by
  rw [polynomial_output,SourceNativeSystemInput.canonical_extra D suffix extra]

theorem output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

theorem machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 24 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

end PNP.Concrete.ResidualReduction.SourceNativeSystemPolynomial
