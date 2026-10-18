import PNP.Concrete.ResidualReduction.SourceHistoryRaw

/-! One concrete polynomial-time machine computes the entire linked reduction
history from an arbitrary source-family packet. The bound includes physical
word copies. This neither solves a positive-dimensional stopped core nor
completes the separate native-source wrapper. -/

namespace PNP.Concrete.ResidualReduction.SourceHistoryPolynomial
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceHistoryEncoding
open PNP.Concrete.ResidualReduction.SourceHistoryRaw (answer canonicalAnswer outputCodec sourceFuel)

def program : Program 63 := SourceHistoryRaw.block.program 0 8
private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0,SourceHistoryState.initial input⟩ := rfl

theorem source_result (input : BitString) :
    ∃ after : Store 63, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted,after⟩ ∧ after.get 8 = answer input := by
  obtain ⟨used,after,checked,bound,output⟩ := SourceHistoryRaw.block_exec input
  have run : BitRegister.run program (used + 1) (BitRegister.initial program input) = ⟨.accepted,after⟩ := by
    rw [initial_eq]
    exact checked.program_run 0 8
  have enough : used + 1 ≤ sourceFuel.eval input.length := by
    rw [SourceHistoryRaw.sourceFuel_eval]
    omega
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
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 63 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem output_projection (input : BitString) : polynomial.output input =
    (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = answer input := by
  rw [output_projection,CompilerIO.compilePolynomial_output]
  exact source_output input

theorem polynomial_canonical (n : Nat) (F : Family n) :
    polynomial.output (packet F) =
      outputCodec.encode (some (SourceEncoding.toData (SourceChain.reduce n F))) := by
  rw [polynomial_output,SourceHistoryRaw.answer_canonical]
  rfl
theorem polynomial_malformed (input : BitString) (h : SourceMatrixEncoding.codec.decode input = none) :
    polynomial.output input = [false] := by
  rw [polynomial_output,SourceHistoryRaw.answer_malformed input h]
theorem exact_decoded_result (n : Nat) (F : Family n) :
    outputCodec.decode (polynomial.output (packet F)) =
      some (some (SourceEncoding.toData (SourceChain.reduce n F))) := by
  rw [polynomial_canonical]
  exact decode_encode _ _

theorem result_eq (n : Nat) (F : Family n) (r : SourceEncoding.ReductionData)
    (decoded : outputCodec.decode (polynomial.output (packet F)) = some (some r)) :
    r = SourceEncoding.toData (SourceChain.reduce n F) := by
  rw [exact_decoded_result] at decoded
  exact (Option.some.inj (Option.some.inj decoded)).symm
theorem history_linked (n : Nat) (F : Family n) (r : SourceEncoding.ReductionData)
    (decoded : outputCodec.decode (polynomial.output (packet F)) = some (some r)) :
    SourceChain.Linked F r.history r.core := by
  rw [result_eq n F r decoded]
  exact SourceChain.reduce_trace_linked n F
theorem terminal (n : Nat) (F : Family n) (r : SourceEncoding.ReductionData)
    (decoded : outputCodec.decode (polynomial.output (packet F)) = some (some r)) :
    SourceChain.stopped r.core := by
  rw [result_eq n F r decoded]
  exact SourceChain.reduce_terminal n F
theorem dimension_accounting (n : Nat) (F : Family n) (r : SourceEncoding.ReductionData)
    (decoded : outputCodec.decode (polynomial.output (packet F)) = some (some r)) :
    r.history.length + r.dimension = n := by
  rw [result_eq n F r decoded]
  exact SourceChain.reduce_dimension_accounting n F
theorem row_count (n : Nat) (F : Family n) (r : SourceEncoding.ReductionData)
    (decoded : outputCodec.decode (polynomial.output (packet F)) = some (some r)) :
    r.core.length = F.length := by
  rw [result_eq n F r decoded]
  exact SourceChain.reduce_row_count n F

def outputPolynomial : NatPolynomial :=
  .add (SourceEncoding.dataPolynomial .variable .variable) (.constant 1)
theorem canonical_output_bound (n : Nat) (F : Family n) :
    (canonicalAnswer n F).length ≤ outputPolynomial.eval (packet F).length := by
  have storage := SourceEncoding.reduce_encoded_bound n F
  have monotone := SourceEncoding.dataBound_mono (SourceMatrixEncoding.dimension_bound n F)
    (SourceMatrixEncoding.rowCount_bound n F)
  have bound := Nat.le_trans storage monotone
  change (SourceEncoding.dataCodec.encode (SourceEncoding.toData (SourceChain.reduce n F))).length + 1 ≤ _
  simp only [outputPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_constant,
    SourceEncoding.dataPolynomial_eval,NatPolynomial.eval_variable]
  exact Nat.add_le_add_right bound 1

theorem polynomial_output_bound (input : BitString) :
    (polynomial.output input).length ≤ outputPolynomial.eval input.length := by
  rw [polynomial_output]
  cases decoded : SourceMatrixEncoding.codec.decode input with
  | none =>
    rw [SourceHistoryRaw.answer_malformed input decoded]
    simp only [List.length_cons,List.length_nil,outputPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_constant]
    omega
  | some problem =>
    rcases problem with ⟨n,F⟩
    have bytes := (SourceMatrixEncoding.canonical input ⟨n,F⟩).mp decoded
    change packet F = input at bytes
    rw [← bytes,SourceHistoryRaw.answer_canonical]
    exact canonical_output_bound n F

theorem polynomial_machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 63 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

end PNP.Concrete.ResidualReduction.SourceHistoryPolynomial
