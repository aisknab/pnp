import PNP.Concrete.ResidualReduction.SourceAffineRawQuery

/-! A literal finite machine for one complete source-derived affine query.
The polynomial bound uses the original encoded input length and includes
parsing, matrix construction, solving, every candidate search, serialization
and the raw compiler's word-copying and input/output costs. This is one query,
not the complete contraction loop, global ZeroSlack or a SAT algorithm. -/

namespace PNP.Concrete.ResidualReduction.SourcePolynomialAffineQuery
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding

def program : Program 22 := SourceAffineRawQuery.block.program 0 8

def matrixLengthPolynomial : NatPolynomial :=
  .add (.add (.add .variable (.constant 1))
    (.add (.mul .variable .variable) (.constant 1)))
    (.mul (.add .variable (.constant 1)) (.mul .variable .variable))
theorem matrixLengthPolynomial_eval (L : Nat) :
    matrixLengthPolynomial.eval L = SourceAffineRawQuery.matrixLength L := rfl

def directionPolynomial : NatPolynomial :=
  .add (.mul (.add (.mul
    (.add (.add (.mul (.constant 9) .variable) (.mul (.constant 24) .variable)) (.constant 98))
    .variable) (.constant 22)) .variable) (.constant 1)
theorem directionPolynomial_eval (L : Nat) :
    directionPolynomial.eval L = SourceAffineSearch.directionBudget L L L := rfl

def queryPolynomial : NatPolynomial :=
  .add (.mul (.add directionPolynomial (.constant 7)) (.add .variable (.constant 1)))
    (.add (.add (.mul (.add (.mul (.constant 9) .variable) (.constant 29)) .variable)
      (.mul (.constant 8) .variable)) (.constant 13))
theorem queryPolynomial_eval (L : Nat) :
    queryPolynomial.eval L = SourceAffineOutput.originalInputBudget L := rfl

/-- Conservative source fuel, including the final accepting instruction.
The substituted solver polynomial is charged at the constructed matrix bound,
not at an assumed constant-sized intermediate representation. -/
def sourceFuel : NatPolynomial :=
  .add (.add (.add SourcePolynomialMatrix.sourceFuel
    (NatPolynomial.substitute MatrixPolynomialSolver.sourceFuel matrixLengthPolynomial))
    queryPolynomial) (.constant 32)
theorem sourceFuel_eval (L : Nat) : sourceFuel.eval L = SourceAffineRawQuery.budget L + 1 := by
  simp only [sourceFuel, NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_substitute, matrixLengthPolynomial_eval, queryPolynomial_eval,
    SourceAffineRawQuery.budget]

private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (SourceAffineInput.rawStart input).store⟩ := rfl

theorem source_result (input : BitString) :
    ∃ after : Store 22, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted, after⟩ ∧ after.get 8 = SourceAffineRawQuery.answer input := by
  obtain ⟨fuel, after, checked, output, bound⟩ := SourceAffineRawQuery.block_exec input
  have run : BitRegister.run program (fuel + 1) (BitRegister.initial program input) =
      ⟨.accepted, after⟩ := by
    rw [initial_eq]
    exact checked.program_run 0 8
  have enough : fuel + 1 ≤ sourceFuel.eval input.length := by rw [sourceFuel_eval]; omega
  have slack : sourceFuel.eval input.length = (fuel + 1) + (sourceFuel.eval input.length - (fuel + 1)) := by omega
  refine ⟨after, ?_, output⟩
  unfold CompilerIO.sourceResult
  rw [slack, BitRegister.run_add, run, BitRegister.run_accepted]

theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  obtain ⟨after, run, _⟩ := source_result input
  rw [run]
theorem source_output (input : BitString) :
    (CompilerIO.sourceResult program (sourceFuel.eval input.length) input).store.get 8 =
      SourceAffineRawQuery.answer input := by
  obtain ⟨after, run, output⟩ := source_result input
  rw [run]
  exact output

def polynomial : PolynomialTimeFunction := CompilerIO.compilePolynomial program sourceFuel acceptsWithin
theorem polynomial_program : polynomial.program =
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 22 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem output_projection (input : BitString) : polynomial.output input =
    (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) :
    polynomial.output input = SourceAffineRawQuery.answer input := by
  rw [output_projection, CompilerIO.compilePolynomial_output]
  exact source_output input
theorem polynomial_canonical (n : Nat) (F : Family n) :
    polynomial.output (codec.encode ⟨n, F⟩) =
      (SourceAffineOutput.witnessCodec F.length n).encode (SourceClosure.sourceAffineQuery F) := by
  rw [polynomial_output, SourceAffineRawQuery.answer_canonical]
theorem polynomial_malformed (input : BitString) (invalid : codec.decode input = none) :
    polynomial.output input = [false] := by
  rw [polynomial_output, SourceAffineRawQuery.answer_malformed input invalid]
theorem polynomial_machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 22 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_bound (input : BitString) :
    (polynomial.output input).length ≤ 2 * input.length + 1 := by
  rw [polynomial_output]
  exact SourceAffineRawQuery.answer_length input

theorem exact_decoded_query (n : Nat) (F : Family n) :
    (SourceAffineOutput.witnessCodec F.length n).decode (polynomial.output (codec.encode ⟨n, F⟩)) =
      some (SourceClosure.sourceAffineQuery F) := by
  rw [polynomial_canonical]
  exact PNP.Concrete.NativeNormalization.NativeBitCodec.decode_encode _ _

/-- Soundness is for the affine-mask query, not for every possible contraction
route. The program obtains its own map and witness from the encoded family. -/
theorem polynomial_sound {n : Nat} (F : Family n)
    (w : Point F.length × Point n)
    (returned : (SourceAffineOutput.witnessCodec F.length n).decode
      (polynomial.output (codec.encode ⟨n, F⟩)) = some (some w)) :
    SourceClosure.AffineGood F w := by
  rw [exact_decoded_query] at returned
  exact SourceClosure.sourceAffineQuery_sound F w (Option.some.inj returned)

theorem polynomial_complete {n : Nat} (F : Family n)
    (existsWitness : ∃ w, SourceClosure.AffineGood F w) :
    ∃ w, (SourceAffineOutput.witnessCodec F.length n).decode
      (polynomial.output (codec.encode ⟨n, F⟩)) = some (some w) := by
  obtain ⟨w, found⟩ := SourceClosure.sourceAffineQuery_complete F existsWitness
  exact ⟨w, by rw [exact_decoded_query, found]⟩

/-- Failure rules out precisely affine-mask activity. It does not prove
satisfiability, absence of other routes, ZeroSlack or global minimality. -/
theorem polynomial_none_iff {n : Nat} (F : Family n) :
    (SourceAffineOutput.witnessCodec F.length n).decode (polynomial.output (codec.encode ⟨n, F⟩)) =
      some none ↔ ¬ ∃ w, SourceClosure.AffineGood F w := by
  rw [exact_decoded_query]
  constructor
  · intro missing
    exact (SourceClosure.sourceAffineQuery_none_iff F).mp (Option.some.inj missing)
  · intro absent
    rw [(SourceClosure.sourceAffineQuery_none_iff F).mpr absent]

end PNP.Concrete.ResidualReduction.SourcePolynomialAffineQuery
