import PNP.Concrete.ResidualReduction.SourceDirectionRaw

/-! A uniformly polynomial finite machine for the exact source-derived
direction space. Runtime is charged to the original encoded normals and family,
including raw input/output and compiler word-copy costs. This shared operation
does not establish completeness of contraction, global ZeroSlack or SAT in P. -/

namespace PNP.Concrete.ResidualReduction.SourcePolynomialDirection
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding
open PNP.Concrete.ResidualReduction.SourceDirectionInput (directionEncoded)
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceDirectionInstructions (State)

def program : Program 20 := SourceDirectionRaw.block.program 0 8
def payloadPolynomial (width : NatPolynomial) : NatPolynomial :=
  .add (.add (.mul (.add (.mul (.constant 3) width) (.constant 4)) .variable) (.constant 1))
    (.add (.mul (.constant 5) (.mul width .variable)) (.constant 1))
def normalPayload : NatPolynomial := payloadPolynomial (.add .variable (.constant 1))
def familyPayload : NatPolynomial := payloadPolynomial (.add (.mul (.constant 2) .variable) (.constant 3))
theorem normalPayload_eval (L : Nat) : normalPayload.eval L = MatrixInputPayload.fuel L L := rfl
theorem familyPayload_eval (L : Nat) : familyPayload.eval L = SourceFamilyLoader.fuel L L := rfl

/-- The final accepting instruction is included. Both intermediate kernels
are already charged by the prepared polynomial at their derived sizes. -/
def sourceFuel : NatPolynomial := .add
  (.add (.add normalPayload familyPayload) SourceDirectionBudget.costPolynomial) (.linear 23 75)
theorem sourceFuel_eval (L : Nat) : sourceFuel.eval L = SourceDirectionRaw.sourceBudget L + 1 := by
  simp only [sourceFuel, NatPolynomial.eval_add, NatPolynomial.eval_linear,
    normalPayload_eval, familyPayload_eval, SourceDirectionBudget.costPolynomial_eval,
    SourceDirectionRaw.sourceBudget, SourceDirectionRaw.selectionBudget,
    SourceDirectionRaw.normalBudget, SourceDirectionRaw.familyBudget, SourceDirectionRaw.completionBudget]
  omega

private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (SourceDirectionLoader.rawStart input).store⟩ := rfl
theorem source_result (input : BitString) :
    ∃ after : State, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted, after.store⟩ ∧ after.store.get 8 = directionEncoded input := by
  obtain ⟨fuel, after, checked, bound, output⟩ := SourceDirectionRaw.block_exec input
  have run : BitRegister.run program (fuel + 1) (BitRegister.initial program input) = ⟨.accepted, after.store⟩ := by
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
    (CompilerIO.sourceResult program (sourceFuel.eval input.length) input).store.get 8 = directionEncoded input := by
  obtain ⟨after, run, output⟩ := source_result input
  rw [run]
  exact output

def polynomial : PolynomialTimeFunction := CompilerIO.compilePolynomial program sourceFuel acceptsWithin
theorem polynomial_program : polynomial.program =
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 20 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem output_projection (input : BitString) : polynomial.output input =
    (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = directionEncoded input := by
  rw [output_projection, CompilerIO.compilePolynomial_output]
  exact source_output input
theorem polynomial_canonical (n : Nat) (F : Family n) (U : System n) :
    polynomial.output (codec.encode ⟨n, U, F⟩) = (solutionCodec n).encode (some (directionSpace F U)) := by
  rw [polynomial_output, SourceDirectionInput.directionEncoded_canonical]
theorem polynomial_malformed (input : BitString) (invalid : codec.decode input = none) :
    polynomial.output input = [false] := by
  rw [polynomial_output, SourceDirectionInput.directionEncoded_malformed input invalid]
theorem exact_decoded_direction (n : Nat) (F : Family n) (U : System n) :
    (solutionCodec n).decode (polynomial.output (codec.encode ⟨n, U, F⟩)) = some (some (directionSpace F U)) := by
  rw [polynomial_canonical]
  exact solution_roundtrip n _
theorem polynomial_machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 20 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_bound (input : BitString) :
    (polynomial.output input).length ≤ (input.length + 1) * (input.length + 1) + 1 := by
  cases decoded : codec.decode input with
  | none => rw [polynomial_malformed input decoded]; simp only [List.length_cons, List.length_nil]; omega
  | some problem =>
    rcases problem with ⟨n, U, F⟩
    have bytes := (canonical input ⟨n, U, F⟩).mp decoded
    rw [← bytes, polynomial_canonical, ← SourceDirectionInstructions.result_output F U]
    exact SourceDirectionBudget.output_bound F U

theorem polynomial_sound {n : Nat} (F : Family n) (U : System n) (s : Space n)
    (returned : (solutionCodec n).decode (polynomial.output (codec.encode ⟨n, U, F⟩)) = some (some s))
    (z : Point s.parameters) : DirectionSpec F U (s.direction z) := by
  rw [exact_decoded_direction] at returned
  have equal : directionSpace F U = s := Option.some.inj (Option.some.inj returned)
  subst s
  exact directionSpace_sound F U z
theorem polynomial_complete {n : Nat} (F : Family n) (U : System n) (v : Point n)
    (valid : DirectionSpec F U v) :
    ∃ s : Space n, (solutionCodec n).decode (polynomial.output (codec.encode ⟨n, U, F⟩)) = some (some s) ∧
      ∃ z, s.direction z = v :=
  ⟨directionSpace F U, exact_decoded_direction n F U, directionSpace_complete F U v valid⟩

end PNP.Concrete.ResidualReduction.SourcePolynomialDirection
