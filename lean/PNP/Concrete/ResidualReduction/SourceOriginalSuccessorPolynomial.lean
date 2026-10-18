import PNP.Concrete.ResidualReduction.SourceOriginalSuccessorRaw

/-! The entire original-source successor as one concrete polynomial-time
function on arbitrary bitstrings. The compiler theorem includes physical
register word-copy costs. This is a complete single-step construction, not
yet the complete history runner or an unconditional stopped-core solver. -/

namespace PNP.Concrete.ResidualReduction.SourceOriginalSuccessorPolynomial
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (codec)
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorState (stepCodec)
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorRaw (answer canonicalAnswer)
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorBounds (sourceFuel)

def program : Program 56 := SourceOriginalSuccessorRaw.block.program 0 8
private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0,SourceOriginalSuccessorState.initial input⟩ := rfl

theorem source_result (input : BitString) :
    ∃ after : Store 56, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted,after⟩ ∧ after.get 8 = answer input := by
  obtain ⟨used,after,checked,bound,output⟩ := SourceOriginalSuccessorRaw.block_exec input
  have run : BitRegister.run program (used + 1) (BitRegister.initial program input) = ⟨.accepted,after⟩ := by
    rw [initial_eq]
    exact checked.program_run 0 8
  have enough : used + 1 ≤ sourceFuel.eval input.length := by
    rw [SourceOriginalSuccessorBounds.sourceFuel_eval]
    unfold SourceOriginalSuccessorRaw.budget at bound
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
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 56 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem output_projection (input : BitString) : polynomial.output input =
    (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = answer input := by
  rw [output_projection,CompilerIO.compilePolynomial_output]
  exact source_output input
theorem polynomial_canonical {n : Nat} (F : Family (n + 1)) :
    polynomial.output (codec.encode ⟨n + 1,F⟩) =
      (stepCodec n F.length).encode (SourceChain.globalStep F) := by
  rw [polynomial_output,SourceOriginalSuccessorRaw.answer_canonical]
  rfl
theorem polynomial_zero (F : Family 0) : polynomial.output (codec.encode ⟨0,F⟩) = [false] := by
  rw [polynomial_output,SourceOriginalSuccessorRaw.answer_canonical]
  rfl
theorem polynomial_malformed (input : BitString) (h : codec.decode input = none) :
    polynomial.output input = [false] := by
  rw [polynomial_output,SourceOriginalSuccessorRaw.answer_malformed input h]
theorem exact_decoded_step {n : Nat} (F : Family (n + 1)) :
    (stepCodec n F.length).decode (polynomial.output (codec.encode ⟨n + 1,F⟩)) =
      some (SourceChain.globalStep F) := by
  rw [polynomial_canonical]
  exact NativeNormalization.NativeBitCodec.decode_encode _ _

theorem polynomial_step_sound {n : Nat} (F : Family (n + 1))
    (s : SourceClosure.ConstructedStep n F.length)
    (h : (stepCodec n F.length).decode (polynomial.output (codec.encode ⟨n + 1,F⟩)) = some (some s)) :
    SourceClosure.StepSound F s := by
  rw [exact_decoded_step] at h
  exact SourceChain.globalStep_sound F s (Option.some.inj h)
theorem exact_absence {n : Nat} (F : Family (n + 1)) :
    (stepCodec n F.length).decode (polynomial.output (codec.encode ⟨n + 1,F⟩)) = some none ↔
      SourceChain.globalStep F = none := by
  rw [exact_decoded_step,Option.some.injEq]

theorem canonical_output_bound (n : Nat) (F : Family n) :
    let L := (codec.encode ⟨n,F⟩).length
    (canonicalAnswer n F).length ≤ 2 * (L * L) + 8 * L + 5 := by
  dsimp only
  cases n with
  | zero => change 1 ≤ _; omega
  | succ n =>
    have dimension := SourceMatrixEncoding.dimension_bound (n + 1) F
    have rows := SourceMatrixEncoding.rowCount_bound (n + 1) F
    cases h : SourceChain.globalStep F with
    | none => simp only [canonicalAnswer,h,SourceOriginalSuccessorState.step_none,List.length_cons,List.length_nil]; omega
    | some s =>
      have size := SourceEncoding.step_length s (SourceChain.globalStep_sound F s h).1
      have coefficient : 2 * n + 4 ≤ 2 * (codec.encode ⟨n + 1,F⟩).length + 4 := by omega
      have product := Nat.mul_le_mul coefficient rows
      unfold SourceEncoding.stepBound at size
      simp only [Nat.add_mul,Nat.mul_assoc] at product size
      simp only [canonicalAnswer,h]
      change ((SourceEncoding.stepCodec n F.length).encode s).length + 1 ≤ _
      omega

theorem polynomial_output_bound (input : BitString) :
    (polynomial.output input).length ≤ 2 * (input.length * input.length) + 8 * input.length + 5 := by
  rw [polynomial_output]
  cases decoded : codec.decode input with
  | none => rw [SourceOriginalSuccessorRaw.answer_malformed input decoded]; change 1 ≤ _; omega
  | some problem =>
    rcases problem with ⟨n,F⟩
    have bytes := (SourceMatrixEncoding.canonical input ⟨n,F⟩).mp decoded
    rw [← bytes,SourceOriginalSuccessorRaw.answer_canonical]
    exact canonical_output_bound n F

theorem polynomial_machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 56 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

end PNP.Concrete.ResidualReduction.SourceOriginalSuccessorPolynomial
