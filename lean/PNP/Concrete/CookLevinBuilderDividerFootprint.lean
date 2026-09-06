/-
Copyright (c) 2026 PNP Labs.

The actual initializer's new register footprint covers both the previous header
scratch and the input framer's exterior cells. Consequently its preserved tail,
and the divider operand assembly's expansion-side tail, are genuinely empty.
No tape cells are discarded by a host operation and no empty-tail premise is
supplied. Divider marker conversion, execution and later cleanup remain separate.
-/

import PNP.Concrete.CookLevinBuilderDividerOperands

namespace PNP.Concrete.CookLevin.BuilderDividerFootprint

open BuilderUnaryPolynomial

/-- Exact occupied register span, excluding the active end marker. -/
def span (polynomial : NatPolynomial) (input : Nat) : Nat :=
  (registerSpanPolynomial polynomial).eval input

theorem scratchWord_length_eq_span (polynomial : NatPolynomial) (input : Nat) :
    (scratchWord polynomial input).length = span polynomial input :=
  scratchWord_length polynomial input

private theorem span_add (left right : NatPolynomial) (input : Nat) :
    span (.add left right) input =
      span left input + span right input + (left.eval input + right.eval input) + 1 := by
  simp only [span, registerSpanPolynomial, nodeCount, subtreeValueSumPolynomial,
    NatPolynomial.eval_add, NatPolynomial.eval_constant]
  omega

private theorem span_mul (left right : NatPolynomial) (input : Nat) :
    span (.mul left right) input =
      span left input + span right input + left.eval input * right.eval input + 1 := by
  simp only [span, registerSpanPolynomial, nodeCount, subtreeValueSumPolynomial,
    NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
  omega

private theorem span_constant (value input : Nat) :
    span (.constant value) input = 1 + value := rfl

private theorem span_variable (input : Nat) : span .variable input = 1 + input := rfl

private theorem inputOnly_span_bound (common certificate : NatPolynomial) (input : Nat) :
    span common input ≤
      2 * span (.add (.add common certificate) (.add certificate (.constant 1))) input := by
  simp only [span_add]
  omega

/-- Reassociation changes the intermediate registers, even when root values agree. -/
private theorem paired_span_bound (common certificate : NatPolynomial) (input : Nat) :
    span (.add common (.add certificate (.add certificate (.constant 1)))) input ≤
      2 * span (.add (.add common certificate) (.add certificate (.constant 1))) input := by
  simp only [span_add, span_constant, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  omega

theorem header_span_le_double_variable_span {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : Nat) :
    span (formulaWidthPolynomial verifier) input ≤
      2 * span (formulaVariableCountPolynomial verifier) input := by
  let time := formulaTimeCountPolynomial verifier
  let tape := formulaTapeWidthPolynomial verifier
  let states := formulaStateCountPolynomial verifier
  let common := NatPolynomial.add
    (.add (.mul (.mul (.constant 3) time) tape) (.mul time tape)) (.mul time states)
  have hVariable : formulaVariableCountPolynomial verifier =
      .add (.add common verifier.certificateBound)
        (.add verifier.certificateBound (.constant 1)) := rfl
  have hWidth : formulaWidthPolynomial verifier =
      match verifier.program.inputMode with
      | .inputOnly => common
      | .paired => .add common
          (.add verifier.certificateBound (.add verifier.certificateBound (.constant 1))) := rfl
  rw [hVariable, hWidth]
  cases verifier.program.inputMode with
  | inputOnly => exact inputOnly_span_bound common verifier.certificateBound input
  | paired => exact paired_span_bound common verifier.certificateBound input

private theorem encoded_input_span (mode : InputMode) (certificate : NatPolynomial)
    (input : Nat) :
    input + 1 ≤ span (encodedInputPolynomial mode certificate) input := by
  cases mode <;>
    simp only [encodedInputPolynomial, span_add, span_mul, span_constant, span_variable] <;> omega

theorem input_length_le_variable_span {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : Nat) :
    input + 1 ≤ span (formulaVariableCountPolynomial verifier) input := by
  have hInput := encoded_input_span (inputModeOfVerifier verifier.program.inputMode)
    verifier.certificateBound input
  have hTape : input + 1 ≤ span (formulaTapeWidthPolynomial verifier) input := by
    simp only [formulaTapeWidthPolynomial, tapeWidthPolynomial, span_add]
    omega
  simp only [formulaVariableCountPolynomial, span_add, span_mul]
  omega

/-- The eagerly retained width subtree contains two complete variable-count evaluations. -/
theorem double_variable_span_le_preparation_span {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : Nat) :
    2 * span (formulaVariableCountPolynomial verifier) input ≤
      span (BuilderDimensionRegisters.polynomial verifier) input := by
  simp only [BuilderDimensionRegisters.polynomial,
    BuilderDimensionRegisters.preparationPolynomial, BuilderDimensionRegisters.widthPolynomial,
    span_add, span_mul]
  omega

theorem rootPrefix_eval_add_eval_eq_span (polynomial : NatPolynomial) (input : Nat) :
    (rootPrefixPolynomial polynomial).eval input + polynomial.eval input = span polynomial input := by
  obtain ⟨wordPrefix, hWord, hPrefix⟩ := root_prefix_length polynomial input
  have hLength := congrArg List.length hWord
  simp only [scratchWord_length_eq_span, List.length_append, List.length_cons,
    List.length_replicate] at hLength
  omega

private theorem packed_symbols_length_le : ∀ symbols : List TapeSymbol,
    (packWorkSymbols symbols).length ≤ symbols.length
  | [] => Nat.le_refl 0
  | _ :: [] => Nat.le_refl 1
  | _ :: _ :: rest => by
      have hRest := packed_symbols_length_le rest
      simp only [packWorkSymbols, List.length_cons]
      omega

theorem packedInputCount_le (input : BitString) :
    PipelineInputFramer.packedInputCount input ≤ input.length := by
  have h := packed_symbols_length_le (input.map TapeSymbol.ofBool)
  simpa only [PipelineInputFramer.packedInputCount, List.length_map] using h

theorem framerOutside_length_le (input : BitString) :
    (PipelineInputFramer.totalInputFramerOutsideLeft input).length ≤ input.length + 1 := by
  have h := packedInputCount_le input
  cases input with
  | nil => exact Nat.zero_le _
  | cons bit rest =>
    simp only [PipelineInputFramer.totalInputFramerOutsideLeft, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
    simp only [List.length_cons] at h
    omega

/-- The header overwrites a prefix but never lengthens its unprocessed tail. -/
theorem headerOutside_length {language : Language} (problem : VerifierTableauProblem language) :
    (BuilderCompleteHeader.finalOutside problem).length =
      max (span (formulaWidthPolynomial problem.verifier) problem.input.length + 1)
        (BuilderCompleteHeader.baseOutside problem).length := by
  have hRoot :
      BuilderCompleteHeader.rootPrefixLength problem + BuilderCompleteHeader.width problem =
        span (formulaWidthPolynomial problem.verifier) problem.input.length :=
    rootPrefix_eval_add_eval_eq_span (BuilderCompleteHeader.widthPolynomial problem)
      problem.input.length
  simp only [BuilderCompleteHeader.finalOutside, List.length_append, List.length_take,
    List.length_replicate, List.length_drop, scratchWord_length_eq_span,
    BuilderCompleteHeader.widthPolynomial]
  omega

theorem headerOutside_length_le_preparation {language : Language}
    (problem : VerifierTableauProblem language) :
    (BuilderCompleteHeader.finalOutside problem).length ≤
      (scratchWord (BuilderDimensionRegisters.polynomial problem.verifier)
        problem.input.length).length + 1 := by
  have hHeader := header_span_le_double_variable_span problem.verifier problem.input.length
  have hDimension := double_variable_span_le_preparation_span problem.verifier problem.input.length
  have hInput := input_length_le_variable_span problem.verifier problem.input.length
  have hBase : (BuilderCompleteHeader.baseOutside problem).length ≤ problem.input.length + 1 :=
    framerOutside_length_le problem.input
  rw [headerOutside_length, scratchWord_length_eq_span]
  omega

/-- This is derived from the actual initialization footprint, not an added premise. -/
theorem preservedTail_eq_nil {language : Language} (problem : VerifierTableauProblem language) :
    BuilderCursorSource.preservedTail problem = [] := by
  unfold BuilderCursorSource.preservedTail
  exact List.drop_eq_nil_iff.mpr (headerOutside_length_le_preparation problem)

theorem operandFinal_left_eq_nil {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderDividerOperands.finalConfiguration problem index remaining output).tape.left = [] := by
  change (BuilderCursorSource.preservedTail problem).drop
    (registerWord (BuilderDividerOperands.appended problem index)).length = []
  apply List.drop_eq_nil_iff.mpr
  rw [preservedTail_eq_nil]
  exact Nat.zero_le _

theorem fromRawFinal_left_eq_nil {language : Language} (problem : VerifierTableauProblem language) :
    (BuilderDividerOperands.fromRawFinal problem).tape.left = [] :=
  operandFinal_left_eq_nil problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)
    (encodeUnaryTokens problem.FormulaWidth)

end PNP.Concrete.CookLevin.BuilderDividerFootprint
