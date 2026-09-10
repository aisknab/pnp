/-
Copyright (c) 2026 PNP Labs.

Source-derived dimension registers for the complete Cook-Levin builder.
The existing finite unary evaluator materializes the clause width before
coordinate records are created. A zero-valued subtree retains the width in
the checked postorder register layout while leaving the final counter value
unchanged. All of that computation remains included in the exact time polynomial.

This is workspace construction, not the physical classifier handoff, complete
selector, repeated formula-building loop, or packaged polynomial reduction.
-/

import PNP.Concrete.CookLevinBuilderFullScheduleCursorController

namespace PNP.Concrete.CookLevin.BuilderDimensionRegisters

open BuilderUnaryPolynomial

/-- The extra subtree is evaluated and retained, not constant-folded away. -/
def preparationPolynomial (counter width : NatPolynomial) : NatPolynomial :=
  .add counter (.mul (.constant 0) width)

theorem preparationPolynomial_eval (counter width : NatPolynomial) (input : Nat) :
    (preparationPolynomial counter width).eval input = counter.eval input := by
  simp only [preparationPolynomial, NatPolynomial.eval_add,
    NatPolynomial.eval_mul, NatPolynomial.eval_constant, Nat.zero_mul,
    Nat.add_zero]

/-- The last three registers are width, the zero product, and the counter. -/
theorem registerValues_layout (counter width : NatPolynomial) (input : Nat) :
    ∃ valuesPrefix,
      registerValues (preparationPolynomial counter width) input =
        valuesPrefix ++ [width.eval input, 0, counter.eval input] ∧
      valuesPrefix.length = nodeCount counter + nodeCount width := by
  obtain ⟨widthPrefix, hWidth⟩ := registerValues_eq_prefix_append_root width input
  refine ⟨registerValues counter input ++ [0] ++ widthPrefix, ?_, ?_⟩
  · simp only [preparationPolynomial, registerValues, NatPolynomial.eval_mul,
      NatPolynomial.eval_constant, Nat.zero_mul,
      Nat.add_zero, hWidth, List.append_assoc, List.cons_append,
      List.nil_append]
  · have hLength := congrArg List.length hWidth
    rw [registerValues_length, List.length_append] at hLength
    simp only [List.length_cons, List.length_nil] at hLength
    simp only [List.length_append, registerValues_length,
      List.length_cons, List.length_nil]
    omega

/-- A literal width register, empty product register, and final counter. -/
def dimensionWord (width counter : Nat) : List WorkSymbol :=
  registerWord [width, 0, counter]

theorem dimensionWord_eq (width counter : Nat) :
    dimensionWord width counter =
      separatorSymbol :: (List.replicate width unitSymbol ++
        separatorSymbol :: separatorSymbol :: List.replicate counter unitSymbol) := by
  simp only [dimensionWord, registerWord, List.replicate_zero,
    List.nil_append, List.append_nil]

theorem dimensionWord_length (width counter : Nat) :
    (dimensionWord width counter).length = width + counter + 3 := by
  rw [dimensionWord_eq]
  simp only [List.length_cons, List.length_append, List.length_replicate]
  omega

theorem scratchWord_layout (counter width : NatPolynomial) (input : Nat) :
    ∃ valuesPrefix,
      scratchWord (preparationPolynomial counter width) input =
        valuesPrefix ++ dimensionWord (width.eval input) (counter.eval input) := by
  obtain ⟨valuesPrefix, hValues, _⟩ := registerValues_layout counter width input
  refine ⟨registerWord valuesPrefix, ?_⟩
  unfold scratchWord
  rw [hValues, registerWord_append]
  rfl

def widthPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let variables := formulaVariableCountPolynomial verifier
  .add (.constant 1) (.mul variables variables)

theorem widthPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (widthPolynomial problem.verifier).eval problem.input.length =
      problem.formulaClauseSlotsPerConstraint := by
  rfl

def polynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  preparationPolynomial
    (BuilderFullScheduleCursorController.bodySlotCountPolynomial verifier)
    (widthPolynomial verifier)

theorem polynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (polynomial problem.verifier).eval problem.input.length =
      BuilderFullScheduleCursorController.bodySlotCount problem := by
  exact preparationPolynomial_eval _ _ _

def machine {language : Language}
    (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  BuilderUnaryPolynomial.machine (polynomial verifier)

theorem machine_rules_pairwise {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) :=
  BuilderUnaryPolynomial.rules_pairwise_query_distinct (polynomial verifier)

def rawTimePolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .mul (.constant 6) (workTimePolynomial (polynomial verifier))

theorem rawTimePolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimePolynomial problem.verifier).eval problem.input.length =
      6 * workSteps (polynomial problem.verifier) problem.input := by
  rw [rawTimePolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_constant,
    workTimePolynomial_eval]

/-- Construct both dimensions by a fixed finite program, preserve the input and
existing builder output, and charge the entire register construction. Initial
outside cells are scratch, not previously retained coordinate records. -/
theorem construct_dimensions {language : Language}
    (problem : VerifierTableauProblem language)
    (outside : List WorkSymbol) (output : List CNFToken) :
    let program := machine problem.verifier
    let steps := workSteps (polynomial problem.verifier) problem.input
    let initial := initialConfiguration (polynomial problem.verifier)
      problem.input outside output
    let final := finalConfiguration (polynomial problem.verifier)
      problem.input outside output
    ∃ valuesPrefix,
      workRunExact? program steps initial = some final ∧
      run (compileWorkMachine program) (6 * steps)
          (encodeWorkConfiguration initial) = encodeWorkConfiguration final ∧
      final.tape = BuilderTokenAppender.workspaceTape problem.input
        ((valuesPrefix ++ dimensionWord problem.formulaClauseSlotsPerConstraint
          (BuilderFullScheduleCursorController.bodySlotCount problem)) ++
          scratchEndSymbol :: outside.drop
            ((scratchWord (polynomial problem.verifier) problem.input.length).length + 1))
        output ∧
      6 * steps = (rawTimePolynomial problem.verifier).eval problem.input.length := by
  dsimp only
  obtain ⟨valuesPrefix, hWord⟩ := scratchWord_layout
    (BuilderFullScheduleCursorController.bodySlotCountPolynomial problem.verifier)
    (widthPolynomial problem.verifier) problem.input.length
  have hLayout : scratchWord (polynomial problem.verifier) problem.input.length =
      valuesPrefix ++ dimensionWord problem.formulaClauseSlotsPerConstraint
        (BuilderFullScheduleCursorController.bodySlotCount problem) := by
    simpa only [polynomial, widthPolynomial_eval, BuilderFullScheduleCursorController.bodySlotCount]
      using hWord
  have hRun := workRunExact (polynomial problem.verifier) problem.input outside output
  refine ⟨valuesPrefix, hRun,
    run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun, ?_,
    (rawTimePolynomial_eval problem).symm⟩
  change BuilderTokenAppender.workspaceTape problem.input
    (overlayScratch (scratchWord (polynomial problem.verifier) problem.input.length)
      outside) output = _
  unfold overlayScratch
  rw [hLayout]

end PNP.Concrete.CookLevin.BuilderDimensionRegisters
