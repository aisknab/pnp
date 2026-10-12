/-
Copyright (c) 2026 PNP Labs.

A closed polynomial occurrence query over a full encoded clause list.
Clause selection and occurrence scanning are actual sequential finite machines.
This supplies an incidence-lookup dependency for the derived matching stage,
not a matching algorithm, cache constructor or satisfiability solver.
-/

import PNP.Concrete.NormalizerClauseCanonical
import PNP.Concrete.PipelineRefinement

namespace PNP.Concrete.NormalizerBlocks.ClauseQuery

def occurrencePolynomial : PolynomialTimeFunction :=
  PolynomialTimeFunction.compose polynomial Occurrence.polynomial

theorem occurrencePolynomial_program :
    occurrencePolynomial.program = .compose polynomial.program Occurrence.polynomial.program := rfl

private theorem occurrence_projection (input : BitString) :
    occurrencePolynomial.output input =
      (PolynomialTimeFunction.compose polynomial Occurrence.polynomial).output input := rfl

theorem occurrencePolynomial_output (input : BitString) :
    occurrencePolynomial.output input = Occurrence.polynomial.output (polynomial.output input) := by
  rw [occurrence_projection, PolynomialTimeFunction.compose_output]

theorem occurrencePolynomial_canonical (target index : Nat) (clauses : List (List CNFLiteral)) :
    occurrencePolynomial.output (encodeQuery target index clauses) =
      Occurrence.answer ((clauses[index]?.getD []).find? (fun literal => literal.variableIndex == target)) := by
  rw [occurrencePolynomial_output, polynomial_canonical, Occurrence.polynomial_canonical]

theorem incidence_canonical (target index : Nat) (clauses : List (List CNFLiteral)) :
    (occurrencePolynomial.output (encodeQuery target index clauses)).head! =
      ((clauses[index]?.getD []).find? (fun literal => literal.variableIndex == target)).isSome := by
  rw [occurrencePolynomial_canonical]
  cases (clauses[index]?.getD []).find? (fun literal => literal.variableIndex == target) <;> rfl

def queryRawRefinement : FunctionProgram.RawRefinement polynomial.program := by
  rw [polynomial_program]
  exact FunctionProgram.RawRefinement.ofMachine (BitRegister.CompilerIO.rawMachine program)
    (BitRegister.CompilerIO.runtimePolynomial 9 sourceFuel)

def literalRawRefinement : FunctionProgram.RawRefinement Occurrence.polynomial.program := by
  rw [Occurrence.polynomial_program]
  exact FunctionProgram.RawRefinement.ofMachine (BitRegister.CompilerIO.rawMachine Occurrence.program)
    (BitRegister.CompilerIO.runtimePolynomial 9 Occurrence.sourceFuel)

def occurrenceRawRefinement : FunctionProgram.RawRefinement occurrencePolynomial.program := by
  rw [occurrencePolynomial_program]
  exact FunctionProgram.RawRefinement.compose queryRawRefinement literalRawRefinement

theorem occurrenceMachine_output (input : BitString) :
    machineOutput occurrenceRawRefinement.machine
      (occurrenceRawRefinement.timeBound.eval (BitString.size input)) input =
        Occurrence.polynomial.output (polynomial.output input) :=
  (occurrenceRawRefinement.output_eq input (occurrencePolynomial.haltsWithin input)).trans
    (occurrencePolynomial_output input)

theorem occurrenceMachine_canonical (target index : Nat) (clauses : List (List CNFLiteral)) :
    machineOutput occurrenceRawRefinement.machine
      (occurrenceRawRefinement.timeBound.eval (BitString.size (encodeQuery target index clauses)))
      (encodeQuery target index clauses) =
        Occurrence.answer ((clauses[index]?.getD []).find? (fun literal => literal.variableIndex == target)) :=
  (occurrenceRawRefinement.output_eq (encodeQuery target index clauses)
    (occurrencePolynomial.haltsWithin (encodeQuery target index clauses))).trans
    (occurrencePolynomial_canonical target index clauses)

theorem occurrenceMachine_halts (input : BitString) :
    boundedDecide occurrenceRawRefinement.machine
      (occurrenceRawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  occurrenceRawRefinement.haltsWithin input (occurrencePolynomial.haltsWithin input)

theorem occurrenceMachine_output_size (input : BitString) :
    BitString.size (machineOutput occurrenceRawRefinement.machine
      (occurrenceRawRefinement.timeBound.eval (BitString.size input)) input) ≤
        occurrencePolynomial.outputSizeBound.eval (BitString.size input) :=
  FunctionProgram.RawRefinement.output_size_le occurrencePolynomial occurrenceRawRefinement input

end PNP.Concrete.NormalizerBlocks.ClauseQuery
