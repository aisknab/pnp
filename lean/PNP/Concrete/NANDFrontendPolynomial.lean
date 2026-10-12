/-
Copyright (c) 2026 PNP Labs.

A closed concrete polynomial-time implementation of the circuit frontend.
The raw intermediate transformation is total; it is not advertised as a strict
validator of every arbitrary circuit encoding. Exact frontend semantics on the
internally derived compiler image and the all-source-bitstring composition are
separate obligations. This machine is not a SAT solver.
-/

import PNP.Concrete.NANDFrontendBounds
import PNP.Concrete.BitRegisterCompilerIOPolynomial

namespace PNP.Concrete.NANDFrontend

open BitRegister

def headerFuelPolynomial : NatPolynomial := .linear 6 19

def constantsFuelPolynomial : NatPolynomial :=
  .add (.mul (.constant 24) (.add .variable headerFuelPolynomial)) (.constant 58)

def preLoopPolynomial : NatPolynomial :=
  .add (.add .variable headerFuelPolynomial) constantsFuelPolynomial

def traversalFuelPolynomial : NatPolynomial :=
  .mul (.mul (.constant 128) (.add preLoopPolynomial (.constant 1)))
    (.add (.mul (.constant 3) preLoopPolynomial) (.constant 1))

def outputFuelPolynomial : NatPolynomial :=
  .mul (.constant 256)
    (.add (.mul (.constant 4) (.add preLoopPolynomial traversalFuelPolynomial)) (.constant 1))

def sourceFuel : NatPolynomial :=
  .add (.add (.add (.add headerFuelPolynomial constantsFuelPolynomial)
    traversalFuelPolynomial) outputFuelPolynomial) (.constant 3)

theorem sourceFuel_eval (length : Nat) : sourceFuel.eval length = frontendBudget length := by
  simp only [sourceFuel, headerFuelPolynomial, constantsFuelPolynomial, preLoopPolynomial,
    traversalFuelPolynomial, outputFuelPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, NatPolynomial.eval_variable, NatPolynomial.eval_linear,
    frontendBudget, headerBudget, constantsBudget, preLoopBound, traversalBudget, outputBudget]

theorem frontend_padded (input : BitString) :
    BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input) =
      ⟨.accepted, (frontendFinal (initialRegisters input)).store⟩ := by
  have bound := frontend_input_bound input
  rw [sourceFuel_eval]
  have split : frontendBudget input.length = frontendFuel (initialRegisters input) +
      (frontendBudget input.length - frontendFuel (initialRegisters input)) := by omega
  rw [split, BitRegister.run_add, initial_registers, frontend_run, BitRegister.run_accepted]

theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  change (BitRegister.run program (sourceFuel.eval input.length)
    (BitRegister.initial program input)).control = .accepted
  rw [frontend_padded]

def polynomial : PolynomialTimeFunction :=
  CompilerIO.compilePolynomial program sourceFuel acceptsWithin

theorem polynomial_program :
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 9 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin

private theorem output_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl

theorem polynomial_output (input : BitString) :
    polynomial.output input = (frontendFinal (initialRegisters input)).output := by
  rw [output_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length)
    (BitRegister.initial program input)).store.get 8 = _
  rw [frontend_padded]
  rfl

theorem polynomial_machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

theorem polynomial_empty : polynomial.output [] = [false] := by
  rw [polynomial_output]
  rfl

end PNP.Concrete.NANDFrontend
