/-
Copyright (c) 2026 PNP Labs.

A finite compiler into the concrete polynomial-time function interface.
A source program with a proved polynomial accepting-fuel bound yields an actual
raw Machine leaf, exact output semantics, and proved runtime/output-size bounds.
No executable callback is introduced.

The source accepting-fuel proof is a genuine obligation. This generic compiler
does not supply that proof for the normalizer or for arbitrary register programs.
-/

import PNP.Concrete.BitRegisterCompilerIOBounds

namespace PNP.Concrete.BitRegister.CompilerIO

open IOAdapter

def spanPolynomial : NatPolynomial :=
  .add
    (.add
      (.mul (.mul (.constant 9) (.add .variable (.constant 2))) (.add .variable (.constant 2)))
      (.mul (.constant 15) (.add .variable (.constant 2))))
    (.constant 9)

theorem spanPolynomial_eval (span : Nat) :
    spanPolynomial.eval span = CopyFreeCompiler.spanBudget span := rfl

def instructionPolynomial (count : Nat) : NatPolynomial :=
  .add
    (.mul (.linear 7 5)
      (NatPolynomial.substitute spanPolynomial
        (.mul (.constant (count + 1)) (.add (.add .variable (.linear 7 5)) (.constant 1)))))
    (.constant 1)

theorem instructionPolynomial_eval (count bound : Nat) :
    (instructionPolynomial count).eval bound = Compiler.instructionBudget count bound := by
  simp only [instructionPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, NatPolynomial.eval_substitute, spanPolynomial_eval,
    NatPolynomial.eval_linear, NatPolynomial.eval_variable, Compiler.instructionBudget]

def runtimePolynomial (count : Nat) (sourceFuel : NatPolynomial) : NatPolynomial :=
  .add
    (.add
      (.add (inputRawBound count)
        (.mul (.constant 6)
          (.mul sourceFuel
            (NatPolynomial.substitute (instructionPolynomial count) (.add .variable sourceFuel)))))
      (NatPolynomial.substitute outputRawBound
        (.mul (.constant (count + 1)) (.add (.add .variable sourceFuel) (.constant 1)))))
    (.constant 18)

theorem runtimePolynomial_eval (count : Nat) (sourceFuel : NatPolynomial) (inputLength : Nat) :
    (runtimePolynomial count sourceFuel).eval inputLength =
      rawBudget count inputLength (sourceFuel.eval inputLength) := by
  simp only [runtimePolynomial, rawBudget, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, NatPolynomial.eval_substitute, NatPolynomial.eval_variable,
    instructionPolynomial_eval]

def outputPolynomial (sourceFuel : NatPolynomial) : NatPolynomial :=
  .add .variable sourceFuel

theorem outputPolynomial_eval (sourceFuel : NatPolynomial) (inputLength : Nat) :
    (outputPolynomial sourceFuel).eval inputLength = inputLength + sourceFuel.eval inputLength := rfl

/-- This premise must be proved for the actual closed source program. -/
def AcceptsWithin {count : Nat} (program : Program count) (sourceFuel : NatPolynomial) : Prop :=
  ∀ input, (sourceResult program (sourceFuel.eval input.length) input).control = .accepted

/-- Only finite machine and polynomial syntax occur in the executable field. -/
def compilePolynomial {count : Nat} (program : Program count) (sourceFuel : NatPolynomial)
    (accepts : AcceptsWithin program sourceFuel) : PolynomialTimeFunction :=
  { program := .machine (rawMachine program) (runtimePolynomial count sourceFuel)
    runtimeBound := runtimePolynomial count sourceFuel
    outputSizeBound := outputPolynomial sourceFuel
    haltsWithin := by
      intro input
      change boundedDecide (rawMachine program)
        ((runtimePolynomial count sourceFuel).eval input.length) input ≠ .timeout
      rw [runtimePolynomial_eval, raw_accepts program _ input (accepts input)]
      exact Verdict.noConfusion
    runtime_le := by
      intro input
      exact Nat.le_refl _
    output_size_le := by
      intro input
      change (machineOutput (rawMachine program)
        ((runtimePolynomial count sourceFuel).eval input.length) input).length ≤
        (outputPolynomial sourceFuel).eval input.length
      rw [runtimePolynomial_eval, outputPolynomial_eval]
      exact raw_output_length_le program _ input (accepts input) }

theorem compilePolynomial_program {count : Nat} (program : Program count) (sourceFuel : NatPolynomial)
    (accepts : AcceptsWithin program sourceFuel) :
    (compilePolynomial program sourceFuel accepts).program =
      .machine (rawMachine program) (runtimePolynomial count sourceFuel) := rfl

private theorem output_projection {count : Nat} (program : Program count) (sourceFuel : NatPolynomial)
    (accepts : AcceptsWithin program sourceFuel) (input : BitString) :
    (compilePolynomial program sourceFuel accepts).output input =
      machineOutput (rawMachine program) ((runtimePolynomial count sourceFuel).eval input.length) input := rfl

theorem compilePolynomial_output {count : Nat} (program : Program count) (sourceFuel : NatPolynomial)
    (accepts : AcceptsWithin program sourceFuel) (input : BitString) :
    (compilePolynomial program sourceFuel accepts).output input =
      (sourceResult program (sourceFuel.eval input.length) input).store.get program.output := by
  rw [output_projection, runtimePolynomial_eval]
  exact raw_output program _ input (accepts input)

theorem compilePolynomial_accepts {count : Nat} (program : Program count) (sourceFuel : NatPolynomial)
    (accepts : AcceptsWithin program sourceFuel) (input : BitString) :
    boundedDecide (rawMachine program) ((runtimePolynomial count sourceFuel).eval input.length) input = .accept := by
  rw [runtimePolynomial_eval]
  exact raw_accepts program _ input (accepts input)

theorem compilePolynomial_output_length_le {count : Nat} (program : Program count) (sourceFuel : NatPolynomial)
    (accepts : AcceptsWithin program sourceFuel) (input : BitString) :
    ((compilePolynomial program sourceFuel accepts).output input).length ≤
      input.length + sourceFuel.eval input.length := by
  rw [output_projection, runtimePolynomial_eval]
  exact raw_output_length_le program _ input (accepts input)

end PNP.Concrete.BitRegister.CompilerIO
