/-
Copyright (c) 2026 PNP Labs.

Fixed Boolean projection for encoded query answers. Empty malformed output
is false; a present head is compared with one fixed Boolean tag. This finite
three-step program is used for absence and presence tests in graph queries.
-/

import PNP.Concrete.NormalizerMatchingRead

namespace PNP.Concrete.NormalizerBlocks.BooleanHead

open BitRegister Occurrence

def value (expected : Bool) : BitString → Bool
  | [] => false
  | bit :: _ => bit == expected

def block (expected : Bool) : Block 9 :=
  .branch 0 (.action (.push 8 false)) (.action (.push 8 (!expected))) (.action (.push 8 expected))
def program (expected : Bool) : Program 9 := (block expected).program 0 8
def result (expected : Bool) (input : BitString) : Registers :=
  {initialRegisters input with output := [value expected input]}
def sourceFuel : NatPolynomial := .constant 3

theorem block_exec (expected : Bool) (input : BitString) :
    Exec (block expected) (initialRegisters input).store 2 (result expected input).store := by
  cases input with
  | nil => exact Exec.empty rfl (.action _ _)
  | cons bit rest =>
      cases bit <;> cases expected
      · exact Exec.zero rfl (.action _ _)
      · exact Exec.zero rfl (.action _ _)
      · exact Exec.one rfl (.action _ _)
      · exact Exec.one rfl (.action _ _)

theorem initial_registers (expected : Bool) (input : BitString) :
    BitRegister.initial (program expected) input = ⟨.running 0, (initialRegisters input).store⟩ := rfl

theorem closed_run (expected : Bool) (input : BitString) :
    BitRegister.run (program expected) 3 (BitRegister.initial (program expected) input) =
      ⟨.accepted, (result expected input).store⟩ := by
  rw [initial_registers]
  exact (block_exec expected input).program_run 0 8

theorem acceptsWithin (expected : Bool) : CompilerIO.AcceptsWithin (program expected) sourceFuel := by
  intro input
  change (BitRegister.run (program expected) 3 (BitRegister.initial (program expected) input)).control = .accepted
  rw [closed_run]

def polynomial (expected : Bool) : PolynomialTimeFunction :=
  CompilerIO.compilePolynomial (program expected) sourceFuel (acceptsWithin expected)

theorem polynomial_program (expected : Bool) :
    (polynomial expected).program =
      .machine (CompilerIO.rawMachine (program expected)) (CompilerIO.runtimePolynomial 9 sourceFuel) :=
  CompilerIO.compilePolynomial_program (program expected) sourceFuel (acceptsWithin expected)

private theorem output_projection (expected : Bool) (input : BitString) :
    (polynomial expected).output input =
      (CompilerIO.compilePolynomial (program expected) sourceFuel (acceptsWithin expected)).output input := rfl

theorem polynomial_output (expected : Bool) (input : BitString) :
    (polynomial expected).output input = [value expected input] := by
  rw [output_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run (program expected) 3 (BitRegister.initial (program expected) input)).store.get 8 = _
  rw [closed_run]
  rfl

def rawRefinement (expected : Bool) : FunctionProgram.RawRefinement (polynomial expected).program := by
  rw [polynomial_program]
  exact FunctionProgram.RawRefinement.ofMachine (CompilerIO.rawMachine (program expected))
    (CompilerIO.runtimePolynomial 9 sourceFuel)

theorem machine_output (expected : Bool) (input : BitString) :
    machineOutput (rawRefinement expected).machine
      ((rawRefinement expected).timeBound.eval (BitString.size input)) input = [value expected input] :=
  ((rawRefinement expected).output_eq input ((polynomial expected).haltsWithin input)).trans
    (polynomial_output expected input)

theorem absence_answer (found : Option Nat) :
    (polynomial false).output (TableOwner.answer found) = [found.isNone] := by
  rw [polynomial_output]
  cases found <;> rfl

theorem presence_answer (found : Option CNFLiteral) :
    (polynomial true).output (Occurrence.answer found) = [found.isSome] := by
  rw [polynomial_output]
  cases found <;> rfl

end PNP.Concrete.NormalizerBlocks.BooleanHead
