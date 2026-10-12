/-
Copyright (c) 2026 PNP Labs.

Closed construction of both search-vertex ranges. Both counts are read from
the input. Every raw bitstring terminates within an encoded-input polynomial,
including output-buffer packing; the compiler supplies actual tape runtime.
-/

import PNP.Concrete.NormalizerVertexPhase

namespace PNP.Concrete.NormalizerBlocks.SearchVertices

open BitRegister Occurrence

def front : Block 9 := .seq (phase true) (phase false)
def leftResult (input : BitString) : Registers := phaseResult true (initialRegisters input)
def frontResult (input : BitString) : Registers := phaseResult false (leftResult input)
def frontSteps (input : BitString) : Nat :=
  phaseSteps true (initialRegisters input) + phaseSteps false (leftResult input)

theorem front_exec (input : BitString) :
    Exec front (initialRegisters input).store (frontSteps input) (frontResult input).store :=
  Exec.seq (phase_exec true (initialRegisters input)) (phase_exec false (leftResult input))

theorem frontSteps_bound (input : BitString) :
    frontSteps input ≤ 2 * phaseBudget.eval input.length := by
  have left := phaseSteps_bound true (initialRegisters input)
  have right := phaseSteps_bound false (leftResult input)
  have size : (leftResult input).input.length ≤ input.length := phase_input_bound true (initialRegisters input)
  have mono := phaseBudget_mono size
  change phaseSteps true (initialRegisters input) ≤ phaseBudget.eval input.length at left
  simp only [frontSteps]
  omega

def block : Block 9 := .seq front ClauseQuery.pack
def program : Program 9 := block.program 0 8
def result (input : BitString) : Registers := ClauseQuery.packed (frontResult input)
def sourceSteps (input : BitString) : Nat := frontSteps input + ClauseQuery.packFuel (frontResult input)
def sourceFuel : NatPolynomial := .add (.mul (.constant 10) phaseBudget) (.linear 4 13)

theorem sourceFuel_eval (size : Nat) :
    sourceFuel.eval size = 10 * phaseBudget.eval size + (4 * size + 13) := rfl

theorem block_exec (input : BitString) :
    Exec block (initialRegisters input).store (sourceSteps input) (result input).store :=
  Exec.seq (front_exec input) (ClauseQuery.pack_exec (frontResult input))

theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (initialRegisters input).store⟩ := rfl

theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have initial : (initialRegisters input).store.Bounded input.length :=
    ⟨Nat.le_refl _, Store.empty_bounded 8 input.length⟩
  have bounded := (front_exec input).bounded input.length initial
  have buffer := Store.get_length_le (frontResult input).store (3 : Fin 9) bounded
  change (frontResult input).excess.length ≤ input.length + frontSteps input at buffer
  have front := frontSteps_bound input
  rw [sourceFuel_eval]
  change frontSteps input + (4 * (frontResult input).excess.length + 12) + 1 ≤
    10 * phaseBudget.eval input.length + (4 * input.length + 13)
  omega

theorem padded_run (input : BitString) :
    BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  have bound := sourceSteps_bound input
  have split : sourceFuel.eval input.length =
      (sourceSteps input + 1) + (sourceFuel.eval input.length - (sourceSteps input + 1)) := by omega
  rw [split, BitRegister.run_add, closed_run, BitRegister.run_accepted]

theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).control = .accepted
  rw [padded_run]

def polynomial : PolynomialTimeFunction := CompilerIO.compilePolynomial program sourceFuel acceptsWithin

theorem polynomial_program :
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 9 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin

private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl

theorem polynomial_output (input : BitString) : polynomial.output input = (result input).output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 8 = _
  rw [padded_run]
  rfl

theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

end PNP.Concrete.NormalizerBlocks.SearchVertices
