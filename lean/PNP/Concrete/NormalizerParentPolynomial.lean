/-
Copyright (c) 2026 PNP Labs.

Complete concrete parent query, compiled to a deterministic finite tape
machine. Every raw packet terminates in a uniform encoded-size polynomial;
canonical packets agree with root-first ordered predecessor selection.
This is a graph-search primitive, not a solver for the original problem.
-/

import PNP.Concrete.NormalizerParentLoader

namespace PNP.Concrete.NormalizerBlocks.ParentQuery

open BitRegister

def block : Block 21 := .seq loader phase
def program : Program 21 := block.program 0 19
def result (input : BitString) : State := phaseResult (loaded input)
def sourceSteps (input : BitString) : Nat := loaderFuel input + phaseFuel (loaded input)
def sourceFuel : NatPolynomial :=
  .add (.linear 2119 3497) (.mul (.linear 784 1134) (.linear 1 1))

theorem block_exec (input : BitString) : Exec block (initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (loader_exec input) (phase_exec (loaded input))
theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (initial input).store⟩ := rfl

theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 19

theorem sourceFuel_eval (size : Nat) :
    sourceFuel.eval size = 2119 * size + 3497 + (784 * size + 1134) * (size + 1) := by
  change 2119 * size + 3497 + (784 * size + 1134) * (1 * size + 1) = _
  rw [Nat.one_mul]

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have load := loaderFuel_bound input
  have sizes := loaded_size input
  have query := phaseFuel_bound (loaded input)
  have step : stepBound (loaded input) + 1 ≤ 784 * input.length + 1134 := by
    unfold stepBound
    omega
  have product := Nat.mul_le_mul step (Nat.add_le_add_right sizes.2.2.2 1)
  rw [sourceFuel_eval]
  unfold sourceSteps
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
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 21 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin

private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl

theorem polynomial_output (input : BitString) : polynomial.output input = (result input).output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 19 = _
  rw [padded_run]
  rfl

theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 21 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

theorem polynomial_canonical (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) :
    polynomial.output (encode target clauses entries trace) = answer (value target clauses entries trace) := by
  rw [polynomial_output]
  have data := loaded_canonical target clauses entries trace
  exact phase_canonical _ target clauses entries trace data.1 data.2

private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 21 sourceFuel).eval input.length) input := rfl

theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 21 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm

theorem machine_canonical (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 21 sourceFuel).eval (encode target clauses entries trace).length)
      (encode target clauses entries trace) = answer (value target clauses entries trace) := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.ParentQuery
