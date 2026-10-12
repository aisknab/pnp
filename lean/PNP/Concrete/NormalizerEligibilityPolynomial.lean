/-
Copyright (c) 2026 PNP Labs.

Complete concrete eligibility, compiled to a deterministic finite tape
machine. Every raw packet terminates within an encoded-size polynomial.
Canonical packets reject already visited vertices before computing a
root-first parent, with no supplied membership or graph answers.
This is a graph-search primitive, not a solver for the original problem.
-/

import PNP.Concrete.NormalizerEligibility

namespace PNP.Concrete.NormalizerBlocks.Eligibility

open BitRegister

def initial (input : BitString) : State := ⟨ParentQuery.initial input, []⟩
def loader : Block 22 := Frame.block 1 ParentQuery.loader
def loaded (input : BitString) : State := ⟨ParentQuery.loaded input, []⟩
theorem loader_exec (input : BitString) :
    Exec loader (initial input).store (ParentQuery.loaderFuel input) (loaded input).store :=
  Frame.execution (ParentQuery.loader_exec input) (initial input).frame

def block : Block 22 := .seq loader phase
def program : Program 22 := block.program 0 19
def result (input : BitString) : State := phaseResult (loaded input)
def sourceSteps (input : BitString) : Nat := ParentQuery.loaderFuel input + phaseFuel (loaded input)
def sourceFuel : NatPolynomial :=
  .add (.linear 2119 3504) (.mul (.linear 812 1215) (.linear 1 1))

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
    sourceFuel.eval size = 2119 * size + 3504 + (812 * size + 1215) * (size + 1) := by
  change 2119 * size + 3504 + (812 * size + 1215) * (1 * size + 1) = _
  rw [Nat.one_mul]

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have load := ParentQuery.loaderFuel_bound input
  have sizes := ParentQuery.loaded_size input
  have query := phaseFuel_bound (loaded input)
  change (loaded input).core.targetIndex.length ≤ 5 * input.length + 6 ∧
    (loaded input).core.graph.core.formula.length ≤ input.length ∧
    (loaded input).core.graph.core.matching.length ≤ input.length ∧
    (loaded input).core.pending.length ≤ input.length at sizes
  have parentStep : ParentQuery.stepBound (loaded input).core + 1 ≤ 784 * input.length + 1134 := by
    unfold ParentQuery.stepBound
    omega
  have memberStep : 28 * (loaded input).core.pending.length + 81 ≤ 28 * input.length + 81 := by omega
  have parentProduct := Nat.mul_le_mul parentStep (Nat.add_le_add_right sizes.2.2.2 1)
  have memberProduct := Nat.mul_le_mul memberStep (Nat.add_le_add_right sizes.2.2.2 1)
  have joined : (784 * input.length + 1134) * (input.length + 1) +
      (28 * input.length + 81) * (input.length + 1) = (812 * input.length + 1215) * (input.length + 1) := by
    rw [← Nat.add_mul]
    congr 1
    omega
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
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 22 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin

private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl

theorem polynomial_output (input : BitString) : polynomial.output input = (result input).core.output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 19 = _
  rw [padded_run]
  rfl

theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 22 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

theorem polynomial_canonical (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) :
    polynomial.output (ParentQuery.encode target clauses entries trace) = ParentQuery.answer (value target clauses entries trace) := by
  rw [polynomial_output]
  have data := ParentQuery.loaded_canonical target clauses entries trace
  exact phase_canonical _ target clauses entries trace data.1 data.2

private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 22 sourceFuel).eval input.length) input := rfl

theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 22 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm

theorem machine_canonical (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 22 sourceFuel).eval (ParentQuery.encode target clauses entries trace).length)
      (ParentQuery.encode target clauses entries trace) = ParentQuery.answer (value target clauses entries trace) := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.Eligibility
