/-
Copyright (c) 2026 PNP Labs.

Complete internally generated exploration compiled to a deterministic
finite tape machine. Initialization and the whole growing-trace loop have
one encoded-input polynomial bound, including arbitrary malformed input.
Canonical input returns the source exploration trace from no supplied
vertices, predecessors, selected candidates or search budget.
-/

import PNP.Concrete.NormalizerExplorationInitialize

namespace PNP.Concrete.NormalizerBlocks.Exploration
open BitRegister

def finish : Block 28 := .action (.copy 8 24)
def finished (r : State) : State := r.withRegisters {r.registers with output := r.core.trace}
theorem finish_exec (r : State) : Exec finish r.store 1 (finished r).store := .action _ _

def block : Block 28 := .seq initializeBlock (.seq loop finish)
def program : Program 28 := block.program 0 8
def result (input : BitString) : State := finished (whole (initialized input)).state
def sourceSteps (input : BitString) : Nat := initializeFuel input + ((whole (initialized input)).fuel + 1)
theorem block_exec (input : BitString) : Exec block (initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (initialize_exec input) (Exec.seq (whole_exec (initialized input)) (finish_exec (whole (initialized input)).state))
theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (initial input).store⟩ := rfl
theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

def limitPolynomial : NatPolynomial := .linear 6 6
def unseenPolynomial : NatPolynomial :=
  .add (.mul (.add (.mul (.constant 2) limitPolynomial) (.constant 8)) limitPolynomial) (.constant 2)
def tracePolynomial : NatPolynomial :=
  .mul (.add (.mul (.constant 2) limitPolynomial) (.constant 5)) limitPolynomial
def extractionPolynomial : NatPolynomial :=
  .add (.add (.add (.mul (.constant 349) unseenPolynomial) (.linear 339 0)) (.constant 1375))
    (.mul (.add (.add (.add (.add (.linear 188 0) (.linear 188 0))
      (.mul (.constant 236) tracePolynomial)) (.mul (.constant 40) unseenPolynomial)) (.constant 975))
      (.add tracePolynomial (.constant 1)))
def workPolynomial : NatPolynomial :=
  .add (.add (.add (.mul (.add extractionPolynomial (.constant 1)) (.add unseenPolynomial (.constant 1)))
    (.mul (.constant 4) unseenPolynomial)) (.mul (.constant 6) limitPolynomial)) (.constant 45)
def sourceFuel : NatPolynomial :=
  .add initializePolynomial (.add
    (.mul (.add workPolynomial (.constant 1)) (.add limitPolynomial (.constant 1))) (.constant 3))

theorem unseenPolynomial_eval (size : Nat) : unseenPolynomial.eval size = unseenBytes (6 * size + 6) := rfl
theorem tracePolynomial_eval (size : Nat) : tracePolynomial.eval size = traceBytes (6 * size + 6) := rfl
theorem extractionPolynomial_eval (size : Nat) :
    extractionPolynomial.eval size = extractionBound size size (6 * size + 6) := rfl
theorem workPolynomial_eval (size : Nat) :
    workPolynomial.eval size = workBound size size (6 * size + 6) := rfl
theorem sourceFuel_eval (size : Nat) :
    sourceFuel.eval size = initializePolynomial.eval size +
      ((workBound size size (6 * size + 6) + 1) * (6 * size + 6 + 1) + 3) := rfl

theorem initialized_loop_bound (input : BitString) :
    (whole (initialized input)).fuel ≤
      (workBound input.length input.length (6 * input.length + 6) + 1) * (6 * input.length + 6 + 1) + 1 := by
  have fields := initialized_fields input
  have sizes := source_sizes input
  exact whole_fuel_bound input.length input.length (6 * input.length + 6)
    (sourceVertices input) [] (initialized input) (initialized_within input)
    (by rw [fields.1]; exact sizes.2.1) (by rw [fields.2.1]; exact sizes.2.2.1)

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have start := initializeFuel_bound input
  have loop := initialized_loop_bound input
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
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 28 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin

private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = (result input).registers.output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 8 = _
  rw [padded_run]
  rfl
theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 28 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

theorem polynomial_canonical (variables : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    polynomial.output (encode variables clauses entries) =
      TraceData.encode (value clauses entries (clauses.length + variables)
        (SearchVertices.vertices clauses.length variables) []) := by
  have fields := initialized_fields (encode variables clauses entries)
  have data := source_canonical variables clauses entries
  have vertices : sourceVertices (encode variables clauses entries) =
      SearchVertices.vertices clauses.length variables := by
    unfold sourceVertices
    rw [data.1, data.2.2.2, List.length_replicate]
  have budget : (initialized (encode variables clauses entries)).remaining.length = clauses.length + variables := by
    rw [fields.2.2.2.2, List.length_replicate]
    unfold sourceLimit
    rw [data.1, data.2.2.2, List.length_replicate]
  have checked := whole_value (initialized (encode variables clauses entries)) clauses entries
    (SearchVertices.vertices clauses.length variables) []
    (fields.1.trans data.2.1) (fields.2.1.trans data.2.2.1)
    (by rw [fields.2.2.2.1, vertices]) fields.2.2.1
  rw [budget] at checked
  rw [polynomial_output]
  exact checked

private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 28 sourceFuel).eval input.length) input := rfl
theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 28 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm

theorem machine_canonical (variables : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 28 sourceFuel).eval (encode variables clauses entries).length)
      (encode variables clauses entries) =
      TraceData.encode (value clauses entries (clauses.length + variables)
        (SearchVertices.vertices clauses.length variables) []) := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.Exploration
