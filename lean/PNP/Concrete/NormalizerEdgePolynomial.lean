/-
Copyright (c) 2026 PNP Labs.

Complete closed directed-edge query. The endpoint kinds, endpoint indices,
formula and matching are all read from a single input word. A uniform
encoded-size polynomial covers every raw word and each of the four kinds.
-/

import PNP.Concrete.NormalizerEdgeDispatch

namespace PNP.Concrete.NormalizerBlocks.EdgeKinds

open BitRegister

def block : Block 16 := .seq loader dispatch
def program : Program 16 := block.program 0 8
def result (input : BitString) : State := dispatchResult (loaded input)
def sourceSteps (input : BitString) : Nat := loaderFuel input + dispatchFuel (loaded input)
def sourceFuel : NatPolynomial := .linear 817 1173

theorem block_exec (input : BitString) : Exec block (initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (loader_exec input) (dispatch_exec (loaded input))

theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (initial input).store⟩ := rfl

theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have loader := loaderFuel_bound input
  have sizes := loaded_size input
  have dispatch := dispatchFuel_bound (loaded input)
  simp only [branchBound] at dispatch
  change loaderFuel input + dispatchFuel (loaded input) + 1 ≤ 817 * input.length + 1173
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
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 16 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin

private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl

theorem polynomial_output (input : BitString) : polynomial.output input = (result input).core.core.output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 8 = _
  rw [padded_run]
  rfl

theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 16 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

def value (first second : CNFLiteral) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) : Bool :=
  if first.positive then
    if second.positive then false else ForwardEdge.value second.variableIndex first.variableIndex clauses entries
  else if second.positive then MatchingTable.read entries second.variableIndex == some first.variableIndex else false

theorem polynomial_canonical (first second : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) :
    polynomial.output (encode first second clauses entries) = [value first second clauses entries] := by
  obtain ⟨targetRead, indexRead, formulaRead, matchingRead⟩ :=
    ForwardEdge.loaded_canonical first.variableIndex second.variableIndex clauses entries
  rw [polynomial_output]
  change (dispatchResult (loaded (encode first second clauses entries))).core.core.output = _
  rw [dispatch_output, loaded_first, loaded_second, loaded_core]
  cases firstKind : first.positive <;> cases secondKind : second.positive
  · simp only [value, firstKind, secondKind, Bool.false_eq_true, ite_false]
  · simp only [value, firstKind, secondKind, Bool.false_eq_true, ite_false, ite_true]
    exact reverse_canonical _ _ _ entries targetRead indexRead matchingRead
  · simp only [value, firstKind, secondKind, Bool.false_eq_true, ite_false, ite_true]
    exact forward_canonical _ _ _ clauses entries targetRead indexRead formulaRead matchingRead
  · simp only [value, firstKind, secondKind, ite_true]

private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 16 sourceFuel).eval input.length) input := rfl

theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 16 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm

theorem machine_canonical (first second : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 16 sourceFuel).eval (encode first second clauses entries).length)
      (encode first second clauses entries) = [value first second clauses entries] := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.EdgeKinds
