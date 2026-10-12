/-
Copyright (c) 2026 PNP Labs.

Closed tagged root query. A clause vertex is a root exactly when its
actual matching entry is absent; a variable vertex is never a root. The
tag and index are read internally, and every raw input has polynomial
encoded execution, including empty and truncated packets.
-/

import PNP.Concrete.NormalizerRootKernel

namespace PNP.Concrete.NormalizerBlocks.RootKinds

open BitRegister Occurrence

def prepare : Block 9 := .seq (.action (.pop 0)) (.action (.push 0 false))
def clause : Block 9 := .seq prepare RootKernel.block
def block : Block 9 := .branch 0 (.action (.push 8 false)) (.action (.push 8 false)) clause
def program : Program 9 := block.program 0 8
def result : BitString → Registers
  | true :: rest => RootKernel.result (false :: rest)
  | input => {initialRegisters input with output := [false]}
def sourceSteps : BitString → Nat
  | true :: rest => 1 + (2 + RootKernel.sourceSteps (false :: rest))
  | _ => 2
def sourceFuel : NatPolynomial := .linear 339 625

theorem prepare_exec (rest : BitString) :
    Exec prepare (initialRegisters (true :: rest)).store 2 (initialRegisters (false :: rest)).store :=
  Exec.seq (.action _ _) (.action _ _)

theorem block_exec (input : BitString) :
    Exec block (initialRegisters input).store (sourceSteps input) (result input).store := by
  cases input with
  | nil => exact Exec.empty (source := (0 : Fin 9)) rfl (.action _ _)
  | cons bit rest =>
      cases bit with
      | false => exact Exec.zero (source := (0 : Fin 9)) rfl (.action _ _)
      | true =>
          exact Exec.one (source := (0 : Fin 9)) rfl
            (Exec.seq (prepare_exec rest) (RootKernel.block_exec (false :: rest)))

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  cases input with
  | nil => change 3 ≤ 625; decide
  | cons bit rest =>
      cases bit with
      | false =>
          change 3 ≤ 339 * (false :: rest).length + 625
          omega
      | true =>
          have bound := RootKernel.sourceSteps_bound (false :: rest)
          change (1 + (2 + RootKernel.sourceSteps (false :: rest))) + 1 ≤ 339 * (true :: rest).length + 625
          simp only [List.length_cons] at bound ⊢
          omega

theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (initialRegisters input).store⟩ := rfl

theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

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

def encode (vertex : CNFLiteral) (entries : MatchingTable.Entries) : BitString :=
  vertex.positive :: TableInit.encodeCount vertex.variableIndex (MatchingTable.encode entries)
def value (vertex : CNFLiteral) (entries : MatchingTable.Entries) : Bool :=
  if vertex.positive then (MatchingTable.read entries vertex.variableIndex).isNone else false

theorem polynomial_canonical (vertex : CNFLiteral) (entries : MatchingTable.Entries) :
    polynomial.output (encode vertex entries) = [value vertex entries] := by
  rw [polynomial_output]
  cases kind : vertex.positive with
  | false =>
      simp only [encode, kind, result, value, Bool.false_eq_true, ite_false]
  | true =>
      simp only [encode, kind, result, value, ite_true]
      change (RootKernel.result (MatchingRead.encodeQuery vertex.variableIndex entries)).output = _
      exact RootKernel.result_canonical vertex.variableIndex entries

private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval input.length) input := rfl

theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm

theorem machine_canonical (vertex : CNFLiteral) (entries : MatchingTable.Entries) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval (encode vertex entries).length)
      (encode vertex entries) = [value vertex entries] := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.RootKinds
