/-
Copyright (c) 2026 PNP Labs.

Closed decoder for the selected matching-entry query. The finite program
skips the fixed empty target header, counts true pairs, and returns a defined
absence value when none were present. A linear source bound covers all raw
inputs; the verified compiler supplies polynomial tape execution.
-/

import PNP.Concrete.NormalizerMatchingValueScan

namespace PNP.Concrete.NormalizerBlocks.MatchingValue

open BitRegister Occurrence

def normalizeWord : BitString → BitString
  | [] => [false]
  | bit :: rest => bit :: rest
def finished (r : Registers) : Registers := {r with output := normalizeWord r.output}
def finish : Block 9 := .branch 8 (.action (.push 8 false)) .skip .skip

theorem finish_exec (r : Registers) : Exec finish r.store 2 (finished r).store := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      cases output with
      | nil => exact Exec.empty rfl (.action _ _)
      | cons bit rest => exact Exec.nonempty rfl (.skip _)

def start : Block 9 := .seq (.action (.pop 0)) (.action (.push 6 true))
def seeded (input : BitString) : Registers := {initialRegisters input.tail with active := [true]}

theorem start_exec (input : BitString) :
    Exec start (initialRegisters input).store 2 (seeded input).store :=
  Exec.seq (.action _ _) (.action _ _)

def block : Block 9 := .seq start (.seq loop finish)
def program : Program 9 := block.program 0 8
def result (input : BitString) : Registers := finished (scan input.tail (seeded input)).state
def sourceSteps (input : BitString) : Nat := 2 + ((scan input.tail (seeded input)).fuel + 2)
def sourceFuel : NatPolynomial := .linear 3 11

theorem block_exec (input : BitString) :
    Exec block (initialRegisters input).store (sourceSteps input) (result input).store :=
  Exec.seq (start_exec input) (Exec.seq (scan_exec input.tail (seeded input))
    (finish_exec (scan input.tail (seeded input)).state))

theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (initialRegisters input).store⟩ := rfl

theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have checked := scan_fuel_bound input.tail (seeded input)
  have tail : input.tail.length ≤ input.length := by
    cases input <;> simp only [List.tail_nil, List.tail_cons, List.length_nil, List.length_cons] <;> omega
  change sourceSteps input + 1 ≤ 3 * input.length + 11
  simp only [sourceSteps]
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

end PNP.Concrete.NormalizerBlocks.MatchingValue
