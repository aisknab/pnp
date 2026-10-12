/-
Copyright (c) 2026 PNP Labs.

Closed table initialization: read the count, construct all empty entries and
pack their bytes with one outer finish token. The budget covers every raw
bitstring, and the verified compiler supplies actual polynomial tape time.
-/

import PNP.Concrete.NormalizerTableInitialization

namespace PNP.Concrete.NormalizerBlocks.TableInit

open BitRegister Occurrence

def header : Block 9 := .seq (.action (.push 6 true)) headerLoop
def seeded (input : BitString) : Registers := ⟨input, [], [], [], [], [], [true], [], []⟩
def readCount (input : BitString) : Result := headerResult input (seeded input)
def headerFuel (input : BitString) : Nat := 1 + (readCount input).fuel

theorem header_exec (input : BitString) :
    Exec header (initialRegisters input).store (headerFuel input) (readCount input).state.store := by
  have start : Exec (.action (.push 6 true)) (initialRegisters input).store 1 (seeded input).store :=
    .action _ _
  exact Exec.seq start (Occurrence.header_exec input (seeded input))

theorem headerFuel_bound (input : BitString) : headerFuel input ≤ 4 * input.length + 6 := by
  have bound : (readCount input).fuel ≤ 4 * input.length + 5 := header_fuel_bound input (seeded input)
  simp only [headerFuel]
  omega

theorem count_length_bound (input : BitString) :
    (readCount input).state.target.length ≤ 5 * input.length + 6 := by
  have initial : (initialRegisters input).store.Bounded input.length :=
    ⟨Nat.le_refl _, Store.empty_bounded 8 input.length⟩
  have bounded := (header_exec input).bounded input.length initial
  have target := Store.get_length_le (readCount input).state.store (1 : Fin 9) bounded
  change (readCount input).state.target.length ≤ input.length + headerFuel input at target
  have cost := headerFuel_bound input
  omega

def front : Block 9 := .seq header loop
def constructed (input : BitString) : Registers := built (readCount input).state.target (readCount input).state
def frontFuel (input : BitString) : Nat := headerFuel input + (6 * (readCount input).state.target.length + 1)

theorem front_exec (input : BitString) :
    Exec front (initialRegisters input).store (frontFuel input) (constructed input).store :=
  Exec.seq (header_exec input) (loop_exec (readCount input).state.target (readCount input).state)

theorem frontFuel_bound (input : BitString) : frontFuel input ≤ 34 * input.length + 43 := by
  have header := headerFuel_bound input
  have count := count_length_bound input
  simp only [frontFuel]
  omega

def block : Block 9 := .seq front ClauseQuery.pack
def program : Program 9 := block.program 0 8
def result (input : BitString) : Registers := ClauseQuery.packed (constructed input)
def sourceSteps (input : BitString) : Nat := frontFuel input + ClauseQuery.packFuel (constructed input)
def sourceFuel : NatPolynomial := .linear 174 228

theorem block_exec (input : BitString) :
    Exec block (initialRegisters input).store (sourceSteps input) (result input).store :=
  Exec.seq (front_exec input) (ClauseQuery.pack_exec (constructed input))

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
  have buffer := Store.get_length_le (constructed input).store (3 : Fin 9) bounded
  change (constructed input).excess.length ≤ input.length + frontFuel input at buffer
  have front := frontFuel_bound input
  change frontFuel input + (4 * (constructed input).excess.length + 12) + 1 ≤ 174 * input.length + 228
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

def encodeCount (count : Nat) (suffix : BitString) : BitString :=
  List.replicate count true ++ false :: suffix

end PNP.Concrete.NormalizerBlocks.TableInit
