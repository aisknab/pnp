/-
Copyright (c) 2026 PNP Labs.

Closed literal-occurrence query on encoded byte input. Its program is finite,
its header and scan are internally executed, and its polynomial budget holds
for every bitstring. This query is a dependency of the derived matching/cache
construction, not a satisfiability solver or a strict standalone clause codec.
-/

import PNP.Concrete.NormalizerOccurrenceHeader
import PNP.Concrete.BitRegisterCompilerIOPolynomial

namespace PNP.Concrete.NormalizerBlocks.Occurrence

open BitRegister

def initializeBlock : Block 9 := .seq (.action (.push 8 false)) (.action (.push 6 true))

def block : Block 9 :=
  .seq initializeBlock (.seq headerLoop (.seq (.action (.push 6 true)) loop))

def program : Program 9 := block.program 0 8

def initialRegisters (input : BitString) : Registers := ⟨input, [], [], [], [], [], [], [], []⟩

def seeded (input : BitString) : Registers := ⟨input, [], [], [], [], [], [true], [], [false]⟩

def readHeader (input : BitString) : Result := headerResult input (seeded input)

def entered (input : BitString) : Registers :=
  {(readHeader input).state with active := true :: (readHeader input).state.active}

def result (input : BitString) : Result := queryResult (entered input)

def sourceSteps (input : BitString) : Nat := 2 + ((readHeader input).fuel + (1 + (result input).fuel))

theorem block_exec (input : BitString) :
    Exec block (initialRegisters input).store (sourceSteps input) (result input).state.store := by
  have start : Exec initializeBlock (initialRegisters input).store 2 (seeded input).store :=
    Exec.seq (.action _ _) (.action _ _)
  have header : Exec headerLoop (seeded input).store (readHeader input).fuel
      (readHeader input).state.store := header_exec input (seeded input)
  have activate : Exec (.action (.push 6 true)) (readHeader input).state.store 1 (entered input).store :=
    .action _ _
  exact Exec.seq start (Exec.seq header (Exec.seq activate (query_exec (entered input))))

theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (initialRegisters input).store⟩ := rfl

theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).state.store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ 16 * input.length + 22 := by
  have header := header_fuel_bound input (seeded input)
  have remaining := header_input_bound input (seeded input)
  have query := query_fuel_bound (entered input)
  change (readHeader input).fuel ≤ 4 * input.length + 5 at header
  change (readHeader input).state.input.length ≤ input.length at remaining
  change (result input).fuel ≤ 12 * ((readHeader input).state.input.length + 1) + 1 at query
  simp only [sourceSteps]
  omega

def sourceFuel : NatPolynomial := .linear 16 22

theorem padded_run (input : BitString) :
    BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input) =
      ⟨.accepted, (result input).state.store⟩ := by
  have bounded := sourceSteps_bound input
  have split : 16 * input.length + 22 =
      (sourceSteps input + 1) + (16 * input.length + 22 - (sourceSteps input + 1)) := by omega
  change BitRegister.run program (16 * input.length + 22) _ = _
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

theorem polynomial_output (input : BitString) : polynomial.output input = (result input).state.output := by
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

def encodeQuery (target : Nat) (clause : List CNFLiteral) : BitString :=
  List.replicate target true ++ false :: encodeTokenPairs (encodeLiteralListTokens clause ++ [.finish])

end PNP.Concrete.NormalizerBlocks.Occurrence
