/-
Copyright (c) 2026 PNP Labs.

Closed finite query preparation from encoded target/index headers and a full
clause-list stream. Both headers, index traversal, selected bytes and packing
are executed internally. All raw words terminate within an encoded-size
polynomial bound, independently of the later canonical semantic theorem.
-/

import PNP.Concrete.NormalizerClausePack
import PNP.Concrete.NormalizerOccurrencePolynomial

namespace PNP.Concrete.NormalizerBlocks.ClauseQuery

open BitRegister Occurrence

def save : Block 9 :=
  .seq (.action (.copy 7 1)) (.seq (.action (.clear 1)) (.action (.push 6 true)))

def saved (r : Registers) : Registers :=
  {r with reserved := r.target, target := [], active := true :: r.active}

theorem save_exec (r : Registers) : Exec save r.store 3 (saved r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def prepare : Block 9 :=
  .seq (.action (.copy 2 1)) (.seq (.action (.copy 3 7))
    (.seq (.action (.push 3 false)) (.action (.push 6 true))))

def ready (r : Registers) : Registers :=
  {r with remaining := r.target, excess := false :: r.reserved, active := true :: r.active}

theorem prepare_exec (r : Registers) : Exec prepare r.store 4 (ready r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def front : Block 9 :=
  .seq (.action (.push 6 true)) (.seq headerLoop (.seq save (.seq headerLoop (.seq prepare loop))))

def seeded (input : BitString) : Registers := ⟨input, [], [], [], [], [], [true], [], []⟩
def readTarget (input : BitString) : Result := headerResult input (seeded input)
def readIndex (input : BitString) : Result :=
  headerResult (readTarget input).state.input (saved (readTarget input).state)
def scanned (input : BitString) : Result := queryResult (ready (readIndex input).state)
def frontFuel (input : BitString) : Nat :=
  1 + ((readTarget input).fuel + (3 + ((readIndex input).fuel + (4 + (scanned input).fuel))))

theorem front_exec (input : BitString) :
    Exec front (Occurrence.initialRegisters input).store (frontFuel input) (scanned input).state.store := by
  have start : Exec (.action (.push 6 true)) (Occurrence.initialRegisters input).store 1 (seeded input).store :=
    .action _ _
  have first : Exec headerLoop (seeded input).store (readTarget input).fuel (readTarget input).state.store :=
    header_exec input (seeded input)
  have second : Exec headerLoop (saved (readTarget input).state).store
      (readIndex input).fuel (readIndex input).state.store :=
    header_exec (readTarget input).state.input (saved (readTarget input).state)
  exact Exec.seq start (Exec.seq first (Exec.seq (save_exec (readTarget input).state)
    (Exec.seq second (Exec.seq (prepare_exec (readIndex input).state)
      (query_exec (ready (readIndex input).state))))))

theorem frontFuel_bound (input : BitString) : frontFuel input ≤ 16 * input.length + 27 := by
  have first : (readTarget input).fuel ≤ 4 * input.length + 5 := header_fuel_bound input (seeded input)
  have firstInput : (readTarget input).state.input.length ≤ input.length := header_input_bound input (seeded input)
  have second : (readIndex input).fuel ≤ 4 * (readTarget input).state.input.length + 5 :=
    header_fuel_bound (readTarget input).state.input (saved (readTarget input).state)
  have secondInput : (readIndex input).state.input.length ≤ (readTarget input).state.input.length :=
    header_input_bound (readTarget input).state.input (saved (readTarget input).state)
  have scan : (scanned input).fuel ≤ 8 * ((readIndex input).state.input.length + 1) + 1 :=
    query_fuel_bound (ready (readIndex input).state)
  simp only [frontFuel]
  omega

def block : Block 9 := .seq front pack
def program : Program 9 := block.program 0 8
def result (input : BitString) : Registers := packed (scanned input).state
def sourceSteps (input : BitString) : Nat := frontFuel input + packFuel (scanned input).state

theorem block_exec (input : BitString) :
    Exec block (Occurrence.initialRegisters input).store (sourceSteps input) (result input).store :=
  Exec.seq (front_exec input) (pack_exec (scanned input).state)

theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (Occurrence.initialRegisters input).store⟩ := rfl

theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ 84 * input.length + 148 := by
  have initial : (Occurrence.initialRegisters input).store.Bounded input.length :=
    ⟨Nat.le_refl _, Store.empty_bounded 8 input.length⟩
  have bound := (front_exec input).bounded input.length initial
  have buffer := Store.get_length_le (scanned input).state.store (3 : Fin 9) bound
  change (scanned input).state.excess.length ≤ input.length + frontFuel input at buffer
  have prefixBound := frontFuel_bound input
  simp only [sourceSteps, packFuel]
  omega

def sourceFuel : NatPolynomial := .linear 84 148

theorem padded_run (input : BitString) :
    BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  have bound := sourceSteps_bound input
  have split : 84 * input.length + 148 =
      (sourceSteps input + 1) + (84 * input.length + 148 - (sourceSteps input + 1)) := by omega
  change BitRegister.run program (84 * input.length + 148) _ = _
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

def encodeQuery (target index : Nat) (clauses : List (List CNFLiteral)) : BitString :=
  List.replicate target true ++ false ::
    (List.replicate index true ++ false :: encodeTokenPairs (encodeClauseListTokens clauses ++ [.finish]))

end PNP.Concrete.NormalizerBlocks.ClauseQuery
