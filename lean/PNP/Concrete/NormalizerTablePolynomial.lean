/-
Copyright (c) 2026 PNP Labs.

Closed table writer with internally read index and value headers. Its fixed
register program has a polynomial encoded-input budget on every bitstring.
The compiler turns that source execution bound into a concrete tape-runtime
bound. Canonical read/write semantics are an additional, separate obligation.
-/

import PNP.Concrete.NormalizerTableScan

namespace PNP.Concrete.NormalizerBlocks.TableWrite

open BitRegister Occurrence

def prepare : Block 9 :=
  .seq (.action (.copy 2 7)) (.action (.push 6 true))

def ready (r : Registers) : Registers :=
  {r with remaining := r.reserved, active := true :: r.active}

theorem prepare_exec (r : Registers) : Exec prepare r.store 2 (ready r).store :=
  Exec.seq (.action _ _) (.action _ _)

def headers : Block 9 :=
  .seq (.action (.push 6 true))
    (.seq headerLoop (.seq ClauseQuery.save (.seq headerLoop prepare)))

def seeded (input : BitString) : Registers := ⟨input, [], [], [], [], [], [true], [], []⟩
def readIndex (input : BitString) : Result := headerResult input (seeded input)
def readValue (input : BitString) : Result :=
  headerResult (readIndex input).state.input (ClauseQuery.saved (readIndex input).state)
def prepared (input : BitString) : Registers := ready (readValue input).state
def headerFuel (input : BitString) : Nat :=
  1 + ((readIndex input).fuel + (3 + ((readValue input).fuel + 2)))

theorem headers_exec (input : BitString) :
    Exec headers (initialRegisters input).store (headerFuel input) (prepared input).store := by
  have start : Exec (.action (.push 6 true)) (initialRegisters input).store 1 (seeded input).store :=
    .action _ _
  have first : Exec headerLoop (seeded input).store (readIndex input).fuel (readIndex input).state.store :=
    header_exec input (seeded input)
  have second : Exec headerLoop (ClauseQuery.saved (readIndex input).state).store
      (readValue input).fuel (readValue input).state.store :=
    header_exec (readIndex input).state.input (ClauseQuery.saved (readIndex input).state)
  exact Exec.seq start (Exec.seq first (Exec.seq (ClauseQuery.save_exec (readIndex input).state)
    (Exec.seq second (prepare_exec (readValue input).state))))

theorem headerFuel_bound (input : BitString) : headerFuel input ≤ 8 * input.length + 16 := by
  have first : (readIndex input).fuel ≤ 4 * input.length + 5 := header_fuel_bound input (seeded input)
  have firstInput : (readIndex input).state.input.length ≤ input.length := header_input_bound input (seeded input)
  have second : (readValue input).fuel ≤ 4 * (readIndex input).state.input.length + 5 :=
    header_fuel_bound (readIndex input).state.input (ClauseQuery.saved (readIndex input).state)
  simp only [headerFuel]
  omega

theorem prepared_input_bound (input : BitString) : (prepared input).input.length ≤ input.length := by
  have first := header_input_bound input (seeded input)
  have second := header_input_bound (readIndex input).state.input (ClauseQuery.saved (readIndex input).state)
  exact Nat.le_trans second first

theorem prepared_target_bound (input : BitString) :
    (prepared input).target.length ≤ 9 * input.length + 16 := by
  have initial : (initialRegisters input).store.Bounded input.length :=
    ⟨Nat.le_refl _, Store.empty_bounded 8 input.length⟩
  have bounded := (headers_exec input).bounded input.length initial
  have target := Store.get_length_le (prepared input).store (1 : Fin 9) bounded
  change (prepared input).target.length ≤ input.length + headerFuel input at target
  have cost := headerFuel_bound input
  omega

def front : Block 9 := .seq headers loop
def scanned (input : BitString) : Result := queryResult (prepared input)
def frontFuel (input : BitString) : Nat := headerFuel input + (scanned input).fuel
def frontBound : NatPolynomial := .add (.linear 8 17) (.mul (.linear 36 82) (.linear 1 1))

theorem front_exec (input : BitString) :
    Exec front (initialRegisters input).store (frontFuel input) (scanned input).state.store :=
  Exec.seq (headers_exec input) (query_exec (prepared input))

theorem frontFuel_bound (input : BitString) : frontFuel input ≤ frontBound.eval input.length := by
  have headers := headerFuel_bound input
  have length := prepared_input_bound input
  have target := prepared_target_bound input
  have scan : (scanned input).fuel ≤
      (4 * (prepared input).target.length + 18) * ((prepared input).input.length + 1) + 1 :=
    query_fuel_bound (prepared input)
  have factor : 4 * (prepared input).target.length + 18 ≤ 36 * input.length + 82 := by omega
  have count : (prepared input).input.length + 1 ≤ input.length + 1 := Nat.add_le_add_right length 1
  have product := Nat.mul_le_mul factor count
  simp only [frontFuel, frontBound, NatPolynomial.eval, NatPolynomial.linear, Nat.one_mul]
  omega

def pack : Block 9 := .seq (.action (.clear 8)) ClauseQuery.reverseLoop
def packed (r : Registers) : Registers := {r with excess := [], output := r.excess.reverse}
def packFuel (r : Registers) : Nat := 4 * r.excess.length + 2

theorem pack_exec (r : Registers) : Exec pack r.store (packFuel r) (packed r).store := by
  have rev : Exec ClauseQuery.reverseLoop ({r with output := []}).store
      (4 * r.excess.length + 1) (packed r).store := by
    simpa only [packed, List.append_nil] using ClauseQuery.reverse_exec {r with output := []} r.excess
  have checked := Exec.seq (Exec.action (.clear 8) r.store) rev
  have cost : packFuel r = 1 + (4 * r.excess.length + 1) := by
    simp only [packFuel]
    omega
  rw [cost]
  exact checked

def block : Block 9 := .seq front pack
def program : Program 9 := block.program 0 8
def result (input : BitString) : Registers := packed (scanned input).state
def sourceSteps (input : BitString) : Nat := frontFuel input + packFuel (scanned input).state
def sourceFuel : NatPolynomial := .add (.mul (.constant 5) frontBound) (.linear 4 3)

theorem block_exec (input : BitString) :
    Exec block (initialRegisters input).store (sourceSteps input) (result input).store :=
  Exec.seq (front_exec input) (pack_exec (scanned input).state)

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
  have buffer := Store.get_length_le (scanned input).state.store (3 : Fin 9) bounded
  change (scanned input).state.excess.length ≤ input.length + frontFuel input at buffer
  have front := frontFuel_bound input
  change frontFuel input + (4 * (scanned input).state.excess.length + 2) + 1 ≤
    5 * frontBound.eval input.length + (4 * input.length + 3)
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

def encodeWrite (index value : Nat) (entries : MatchingTable.Entries) : BitString :=
  List.replicate index true ++ false :: (List.replicate value true ++ false :: MatchingTable.encode entries)

end PNP.Concrete.NormalizerBlocks.TableWrite
