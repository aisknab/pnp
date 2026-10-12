/-
Copyright (c) 2026 PNP Labs.

Complete dense-clause construction call. The output buffer is initialized
once, all selected clauses are derived, and finite reversal emits the exact
clause-list encoding. Formula and variable data remain protected throughout.
-/
import PNP.Concrete.NormalizerDenseSemantics

namespace PNP.Concrete.NormalizerBlocks.DenseClauses
open BitRegister Occurrence

def start : Block 16 := .action (.clear 11)
def started (r : State) : State := {r with core := {r.core with buffer := []}}
theorem start_exec (r : State) : Exec start r.store 1 (started r).store := .action _ _
def front : Block 16 := .seq start loop
def frontResult (r : State) : State := (whole (started r)).state
def frontSteps (r : State) : Nat := 1 + (whole (started r)).fuel
theorem front_exec (r : State) : Exec front r.store (frontSteps r) (frontResult r).store :=
  Exec.seq (start_exec r) (whole_exec (started r))

def loadBuffer : Block 16 := .action (.copy 3 11)
def bufferLoaded (r : State) : State := r.withRegisters {r.registers with excess := r.core.buffer}
theorem loadBuffer_exec (r : State) : Exec loadBuffer r.store 1 (bufferLoaded r).store := .action _ _
def finish : Block 16 := .seq loadBuffer (liftCore ClauseQuery.pack)
def finished (r : State) : State :=
  r.withRegisters (ClauseQuery.packed {r.registers with excess := r.core.buffer})
def finishFuel (r : State) : Nat := 1 + (4 * r.core.buffer.length + 12)
theorem finish_exec (r : State) : Exec finish r.store (finishFuel r) (finished r).store :=
  Exec.seq (loadBuffer_exec r)
    (liftCore_exec _ (bufferLoaded r) _ _ (ClauseQuery.pack_exec (bufferLoaded r).registers))
theorem finished_output (r : State) :
    (finished r).registers.output = r.core.buffer.reverse ++ [true,false] := rfl

def call : Block 16 := .seq front finish
def called (r : State) : State := finished (frontResult r)
def callSteps (r : State) : Nat := frontSteps r + finishFuel (frontResult r)
theorem call_exec (r : State) : Exec call r.store (callSteps r) (called r).store :=
  Exec.seq (front_exec r) (finish_exec (frontResult r))

theorem front_buffer (formula : List (List CNFLiteral)) (vertices selected : List CNFLiteral)
    (r : State)
    (remaining : r.remaining = SearchVertices.encodeVertices selected)
    (variables : r.core.variables = SearchVertices.encodeVertices vertices)
    (original : r.formula = GraphQuery.clauseData formula) :
    (frontResult r).core.buffer = (prefixBits (value formula vertices selected)).reverse := by
  have checked := whole_buffer formula vertices selected (started r) remaining variables original
  change (frontResult r).core.buffer = _ ++ [] at checked
  rw [List.append_nil] at checked
  exact checked

theorem called_canonical (formula : List (List CNFLiteral)) (vertices selected : List CNFLiteral)
    (r : State)
    (remaining : r.remaining = SearchVertices.encodeVertices selected)
    (variables : r.core.variables = SearchVertices.encodeVertices vertices)
    (original : r.formula = GraphQuery.clauseData formula) :
    (called r).registers.output = GraphQuery.clauseData (value formula vertices selected) := by
  rw [called, finished_output, front_buffer formula vertices selected r remaining variables original,
    List.reverse_reverse, prefix_data]

theorem called_fields (r : State) :
    (called r).formula = r.formula ∧ (called r).core.variables = r.core.variables :=
  whole_fields (started r)

def frontBound : NatPolynomial := .add (.constant 1) loopBound
theorem frontSteps_bound (r : State) (bound : Nat) (bounded : r.store.Bounded bound) :
    frontSteps r ≤ frontBound.eval bound := by
  have remaining := Store.get_length_le r.store (14 : Fin 16) bounded
  have formula := Store.get_length_le r.store (13 : Fin 16) bounded
  have variables := Store.get_length_le r.store (10 : Fin 16) bounded
  change r.remaining.length ≤ bound at remaining
  change r.formula.length ≤ bound at formula
  change r.core.variables.length ≤ bound at variables
  have loop := whole_fuel_bound (started r) bound remaining formula variables
  change 1 + (whole (started r)).fuel ≤ 1 + loopBound.eval bound
  omega

def callBound : NatPolynomial :=
  .add (.mul (.constant 5) frontBound) (.linear 4 13)
theorem callBound_eval (bound : Nat) :
    callBound.eval bound = 5 * frontBound.eval bound + (4 * bound + 13) := rfl
theorem callSteps_bound (r : State) (bound : Nat) (bounded : r.store.Bounded bound) :
    callSteps r ≤ callBound.eval bound := by
  have front := frontSteps_bound r bound bounded
  have boundedAfter := (front_exec r).bounded bound bounded
  have buffer := Store.get_length_le (frontResult r).store (11 : Fin 16) boundedAfter
  change (frontResult r).core.buffer.length ≤ bound + frontSteps r at buffer
  rw [callBound_eval]
  unfold callSteps finishFuel
  omega

end PNP.Concrete.NormalizerBlocks.DenseClauses
