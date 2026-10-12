/-
Copyright (c) 2026 PNP Labs.

Whole-list output and polynomial accounting for finite source-cache folds.
Each body emits one proved byte segment into a reversed buffer; initialization
and final reversal happen once. No output-sized factor is iterated recursively.
-/
import PNP.Concrete.NormalizerSelectedFold

namespace PNP.Concrete.NormalizerBlocks.SelectedFold
open BitRegister Occurrence
variable (op : Operation)

def prefixBits (output : CNFLiteral → BitString) (selected : List CNFLiteral) : BitString :=
  selected.flatMap output
theorem prefix_cons (output : CNFLiteral → BitString) (first : CNFLiteral) (rest : List CNFLiteral) :
    prefixBits output (first :: rest) = output first ++ prefixBits output rest := rfl

def BodyOutput (formula variables : BitString) (output : CNFLiteral → BitString) : Prop :=
  ∀ r first rest, r.formula = formula → r.core.variables = variables →
    r.remaining = SearchVertices.encodeVertices (first :: rest) →
    (op.after r).core.buffer = (output first).reverse ++ r.core.buffer

theorem stepped_cons (r : State) (first : CNFLiteral) (rest : List CNFLiteral)
    (remaining : r.remaining = SearchVertices.encodeVertices (first :: rest)) :
    stepped op r = op.after r := by
  have bytes := remaining.trans (UnseenData.encoded_cons first rest)
  unfold stepped
  rw [bytes, UnseenData.entry_shape]
theorem step_canonical (r : State) (first : CNFLiteral) (rest : List CNFLiteral)
    (remaining : r.remaining = SearchVertices.encodeVertices (first :: rest)) :
    (stepped op r).remaining = SearchVertices.encodeVertices rest := by
  rw [stepped_cons op r first rest remaining, op.remaining r,
    remaining, UnseenData.encoded_cons]
  exact (UnseenData.parsed_canonical first (SearchVertices.encodeVertices rest)).2.1

theorem scan_state_step (fuel : Nat) (r : State) (nonempty : r.remaining ≠ []) :
    (scan op (fuel + 1) r).state = (scan op fuel (stepped op r)).state := by
  cases remaining : r.remaining with
  | nil => exact False.elim (nonempty remaining)
  | cons bit rest => simp only [scan, remaining]

theorem scan_buffer (formula variables : BitString) (output : CNFLiteral → BitString)
    (body : BodyOutput op formula variables output) (selected : List CNFLiteral)
    (fuel : Nat) (r : State)
    (remaining : r.remaining = SearchVertices.encodeVertices selected)
    (original : r.formula = formula) (selectedVariables : r.core.variables = variables)
    (enough : r.remaining.length < fuel) :
    (scan op fuel r).state.core.buffer = (prefixBits output selected).reverse ++ r.core.buffer := by
  induction selected generalizing fuel r with
  | nil =>
      have nonempty := DenseClauses.remaining_nonempty [] r remaining
      change r.remaining = [true,false] at remaining
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          have ended : (stepped op r).remaining = [] := by
            simp only [stepped, remaining, stopped]
          rw [scan_state_step op fuel r nonempty, scan_stopped op fuel (stepped op r) ended]
          change (stepped op r).core.buffer = r.core.buffer
          simp only [stepped, remaining, stopped]
  | cons first selected ih =>
      have nonempty := DenseClauses.remaining_nonempty (first :: selected) r remaining
      have next := step_canonical op r first selected remaining
      have buffer : (stepped op r).core.buffer = (output first).reverse ++ r.core.buffer := by
        rw [stepped_cons op r first selected remaining]
        exact body r first selected original selectedVariables remaining
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          have enoughNext : (stepped op r).remaining.length < fuel :=
            Nat.lt_of_lt_of_le (step_progress op r nonempty) (Nat.le_of_lt_succ enough)
          rw [scan_state_step op fuel r nonempty,
            ih fuel (stepped op r) next ((stepped_fields op r).1.trans original)
              ((stepped_fields op r).2.trans selectedVariables) enoughNext,
            buffer, prefix_cons, List.reverse_append, List.append_assoc]

def front : Block 16 := .seq DenseClauses.start (loop op)
def frontResult (r : State) : State := (whole op (DenseClauses.started r)).state
def frontSteps (r : State) : Nat := 1 + (whole op (DenseClauses.started r)).fuel
theorem front_exec (r : State) :
    Exec (front op) r.store (frontSteps op r) (frontResult op r).store :=
  Exec.seq (DenseClauses.start_exec r) (whole_exec op (DenseClauses.started r))
theorem front_buffer (formula variables : BitString) (output : CNFLiteral → BitString)
    (body : BodyOutput op formula variables output) (selected : List CNFLiteral) (r : State)
    (remaining : r.remaining = SearchVertices.encodeVertices selected)
    (original : r.formula = formula) (selectedVariables : r.core.variables = variables) :
    (frontResult op r).core.buffer = (prefixBits output selected).reverse := by
  have checked := scan_buffer op formula variables output body selected _ (DenseClauses.started r)
    remaining original selectedVariables (Nat.lt_succ_self _)
  change (frontResult op r).core.buffer = _ ++ [] at checked
  rw [List.append_nil] at checked
  exact checked

def call : Block 16 := .seq (front op) DenseClauses.finish
def called (r : State) : State := DenseClauses.finished (frontResult op r)
def callSteps (r : State) : Nat := frontSteps op r + DenseClauses.finishFuel (frontResult op r)
theorem call_exec (r : State) : Exec (call op) r.store (callSteps op r) (called op r).store :=
  Exec.seq (front_exec op r) (DenseClauses.finish_exec (frontResult op r))
theorem called_fields (r : State) :
    (called op r).formula = r.formula ∧ (called op r).core.variables = r.core.variables :=
  whole_fields op (DenseClauses.started r)
theorem called_output (formula variables : BitString) (output : CNFLiteral → BitString)
    (body : BodyOutput op formula variables output) (selected : List CNFLiteral) (r : State)
    (remaining : r.remaining = SearchVertices.encodeVertices selected)
    (original : r.formula = formula) (selectedVariables : r.core.variables = variables) :
    (called op r).registers.output = prefixBits output selected ++ [true,false] := by
  rw [called, DenseClauses.finished_output,
    front_buffer op formula variables output body selected r remaining original selectedVariables,
    List.reverse_reverse]

def frontBound : NatPolynomial := .add (.constant 1) (loopBound op)
theorem frontSteps_bound (r : State) (bound : Nat) (bounded : r.store.Bounded bound) :
    frontSteps op r ≤ (frontBound op).eval bound := by
  have remaining := Store.get_length_le r.store (14 : Fin 16) bounded
  have formula := Store.get_length_le r.store (13 : Fin 16) bounded
  have variables := Store.get_length_le r.store (10 : Fin 16) bounded
  change r.remaining.length ≤ bound at remaining
  change r.formula.length ≤ bound at formula
  change r.core.variables.length ≤ bound at variables
  have checked := whole_fuel_bound op (DenseClauses.started r) bound remaining formula variables
  change 1 + (whole op (DenseClauses.started r)).fuel ≤ 1 + (loopBound op).eval bound
  omega
def callBound : NatPolynomial := .add (.mul (.constant 5) (frontBound op)) (.linear 4 13)
theorem callBound_eval (bound : Nat) :
    (callBound op).eval bound = 5 * (frontBound op).eval bound + (4 * bound + 13) := rfl
theorem callSteps_bound (r : State) (bound : Nat) (bounded : r.store.Bounded bound) :
    callSteps op r ≤ (callBound op).eval bound := by
  have front := frontSteps_bound op r bound bounded
  have boundedAfter := (front_exec op r).bounded bound bounded
  have buffer := Store.get_length_le (frontResult op r).store (11 : Fin 16) boundedAfter
  change (frontResult op r).core.buffer.length ≤ bound + frontSteps op r at buffer
  rw [callBound_eval]
  unfold callSteps DenseClauses.finishFuel
  omega

end PNP.Concrete.NormalizerBlocks.SelectedFold
