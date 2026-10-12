/-
Copyright (c) 2026 PNP Labs.

Every selected original clause contributes one mode cell, in dense row
order, including unmatched clauses. The theorem covers arbitrary selection
lengths and a runtime row counter, not a fixed prefix.
-/
import PNP.Concrete.NormalizerCacheModeLoop

namespace PNP.Concrete.NormalizerBlocks.CacheMode
open BitRegister Occurrence

def values (table : MatchingTable.Entries) (variables : List CNFLiteral)
    (formula : List (List CNFLiteral)) : List CNFLiteral → Nat → MatchingTable.Entries
  | [],_ => []
  | first :: rest,row => value table variables formula first.variableIndex row ::
      values table variables formula rest (row + 1)
def prefixBits (table : MatchingTable.Entries) (variables : List CNFLiteral)
    (formula : List (List CNFLiteral)) (selected : List CNFLiteral) (row : Nat) : BitString :=
  DenseClauses.prefixBits (MatchingTable.clauses (values table variables formula selected row))
theorem prefix_cons (table : MatchingTable.Entries) (variables : List CNFLiteral)
    (formula : List (List CNFLiteral)) (first : CNFLiteral) (rest : List CNFLiteral) (row : Nat) :
    prefixBits table variables formula (first :: rest) row =
      DenseClauses.clauseBits (MatchingTable.entryClause (value table variables formula first.variableIndex row)) ++
        prefixBits table variables formula rest (row + 1) := by
  unfold prefixBits
  rw [values]
  exact DenseClauses.prefix_cons _ _

theorem stepped_cons (r : State) (first : CNFLiteral) (rest : List CNFLiteral)
    (remaining : r.core.remaining = SearchVertices.encodeVertices (first :: rest)) :
    stepped r = bodyResult r := by
  have bytes := remaining.trans (UnseenData.encoded_cons first rest)
  unfold stepped
  rw [bytes,UnseenData.entry_shape]
theorem scan_state_step (fuel : Nat) (r : State) (nonempty : r.core.remaining ≠ []) :
    (scan (fuel + 1) r).state = (scan fuel (stepped r)).state := by
  cases remaining : r.core.remaining with
  | nil => exact False.elim (nonempty remaining)
  | cons bit rest => simp only [scan,remaining]
theorem scan_buffer (table : MatchingTable.Entries) (variables selected : List CNFLiteral)
    (formula : List (List CNFLiteral)) (row fuel : Nat) (r : State)
    (remaining : r.core.remaining = SearchVertices.encodeVertices selected)
    (counter : r.counter = List.replicate row true)
    (matching : r.matching = MatchingTable.encode table)
    (selectedVariables : r.core.core.variables = SearchVertices.encodeVertices variables)
    (dense : r.core.formula = GraphQuery.clauseData formula)
    (enough : r.core.remaining.length < fuel) :
    (scan fuel r).state.core.core.buffer =
      (prefixBits table variables formula selected row).reverse ++ r.core.core.buffer := by
  induction selected generalizing row fuel r with
  | nil =>
      have nonempty := DenseClauses.remaining_nonempty [] r.core remaining
      change r.core.remaining = [true,false] at remaining
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          have ended : (stepped r).core.remaining = [] := by
            simp only [stepped,remaining,stopped,State.withDense]
          rw [scan_state_step fuel r nonempty,scan_stopped fuel (stepped r) ended]
          change (stepped r).core.core.buffer = r.core.core.buffer
          simp only [stepped,remaining,stopped,State.withDense]
  | cons first selected ih =>
      have nonempty := DenseClauses.remaining_nonempty (first :: selected) r.core remaining
      have next := body_canonical r first selected variables table formula row
        remaining counter matching selectedVariables dense
      rw [← stepped_cons r first selected remaining] at next
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          have enoughNext : (stepped r).core.remaining.length < fuel :=
            Nat.lt_of_lt_of_le (step_progress r nonempty) (Nat.le_of_lt_succ enough)
          rw [scan_state_step fuel r nonempty,
            ih (row + 1) fuel (stepped r) next.1 next.2.1
              ((stepped_fields r).2.2.trans matching) ((stepped_fields r).2.1.trans selectedVariables)
              ((stepped_fields r).1.trans dense) enoughNext,
            next.2.2,prefix_cons,List.reverse_append,List.append_assoc]

def start : Block 19 := .seq (.action (.clear 11)) (.action (.clear 17))
def started (r : State) : State :=
  {r with core := {r.core with core := {r.core.core with buffer := []}}, counter := []}
theorem start_exec (r : State) : Exec start r.store 2 (started r).store :=
  Exec.seq (.action _ _) (.action _ _)
def front : Block 19 := .seq start loop
def frontResult (r : State) : State := (whole (started r)).state
def frontSteps (r : State) : Nat := 2 + (whole (started r)).fuel
theorem front_exec (r : State) : Exec front r.store (frontSteps r) (frontResult r).store :=
  Exec.seq (start_exec r) (whole_exec (started r))
theorem front_buffer (table : MatchingTable.Entries) (variables selected : List CNFLiteral)
    (formula : List (List CNFLiteral)) (r : State)
    (remaining : r.core.remaining = SearchVertices.encodeVertices selected)
    (matching : r.matching = MatchingTable.encode table)
    (selectedVariables : r.core.core.variables = SearchVertices.encodeVertices variables)
    (dense : r.core.formula = GraphQuery.clauseData formula) :
    (frontResult r).core.core.buffer = (prefixBits table variables formula selected 0).reverse := by
  have checked := scan_buffer table variables selected formula 0 _ (started r)
    remaining rfl matching selectedVariables dense (Nat.lt_succ_self _)
  change (frontResult r).core.core.buffer = _ ++ [] at checked
  rw [List.append_nil] at checked
  exact checked
def call : Block 19 := .seq front (liftDense DenseClauses.finish)
def called (r : State) : State :=
  (frontResult r).withDense (DenseClauses.finished (frontResult r).core)
def callSteps (r : State) : Nat := frontSteps r + DenseClauses.finishFuel (frontResult r).core
theorem call_exec (r : State) : Exec call r.store (callSteps r) (called r).store :=
  Exec.seq (front_exec r) (liftDense_exec _ (frontResult r) _ _ (DenseClauses.finish_exec _))
theorem called_fields (r : State) :
    (called r).core.formula = r.core.formula ∧
    (called r).core.core.variables = r.core.core.variables ∧
    (called r).matching = r.matching := whole_fields (started r)
theorem called_canonical (table : MatchingTable.Entries) (variables selected : List CNFLiteral)
    (formula : List (List CNFLiteral)) (r : State)
    (remaining : r.core.remaining = SearchVertices.encodeVertices selected)
    (matching : r.matching = MatchingTable.encode table)
    (selectedVariables : r.core.core.variables = SearchVertices.encodeVertices variables)
    (dense : r.core.formula = GraphQuery.clauseData formula) :
    (called r).registers.output = MatchingTable.encode (values table variables formula selected 0) := by
  change (DenseClauses.finished (frontResult r).core).registers.output = _
  rw [DenseClauses.finished_output,front_buffer table variables selected formula r
    remaining matching selectedVariables dense,List.reverse_reverse]
  exact DenseClauses.prefix_data _

def frontBound : NatPolynomial := .add (.constant 2) loopBound
theorem frontSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    frontSteps r ≤ frontBound.eval n := by
  have cursor := Store.get_length_le r.store (14 : Fin 19) bounded
  have formula := Store.get_length_le r.store (13 : Fin 19) bounded
  have variables := Store.get_length_le r.store (10 : Fin 19) bounded
  have matching := Store.get_length_le r.store (16 : Fin 19) bounded
  change r.core.remaining.length ≤ n at cursor
  change r.core.formula.length ≤ n at formula
  change r.core.core.variables.length ≤ n at variables
  change r.matching.length ≤ n at matching
  have budget : cursorBudget (started r) ≤ n := by
    change 0 + r.core.remaining.length ≤ n
    omega
  have checked := whole_fuel_bound (started r) n budget formula variables matching
  change 2 + (whole (started r)).fuel ≤ 2 + loopBound.eval n
  omega
def callBound : NatPolynomial := .add (.mul (.constant 5) frontBound) (.linear 4 13)
theorem callBound_eval (n : Nat) : callBound.eval n = 5 * frontBound.eval n + (4 * n + 13) := rfl
theorem callSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    callSteps r ≤ callBound.eval n := by
  have front := frontSteps_bound r n bounded
  have boundedAfter := (front_exec r).bounded n bounded
  have buffer := Store.get_length_le (frontResult r).store (11 : Fin 19) boundedAfter
  change (frontResult r).core.core.buffer.length ≤ n + frontSteps r at buffer
  rw [callBound_eval]
  unfold callSteps DenseClauses.finishFuel
  omega

end PNP.Concrete.NormalizerBlocks.CacheMode
