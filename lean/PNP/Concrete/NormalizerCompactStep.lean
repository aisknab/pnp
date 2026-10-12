/-
Copyright (c) 2026 PNP Labs.

A total guarded compaction step. Equal token bits start a literal; a clause
delimiter or malformed/truncated token ends the scan. Every live step
strictly shortens the pending cursor, independently of lookup success.
-/
import PNP.Concrete.NormalizerCompactLiteral

namespace PNP.Concrete.NormalizerBlocks.CompactClause
open BitRegister Occurrence

def guardInput : Block 13 := .seq (.action (.copy 0 9)) (.action (.pop 0))
def guarded (r : State) : State := r.withCore {r.core with input := r.pending.tail}
theorem guardInput_exec (r : State) : Exec guardInput r.store 2 (guarded r).store :=
  Exec.seq (.action _ _) (.action _ _)

def stop : Block 13 := .action (.clear 9)
def stopped (r : State) : State := {r with pending := []}
theorem stop_exec (r : State) : Exec stop r.store 1 (stopped r).store := .action _ _

def secondBit (first : Bool) : Block 13 :=
  if first then .branch 0 stop stop body else .branch 0 stop body stop
def step : Block 13 :=
  .seq guardInput (.branch 9 stop (secondBit false) (secondBit true))
def stepped (r : State) : State :=
  match r.pending with
  | false :: false :: _ | true :: true :: _ => compacted (guarded r)
  | _ => stopped (guarded r)
def stepFuel (r : State) : Nat :=
  match r.pending with
  | [] => 4
  | false :: false :: _ | true :: true :: _ => 4 + bodyFuel (guarded r)
  | _ => 5

private theorem four_add (fuel : Nat) : 4 + fuel = 2 + (1 + (1 + fuel)) := by omega

theorem step_exec (r : State) : Exec step r.store (stepFuel r) (stepped r).store := by
  cases pending : r.pending with
  | nil =>
      simpa only [step, stepFuel, stepped, pending] using
        Exec.seq (guardInput_exec r)
          (Exec.empty (source := (9 : Fin 13)) (before := (guarded r).store)
            pending (stop_exec (guarded r)))
  | cons first tail =>
      cases tail with
      | nil =>
          have empty : (guarded r).store.get 0 = [] := by
            change r.pending.tail = []
            rw [pending]
            rfl
          cases first
          · simpa only [step, secondBit, Bool.false_eq_true, ite_false, stepFuel, stepped, pending] using
              Exec.seq (guardInput_exec r)
                (Exec.zero (source := (9 : Fin 13)) (before := (guarded r).store) pending
                  (Exec.empty (source := (0 : Fin 13)) empty (stop_exec (guarded r))))
          · simpa only [step, secondBit, ite_true, stepFuel, stepped, pending] using
              Exec.seq (guardInput_exec r)
                (Exec.one (source := (9 : Fin 13)) (before := (guarded r).store) pending
                  (Exec.empty (source := (0 : Fin 13)) empty (stop_exec (guarded r))))
      | cons second rest =>
          have read : (guarded r).store.get 0 = second :: rest := by
            change r.pending.tail = second :: rest
            rw [pending]
            rfl
          cases first <;> cases second
          · simpa only [step, secondBit, Bool.false_eq_true, ite_false, stepFuel, stepped, pending, four_add] using
              Exec.seq (guardInput_exec r)
                (Exec.zero (source := (9 : Fin 13)) (before := (guarded r).store) pending
                  (Exec.zero (source := (0 : Fin 13)) read (body_exec (guarded r))))
          · simpa only [step, secondBit, Bool.false_eq_true, ite_false, stepFuel, stepped, pending] using
              Exec.seq (guardInput_exec r)
                (Exec.zero (source := (9 : Fin 13)) (before := (guarded r).store) pending
                  (Exec.one (source := (0 : Fin 13)) read (stop_exec (guarded r))))
          · simpa only [step, secondBit, ite_true, stepFuel, stepped, pending] using
              Exec.seq (guardInput_exec r)
                (Exec.one (source := (9 : Fin 13)) (before := (guarded r).store) pending
                  (Exec.zero (source := (0 : Fin 13)) read (stop_exec (guarded r))))
          · simpa only [step, secondBit, ite_true, stepFuel, stepped, pending, four_add] using
              Exec.seq (guardInput_exec r)
                (Exec.one (source := (9 : Fin 13)) (before := (guarded r).store) pending
                  (Exec.one (source := (0 : Fin 13)) read (body_exec (guarded r))))

theorem stepped_variables (r : State) : (stepped r).variables = r.variables := by
  unfold stepped
  split
  · exact (compacted_fields (guarded r)).2.1
  · exact (compacted_fields (guarded r)).2.1
  · rfl

theorem step_progress (r : State) (nonempty : r.pending ≠ []) :
    (stepped r).pending.length < r.pending.length := by
  unfold stepped
  split
  · rw [(compacted_fields (guarded r)).1]
    exact next_shorter r.pending nonempty
  · rw [(compacted_fields (guarded r)).1]
    exact next_shorter r.pending nonempty
  · change 0 < r.pending.length
    exact List.length_pos_iff.mpr nonempty

theorem stepFuel_bound (r : State) :
    stepFuel r ≤ 7 * r.pending.length + 64 * r.variables.length + 118 := by
  have bound := bodyFuel_bound (guarded r)
  change bodyFuel (guarded r) ≤ 7 * r.pending.length + 64 * r.variables.length + 114 at bound
  unfold stepFuel
  split <;> omega

theorem stepped_literal (r : State) (literal : CNFLiteral) (suffix : BitString)
    (pending : r.pending = NANDFrontend.literalBits literal.positive literal.variableIndex ++ suffix) :
    stepped r = compacted (guarded r) := by
  cases positive : literal.positive <;>
    simp only [stepped, pending, NANDFrontend.literalBits, positive,
      List.cons_append, List.nil_append]

theorem step_canonical (r : State) (literal : CNFLiteral) (vertices : List CNFLiteral)
    (suffix : BitString)
    (pending : r.pending = NANDFrontend.literalBits literal.positive literal.variableIndex ++ suffix)
    (variables : r.variables = SearchVertices.encodeVertices vertices) :
    (stepped r).pending = suffix ∧
      (stepped r).buffer = (literalOutput (compactLiteral vertices literal)).reverse ++ r.buffer := by
  rw [stepped_literal r literal suffix pending]
  exact ⟨compacted_suffix (guarded r) literal suffix pending,
    compacted_buffer (guarded r) literal vertices suffix pending variables⟩

end PNP.Concrete.NormalizerBlocks.CompactClause
