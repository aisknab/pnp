/-
Copyright (c) 2026 PNP Labs.

Finite emission of a replacement matching-table entry. The unary value is
copied and consumed by a fixed loop; no value-dependent program is generated.
The resulting buffer is reversed, ready for the enclosing table scanner.
-/

import PNP.Concrete.NormalizerMatchingTable

namespace PNP.Concrete.NormalizerBlocks.TableWrite

open BitRegister Occurrence

def valueStep : Block 9 := .seq (.action (.pop 4)) (ClauseQuery.emit true true)
def valueLoop : Block 9 := .loop 4 valueStep

def valueResult (word : BitString) (r : Registers) : Registers :=
  {r with sign := [], excess := List.replicate (2 * word.length) true ++ r.excess}

theorem value_exec (word : BitString) (r : Registers) :
    Exec valueLoop ({r with sign := word}).store (4 * word.length + 1)
      (valueResult word r).store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop rfl
  | cons bit rest ih =>
      have step : Exec valueStep ({r with sign := bit :: rest}).store 3
          ({r with sign := rest, excess := true :: true :: r.excess}).store :=
        Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
      have tail := ih {r with excess := true :: true :: r.excess}
      have checked := Exec.loopStep (source := (4 : Fin 9)) (body := valueStep)
        (before := ({r with sign := bit :: rest}).store) rfl step tail
      have cost : 4 * (bit :: rest).length + 1 = 1 + (3 + (4 * rest.length + 1)) := by
        simp only [List.length_cons]
        omega
      rw [cost]
      simpa only [valueLoop, valueResult, List.length_cons, Nat.mul_succ,
        List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append] using checked

def replacement : Block 9 :=
  .seq (.action (.copy 4 1))
    (.seq (ClauseQuery.emit false true)
      (.seq (ClauseQuery.emit true true)
        (.seq valueLoop
          (.seq (ClauseQuery.emit false false)
            (.seq (ClauseQuery.emit true false) (.action (.push 5 true)))))))

def replaced (r : Registers) : Registers :=
  ⟨r.input, r.target, r.remaining,
    false :: true :: false :: false ::
      (List.replicate (2 * r.target.length) true ++ true :: true :: true :: false :: r.excess),
    [], true :: r.mode, r.active, r.reserved, r.output⟩

def replacementFuel (r : Registers) : Nat := 4 * r.target.length + 11

theorem replacement_exec (r : Registers) :
    Exec replacement r.store (replacementFuel r) (replaced r).store := by
  have checked := Exec.seq (Exec.action (.copy 4 1) r.store)
    (Exec.seq (ClauseQuery.emit_exec false true {r with sign := r.target})
      (Exec.seq (ClauseQuery.emit_exec true true (ClauseQuery.emitted false true {r with sign := r.target}))
        (Exec.seq (value_exec r.target
          (ClauseQuery.emitted true true (ClauseQuery.emitted false true {r with sign := r.target})))
          (Exec.seq (ClauseQuery.emit_exec false false _)
            (Exec.seq (ClauseQuery.emit_exec true false _) (Exec.action (.push 5 true) _))))))
  have cost : replacementFuel r =
      1 + (2 + (2 + ((4 * r.target.length + 1) + (2 + (2 + 1))))) := by
    simp only [replacementFuel]
    omega
  rw [cost]
  exact checked

theorem replacement_input (r : Registers) : (replaced r).input = r.input := rfl
theorem replacement_target (r : Registers) : (replaced r).target = r.target := rfl
theorem replacement_sign (r : Registers) : (replaced r).sign = [] := rfl

end PNP.Concrete.NormalizerBlocks.TableWrite
