/-
Copyright (c) 2026 PNP Labs.

Concrete output packing for internally selected clause data. The buffer is
reversed by finite bit operations, and a finish token is appended exactly once.
-/

import PNP.Concrete.NormalizerClauseScan

namespace PNP.Concrete.NormalizerBlocks.ClauseQuery

open BitRegister Occurrence

def reverseStep : Block 9 :=
  .branch 3 .skip
    (.seq (.action (.pop 3)) (.action (.push 8 false)))
    (.seq (.action (.pop 3)) (.action (.push 8 true)))

def reverseLoop : Block 9 := .loop 3 reverseStep

theorem reverse_step (r : Registers) (bit : Bool) (rest : BitString) :
    Exec reverseStep ({r with excess := bit :: rest}).store 3
      ({r with excess := rest, output := bit :: r.output}).store := by
  cases bit
  · exact Exec.zero (source := (3 : Fin 9)) rfl (Exec.seq (.action _ _) (.action _ _))
  · exact Exec.one (source := (3 : Fin 9)) rfl (Exec.seq (.action _ _) (.action _ _))

theorem reverse_exec (r : Registers) (word : BitString) :
    Exec reverseLoop ({r with excess := word}).store (4 * word.length + 1)
      ({r with excess := [], output := word.reverse ++ r.output}).store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop rfl
  | cons bit rest ih =>
      have next := ih {r with output := bit :: r.output}
      have step := Exec.loopStep (source := (3 : Fin 9)) (body := reverseStep)
        (before := ({r with excess := bit :: rest}).store) rfl (reverse_step r bit rest) next
      have cost : 4 * (bit :: rest).length + 1 = 1 + (3 + (4 * rest.length + 1)) := by
        simp only [List.length_cons]
        omega
      simpa only [reverseLoop, cost, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using step

def pack : Block 9 := .seq (.action (.clear 8)) (.seq (emit true false) reverseLoop)

def packed (r : Registers) : Registers :=
  {r with excess := [], output := r.excess.reverse ++ [true, false]}

def packFuel (r : Registers) : Nat := 4 * r.excess.length + 12

theorem pack_exec (r : Registers) : Exec pack r.store (packFuel r) (packed r).store := by
  have rev : Exec reverseLoop (emitted true false {r with output := []}).store
      (4 * (false :: true :: r.excess).length + 1) (packed r).store := by
    simpa only [emitted, packed, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append, List.append_nil] using reverse_exec {r with output := []} (false :: true :: r.excess)
  have checked := Exec.seq (Exec.action (.clear 8) r.store)
    (Exec.seq (emit_exec true false {r with output := []}) rev)
  have cost : packFuel r = 1 + (2 + (4 * (false :: true :: r.excess).length + 1)) := by
    simp only [packFuel, List.length_cons]
    omega
  simpa only [pack, cost] using checked

end PNP.Concrete.NormalizerBlocks.ClauseQuery
