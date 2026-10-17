import PNP.Concrete.ResidualReduction.SourceOrderedScanInstructions

/-! Counted row/column recovery from the internally computed scan position.
The machine increments unary counters and resets the column at each row boundary;
division, list indexing and coordinate construction are not machine primitives. -/

namespace PNP.Concrete.ResidualReduction.SourceOrderedScan
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence

def walk (width row column : Nat) : Nat → Nat × Nat
  | 0 => (row, column)
  | count + 1 =>
      if column + 1 = width then walk width (row + 1) 0 count
      else walk width row (column + 1) count

def walkFuel (width column : Nat) : Nat → Nat
  | 0 => 1
  | count + 1 =>
      if column + 1 = width then 7 + walkFuel width 0 count
      else 5 + walkFuel width (column + 1) count

theorem walkFuel_bound (width column count : Nat) :
    walkFuel width column count ≤ 7 * count + 1 := by
  induction count generalizing column with
  | zero => exact Nat.le_refl 1
  | succ count ih =>
    simp only [walkFuel]
    split
    · have bound := ih 0; omega
    · have bound := ih (column + 1); omega

theorem walk_invariant (width row column count : Nat) (h : column < width) :
    (walk width row column count).1 * width + (walk width row column count).2 =
        row * width + column + count ∧
      (walk width row column count).2 < width := by
  induction count generalizing row column with
  | zero => exact ⟨by simp only [walk, Nat.add_zero], h⟩
  | succ count ih =>
    simp only [walk]
    split
    · rename_i boundary
      have result := ih (row + 1) 0 (by omega)
      rw [Nat.add_mul, Nat.one_mul] at result
      exact ⟨by omega, result.2⟩
    · rename_i interior
      have result := ih row (column + 1) (by omega)
      exact ⟨by omega, result.2⟩

theorem walk_row_bound (rows width count : Nat) (hn : 0 < width) (h : count < rows * width) :
    (walk width 0 0 count).1 < rows := by
  have invariant := walk_invariant width 0 0 count hn
  simp only [Nat.zero_mul, Nat.zero_add] at invariant
  by_cases order : rows ≤ (walk width 0 0 count).1
  · have product := Nat.mul_le_mul_right width order
    omega
  · omega

def cursor (r : Registers) (width row column count : Nat) : Registers :=
  {r with
    target := List.replicate row true
    remaining := List.replicate (width - column) true
    excess := List.replicate column true
    mode := List.replicate width true
    output := List.replicate count true}

def coordinateStep : Block 9 :=
  .seq (.action (.pop 8)) <| .seq (.action (.pop 2)) <|
    .branch 2
      (.seq (.action (.clear 3)) (.seq (.action (.copy 2 5)) (.action (.push 1 true))))
      (.action (.push 3 true))
      (.action (.push 3 true))
def coordinateLoop : Block 9 := .loop 8 coordinateStep

theorem coordinate_step_boundary (r : Registers) :
    Exec coordinateStep ({r with remaining := [true], output := true :: r.output}).store 6
      ({r with target := true :: r.target, remaining := r.mode, excess := []}).store := by
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.empty rfl (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))))

theorem coordinate_step_interior (r : Registers) (tail : BitString) :
    Exec coordinateStep ({r with remaining := true :: true :: tail, output := true :: r.output}).store 4
      ({r with remaining := true :: tail, excess := true :: r.excess}).store := by
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.one rfl (.action _ _)))

theorem coordinate_loop_exec (r : Registers) (width row column count : Nat) (h : column < width) :
    Exec coordinateLoop (cursor r width row column count).store (walkFuel width column count)
      (cursor r width (walk width row column count).1 (walk width row column count).2 0).store := by
  induction count generalizing row column with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    by_cases boundary : column + 1 = width
    · have left : width - column = 1 := by omega
      have first : Exec coordinateStep (cursor r width row column (count + 1)).store 6
          (cursor r width (row + 1) 0 count).store := by
        simpa only [cursor, left, List.replicate_succ, List.replicate_zero,
          Nat.sub_zero] using coordinate_step_boundary (cursor r width row column count)
      have rest := ih (row + 1) 0 (by omega)
      have checked := Exec.loopStep (source := (8 : Fin 9)) rfl first rest
      simpa only [coordinateLoop, walk, walkFuel, boundary, if_true, ← Nat.add_assoc] using checked
    · have next : column + 1 < width := by omega
      obtain ⟨tail, remaining⟩ : ∃ tail, width - (column + 1) = tail + 1 :=
        ⟨width - (column + 1) - 1, by omega⟩
      have left : width - column = tail + 2 := by omega
      have first : Exec coordinateStep (cursor r width row column (count + 1)).store 4
          (cursor r width row (column + 1) count).store := by
        simpa only [cursor, left, remaining, List.replicate_succ] using
          coordinate_step_interior (cursor r width row column count) (List.replicate tail true)
      have rest := ih row (column + 1) next
      have checked := Exec.loopStep (source := (8 : Fin 9)) rfl first rest
      simpa only [coordinateLoop, walk, walkFuel, boundary, if_false, ← Nat.add_assoc] using checked

def coordinatePrepare : Block 9 :=
  .seq (.action (.clear 1)) (.seq (.action (.copy 2 5)) (.action (.clear 3)))
def coordinateBlock : Block 9 := .seq coordinatePrepare coordinateLoop

theorem coordinate_prepare_exec (r : Registers) (width count : Nat) :
    Exec coordinatePrepare ({r with mode := List.replicate width true, output := List.replicate count true}).store 3
      (cursor r width 0 0 count).store := by
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

theorem coordinate_exec (r : Registers) (width count : Nat) (hn : 0 < width) :
    Exec coordinateBlock ({r with mode := List.replicate width true, output := List.replicate count true}).store
      (3 + walkFuel width 0 count)
      (cursor r width (walk width 0 0 count).1 (walk width 0 0 count).2 0).store :=
  Exec.seq (coordinate_prepare_exec r width count) (coordinate_loop_exec r width 0 0 count hn)

theorem entries_succ (m n : Nat) :
    BilinearSelection.entries (m + 1) n =
      (List.finRange n).map (fun j => ((0 : Fin (m + 1)), j)) ++
        (BilinearSelection.entries m n).map (fun e => (e.1.succ, e.2)) := by
  simp only [BilinearSelection.entries, List.finRange_succ, List.flatMap_cons,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]

theorem finRange_get {n : Nat} (j : Fin n) : (List.finRange n)[j.val]? = some j := by
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨by simpa only [List.length_finRange] using j.isLt, ?_⟩
  rw [List.getElem_finRange]
  rfl

theorem entries_get {m n : Nat} (i : Fin m) (j : Fin n) :
    (BilinearSelection.entries m n)[i.val * n + j.val]? = some (i, j) := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [entries_succ]
      simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add]
      rw [List.getElem?_append_left (by simpa only [List.length_map, List.length_finRange] using j.isLt),
        List.getElem?_map, finRange_get]
      rfl
    · rw [entries_succ, List.getElem?_append_right (by
          simp only [List.length_map, List.length_finRange, Fin.val_succ, Nat.add_mul, Nat.one_mul]
          omega)]
      simp only [List.length_map, List.length_finRange, Fin.val_succ]
      have offset : (i.val + 1) * n + j.val - n = i.val * n + j.val := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [offset, List.getElem?_map, ih i]
      rfl

def recoveredEntry {m n : Nat} (position : Nat) (hn : 0 < n) (hp : position < m * n) : Fin m × Fin n :=
  (⟨(walk n 0 0 position).1, walk_row_bound m n position hn hp⟩,
    ⟨(walk n 0 0 position).2, (walk_invariant n 0 0 position hn).2⟩)

theorem recovered_entry_exact {m n : Nat} (position : Nat) (hn : 0 < n) (hp : position < m * n) :
    (BilinearSelection.entries m n)[position]? = some (recoveredEntry position hn hp) := by
  have invariant := (walk_invariant n 0 0 position hn).1
  simp only [Nat.zero_mul, Nat.zero_add] at invariant
  have checked := entries_get (recoveredEntry position hn hp).1 (recoveredEntry position hn hp).2
  simpa only [recoveredEntry, invariant] using checked

end PNP.Concrete.ResidualReduction.SourceOrderedScan
