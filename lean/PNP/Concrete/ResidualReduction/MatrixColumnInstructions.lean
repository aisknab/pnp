import PNP.Concrete.ResidualReduction.MatrixPivotInstructions

/-! One complete Gaussian-elimination column on arbitrary encoded matrices.
The finite program discovers its own first pivot and transforms every row.
It agrees with the existing solver in both pivot and no-pivot branches and
counts all search and row work. This is not yet the complete multi-column
solver, its affine solution-map reconstruction, or a raw-machine bound. -/

namespace PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear

def eliminating {n : Nat} (rows : System (n + 1)) (saved : BitString)
    (pivot : Option (Affine n)) (acc : BitString) : Registers :=
  {pivotResult n saved pivot with input := matrixBits rows, excess := acc}

def copyRow : Block 9 := .seq prepareRow copyLoop
def xorRow : Block 9 := .seq prepareRow (.seq (.action (.copy 5 4)) xorLoop)
def eliminationBody : Block 9 := .branch 0 .skip copyRow xorRow
def eliminationLoop : Block 9 := .loop 0 eliminationBody

theorem copyRow_exec {n : Nat} (a : Affine n) (rows : System (n + 1))
    (saved : BitString) (pivot : Option (Affine n)) (acc : BitString) :
    Exec copyRow (eliminating ((false, a) :: rows) saved pivot acc).store
      (5 * (n + 1) + 3)
      (eliminating rows saved pivot ((affineWord a).reverse ++ acc)).store := by
  have ready : Exec prepareRow (eliminating ((false, a) :: rows) saved pivot acc).store 2
      ({pivotResult n saved pivot with input := affineWord a ++ matrixBits rows, remaining := List.replicate (n + 1) true, excess := acc}).store :=
    Exec.seq (.action _ _) (.action _ _)
  have copied := copy_exec {pivotResult n saved pivot with excess := acc}
    (affineWord a) (matrixBits rows)
  rw [affineWord_length] at copied
  have checked := Exec.seq ready copied
  have cost : 5 * (n + 1) + 3 = 2 + (5 * (n + 1) + 1) := by omega
  simpa only [copyRow, eliminating, pivotResult, base, cost] using checked

theorem xorRow_exec {n : Nat} (p a : Affine n) (rows : System (n + 1))
    (saved acc : BitString) :
    Exec xorRow (eliminating ((true, a) :: rows) saved (some p) acc).store
      (7 * (n + 1) + 4)
      (eliminating rows saved (some p)
        ((affineWord (substitute p (true, a))).reverse ++ acc)).store := by
  have ready : Exec prepareRow (eliminating ((true, a) :: rows) saved (some p) acc).store 2
      ({pivotResult n saved (some p) with input := affineWord a ++ matrixBits rows, remaining := List.replicate (n + 1) true, excess := acc}).store :=
    Exec.seq (.action _ _) (.action _ _)
  have loaded : Exec (.action (.copy (5 : Fin 9) 4))
      ({pivotResult n saved (some p) with input := affineWord a ++ matrixBits rows, remaining := List.replicate (n + 1) true, excess := acc}).store 1
      ({pivotResult n saved (some p) with input := affineWord a ++ matrixBits rows, remaining := List.replicate (n + 1) true, excess := acc, mode := affineWord p}).store :=
    .action _ _
  have copied := xor_exec {pivotResult n saved (some p) with excess := acc}
    (affineWord a) (affineWord p) (matrixBits rows)
    (by rw [affineWord_length, affineWord_length])
  rw [affineWord_length, ← substitute_true] at copied
  have checked := Exec.seq ready (Exec.seq loaded copied)
  have cost : 7 * (n + 1) + 4 = 2 + (1 + (7 * (n + 1) + 1)) := by omega
  simpa only [xorRow, eliminating, pivotResult, base, cost] using checked

def eliminationFuel {n : Nat} : System (n + 1) → Nat
  | [] => 1
  | (false, _) :: rows => 5 * (n + 1) + 5 + eliminationFuel rows
  | (true, _) :: rows => 7 * (n + 1) + 6 + eliminationFuel rows

theorem tailsLoop_exec {n : Nat} (rows : System (n + 1)) (saved acc : BitString)
    (heads : ∀ f ∈ rows, f.1 = false) :
    Exec eliminationLoop (eliminating rows saved none acc).store (eliminationFuel rows)
      (eliminating (n := n) [] saved none ((matrixBits (tails rows)).reverse ++ acc)).store := by
  induction rows generalizing acc with
  | nil => exact Exec.loopStop rfl
  | cons f rows ih =>
    rcases f with ⟨b, a⟩
    have hb : b = false := heads (b, a) List.mem_cons_self
    subst b
    have ht : ∀ f ∈ rows, f.1 = false :=
      fun f hf => heads f (List.mem_cons_of_mem _ hf)
    have body : Exec eliminationBody (eliminating ((false, a) :: rows) saved none acc).store
        (1 + (5 * (n + 1) + 3))
        (eliminating rows saved none ((affineWord a).reverse ++ acc)).store :=
      Exec.zero rfl (copyRow_exec a rows saved none acc)
    have checked := Exec.loopStep (source := (0 : Fin 9)) rfl body
      (ih ((affineWord a).reverse ++ acc) ht)
    have cost : eliminationFuel ((false, a) :: rows) =
        1 + ((1 + (5 * (n + 1) + 3)) + eliminationFuel rows) := by
      simp only [eliminationFuel]; omega
    rw [cost]
    simpa only [eliminationLoop, tails, List.map_cons, matrixBits,
      List.reverse_append, List.append_assoc] using checked

theorem substituteLoop_exec {n : Nat} (rows : System (n + 1)) (p : Affine n)
    (saved acc : BitString) :
    Exec eliminationLoop (eliminating rows saved (some p) acc).store (eliminationFuel rows)
      (eliminating [] saved (some p)
        ((matrixBits (substituteRows p rows)).reverse ++ acc)).store := by
  induction rows generalizing acc with
  | nil => exact Exec.loopStop rfl
  | cons f rows ih =>
    rcases f with ⟨b, a⟩
    cases b with
    | false =>
      have body : Exec eliminationBody
          (eliminating ((false, a) :: rows) saved (some p) acc).store
          (1 + (5 * (n + 1) + 3))
          (eliminating rows saved (some p) ((affineWord a).reverse ++ acc)).store :=
        Exec.zero rfl (copyRow_exec a rows saved (some p) acc)
      have checked := Exec.loopStep (source := (0 : Fin 9)) rfl body
        (ih ((affineWord a).reverse ++ acc))
      have cost : eliminationFuel ((false, a) :: rows) =
          1 + ((1 + (5 * (n + 1) + 3)) + eliminationFuel rows) := by
        simp only [eliminationFuel]; omega
      rw [cost]
      simpa only [eliminationLoop, substituteRows, List.map_cons, matrixBits,
        substitute_false, List.reverse_append, List.append_assoc] using checked
    | true =>
      have body : Exec eliminationBody
          (eliminating ((true, a) :: rows) saved (some p) acc).store
          (1 + (7 * (n + 1) + 4))
          (eliminating rows saved (some p)
            ((affineWord (substitute p (true, a))).reverse ++ acc)).store :=
        Exec.one rfl (xorRow_exec p a rows saved acc)
      have checked := Exec.loopStep (source := (0 : Fin 9)) rfl body
        (ih ((affineWord (substitute p (true, a))).reverse ++ acc))
      have cost : eliminationFuel ((true, a) :: rows) =
          1 + ((1 + (7 * (n + 1) + 4)) + eliminationFuel rows) := by
        simp only [eliminationFuel]; omega
      rw [cost]
      simpa only [eliminationLoop, substituteRows, List.map_cons, matrixBits,
        List.reverse_append, List.append_assoc] using checked

theorem eliminationFuel_bound {n : Nat} (rows : System (n + 1)) :
    eliminationFuel rows ≤ (7 * (n + 1) + 6) * rows.length + 1 := by
  induction rows with
  | nil => exact Nat.le_refl 1
  | cons f rows ih =>
    rcases f with ⟨b, a⟩
    cases b <;>
      simp only [eliminationFuel, List.length_cons, Nat.mul_add, Nat.add_mul,
        Nat.mul_one, Nat.mul_assoc] at * <;> omega

def reducedRows {n : Nat} (rows : System (n + 1)) : System n :=
  match choosePivot rows with
  | none => tails rows
  | some p => substituteRows p rows

theorem reducedRows_length {n : Nat} (rows : System (n + 1)) :
    (reducedRows rows).length = rows.length := by
  unfold reducedRows
  cases choosePivot rows <;> simp only [tails, substituteRows, List.length_map]

def columnStart {n : Nat} (rows : System (n + 1)) : Registers :=
  searching rows (matrixBits rows)
def columnResult {n : Nat} (rows : System (n + 1)) : Registers :=
  {pivotResult n (matrixBits rows) (choosePivot rows) with output := matrixBits (reducedRows rows)}

def column : Block 9 :=
  .seq pivotLoop (.seq (.action (.copy 0 7)) (.seq eliminationLoop ClauseQuery.reverseLoop))

def columnFuel {n : Nat} (rows : System (n + 1)) : Nat :=
  pivotFuel rows + (1 + (eliminationFuel rows + (4 * ((n + 1) * rows.length) + 1)))

/-- The pivot is discovered inside this closed block; it is not a premise. -/
theorem column_exec {n : Nat} (rows : System (n + 1)) :
    Exec column (columnStart rows).store (columnFuel rows) (columnResult rows).store := by
  have searched := pivotLoop_exec rows (matrixBits rows)
  have restored : Exec (.action (.copy (0 : Fin 9) 7))
      (pivotResult n (matrixBits rows) (choosePivot rows)).store 1
      (eliminating rows (matrixBits rows) (choosePivot rows) []).store := .action _ _
  have transformed : Exec eliminationLoop
      (eliminating rows (matrixBits rows) (choosePivot rows) []).store (eliminationFuel rows)
      (eliminating [] (matrixBits rows) (choosePivot rows)
        (matrixBits (reducedRows rows)).reverse).store := by
    cases hp : choosePivot rows with
    | none =>
      simpa only [reducedRows, hp, List.append_nil] using
        tailsLoop_exec rows (matrixBits rows) [] (choosePivot_none rows hp)
    | some p =>
      simpa only [reducedRows, hp, List.append_nil] using
        substituteLoop_exec rows p (matrixBits rows) []
  have reversed : Exec ClauseQuery.reverseLoop
      (eliminating [] (matrixBits rows) (choosePivot rows)
        (matrixBits (reducedRows rows)).reverse).store
      (4 * ((n + 1) * rows.length) + 1) (columnResult rows).store := by
    simpa only [eliminating, columnResult, matrixBits, List.length_reverse,
      matrixBits_length, reducedRows_length, List.reverse_reverse, pivotResult,
      base, List.append_nil] using
      ClauseQuery.reverse_exec (pivotResult n (matrixBits rows) (choosePivot rows))
        (matrixBits (reducedRows rows)).reverse
  exact Exec.seq searched (Exec.seq restored (Exec.seq transformed reversed))

theorem columnFuel_bound {n : Nat} (rows : System (n + 1)) :
    columnFuel rows ≤ (20 * (n + 1) + 20) * (rows.length + 1) := by
  have search := pivotFuel_bound rows
  have substitute := eliminationFuel_bound rows
  simp only [columnFuel, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul,
    Nat.mul_assoc] at *
  omega

def columnProgram : Program 9 := column.program 0 8

theorem column_program_run {n : Nat} (rows : System (n + 1)) :
    BitRegister.run columnProgram (columnFuel rows + 1)
      ⟨.running 0, (columnStart rows).store⟩ =
      ⟨.accepted, (columnResult rows).store⟩ :=
  (column_exec rows).program_run 0 8

end PNP.Concrete.ResidualReduction.MatrixInstructions
