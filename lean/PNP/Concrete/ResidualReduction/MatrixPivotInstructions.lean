import PNP.Concrete.ResidualReduction.MatrixRowInstructions

/-! First-pivot discovery from the encoded matrix itself. The finite program
scans every skipped row, including the complete no-pivot case. The dimension
and row count are unbounded; no pivot or search certificate is supplied. -/

namespace PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear

def base (width : Nat) (saved : BitString) : Registers where
  input := []
  target := List.replicate width true
  remaining := []
  excess := []
  sign := []
  mode := []
  active := []
  reserved := saved
  output := []

def searching {n : Nat} (rows : System (n + 1)) (saved : BitString) : Registers :=
  {base (n + 1) saved with input := matrixBits rows}

def pivotResult (n : Nat) (saved : BitString) (pivot : Option (Affine n)) : Registers :=
  {base (n + 1) saved with
    sign := match pivot with | none => [] | some p => affineWord p
    active := match pivot with | none => [] | some _ => [true]}

def prepareRow : Block 9 := .seq (.action (.pop 0)) (.action (.copy 2 1))

def finishPivot : Block 9 :=
  .seq (.action (.copy 4 8)) <| .seq (.action (.clear 8)) <|
    .seq (.action (.push 6 true)) (.action (.clear 0))

def skipRow : Block 9 := .seq prepareRow dropLoop
def takePivot : Block 9 :=
  .seq prepareRow (.seq copyLoop (.seq ClauseQuery.reverseLoop finishPivot))
def pivotBody : Block 9 := .branch 0 .skip skipRow takePivot
def pivotLoop : Block 9 := .loop 0 pivotBody

theorem skipRow_exec {n : Nat} (a : Affine n) (rows : System (n + 1))
    (saved : BitString) :
    Exec skipRow (searching ((false, a) :: rows) saved).store
      (3 * (n + 1) + 3) (searching rows saved).store := by
  have ready : Exec prepareRow (searching ((false, a) :: rows) saved).store 2
      ({base (n + 1) saved with input := affineWord a ++ matrixBits rows, remaining := List.replicate (n + 1) true}).store :=
    Exec.seq (.action _ _) (.action _ _)
  have dropped := drop_exec (base (n + 1) saved) (affineWord a) (matrixBits rows)
  rw [affineWord_length] at dropped
  have checked := Exec.seq ready dropped
  have cost : 3 * (n + 1) + 3 = 2 + (3 * (n + 1) + 1) := by omega
  simpa only [skipRow, searching, base, cost] using checked

theorem takePivot_exec {n : Nat} (a : Affine n) (rows : System (n + 1))
    (saved : BitString) :
    Exec takePivot (searching ((true, a) :: rows) saved).store
      (9 * (n + 1) + 8) (pivotResult n saved (some a)).store := by
  have ready : Exec prepareRow (searching ((true, a) :: rows) saved).store 2
      ({base (n + 1) saved with input := affineWord a ++ matrixBits rows, remaining := List.replicate (n + 1) true}).store :=
    Exec.seq (.action _ _) (.action _ _)
  have copied : Exec copyLoop
      ({base (n + 1) saved with input := affineWord a ++ matrixBits rows, remaining := List.replicate (n + 1) true}).store
      (5 * (n + 1) + 1)
      ({base (n + 1) saved with input := matrixBits rows, excess := (affineWord a).reverse}).store := by
    simpa only [affineWord_length, base, List.append_nil] using
      copy_exec (base (n + 1) saved) (affineWord a) (matrixBits rows)
  have reversed : Exec ClauseQuery.reverseLoop
      ({base (n + 1) saved with input := matrixBits rows, excess := (affineWord a).reverse}).store
      (4 * (n + 1) + 1)
      ({base (n + 1) saved with input := matrixBits rows, output := affineWord a}).store := by
    simpa only [List.length_reverse, affineWord_length, List.reverse_reverse,
      base, List.append_nil] using
      ClauseQuery.reverse_exec {base (n + 1) saved with input := matrixBits rows}
        (affineWord a).reverse
  have finished : Exec finishPivot
      ({base (n + 1) saved with input := matrixBits rows, output := affineWord a}).store 4
      (pivotResult n saved (some a)).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have checked := Exec.seq ready (Exec.seq copied (Exec.seq reversed finished))
  have cost : 9 * (n + 1) + 8 =
      2 + ((5 * (n + 1) + 1) + ((4 * (n + 1) + 1) + 4)) := by omega
  simpa only [takePivot, cost] using checked

def pivotFuel {n : Nat} : System (n + 1) → Nat
  | [] => 1
  | (false, _) :: rows => 3 * (n + 1) + 5 + pivotFuel rows
  | (true, _) :: _ => 9 * (n + 1) + 11

theorem pivotLoop_exec {n : Nat} (rows : System (n + 1)) (saved : BitString) :
    Exec pivotLoop (searching rows saved).store (pivotFuel rows)
      (pivotResult n saved (choosePivot rows)).store := by
  induction rows with
  | nil => exact Exec.loopStop rfl
  | cons a rows ih =>
    rcases a with ⟨b, a⟩
    cases b with
    | false =>
      have body : Exec pivotBody (searching ((false, a) :: rows) saved).store
          (1 + (3 * (n + 1) + 3)) (searching rows saved).store :=
        Exec.zero rfl (skipRow_exec a rows saved)
      have checked := Exec.loopStep (source := (0 : Fin 9)) rfl body ih
      have cost : pivotFuel ((false, a) :: rows) =
          1 + ((1 + (3 * (n + 1) + 3)) + pivotFuel rows) := by
        simp only [pivotFuel]; omega
      rw [cost]
      exact checked
    | true =>
      have body : Exec pivotBody (searching ((true, a) :: rows) saved).store
          (1 + (9 * (n + 1) + 8)) (pivotResult n saved (some a)).store :=
        Exec.one rfl (takePivot_exec a rows saved)
      have stopped : Exec pivotLoop (pivotResult n saved (some a)).store 1
          (pivotResult n saved (some a)).store := Exec.loopStop rfl
      have checked := Exec.loopStep (source := (0 : Fin 9)) rfl body stopped
      have cost : pivotFuel ((true, a) :: rows) =
          1 + ((1 + (9 * (n + 1) + 8)) + 1) := by
        simp only [pivotFuel]; omega
      rw [cost]
      exact checked

theorem pivotFuel_bound {n : Nat} (rows : System (n + 1)) :
    pivotFuel rows ≤ (9 * (n + 1) + 11) * (rows.length + 1) := by
  induction rows with
  | nil => simp only [pivotFuel, List.length_nil, Nat.zero_add, Nat.mul_one]; omega
  | cons a rows ih =>
    rcases a with ⟨b, a⟩
    simp only [Nat.mul_add, Nat.mul_one] at ih
    cases b <;> simp only [pivotFuel, List.length_cons, Nat.mul_add, Nat.mul_one] <;> omega

end PNP.Concrete.ResidualReduction.MatrixInstructions
