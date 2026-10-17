import PNP.Concrete.ResidualReduction.SourceMenuBudget

/-! Serialize the actual computed menu with the existing matrix-packet codec.
Its count is obtained by scanning complete fixed-width records, not supplied
as an input. Header emission reuses the literal unary-output instruction loop. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuSerialization
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions

def counting {n : Nat} (xs menu : List (Affine n)) (count : Nat) : Registers :=
  {SourceMenuSortStep.initial xs menu with active := List.replicate count true}
def countBody : Block 9 := .seq (.action (.copy 2 1)) <|
  .seq dropLoop (.action (.push 6 true))
def countLoop : Block 9 := .loop 0 countBody
def countFuel (n k : Nat) : Nat := (3 * (n + 1) + 4) * k + 1

theorem countBody_exec {n : Nat} (a : Affine n) (xs menu : List (Affine n)) (count : Nat) :
    Exec countBody (counting (a :: xs) menu count).store (3 * (n + 1) + 3)
      (counting xs menu (count + 1)).store := by
  let r := counting xs menu count
  have first : Exec (.action (.copy (2 : Fin 9) 1)) (counting (a :: xs) menu count).store 1
      ({r with input := affineWord a ++ matrixBits xs, remaining := List.replicate (n + 1) true}).store :=
    Exec.action _ _
  have dropped : Exec dropLoop
      ({r with input := affineWord a ++ matrixBits xs, remaining := List.replicate (n + 1) true}).store
      (3 * (n + 1) + 1) r.store := by
    simpa only [r, counting, SourceMenuSortStep.initial, affineWord_length] using
      drop_exec r (affineWord a) (matrixBits xs)
  have last : Exec (.action (.push (6 : Fin 9) true)) r.store 1
      (counting xs menu (count + 1)).store := Exec.action _ _
  have cost : 3 * (n + 1) + 3 = 1 + ((3 * (n + 1) + 1) + 1) := by omega
  simpa only [countBody, cost] using Exec.seq first (Exec.seq dropped last)

theorem countLoop_exec {n : Nat} (xs menu : List (Affine n)) (count : Nat) :
    Exec countLoop (counting xs menu count).store (countFuel n xs.length)
      (counting [] menu (count + xs.length)).store := by
  induction xs generalizing count with
  | nil =>
    simpa only [countLoop, countFuel, List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.add_zero] using
      (Exec.loopStop (body := countBody) (source := (0 : Fin 9))
        (show (counting ([] : List (Affine n)) menu count).store.get 0 = [] from rfl))
  | cons a xs ih =>
    have rest := ih (count + 1)
    obtain ⟨bit, tail, present⟩ := SourceMenuSort.input_present a xs menu ⟨[], [], []⟩ ⟨[], []⟩
    have read : (counting (a :: xs) menu count).store.get 0 = bit :: tail := present
    have checked := Exec.loopStep (source := (0 : Fin 9)) read (countBody_exec a xs menu count) rest
    have size : countFuel n (a :: xs).length =
        1 + ((3 * (n + 1) + 3) + countFuel n xs.length) := by
      simp only [countFuel, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    have finalCount : count + 1 + xs.length = count + (a :: xs).length := by
      simp only [List.length_cons]
      omega
    simpa only [countLoop, size, finalCount] using checked

def countStart : Block 9 := .action (.copy 0 7)
theorem countStart_exec {n : Nat} (menu : List (Affine n)) :
    Exec countStart (SourceMenuSortStep.initial [] menu).store 1 (counting menu menu 0).store :=
  Exec.action _ _

def ready {n : Nat} (menu : List (Affine n)) : Registers := SourceMenuSortStep.initial [] menu
def withCount {n : Nat} (menu : List (Affine n)) : Registers :=
  {ready menu with remaining := List.replicate menu.length true, output := false :: matrixBits menu}
def afterCount {n : Nat} (menu : List (Affine n)) : Registers :=
  {ready menu with output := natural menu.length ++ matrixBits menu}
def withDimension {n : Nat} (menu : List (Affine n)) : Registers :=
  {ready menu with remaining := List.replicate n true, output := false :: (afterCount menu).output}
def result {n : Nat} (menu : List (Affine n)) : Registers :=
  {ready menu with output := MatrixInputEncoding.codec.encode ⟨n, menu⟩}

def countHeader : Block 9 := .seq (.action (.copy 8 7)) <| .seq (.action (.copy 2 6)) <|
  .seq (.action (.clear 6)) (.action (.push 8 false))
theorem countHeader_exec {n : Nat} (menu : List (Affine n)) :
    Exec countHeader (counting [] menu menu.length).store 4 (withCount menu).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

theorem emitCount_exec {n : Nat} (menu : List (Affine n)) :
    Exec MatrixSolutionSerialization.unaryLoop (withCount menu).store (3 * menu.length + 1)
      (afterCount menu).store := by
  simpa only [withCount, afterCount, ready, SourceMenuSortStep.initial, natural, List.append_assoc, List.singleton_append] using
    MatrixSolutionSerialization.unaryLoop_exec {ready menu with output := false :: matrixBits menu} menu.length

def dimensionHeader : Block 9 := .seq (.action (.copy 2 1)) <|
  .seq (.action (.pop 2)) (.action (.push 8 false))
theorem dimensionHeader_exec {n : Nat} (menu : List (Affine n)) :
    Exec dimensionHeader (afterCount menu).store 3 (withDimension menu).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

theorem emitDimension_exec {n : Nat} (menu : List (Affine n)) :
    Exec MatrixSolutionSerialization.unaryLoop (withDimension menu).store (3 * n + 1)
      (result menu).store := by
  simpa only [withDimension, result, afterCount, ready, SourceMenuSortStep.initial, MatrixInputEncoding.codec_bits, natural,
    List.append_assoc, List.singleton_append] using
      MatrixSolutionSerialization.unaryLoop_exec
        {ready menu with output := false :: (afterCount menu).output} n

def finish : Block 9 := .seq countHeader <| .seq MatrixSolutionSerialization.unaryLoop <|
  .seq dimensionHeader MatrixSolutionSerialization.unaryLoop
theorem finish_exec {n : Nat} (menu : List (Affine n)) :
    Exec finish (counting [] menu menu.length).store (3 * menu.length + 3 * n + 9) (result menu).store := by
  have checked := Exec.seq (countHeader_exec menu)
    (Exec.seq (emitCount_exec menu) (Exec.seq (dimensionHeader_exec menu) (emitDimension_exec menu)))
  have cost : 3 * menu.length + 3 * n + 9 = 4 + ((3 * menu.length + 1) + (3 + (3 * n + 1))) := by omega
  simpa only [finish, cost] using checked

def block : Block 9 := .seq countStart (.seq countLoop finish)
def fuel (n k : Nat) : Nat := (3 * (n + 1) + 7) * k + 3 * n + 11
theorem block_exec {n : Nat} (menu : List (Affine n)) :
    Exec block (ready menu).store (fuel n menu.length) (result menu).store := by
  have counted := countLoop_exec menu menu 0
  simp only [Nat.zero_add] at counted
  have checked := Exec.seq (countStart_exec menu) (Exec.seq counted (finish_exec menu))
  have cost : fuel n menu.length = 1 + (countFuel n menu.length + (3 * menu.length + 3 * n + 9)) := by
    simp only [fuel, countFuel, Nat.add_mul]
    omega
  simpa only [block, cost, ready] using checked

theorem result_output {n : Nat} (menu : List (Affine n)) :
    (result menu).store.get 8 = MatrixInputEncoding.codec.encode ⟨n, menu⟩ := rfl

def costPolynomial : NatPolynomial := .add (.mul (.linear 3 10) (.linear 3 0)) (.linear 3 11)
theorem costPolynomial_eval (L : Nat) : costPolynomial.eval L = fuel L (3 * L) := by
  simp only [costPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_linear,
    fuel, Nat.add_zero]
  have same : 3 * (L + 1) + 7 = 3 * L + 10 := by omega
  rw [same]
  omega
theorem bounded_cost (n k L : Nat) (dimension : n ≤ L) (count : k ≤ 3 * L) :
    fuel n k ≤ costPolynomial.eval L := by
  have product := Nat.mul_le_mul (show 3 * (n + 1) + 7 ≤ 3 * (L + 1) + 7 by omega) count
  rw [costPolynomial_eval]
  unfold fuel
  omega
theorem original_input_bound {n : Nat} (F : Family n) :
    fuel n (SourceChain.sourceMenu F).length ≤
      costPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n, F⟩).length := by
  have count := SourceChain.sourceMenu_length_le F
  have rows := SourceMatrixEncoding.rowCount_bound n F
  exact bounded_cost n _ _ (SourceMatrixEncoding.dimension_bound n F) (by omega)

end PNP.Concrete.ResidualReduction.SourceMenuSerialization
