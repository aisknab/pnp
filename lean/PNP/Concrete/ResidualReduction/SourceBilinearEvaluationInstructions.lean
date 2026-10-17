import PNP.Concrete.ResidualReduction.SourceLineQueryMatrices
import PNP.Concrete.ResidualReduction.SourceLinearMapInstructions

/-! Literal evaluation of an arbitrary encoded Boolean bilinear matrix.
Every row and column is read, including all-false inputs. The outer loop
consumes the left vector even at zero column width, so no data oracle or
nonempty-matrix premise is hidden in the instruction bound. -/

namespace PNP.Concrete.ResidualReduction.SourceBilinearEvaluation
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.SourceLineQueryMatrixAlgebra (matrixBits_cons)
open PNP.Concrete.ResidualReduction.MatrixLinearCombinationInstructions (readInput readInput_exec readMode readMode_exec)
open PNP.Concrete.ResidualReduction.SourceLinearMap (readSign readSign_exec)

def rowBits {n : Nat} (f : Fin n → Bool) : BitString := (List.finRange n).map f
theorem rowBits_cons {n : Nat} (f : Fin (n + 1) → Bool) :
    rowBits f = f 0 :: rowBits (fun i => f i.succ) := by
  simp only [rowBits, List.finRange_succ, List.map_cons, List.map_map, Function.comp_def]
private theorem accumulate_row :
    ∀ b c d e a : Bool, Bool.xor (b && e) (Bool.xor ((b && c) && d) a) =
      Bool.xor (b && Bool.xor (c && d) e) a := by decide
private theorem accumulate_matrix :
    ∀ h t a : Bool, Bool.xor t (Bool.xor h a) = Bool.xor (Bool.xor h t) a := by decide

def columnStep (b : Bool) : Block 9 :=
  readInput fun c => readMode fun d => readSign fun a => .action (.push 4 (Bool.xor ((b && c) && d) a))
theorem columnStep_exec (r : Registers) (b c d a : Bool) :
    Exec (columnStep b) ({r with input := c :: r.input, mode := d :: r.mode, sign := [a]}).store 7
      ({r with sign := [Bool.xor ((b && c) && d) a]}).store := by
  unfold columnStep
  refine readInput_exec {r with mode := d :: r.mode, sign := [a]} c _ 5 _ ?_
  refine readMode_exec {r with sign := [a]} d _ 3 _ ?_
  exact readSign_exec {r with sign := []} a _ 1 _ (.action _ _)
def columnLoop (b : Bool) : Block 9 := .loop 5 (columnStep b)
theorem columnLoop_exec (r : Registers) {n : Nat} (f : Fin n → Bool) (y : Point n)
    (b acc : Bool) (suffix : BitString) :
    Exec (columnLoop b) ({r with input := rowBits f ++ suffix, mode := (SourceEncoding.pointCodec n).encode y, sign := [acc]}).store
      (8 * n + 1)
      ({r with input := suffix, mode := [], sign := [Bool.xor (b && rowDot f y) acc]}).store := by
  induction n generalizing r acc with
  | zero =>
    cases y
    simp only [rowDot, Bool.and_false, Bool.false_xor]
    exact Exec.loopStop rfl
  | succ n ih =>
    rcases y with ⟨d, y⟩
    let rest := {r with input := rowBits (fun i => f i.succ) ++ suffix, mode := (SourceEncoding.pointCodec n).encode y}
    have step := columnStep_exec rest b (f 0) d acc
    have checked := Exec.loopStep (source := (5 : Fin 9)) rfl step
      (ih r (fun i => f i.succ) y (Bool.xor ((b && f 0) && d) acc))
    have cost : 8 * (n + 1) + 1 = 1 + (7 + (8 * n + 1)) := by omega
    simpa only [columnLoop, cost, rest, rowBits_cons, SourceLinearMap.point_bits_cons,
      List.cons_append, rowDot, accumulate_row] using checked

def readTarget (next : Bool → Block 9) : Block 9 :=
  .branch 1 .skip (.seq (.action (.pop 1)) (next false)) (.seq (.action (.pop 1)) (next true))
theorem readTarget_exec (r : Registers) (b : Bool) (next : Bool → Block 9)
    (fuel : Nat) (after : Registers) (checked : Exec (next b) r.store fuel after.store) :
    Exec (readTarget next) ({r with target := b :: r.target}).store (2 + fuel) after.store := by
  have popped : Exec (.action (.pop (1 : Fin 9))) ({r with target := b :: r.target}).store 1 r.store := .action _ _
  rw [show 2 + fuel = 1 + (1 + fuel) by omega]
  cases b with
  | false => exact Exec.zero (source := (1 : Fin 9)) rfl (Exec.seq popped checked)
  | true => exact Exec.one (source := (1 : Fin 9)) rfl (Exec.seq popped checked)

def row : Block 9 := readTarget fun b => .seq (.action (.copy 5 7)) (columnLoop b)
theorem row_exec (r : Registers) {n : Nat} (f : Fin n → Bool) (y : Point n)
    (b acc : Bool) (suffix : BitString) :
    Exec row ({r with input := rowBits f ++ suffix, target := b :: r.target, mode := [], sign := [acc], reserved := (SourceEncoding.pointCodec n).encode y}).store
      (8 * n + 4)
      ({r with input := suffix, mode := [], sign := [Bool.xor (b && rowDot f y) acc], reserved := (SourceEncoding.pointCodec n).encode y}).store := by
  let before := {r with input := rowBits f ++ suffix, mode := [], sign := [acc], reserved := (SourceEncoding.pointCodec n).encode y}
  let copied := {before with mode := (SourceEncoding.pointCodec n).encode y}
  have copy : Exec (.action (.copy (5 : Fin 9) 7)) before.store 1 copied.store := .action _ _
  have columns : Exec (columnLoop b) copied.store (8 * n + 1)
      ({r with input := suffix, mode := [], sign := [Bool.xor (b && rowDot f y) acc], reserved := (SourceEncoding.pointCodec n).encode y}).store :=
    columnLoop_exec {r with reserved := (SourceEncoding.pointCodec n).encode y} f y b acc suffix
  have checked := readTarget_exec before b (fun bit => .seq (.action (.copy 5 7)) (columnLoop bit))
      (1 + (8 * n + 1)) _ (Exec.seq copy columns)
  have cost : 8 * n + 4 = 2 + (1 + (8 * n + 1)) := by omega
  simpa only [row, cost, before] using checked

def matrixLoop : Block 9 := .loop 1 row
def loopFuel (m n : Nat) : Nat := (8 * n + 5) * m + 1
theorem matrixLoop_exec (r : Registers) {m n : Nat} (M : Matrix m n) (x : Point m) (y : Point n) (acc : Bool) :
    Exec matrixLoop ({r with input := coefficientMatrixBits M, target := (SourceEncoding.pointCodec m).encode x, mode := [], sign := [acc], reserved := (SourceEncoding.pointCodec n).encode y}).store
      (loopFuel m n)
      ({r with input := [], target := [], mode := [], sign := [Bool.xor (bilinearEval M x y) acc], reserved := (SourceEncoding.pointCodec n).encode y}).store := by
  induction m generalizing r acc with
  | zero =>
    cases x
    simp only [bilinearEval, Bool.false_xor]
    exact Exec.loopStop rfl
  | succ m ih =>
    rcases x with ⟨b, x⟩
    let rest := {r with target := (SourceEncoding.pointCodec m).encode x}
    have first := row_exec rest (M 0) y b acc (coefficientMatrixBits (fun i => M i.succ))
    have checked := Exec.loopStep (source := (1 : Fin 9)) rfl first
      (ih r (fun i => M i.succ) x (Bool.xor (b && rowDot (M 0) y) acc))
    have cost : loopFuel (m + 1) n = 1 + ((8 * n + 4) + loopFuel m n) := by
      unfold loopFuel
      rw [Nat.mul_add, Nat.mul_one]
      omega
    simpa only [matrixLoop, cost, rest, matrixBits_cons, rowBits, SourceLinearMap.point_bits_cons,
      bilinearEval, accumulate_matrix] using checked

def finish : Block 9 := .seq (.action (.copy 8 4)) (.action (.clear 4))
def block : Block 9 := .seq (.action (.push 4 false)) (.seq matrixLoop finish)
def fuel (m n : Nat) : Nat := 1 + (loopFuel m n + 2)
theorem block_exec (r : Registers) {m n : Nat} (M : Matrix m n) (x : Point m) (y : Point n) :
    Exec block ({r with input := coefficientMatrixBits M, target := (SourceEncoding.pointCodec m).encode x, mode := [], sign := [], reserved := (SourceEncoding.pointCodec n).encode y}).store
      (fuel m n)
      ({r with input := [], target := [], mode := [], sign := [], reserved := (SourceEncoding.pointCodec n).encode y, output := [bilinearEval M x y]}).store := by
  let before := {r with input := coefficientMatrixBits M, target := (SourceEncoding.pointCodec m).encode x, mode := [], sign := [], reserved := (SourceEncoding.pointCodec n).encode y}
  let seeded := {before with sign := [false]}
  let done := {r with input := [], target := [], mode := [], sign := [bilinearEval M x y], reserved := (SourceEncoding.pointCodec n).encode y}
  have seed : Exec (.action (.push (4 : Fin 9) false)) before.store 1 seeded.store := .action _ _
  have matrix : Exec matrixLoop seeded.store (loopFuel m n) done.store := by
    simpa only [seeded, before, done, Bool.xor_false] using matrixLoop_exec r M x y false
  have final : Exec finish done.store 2
      ({r with input := [], target := [], mode := [], sign := [], reserved := (SourceEncoding.pointCodec n).encode y, output := [bilinearEval M x y]}).store :=
    Exec.seq (.action _ _) (.action _ _)
  exact Exec.seq seed (Exec.seq matrix final)
theorem fuel_mono (m n M N : Nat) (hm : m ≤ M) (hn : n ≤ N) : fuel m n ≤ fuel M N := by
  have bound := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hn) 5) hm
  unfold fuel loopFuel
  omega

end PNP.Concrete.ResidualReduction.SourceBilinearEvaluation
