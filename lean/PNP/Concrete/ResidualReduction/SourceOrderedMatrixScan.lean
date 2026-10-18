import PNP.Concrete.ResidualReduction.SourceOrderedScanCoordinate
import PNP.Concrete.ResidualReduction.SourceLinePullbackBudget

/-! A complete prepared scan from encoded coefficients to the exact first entry.
The scan and unary coordinate recovery both execute literal instructions.
This is the entry-search component of the ordered selector, not its nine-candidate
phase, a raw-machine theorem, or the complete contraction runtime. -/

namespace PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.SourceOrderedScan

def base (r : Registers) (width : Nat) : Registers :=
  {r with mode := List.replicate width true, excess := []}
def start {m n : Nat} (r : Registers) (A C : Matrix m n) : Registers :=
  matrixStart (base r n) A C
def scanned {m n : Nat} (r : Registers) (difference : Bool) (A C : Matrix m n) : Registers :=
  matrixResult (base r n) difference A C

def finish : Block 9 := .branch 4 .skip .skip coordinateBlock
def block (difference : Bool) : Block 9 :=
  .seq (SourceOrderedScan.block difference) finish
def result {m n : Nat} (r : Registers) (difference : Bool) (A C : Matrix m n) : Registers :=
  if (matrixSearch difference A C).1 then
    cursor (scanned r difference A C) n
      (walk n 0 0 (matrixSearch difference A C).2).1
      (walk n 0 0 (matrixSearch difference A C).2).2 0
  else scanned r difference A C
def finishFuel {m n : Nat} (difference : Bool) (A C : Matrix m n) : Nat :=
  if (matrixSearch difference A C).1 then
    1 + (3 + walkFuel n 0 (matrixSearch difference A C).2)
  else 2
def fuel {m n : Nat} (difference : Bool) (A C : Matrix m n) : Nat :=
  SourceOrderedScan.fuel (matrixSearch difference A C) + finishFuel difference A C

theorem positive_width {m n : Nat} (difference : Bool) (A C : Matrix m n)
    (h : (matrixSearch difference A C).1 = true) : 0 < n := by
  have bound := matrix_found_bound difference A C h
  cases n with
  | zero => simp only [Nat.mul_zero] at bound; omega
  | succ n => exact Nat.zero_lt_succ n

theorem finish_exec {m n : Nat} (r : Registers) (difference : Bool) (A C : Matrix m n) :
    Exec finish (scanned r difference A C).store (finishFuel difference A C)
      (result r difference A C).store := by
  cases found : (matrixSearch difference A C).1 with
  | false =>
    simp only [result, finishFuel, found, Bool.false_eq_true, if_false]
    exact Exec.empty (by simp only [scanned, matrixResult, found, flag]; rfl) (Exec.skip _)
  | true =>
    simp only [result, finishFuel, found, if_true]
    apply Exec.one (source := (4 : Fin 9)) (by simp only [scanned, matrixResult, found, flag]; rfl)
    exact coordinate_exec (scanned r difference A C) n (matrixSearch difference A C).2
      (positive_width difference A C found)

theorem block_exec {m n : Nat} (r : Registers) (difference : Bool) (A C : Matrix m n) :
    Exec (block difference) (start r A C).store (fuel difference A C)
      (result r difference A C).store :=
  Exec.seq (matrix_exec (base r n) difference A C) (finish_exec r difference A C)

def entry {m n : Nat} (difference : Bool) (A C : Matrix m n) : Option (Nat × Nat) :=
  if (matrixSearch difference A C).1 then some (walk n 0 0 (matrixSearch difference A C).2) else none

theorem entry_exact {m n : Nat} (difference : Bool) (A C : Matrix m n) :
    (BilinearSelection.scan (matrixPredicate difference A C) (BilinearSelection.entries m n)).1.map
      (fun e => (e.1.val, e.2.val)) = entry difference A C := by
  rw [matrix_scan_exact]
  cases found : (matrixSearch difference A C).1 with
  | false => simp only [entry, found, Bool.false_eq_true, if_false, Option.map_none]
  | true =>
    simp only [entry, found, if_true]
    rw [recovered_entry_exact _ (positive_width difference A C found)
      (matrix_found_bound difference A C found)]
    rfl

theorem result_flag {m n : Nat} (r : Registers) (difference : Bool) (A C : Matrix m n) :
    (result r difference A C).store.get 4 = flag (entry difference A C).isSome := by
  cases found : (matrixSearch difference A C).1 <;>
    simp only [result, entry, found, Bool.false_eq_true, if_false, if_true,
      Option.isSome_none, Option.isSome_some, cursor, scanned, matrixResult, flag] <;> rfl

theorem result_coordinates {m n : Nat} (r : Registers) (difference : Bool) (A C : Matrix m n)
    (e : Nat × Nat) (h : entry difference A C = some e) :
    (result r difference A C).store.get 1 = List.replicate e.1 true ∧
      (result r difference A C).store.get 3 = List.replicate e.2 true := by
  cases found : (matrixSearch difference A C).1 with
  | false => simp only [entry, found, Bool.false_eq_true, if_false, reduceCtorEq] at h
  | true =>
    have same : walk n 0 0 (matrixSearch difference A C).2 = e := by
      simpa only [entry, found, if_true, Option.some.injEq] using h
    simp only [result, found, if_true, same, cursor]
    exact ⟨rfl, rfl⟩

theorem fuel_bound {m n : Nat} (difference : Bool) (A C : Matrix m n) :
    fuel difference A C ≤ 13 * (m * n) + 14 := by
  have scan := matrix_fuel_bound difference A C
  have position := matrix_search_bound difference A C
  have coordinates := walkFuel_bound n 0 (matrixSearch difference A C).2
  have scaled := Nat.mul_le_mul_left 7 position
  unfold fuel finishFuel
  split <;> omega

def costPolynomial : NatPolynomial :=
  .add (.mul (.constant 13) (.mul .variable .variable)) (.constant 14)
theorem costPolynomial_eval (L : Nat) : costPolynomial.eval L = 13 * (L * L) + 14 := rfl
theorem bounded_exec {m n : Nat} (r : Registers) (difference : Bool) (A C : Matrix m n)
    (L : Nat) (hm : m ≤ L) (hn : n ≤ L) :
    ∃ used ≤ costPolynomial.eval L,
      Exec (block difference) (start r A C).store used (result r difference A C).store := by
  refine ⟨fuel difference A C, ?_, block_exec r difference A C⟩
  exact Nat.le_trans (fuel_bound difference A C)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 13 (Nat.mul_le_mul hm hn)) 14)

def program (difference : Bool) : Program 9 := (block difference).program 0 4
theorem program_run {m n : Nat} (r : Registers) (difference : Bool) (A C : Matrix m n) :
    BitRegister.run (program difference) (fuel difference A C + 1)
      ⟨.running 0, (start r A C).store⟩ = ⟨.accepted, (result r difference A C).store⟩ :=
  (block_exec r difference A C).program_run 0 4

theorem source_bound {n : Nat} (F : Family n) (alpha : Affine n) (difference : Bool) :
    fuel difference (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) ≤
      26 * ((SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length *
        (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length) + 14 := by
  have bound := fuel_bound difference (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha)
  have left := SourceLinePullback.left_parameter_bound F alpha
  have right := SourceLinePullback.right_parameter_bound F alpha
  have product := Nat.mul_le_mul left right
  have scaled := Nat.mul_le_mul_left 13 product
  rw [Nat.mul_assoc, ← Nat.mul_assoc 13 2] at scaled
  exact Nat.le_trans bound (Nat.add_le_add_right scaled 14)

end PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan
