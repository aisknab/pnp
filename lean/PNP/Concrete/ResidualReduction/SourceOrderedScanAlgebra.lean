import PNP.Concrete.ResidualReduction.SourceBilinearEvaluationInstructions

/-! Exact first-entry semantics for the ordered line-query selector.
Positions count rejected entries, not successful candidates or proof progress.
Both matrix scans preserve the original row-major order, including exhaustion. -/

namespace PNP.Concrete.ResidualReduction.SourceOrderedScan
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra

/-- First true bit and the number of preceding false bits; on exhaustion,
the second component is the complete input length. -/
def search : BitString → Bool × Nat
  | [] => (false, 0)
  | true :: _ => (true, 0)
  | false :: rest =>
      let result := search rest
      (result.1, result.2 + 1)

theorem search_bound (bits : BitString) : (search bits).2 ≤ bits.length := by
  induction bits with
  | nil => exact Nat.le_refl 0
  | cons b bits ih =>
    cases b with
    | false => exact Nat.add_le_add_right ih 1
    | true => exact Nat.zero_le _

theorem search_found_bound (bits : BitString) (h : (search bits).1 = true) :
    (search bits).2 < bits.length := by
  induction bits with
  | nil => cases h
  | cons b bits ih =>
    cases b with
    | false => exact Nat.add_lt_add_right (ih h) 1
    | true => exact Nat.zero_lt_succ _

theorem search_exhausted (bits : BitString) (h : (search bits).1 = false) :
    (search bits).2 = bits.length := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    cases b with
    | false => exact congrArg Nat.succ (ih h)
    | true => cases h

/-- The positional scan chooses exactly the same list element as the original
selector. In particular, this is not merely an existence or soundness result. -/
theorem scan_exact {T : Type} (p : T → Bool) (xs : List T) :
    (BilinearSelection.scan p xs).1 =
      if (search (xs.map p)).1 then xs[(search (xs.map p)).2]? else none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x with
    | false =>
      simp only [BilinearSelection.scan, h, Bool.false_eq_true, if_false,
        List.map_cons, search]
      cases found : (search (xs.map p)).1 <;>
        simpa only [found, Bool.false_eq_true,
          if_false, if_true, List.getElem?_cons_succ] using ih
    | true =>
      simp only [BilinearSelection.scan, h, if_true,
        List.map_cons, search, List.getElem?_cons_zero]

theorem scan_checks {T : Type} (p : T → Bool) (xs : List T) :
    (BilinearSelection.scan p xs).2 =
      (search (xs.map p)).2 + if (search (xs.map p)).1 then 1 else 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x with
    | false =>
      simp only [BilinearSelection.scan, h, Bool.false_eq_true, if_false,
        List.map_cons, search]
      omega
    | true =>
      simp only [BilinearSelection.scan, h, if_true,
        List.map_cons, search, Nat.zero_add]

def test (difference c a : Bool) : Bool :=
  if difference then Bool.xor c a else c

theorem zip_map {T : Type} (f g : T → Bool) (xs : List T) (difference : Bool) :
    List.zipWith (test difference) (xs.map f) (xs.map g) =
      xs.map (fun x => test difference (f x) (g x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons _) ih

theorem matrix_bits_entries {m n : Nat} (M : Matrix m n) :
    coefficientMatrixBits M =
      (BilinearSelection.entries m n).map (fun e => M e.1 e.2) := by
  simp only [coefficientMatrixBits, BilinearSelection.entries,
    List.map_flatMap, List.map_map, Function.comp_def]

def matrixPredicate {m n : Nat} (difference : Bool) (A C : Matrix m n)
    (e : Fin m × Fin n) : Bool := test difference (C e.1 e.2) (A e.1 e.2)
def matrixSearch {m n : Nat} (difference : Bool) (A C : Matrix m n) : Bool × Nat :=
  search (List.zipWith (test difference) (coefficientMatrixBits C) (coefficientMatrixBits A))

theorem matrix_search_entries {m n : Nat} (difference : Bool) (A C : Matrix m n) :
    matrixSearch difference A C =
      search ((BilinearSelection.entries m n).map (matrixPredicate difference A C)) := by
  rw [matrixSearch, matrix_bits_entries, matrix_bits_entries, zip_map]
  rfl

theorem matrix_scan_exact {m n : Nat} (difference : Bool) (A C : Matrix m n) :
    (BilinearSelection.scan (matrixPredicate difference A C) (BilinearSelection.entries m n)).1 =
      if (matrixSearch difference A C).1 then
        (BilinearSelection.entries m n)[(matrixSearch difference A C).2]? else none := by
  rw [matrix_search_entries]
  exact scan_exact _ _

theorem matrix_scan_checks {m n : Nat} (difference : Bool) (A C : Matrix m n) :
    (BilinearSelection.scan (matrixPredicate difference A C) (BilinearSelection.entries m n)).2 =
      (matrixSearch difference A C).2 + if (matrixSearch difference A C).1 then 1 else 0 := by
  rw [matrix_search_entries]
  exact scan_checks _ _

theorem matrix_search_bound {m n : Nat} (difference : Bool) (A C : Matrix m n) :
    (matrixSearch difference A C).2 ≤ m * n := by
  rw [matrix_search_entries]
  simpa only [List.length_map, BilinearSelection.entries_length] using
    search_bound ((BilinearSelection.entries m n).map (matrixPredicate difference A C))

theorem matrix_found_bound {m n : Nat} (difference : Bool) (A C : Matrix m n)
    (h : (matrixSearch difference A C).1 = true) :
    (matrixSearch difference A C).2 < m * n := by
  rw [matrix_search_entries] at h ⊢
  simpa only [List.length_map, BilinearSelection.entries_length] using
    search_found_bound ((BilinearSelection.entries m n).map (matrixPredicate difference A C)) h

theorem nonzero_predicate {m n : Nat} (A C : Matrix m n) :
    matrixPredicate false A C = (fun e => C e.1 e.2) := rfl
theorem difference_predicate {m n : Nat} (A C : Matrix m n) :
    matrixPredicate true A C = (fun e => Bool.xor (C e.1 e.2) (A e.1 e.2)) := rfl

end PNP.Concrete.ResidualReduction.SourceOrderedScan
