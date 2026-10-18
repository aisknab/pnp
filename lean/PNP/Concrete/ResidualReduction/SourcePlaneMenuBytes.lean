import PNP.Concrete.ResidualReduction.SourceMenuInsertStep

/-! Exact bytes and order of the plane candidate menu. The specification permits
arbitrary homogeneous menus, including duplicates and unsorted records. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneMenuBytes
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceMenuOrder

def pairWord {n : Nat} (p : Affine n × Affine n) : BitString :=
  affineWord p.1 ++ affineWord p.2
def pairBits {n : Nat} : List (Affine n × Affine n) → BitString
  | [] => []
  | p :: ps => pairWord p ++ pairBits ps
def rowPairs {n : Nat} (a : Affine n) (us : List (Affine n)) :
    List (Affine n × Affine n) :=
  (us.filter fun b => decide (normalCode b < normalCode a)).map fun b => (a,b)
def rowBits {n : Nat} (a : Affine n) (us : List (Affine n)) : BitString :=
  pairBits (rowPairs a us)

theorem pairWord_length {n : Nat} (p : Affine n × Affine n) :
    (pairWord p).length = 2 * (n + 1) := by
  simp only [pairWord, List.length_append, affineWord_length]
  omega

theorem pairBits_append {n : Nat} (ps qs : List (Affine n × Affine n)) :
    pairBits (ps ++ qs) = pairBits ps ++ pairBits qs := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.cons_append, pairBits, ih, List.append_assoc]

theorem pairBits_length {n : Nat} (ps : List (Affine n × Affine n)) :
    (pairBits ps).length = (2 * (n + 1)) * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pairBits, List.length_append, pairWord_length, ih,
      List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem rowPairs_cons {n : Nat} (a b : Affine n) (us : List (Affine n))
    (ha : Homogeneous a) (hb : Homogeneous b) :
    rowPairs a (b :: us) =
      if lower a b then rowPairs a us else (a,b) :: rowPairs a us := by
  cases h : lower a b with
  | false =>
    have hle : ¬normalCode a ≤ normalCode b :=
      of_decide_eq_false ((lower_exact a b ha hb).symm.trans h)
    have hlt : normalCode b < normalCode a := by omega
    simp only [rowPairs, List.filter_cons, decide_eq_true hlt, ↓reduceIte,
      List.map_cons, Bool.false_eq_true]
  | true =>
    have hle : normalCode a ≤ normalCode b :=
      of_decide_eq_true ((lower_exact a b ha hb).symm.trans h)
    have hlt : ¬normalCode b < normalCode a := by omega
    simp only [rowPairs, List.filter_cons, decide_eq_false hlt, Bool.false_eq_true, ↓reduceIte]

theorem rowBits_cons {n : Nat} (a b : Affine n) (us : List (Affine n))
    (ha : Homogeneous a) (hb : Homogeneous b) :
    rowBits a (b :: us) =
      if lower a b then rowBits a us else pairWord (a,b) ++ rowBits a us := by
  unfold rowBits
  rw [rowPairs_cons a b us ha hb]
  cases lower a b <;> rfl

theorem rowPairs_length {n : Nat} (a : Affine n) (us : List (Affine n)) :
    (rowPairs a us).length ≤ us.length := by
  simpa only [rowPairs, List.length_map] using
    List.length_filter_le (fun b : Affine n => decide (normalCode b < normalCode a)) us

theorem rowBits_length {n : Nat} (a : Affine n) (us : List (Affine n)) :
    (rowBits a us).length ≤ (2 * (n + 1)) * us.length := by
  rw [rowBits, pairBits_length]
  exact Nat.mul_le_mul_left _ (rowPairs_length a us)

def rows {n : Nat} (xs us : List (Affine n)) : List (Affine n × Affine n) :=
  xs.flatMap fun a => rowPairs a us

theorem rows_cons {n : Nat} (a : Affine n) (xs us : List (Affine n)) :
    rows (a :: xs) us = rowPairs a us ++ rows xs us := rfl
theorem rows_menu {n : Nat} (us : List (Affine n)) : rows us us = planeMenu us := rfl

theorem rows_length {n : Nat} (xs us : List (Affine n)) :
    (rows xs us).length ≤ xs.length * us.length := by
  induction xs with
  | nil => simp only [rows, List.flatMap_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons a xs ih =>
    have head := rowPairs_length a us
    simp only [rows_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

theorem rows_bytes_length {n : Nat} (xs us : List (Affine n)) :
    (pairBits (rows xs us)).length ≤ (2 * (n + 1)) * (xs.length * us.length) := by
  rw [pairBits_length]
  exact Nat.mul_le_mul_left _ (rows_length xs us)

theorem menu_bytes_length {n : Nat} (us : List (Affine n)) :
    (pairBits (planeMenu us)).length ≤ (2 * (n + 1)) * (us.length * us.length) := by
  exact rows_bytes_length us us

end PNP.Concrete.ResidualReduction.SourcePlaneMenuBytes
