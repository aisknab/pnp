import PNP.Concrete.ResidualReduction.SourceMatrixStorage

namespace PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceLine

def firstOne : {n : Nat} → Point n → Option (Fin n)
  | 0, _ => none
  | _ + 1, (b, x) => if b then some 0 else (firstOne x).map Fin.succ

theorem firstOne_sound {n : Nat} (x : Point n) (k : Fin n)
    (h : firstOne x = some k) : pointEntry x k = true := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    rcases x with ⟨b, x⟩
    cases b with
    | true =>
      have he : (0 : Fin (n + 1)) = k := by
        simpa only [firstOne, ↓reduceIte, Option.some.injEq] using h
      subst k
      rfl
    | false =>
      cases hp : firstOne x with
      | none => simp only [firstOne, Bool.false_eq_true, ↓reduceIte, hp, Option.map, reduceCtorEq] at h
      | some j =>
        have he : j.succ = k := by
          simpa only [firstOne, Bool.false_eq_true, ↓reduceIte, hp, Option.map, Option.some.injEq] using h
        subst k
        exact ih x j hp

theorem firstOne_none_zero {n : Nat} (x : Point n) (h : firstOne x = none) :
    x = zeroPoint n := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    rcases x with ⟨b, x⟩
    cases b with
    | true => simp only [firstOne, ↓reduceIte, reduceCtorEq] at h
    | false =>
      cases hp : firstOne x with
      | none => exact congrArg (fun z => (false, z)) (ih x hp)
      | some j => simp only [firstOne, Bool.false_eq_true, ↓reduceIte, hp, Option.map, reduceCtorEq] at h

theorem firstOne_complete {n : Nat} (x : Point n) (h : x ≠ zeroPoint n) :
    ∃ k, firstOne x = some k := by
  cases hk : firstOne x with
  | none => exact False.elim (h (firstOne_none_zero x hk))
  | some k => exact ⟨k, rfl⟩

theorem cut_zero {Z : Type} (n : Nat) (x : Tuple Z (n + 1)) :
    cut n 0 x = x := by
  cases n <;> rfl

theorem cut_succ {Z : Type} {n : Nat} (k : Fin (n + 1)) (x : Tuple Z (n + 2)) :
    cut (n + 1) k.succ x = ((cut n k x.2).1, (x.1, (cut n k x.2).2)) := by
  have hk : k.succ.val ≠ 0 := Nat.succ_ne_zero _
  simp only [cut, hk, ↓reduceDIte]
  rfl

theorem cut_head (n : Nat) (k : Fin (n + 1)) (x : Point (n + 1)) :
    (cut n k x).1 = pointEntry x k := by
  induction n with
  | zero =>
    have hk : k = 0 := Fin.ext (by omega)
    subst k
    rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [cut_zero]
      rcases x with ⟨b, x⟩
      rfl
    · rw [cut_succ]
      rcases x with ⟨b, x⟩
      exact ih j x

theorem cut_xor (n : Nat) (k : Fin (n + 1)) (x y : Point (n + 1)) :
    cut n k (pXor x y) =
      pXor (n := n + 1) (cut n k x) (cut n k y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [cut_zero, cut_zero, cut_zero]
    · rcases x with ⟨a, x⟩
      rcases y with ⟨b, y⟩
      simp only [cut_succ, pXor]
      have h := ih j x y
      rw [h]
      rfl

theorem insert_xor (n : Nat) (k : Fin (n + 1)) (x y : Point (n + 1)) :
    insert n k (pXor x y) = pXor (insert n k x) (insert n k y) := by
  have h := cut_xor n k (insert n k x) (insert n k y)
  rw [cut_insert, cut_insert] at h
  have hi := congrArg (insert n k) h
  simpa only [insert_cut] using hi.symm

/-- Choose the first nonzero direction coordinate and retain the exact remaining bits. -/
def chooseChart {n : Nat} (v : Point (n + 1)) : Option (Fin (n + 1) × Point n) :=
  (firstOne v).map fun k => (k, (cut n k v).2)

theorem chooseChart_sound {n : Nat} (v : Point (n + 1))
    (c : Fin (n + 1) × Point n) (h : chooseChart v = some c) :
    insert n c.1 (true, c.2) = v := by
  cases hp : firstOne v with
  | none => simp only [chooseChart, hp, Option.map, reduceCtorEq] at h
  | some k =>
    have he : (k, (cut n k v).2) = c := by
      simpa only [chooseChart, hp, Option.map, Option.some.injEq] using h
    subst c
    have hh : (cut n k v).1 = true := (cut_head n k v).trans (firstOne_sound v k hp)
    have hc : cut n k v = (true, (cut n k v).2) := Prod.ext hh rfl
    rw [← hc, insert_cut]

theorem chooseChart_complete {n : Nat} (v : Point (n + 1)) (h : v ≠ zeroPoint (n + 1)) :
    ∃ c, chooseChart v = some c := by
  obtain ⟨k, hk⟩ := firstOne_complete v h
  exact ⟨(k, (cut n k v).2), by simp only [chooseChart, hk, Option.map]⟩

theorem unchart_flip {n : Nat} (k : Fin (n + 1)) (v z : Point n) :
    unchart k v (true, z) =
      pXor (unchart k v (false, z)) (insert n k (true, v)) := by
  change insert n k (true, pXor z v) =
    pXor (insert n k (false, z)) (insert n k (true, v))
  exact insert_xor n k (false, z) (true, v)

end PNP.Concrete.ResidualReduction.SourceBalance
