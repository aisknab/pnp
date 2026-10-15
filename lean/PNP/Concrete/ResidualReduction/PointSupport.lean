import PNP.Concrete.ResidualReduction.BinarySolutionSpace

namespace PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear

theorem point_zero_xor {n : Nat} (x : Point n) :
    pXor (zeroPoint n) x = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    rcases x with ⟨b, x⟩
    simp only [zeroPoint, pXor, Bool.false_xor, ih]

theorem point_xor_zero {n : Nat} (x : Point n) :
    pXor x (zeroPoint n) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    rcases x with ⟨b, x⟩
    simp only [zeroPoint, pXor, Bool.xor_false, ih]

theorem point_xor_self {n : Nat} (x : Point n) :
    pXor x x = zeroPoint n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨b, x⟩
    simp only [pXor, Bool.xor_self, ih, zeroPoint]

/-- Explicit coordinate recursion. The general equivalence below preserves
    the previously checked Fin.cases-based constructor. -/
def unitPoint : (n : Nat) → Fin n → Point n
  | 0, i => Fin.elim0 i
  | n + 1, ⟨0, _⟩ => (true, zeroPoint n)
  | n + 1, ⟨i + 1, h⟩ => (false, unitPoint n ⟨i, Nat.lt_of_succ_lt_succ h⟩)

def referenceUnitPoint : (n : Nat) → Fin n → Point n
  | 0, i => Fin.elim0 i
  | n + 1, i =>
    Fin.cases (true, zeroPoint n) (fun j => (false, referenceUnitPoint n j)) i

theorem unitPoint_reference_eq (n : Nat) (i : Fin n) :
    unitPoint n i = referenceUnitPoint n i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (false, unitPoint n j) = (false, referenceUnitPoint n j)
      exact congrArg (fun x => (false, x)) (ih j)

theorem unitPoint_zero (n : Nat) :
    unitPoint (n + 1) 0 = (true, zeroPoint n) := rfl

theorem unitPoint_succ {n : Nat} (i : Fin n) :
    unitPoint (n + 1) i.succ = (false, unitPoint n i) := rfl

def sumUnits {n : Nat} : List (Fin n) → Point n
  | [] => zeroPoint n
  | i :: is => pXor (unitPoint n i) (sumUnits is)

def support : {n : Nat} → Point n → List (Fin n)
  | 0, _ => []
  | _ + 1, (b, x) =>
    if b then 0 :: (support x).map Fin.succ else (support x).map Fin.succ

theorem sumUnits_succ {n : Nat} (is : List (Fin n)) :
    sumUnits (is.map Fin.succ) = (false, sumUnits is) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, sumUnits, unitPoint_succ, ih,
      pXor, Bool.false_xor]

theorem sumUnits_support {n : Nat} (x : Point n) :
    sumUnits (support x) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    rcases x with ⟨b, x⟩
    cases b with
    | false =>
      simp only [support, Bool.false_eq_true, ↓reduceIte, sumUnits_succ, ih]
    | true =>
      simp only [support, ↓reduceIte, sumUnits, unitPoint_zero,
        sumUnits_succ, pXor, Bool.xor_false, point_zero_xor, ih]

theorem direction_zero {n : Nat} (s : Space n) :
    s.direction (zeroPoint s.parameters) = zeroPoint n :=
  point_xor_self _

end PNP.Concrete.ResidualReduction.ConstrainedBilinear
