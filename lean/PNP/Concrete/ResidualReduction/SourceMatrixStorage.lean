import PNP.Concrete.ResidualReduction.SourceRankOneMatrices

namespace PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.ConstrainedBilinear

def coefficientPoint : {n : Nat} → (Fin n → Bool) → Point n
  | 0, _ => ()
  | _ + 1, f => (f 0, coefficientPoint (fun i => f i.succ))

def pointEntry : {n : Nat} → Point n → Fin n → Bool
  | 0, _, i => Fin.elim0 i
  | _ + 1, (b, _), ⟨0, _⟩ => b
  | _ + 1, (_, x), ⟨i + 1, h⟩ => pointEntry x ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem pointEntry_coefficients {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    pointEntry (coefficientPoint f) i = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change pointEntry (coefficientPoint (fun k => f k.succ)) j = f j.succ
      exact ih _ j

def MatrixRows (n : Nat) : Nat → Type
  | 0 => Unit
  | m + 1 => Point n × MatrixRows n m

def matrixRows : {m n : Nat} → Matrix m n → MatrixRows n m
  | 0, _, _ => ()
  | _ + 1, _, M => (coefficientPoint (M 0), matrixRows (fun i => M i.succ))

def matrixRow : {m n : Nat} → MatrixRows n m → Fin m → Point n
  | 0, _, _, i => Fin.elim0 i
  | _ + 1, _, (r, _), ⟨0, _⟩ => r
  | _ + 1, _, (_, rs), ⟨i + 1, h⟩ => matrixRow rs ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem matrixRow_coefficients {m n : Nat} (M : Matrix m n) (i : Fin m) :
    matrixRow (matrixRows M) i = coefficientPoint (M i) := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change matrixRow (matrixRows (fun k => M k.succ)) j = coefficientPoint (M j.succ)
      exact ih _ j

/-- Coefficient lookup through explicit finite Boolean data.
    Executable callers materialize matrixRows before constructing access closures. -/
def storedMatrix {m n : Nat} (M : Matrix m n) : Matrix m n :=
  let rows := matrixRows M
  fun i j => pointEntry (matrixRow rows i) j

theorem storedMatrix_eq {m n : Nat} (M : Matrix m n) : storedMatrix M = M := by
  funext i j
  change pointEntry (matrixRow (matrixRows M) i) j = M i j
  rw [matrixRow_coefficients, pointEntry_coefficients]

end PNP.Concrete.ResidualReduction.SourceLine
