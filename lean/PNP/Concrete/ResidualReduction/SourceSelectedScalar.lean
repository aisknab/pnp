import PNP.Concrete.ResidualReduction.SourceRankOneQuery
import PNP.Concrete.ResidualReduction.SourceRankTwoQuery

namespace PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine PNP.Concrete.ResidualReduction.SourcePlane

/-- Retain every original row; replace only its scalar-selection flag. -/
def markSource {n : Nat} : (F : Family n) → Point F.length → Family n
  | [], _ => []
  | r :: F, (b, w) => {r with selected := b} :: markSource F w

def weightedValue {n : Nat} : (F : Family n) → Point F.length → Point n → Bool
  | [], _, _ => false
  | r :: F, (b, w), x => Bool.xor (b && r.eval x) (weightedValue F w x)

theorem markSource_length {n : Nat} (F : Family n) (w : Point F.length) :
    (markSource F w).length = F.length := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    simp only [markSource, List.length_cons, ih]

theorem markSource_models {n : Nat} (F : Family n) (w : Point F.length) (x : Point n) :
    models (markSource F w) x = models F x := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    change ((!r.eval x) && models (markSource F w) x) = ((!r.eval x) && models F x)
    rw [ih]

theorem markSource_scalar_eval {n : Nat} (F : Family n) (w : Point F.length) (x : Point n) :
    qEval (scalar (markSource F w)) x = weightedValue F w x := by
  induction F with
  | nil => simp only [markSource, scalar, qOfAffine_eval, aConst_eval, weightedValue]
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    cases b <;>
      simp only [markSource, scalar, Bool.false_eq_true, ↓reduceIte,
        qAdd_eval, qProduct_eval, weightedValue, Bool.false_and,
        Bool.true_and, Bool.false_xor, ih, Row.eval]

private theorem derivative_cancel : ∀ a b c d p : Bool,
    Bool.xor a d = Bool.xor (Bool.xor (Bool.xor b d) (Bool.xor c d)) p →
      Bool.xor a b = Bool.xor (Bool.xor c d) p := by decide

theorem row_derivative {n : Nat} (r : Row n) (x v : Point n) :
    Bool.xor (r.eval (pXor x v)) (r.eval x) =
      Bool.xor (activity r v) (polar r x v) :=
  derivative_cancel _ _ _ _ _ (activity_polarization r x v)

private theorem weighted_derivative_step (b a a' c c' u p v q : Bool)
    (h1 : Bool.xor a a' = Bool.xor u p)
    (h2 : Bool.xor c c' = Bool.xor v q) :
    Bool.xor (Bool.xor (b && a) c) (Bool.xor (b && a') c') =
      Bool.xor (Bool.xor (b && u) v) (Bool.xor (b && p) q) := by
  rw [xor_interchange, ← and_xor, h1, h2, and_xor]
  exact xor_interchange _ _ _ _

theorem weightedValue_derivative {n : Nat} (F : Family n) (w : Point F.length)
    (x v : Point n) :
    Bool.xor (weightedValue F w (pXor x v)) (weightedValue F w x) =
      Bool.xor (weightedActivity F w v) (weightedPolar F w x v) := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    change Bool.xor (Bool.xor (b && r.eval (pXor x v)) (weightedValue F w (pXor x v)))
      (Bool.xor (b && r.eval x) (weightedValue F w x)) =
      Bool.xor (Bool.xor (b && activity r v) (weightedActivity F w v))
        (Bool.xor (b && polar r x v) (weightedPolar F w x v))
    exact weighted_derivative_step b _ _ _ _ _ _ _ _ (row_derivative r x v) (ih w)

theorem weightedActivity_zero {n : Nat} (F : Family n) (w : Point F.length) :
    weightedActivity F w (zeroPoint n) = false := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    simp only [weightedActivity, activity_zero, Bool.and_false, Bool.false_xor, ih]

theorem scalar_map_eval {m n : Nat} (F : Family m) (f : Row m → Row n)
    (g : Point n → Point m) (hflag : ∀ r, (f r).selected = r.selected)
    (heval : ∀ r x, (f r).eval x = r.eval (g x)) (x : Point n) :
    qEval (scalar (F.map f)) x = qEval (scalar F) (g x) := by
  induction F with
  | nil => simp only [List.map_nil, scalar, qOfAffine_eval, aConst_eval]
  | cons r F ih =>
    cases hs : r.selected with
    | false => simpa only [List.map_cons, scalar, hflag, hs, Bool.false_eq_true, ↓reduceIte] using ih
    | true =>
      simp only [List.map_cons, scalar, hflag, hs, ↓reduceIte, qAdd_eval, qProduct_eval]
      change Bool.xor ((f r).eval x) (qEval (scalar (F.map f)) x) =
        Bool.xor (r.eval (g x)) (qEval (scalar F) (g x))
      rw [heval, ih]

theorem scalar_chart_eval {n : Nat} (F : Family (n + 1))
    (k : Fin (n + 1)) (v : Point n) (x : Point (n + 1)) :
    qEval (scalar (chartRows F k v)) x = qEval (scalar F) (unchart k v x) := by
  apply scalar_map_eval F (fun r => (r.cut k).shear v) (unchart k v)
  · intro r; rfl
  · intro r x
    simp only [Row.shear_eval, Row.cut_eval, unchart]

private theorem xor_cancel_right : ∀ a b c : Bool,
    Bool.xor a c = Bool.xor b c → a = b := by decide

theorem affine_eval_ext {n : Nat} (f g : Affine n)
    (h : ∀ x, aEval f x = aEval g x) : f = g := by
  induction n with
  | zero => exact h ()
  | succ n ih =>
    rcases f with ⟨a, f⟩
    rcases g with ⟨b, g⟩
    have ht : f = g := ih f g (fun x => by
      simpa only [aEval, Bool.and_false, Bool.false_xor] using h (false, x))
    have hh := h (true, zeroPoint n)
    simp only [aEval, Bool.and_true] at hh
    rw [ht] at hh
    exact Prod.ext (xor_cancel_right a b _ hh) ht

theorem qHead_derivative {n : Nat} (q : Quadratic (n + 1)) (z : Point n) :
    Bool.xor (qEval q (true, z)) (qEval q (false, z)) = aEval q.1 z := by
  rcases q with ⟨a, q⟩
  simp only [qEval, Bool.and_true, Bool.and_false, Bool.false_xor,
    Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

end PNP.Concrete.ResidualReduction.SourceBalance
