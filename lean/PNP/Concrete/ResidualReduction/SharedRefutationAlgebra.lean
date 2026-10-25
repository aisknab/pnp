import PNP.Concrete.ResidualReduction.FactoredContraction

/-! Pointwise algebra for a shared scalar-refutation lift. These identities do
not assert that an affine guard exists, that a recursive solver is complete, or
that arbitrary polynomial-circuit identities can be decided efficiently. -/

namespace PNP.Concrete.ResidualReduction.SharedRefutationAlgebra
open PNP.Concrete.ResidualReduction.FactoredContraction

private theorem head_quotient_bool : forall s t h q : Bool,
    Bool.xor (h && s) q =
      Bool.xor (Bool.xor (h && t) q) ((Bool.xor s t) && h) := by decide

/-- A quadratic's head is the exact affine quotient for any head-bit
substitution; the tail value need not be zero. -/
theorem quadratic_head_quotient {n : Nat} (q : Quadratic (n + 1))
    (s t : Bool) (z : Point n) :
    qEval q (s, z) =
      Bool.xor (qEval q (t, z)) ((Bool.xor s t) && aEval q.1 z) := by
  rcases q with ⟨head, tail⟩
  exact head_quotient_bool s t (aEval head z) (qEval tail z)

/-- Every retained factored row has its own exact affine quotient, including
the Boolean diagonal term already present in the product coefficients. -/
theorem row_head_quotient {n : Nat} (r : Row (n + 1)) (u : Affine n)
    (s : Bool) (z : Point n) :
    r.eval (s, z) =
      Bool.xor ((affineRow u r).eval z)
        ((Bool.xor s (aEval u z)) && aEval (qProduct r.left r.right).1 z) := by
  rw [affineRow_eval]
  simpa only [qProduct_eval, Row.eval] using
    quadratic_head_quotient (qProduct r.left r.right) s (aEval u z) z

/-- Values for one aligned source row. In particular, no operation zips or
silently truncates separately supplied coefficient and equation lists. -/
structure LiftRow where
  weight : Bool
  source : Bool
  restricted : Bool
  quotient : Bool
  multiplier : Bool

def rowSum (value : LiftRow → Bool) : List LiftRow → Bool
  | [] => false
  | r :: rows => Bool.xor (value r) (rowSum value rows)

def guardValue (rows : List LiftRow) : Bool :=
  rowSum (fun r => r.weight && r.source) rows

def correctionValue (rows : List LiftRow) : Bool :=
  rowSum (fun r => r.multiplier && r.quotient) rows

def restrictedValue (rows : List LiftRow) : Bool :=
  rowSum (fun r => r.multiplier && r.restricted) rows

/-- The same correction value is used for every updated multiplier. -/
def liftedMultiplier (rows : List LiftRow) (r : LiftRow) : Bool :=
  Bool.xor r.multiplier (r.weight && correctionValue rows)

def liftedValue (rows : List LiftRow) : Bool :=
  rowSum (fun r => liftedMultiplier rows r && r.source) rows

private theorem xor_interchange : forall a b c d : Bool,
    Bool.xor (Bool.xor a b) (Bool.xor c d) =
      Bool.xor (Bool.xor a c) (Bool.xor b d) := by decide

private theorem and_xor : forall a b c : Bool,
    (a && Bool.xor b c) = Bool.xor (a && b) (a && c) := by decide

private theorem update_term : forall h a H q : Bool,
    (Bool.xor h (a && H) && q) =
      Bool.xor (h && q) (H && (a && q)) := by decide

private theorem source_term : forall h q g l : Bool,
    (h && Bool.xor q (g && l)) =
      Bool.xor (h && q) (g && (h && l)) := by decide

private theorem cancel_correction : forall q g H : Bool,
    Bool.xor (Bool.xor q (g && H)) (H && g) = q := by decide

theorem rowSum_congr (f g : LiftRow → Bool) (rows : List LiftRow) :
    (∀ r ∈ rows, f r = g r) → rowSum f rows = rowSum g rows := by
  induction rows with
  | nil => intro _; rfl
  | cons r rows ih =>
    intro same
    change Bool.xor (f r) (rowSum f rows) = Bool.xor (g r) (rowSum g rows)
    rw [same r List.mem_cons_self, ih (fun t ht => same t (List.mem_cons_of_mem r ht))]

theorem rowSum_xor (f g : LiftRow → Bool) (rows : List LiftRow) :
    rowSum (fun r => Bool.xor (f r) (g r)) rows =
      Bool.xor (rowSum f rows) (rowSum g rows) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    simp only [rowSum, ih]
    exact xor_interchange (f r) (g r) (rowSum f rows) (rowSum g rows)

theorem rowSum_scale (b : Bool) (f : LiftRow → Bool) (rows : List LiftRow) :
    rowSum (fun r => b && f r) rows = (b && rowSum f rows) := by
  induction rows with
  | nil => cases b <;> rfl
  | cons r rows ih =>
    simp only [rowSum, ih]
    exact (and_xor b (f r) (rowSum f rows)).symm

theorem rowSum_zero (rows : List LiftRow) :
    rowSum (fun _ => false) rows = false := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    simpa only [rowSum, Bool.false_xor] using ih

theorem liftedValue_decomposition (rows : List LiftRow) :
    liftedValue rows =
      Bool.xor (rowSum (fun r => r.multiplier && r.source) rows)
        (correctionValue rows && guardValue rows) := by
  unfold liftedValue liftedMultiplier
  calc
    rowSum (fun r => Bool.xor r.multiplier
        (r.weight && correctionValue rows) && r.source) rows =
        rowSum (fun r => Bool.xor (r.multiplier && r.source)
          (correctionValue rows && (r.weight && r.source))) rows :=
      rowSum_congr _ _ rows (fun r _ =>
        update_term r.multiplier r.weight (correctionValue rows) r.source)
    _ = Bool.xor (rowSum (fun r => r.multiplier && r.source) rows)
        (correctionValue rows && guardValue rows) := by
      simp only [rowSum_xor, rowSum_scale, guardValue]

theorem sourceValue_decomposition (rows : List LiftRow) (g : Bool)
    (quotients : ∀ r ∈ rows,
      r.source = Bool.xor r.restricted (g && r.quotient)) :
    rowSum (fun r => r.multiplier && r.source) rows =
      Bool.xor (restrictedValue rows) (g && correctionValue rows) := by
  calc
    rowSum (fun r => r.multiplier && r.source) rows =
        rowSum (fun r => Bool.xor (r.multiplier && r.restricted)
          (g && (r.multiplier && r.quotient))) rows := by
      apply rowSum_congr
      intro r hr
      rw [quotients r hr]
      exact source_term r.multiplier r.restricted g r.quotient
    _ = Bool.xor (restrictedValue rows) (g && correctionValue rows) := by
      simp only [rowSum_xor, rowSum_scale, restrictedValue, correctionValue]

/-- Exact finite-row lifting, with constant source weights and one shared
correction. Applying this pointwise proves the polynomial lift identity. -/
theorem refutation_lift_sum (rows : List LiftRow) (g : Bool)
    (guard : guardValue rows = g)
    (quotients : ∀ r ∈ rows,
      r.source = Bool.xor r.restricted (g && r.quotient)) :
    liftedValue rows = restrictedValue rows := by
  rw [liftedValue_decomposition, sourceValue_decomposition rows g quotients, guard]
  exact cancel_correction (restrictedValue rows) g (correctionValue rows)

theorem refutation_lift_one (rows : List LiftRow) (g : Bool)
    (guard : guardValue rows = g)
    (quotients : ∀ r ∈ rows,
      r.source = Bool.xor r.restricted (g && r.quotient))
    (terminal : restrictedValue rows = true) : liftedValue rows = true :=
  (refutation_lift_sum rows g guard quotients).trans terminal

theorem liftedValue_zero_of_source_zero (rows : List LiftRow)
    (zero : ∀ r ∈ rows, r.source = false) : liftedValue rows = false := by
  unfold liftedValue
  have same : rowSum (fun r => liftedMultiplier rows r && r.source) rows =
      rowSum (fun _ => false) rows := by
    apply rowSum_congr
    intro r hr
    rw [zero r hr, Bool.and_false]
  exact same.trans (rowSum_zero rows)

/-- A lifted constant-one identity contradicts simultaneous zero source rows. -/
theorem refutation_lift_contradiction (rows : List LiftRow) (g : Bool)
    (guard : guardValue rows = g)
    (quotients : ∀ r ∈ rows,
      r.source = Bool.xor r.restricted (g && r.quotient))
    (terminal : restrictedValue rows = true)
    (zero : ∀ r ∈ rows, r.source = false) : False := by
  have one := refutation_lift_one rows g guard quotients terminal
  rw [liftedValue_zero_of_source_zero rows zero] at one
  cases one

end PNP.Concrete.ResidualReduction.SharedRefutationAlgebra
