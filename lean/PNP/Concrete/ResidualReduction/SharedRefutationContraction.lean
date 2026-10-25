import PNP.Concrete.ResidualReduction.CheckedContraction
import PNP.Concrete.ResidualReduction.SharedRefutationAlgebra

/-! Row-wise evidence for the existing checked contraction, including its
nonlinear plane tail. Model-set equivalence alone is not enough to transport
row-indexed refutation coefficients. No new contraction search is introduced. -/

namespace PNP.Concrete.ResidualReduction.SharedRefutationContraction
open PNP.Concrete.ResidualReduction.FactoredContraction

theorem planeRows_values {n : Nat} (a b u : Affine n)
    (rows : Family (n + 1)) (out : Family n)
    (checked : planeRows a b u rows = some out) (z : Point n) :
    out.map (fun r => r.eval z) =
      rows.map (fun r => r.eval (planeValue a b u z, z)) := by
  induction rows generalizing out with
  | nil =>
    have same : ([] : Family n) = out := by
      simpa only [planeRows, Option.some.injEq] using checked
    cases same
    rfl
  | cons r rows ih =>
    cases head : planeRow a b u r with
    | none => simp only [planeRows, head, Option.bind, reduceCtorEq] at checked
    | some first =>
      cases rest : planeRows a b u rows with
      | none =>
        simp only [planeRows, head, rest, Option.bind, Option.map, reduceCtorEq] at checked
      | some tail =>
        have same : first :: tail = out := by
          simpa only [planeRows, head, rest, Option.bind, Option.map, Option.some.injEq] using checked
        cases same
        simp only [List.map_cons, planeRow_eval a b u r first head z, ih tail rest]

theorem reduce_values {n : Nat} (form : TailForm n)
    (rows : Family (n + 1)) (out : Family n)
    (checked : form.reduce rows = some out) (z : Point n) :
    out.map (fun r => r.eval z) = rows.map (fun r => r.eval (form.value z, z)) := by
  cases form with
  | affine u =>
    have same : rows.map (affineRow u) = out := by
      simpa only [TailForm.reduce, Option.some.injEq] using checked
    cases same
    simp only [List.map_map, Function.comp_def, affineRow_eval, TailForm.value]
  | plane a b u => exact planeRows_values a b u rows out checked z

theorem contract_values {n : Nat} (rows : Family (n + 1))
    (pivot : Fin (n + 1)) (direction : Point n) (form : TailForm n) (out : Family n)
    (checked : contract rows pivot direction form = some out) (z : Point n) :
    out.map (fun r => r.eval z) =
      (chartRows rows pivot direction).map (fun r => r.eval (form.value z, z)) :=
  reduce_values form _ out (contract_checks rows pivot direction form out checked).2.2 z

private theorem qEval_head {n : Nat} (q : Quadratic (n + 1)) (s : Bool) (z : Point n) :
    qEval q (s, z) = Bool.xor (aEval q.1 z && s) (qEval q.2 z) := by
  cases q
  rfl

/-- Every accepted tail is the exact globally monic selected source scalar,
not merely an origin value or an equality on satisfying assignments. -/
theorem contract_guard_value {n : Nat} (rows : Family (n + 1))
    (pivot : Fin (n + 1)) (direction : Point n) (form : TailForm n) (out : Family n)
    (checked : contract rows pivot direction form = some out) (s : Bool) (z : Point n) :
    qEval (scalar (chartRows rows pivot direction)) (s, z) = Bool.xor s (form.value z) := by
  obtain ⟨head, tail, _⟩ := contract_checks rows pivot direction form out checked
  rw [qEval_head, head, tail, aConst_eval, Bool.true_and, TailForm.polynomial_eval]

/-- Cofactors remain affine even when the checked substitution is nonlinear.
The exact substituted row list is supplied by contract_values above. -/
theorem contract_row_quotients {n : Nat} (rows : Family (n + 1))
    (pivot : Fin (n + 1)) (direction : Point n) (form : TailForm n) (out : Family n)
    (checked : contract rows pivot direction form = some out) :
    ∀ r ∈ chartRows rows pivot direction, ∀ s z,
      r.eval (s, z) =
        Bool.xor (r.eval (form.value z, z))
          (qEval (scalar (chartRows rows pivot direction)) (s, z) &&
            aEval (qProduct r.left r.right).1 z) := by
  intro r _ s z
  rw [contract_guard_value rows pivot direction form out checked s z]
  simpa only [qProduct_eval, Row.eval] using
    SharedRefutationAlgebra.quadratic_head_quotient
      (qProduct r.left r.right) s (form.value z) z

end PNP.Concrete.ResidualReduction.SharedRefutationContraction
