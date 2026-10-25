import PNP.Concrete.ResidualReduction.SourceGlobalSelector
import PNP.Concrete.ResidualReduction.SharedRefutationContraction

/-! Exact row-indexed evidence for source-generated contraction steps.
The tail is recovered from the actual marked source scalar; no extra tail
certificate or change to the retained step record is needed. This module does
not assert that the source selector succeeds on every input. -/

namespace PNP.Concrete.ResidualReduction.SharedRefutationGlobalStep
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceDirections

def charted {n : Nat} (F : Family (n + 1)) (s : ConstructedStep n F.length) :
    Family (n + 1) :=
  chartRows (markSource F s.weights) s.pivot s.tail

def tailPolynomial {n : Nat} (F : Family (n + 1)) (s : ConstructedStep n F.length) :
    Quadratic n :=
  (scalar (charted F s)).2

theorem markSource_values {n : Nat} (F : Family n) (w : Point F.length) (x : Point n) :
    (markSource F w).map (fun r => r.eval x) = F.map (fun r => r.eval x) := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    change r.eval x :: (markSource F w).map (fun row => row.eval x) =
      r.eval x :: F.map (fun row => row.eval x)
    rw [ih w]

theorem chartRows_values {n : Nat} (F : Family (n + 1)) (pivot : Fin (n + 1))
    (direction : Point n) (x : Point (n + 1)) :
    (chartRows F pivot direction).map (fun r => r.eval x) =
      F.map (fun r => r.eval (unchart pivot direction x)) := by
  simp only [chartRows, List.map_map, Function.comp_def,
    Row.shear_eval, Row.cut_eval, unchart]

theorem charted_length {n : Nat} (F : Family (n + 1)) (s : ConstructedStep n F.length) :
    (charted F s).length = F.length := by
  simp only [charted, chartRows, List.length_map, markSource_length]

/-- Marking and charting preserve the order and values of every original row. -/
theorem charted_values {n : Nat} (F : Family (n + 1)) (s : ConstructedStep n F.length)
    (x : Point (n + 1)) :
    (charted F s).map (fun r => r.eval (chart s.pivot s.tail x)) =
      F.map (fun r => r.eval x) := by
  simp only [charted, chartRows_values, unchart_chart, markSource_values]

/-- The coefficient and ordered-row obligations needed to reconstruct one step. -/
def StepData {n : Nat} (F : Family (n + 1)) (s : ConstructedStep n F.length) : Prop :=
  (scalar (charted F s)).1 = aConst n true ∧
    ∀ z, s.output.map (fun r => r.eval z) =
      (charted F s).map (fun r => r.eval (qEval (tailPolynomial F s) z, z))

theorem buildStep_data {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (v : Point (n + 1)) (normals : Option (Affine (n + 1) × Affine (n + 1)))
    (s : ConstructedStep n F.length) (checked : buildStep F w v normals = some s) :
    StepData F s := by
  cases chosen : chooseChart v with
  | none =>
    simp only [buildStep, chosen, Option.bind, reduceCtorEq] at checked
  | some c =>
    cases contracted : contract (markSource F w) c.1 c.2 (computedTail F w c normals) with
    | none =>
      simp only [buildStep, chosen, Option.bind, contracted, Option.map, reduceCtorEq] at checked
    | some out =>
      have same : (⟨w, c.1, c.2, out⟩ : ConstructedStep n F.length) = s := by
        simpa only [buildStep, chosen, Option.bind, contracted, Option.map, Option.some.injEq]
          using checked
      subst s
      obtain ⟨head, tail, _⟩ := contract_checks (markSource F w) c.1 c.2
        (computedTail F w c normals) out contracted
      refine ⟨head, ?_⟩
      intro z
      change out.map (fun r => r.eval z) =
        (chartRows (markSource F w) c.1 c.2).map
          (fun r => r.eval (qEval (scalar (chartRows (markSource F w) c.1 c.2)).2 z, z))
      rw [tail, TailForm.polynomial_eval]
      exact SharedRefutationContraction.contract_values (markSource F w) c.1 c.2
        (computedTail F w c normals) out contracted z

private theorem lineCandidate_data {n : Nat} (F : Family (n + 1)) (a : Affine (n + 1))
    (s : ConstructedStep n F.length) (checked : lineCandidate F a = some s) :
    StepData F s := by
  cases query : sourceLineQuery F a with
  | none => simp only [lineCandidate, query, Option.bind, reduceCtorEq] at checked
  | some w =>
    exact buildStep_data F w.weights w.direction (some (a, betaNormal w.beta)) s
      (by simpa only [lineCandidate, query, Option.bind] using checked)

private theorem planeCandidate_data {n : Nat} (F : Family (n + 1))
    (p : Affine (n + 1) × Affine (n + 1)) (s : ConstructedStep n F.length)
    (checked : planeCandidate F p = some s) : StepData F s := by
  cases query : sourcePlaneQuery F p.1 p.2 with
  | none => simp only [planeCandidate, query, Option.bind, reduceCtorEq] at checked
  | some w =>
    exact buildStep_data F w.1 w.2 (some p) s
      (by simpa only [planeCandidate, query, Option.bind] using checked)

theorem globalStep_data {n : Nat} (F : Family (n + 1))
    (s : ConstructedStep n F.length) (checked : globalStep F = some s) :
    StepData F s := by
  cases affine : sourceAffineQuery F with
  | some w =>
    exact buildStep_data F w.1 w.2 none s
      (by simpa only [globalStep, affine] using checked)
  | none =>
    cases line : firstSome (lineCandidate F) (sourceMenu F) with
    | some t =>
      have same : t = s := by
        simpa only [globalStep, affine, line, Option.some.injEq] using checked
      subst t
      obtain ⟨a, _, accepted⟩ := firstSome_some _ _ _ line
      exact lineCandidate_data F a s accepted
    | none =>
      have plane : firstSome (planeCandidate F) (planeMenu (sourceMenu F)) = some s := by
        simpa only [globalStep, affine, line] using checked
      obtain ⟨p, _, accepted⟩ := firstSome_some _ _ _ plane
      exact planeCandidate_data F p s accepted

/-- This is the coefficient equality checked by the shared source lift. -/
theorem globalStep_guard {n : Nat} (F : Family (n + 1))
    (s : ConstructedStep n F.length) (checked : globalStep F = some s) :
    scalar (charted F s) = (aConst n true, tailPolynomial F s) := by
  exact Prod.ext (globalStep_data F s checked).1 rfl

/-- Every output row is the corresponding source row at the actual scalar tail,
including successful nonlinear plane steps. No permutation or truncation occurs. -/
theorem globalStep_values {n : Nat} (F : Family (n + 1))
    (s : ConstructedStep n F.length) (checked : globalStep F = some s) (z : Point n) :
    s.output.map (fun r => r.eval z) =
      (charted F s).map (fun r => r.eval (qEval (tailPolynomial F s) z, z)) :=
  (globalStep_data F s checked).2 z

end PNP.Concrete.ResidualReduction.SharedRefutationGlobalStep
