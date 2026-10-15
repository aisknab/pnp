import PNP.Concrete.ResidualReduction.AffineBilinearSearch
import PNP.Concrete.ResidualReduction.SourceRankTwoEquations
import PNP.Concrete.ResidualReduction.SourceMatrixStorage

namespace PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceDirections PNP.Concrete.ResidualReduction.SourceLine

def PlaneGood {n : Nat} (F : Family n) (alpha beta : Affine n)
    (p : Point F.length × Point n) : Prop :=
  DirectionSpec F [alpha, beta] p.2 ∧
  (∀ x y, weightedPolar F p.1 x y = fixedWedge alpha beta x y) ∧
  weightedActivity F p.1 p.2 = true

/-- Materialize coefficients before constructing lookup closures. -/
def planeSpaceQuery {n : Nat} (F : Family n) (alpha beta : Affine n)
    (s : Space F.length) :
    Option (Point F.length × Point (directionSpace F [alpha, beta]).parameters) :=
  let d := directionSpace F [alpha, beta]
  let rows := matrixRows (activityMatrix d F)
  affineBilinearQuery s (fun i j => pointEntry (matrixRow rows i) j)

theorem planeSpaceQuery_eq {n : Nat} (F : Family n) (alpha beta : Affine n)
    (s : Space F.length) :
    planeSpaceQuery F alpha beta s =
      affineBilinearQuery s (activityMatrix (directionSpace F [alpha, beta]) F) := by
  change affineBilinearQuery s (storedMatrix (activityMatrix (directionSpace F [alpha, beta]) F)) = _
  rw [storedMatrix_eq]

def planeRawQuery {n : Nat} (F : Family n) (alpha beta : Affine n) :
    Option (Point F.length × Point (directionSpace F [alpha, beta]).parameters) :=
  match solve F.length (planeRows F alpha beta) with
  | none => none
  | some s => planeSpaceQuery F alpha beta s

def liftPlane {n : Nat} (F : Family n) (alpha beta : Affine n)
    (p : Point F.length × Point (directionSpace F [alpha, beta]).parameters) :
    Point F.length × Point n :=
  (p.1, (directionSpace F [alpha, beta]).direction p.2)

/-- No supplied bases, families, coefficient tables or correctness premise. -/
def sourcePlaneQuery {n : Nat} (F : Family n) (alpha beta : Affine n) :
    Option (Point F.length × Point n) :=
  (planeRawQuery F alpha beta).map (liftPlane F alpha beta)

theorem sourcePlaneQuery_sound {n : Nat} (F : Family n) (alpha beta : Affine n)
    (w : Point F.length × Point n) (h : sourcePlaneQuery F alpha beta = some w) :
    PlaneGood F alpha beta w := by
  cases hraw : planeRawQuery F alpha beta with
  | none => simp only [sourcePlaneQuery, hraw, Option.map, reduceCtorEq] at h
  | some p =>
    have he : liftPlane F alpha beta p = w := by
      simpa only [sourcePlaneQuery, hraw, Option.map, Option.some.injEq] using h
    subst w
    cases hs : solve F.length (planeRows F alpha beta) with
    | none => simp only [planeRawQuery, hs, reduceCtorEq] at hraw
    | some s =>
      have hq : affineBilinearQuery s
          (activityMatrix (directionSpace F [alpha, beta]) F) = some p := by
        simpa only [planeRawQuery, hs, planeSpaceQuery_eq] using hraw
      obtain ⟨⟨z, hz⟩, hv⟩ := affineBilinearQuery_sound s _ p hq
      refine ⟨directionSpace_sound F [alpha, beta] p.2, ?_, ?_⟩
      · have hr := solve_some_sound (planeRows F alpha beta) s hs z
        rw [hz] at hr
        exact (planeRows_iff F alpha beta p.1).mp hr
      · exact (computed_activity_matrix_eval F [alpha, beta] p.1 p.2).symm.trans hv

theorem sourcePlaneQuery_complete {n : Nat} (F : Family n) (alpha beta : Affine n)
    (h : ∃ w, PlaneGood F alpha beta w) :
    ∃ w, sourcePlaneQuery F alpha beta = some w := by
  obtain ⟨⟨lambda, v⟩, hd, hp, ha⟩ := h
  have hr : satisfies (planeRows F alpha beta) lambda = true :=
    (planeRows_iff F alpha beta lambda).mpr hp
  obtain ⟨t, ht⟩ := directionSpace_complete F [alpha, beta] v hd
  cases hs : solve F.length (planeRows F alpha beta) with
  | none => exact False.elim ((solve_none_iff (planeRows F alpha beta)).mp hs ⟨lambda, hr⟩)
  | some s =>
    obtain ⟨z, hz⟩ := solve_some_complete (planeRows F alpha beta) s hs lambda hr
    have hm : bilinearEval (activityMatrix (directionSpace F [alpha, beta]) F)
        (mapEval s.forms z) t = true := by
      rw [computed_activity_matrix_eval, hz, ht]
      exact ha
    obtain ⟨p, hq⟩ := affineBilinearQuery_complete s
      (activityMatrix (directionSpace F [alpha, beta]) F) ⟨z, t, hm⟩
    exact ⟨liftPlane F alpha beta p, by
      simp only [sourcePlaneQuery, planeRawQuery, hs, planeSpaceQuery_eq, hq, Option.map]⟩

/-- No result means no witness for this complete stated source condition,
    never that the original Boolean problem is unsatisfiable. -/
theorem sourcePlaneQuery_none_iff {n : Nat} (F : Family n) (alpha beta : Affine n) :
    sourcePlaneQuery F alpha beta = none ↔ ¬ ∃ w, PlaneGood F alpha beta w := by
  constructor
  · intro hn hg
    obtain ⟨w, hw⟩ := sourcePlaneQuery_complete F alpha beta hg
    simp only [hn, reduceCtorEq] at hw
  · intro hg
    cases h : sourcePlaneQuery F alpha beta with
    | none => rfl
    | some w => exact False.elim (hg ⟨w, sourcePlaneQuery_sound F alpha beta w h⟩)

theorem sourcePlaneQuery_exists_iff {n : Nat} (F : Family n) (alpha beta : Affine n) :
    (∃ w, sourcePlaneQuery F alpha beta = some w) ↔ ∃ w, PlaneGood F alpha beta w :=
  ⟨fun ⟨w, h⟩ => ⟨w, sourcePlaneQuery_sound F alpha beta w h⟩,
    sourcePlaneQuery_complete F alpha beta⟩

/-- Number of tested pairs only, not the runtime of the full construction. -/
theorem sourcePlaneQuery_candidate_bound {n : Nat} (F : Family n)
    (alpha beta : Affine n) (s : Space F.length)
    (hs : solve F.length (planeRows F alpha beta) = some s) :
    (affineTestPairs s (directionSpace F [alpha, beta]).parameters).length ≤
      (F.length + 1) * n := by
  rw [affineTestPairs_length]
  exact Nat.mul_le_mul
    (Nat.add_le_add_right (solve_some_parameter_bound (planeRows F alpha beta) s hs) 1)
    (kernelSpace_parameter_bound (directionSystem F [alpha, beta]))

end PNP.Concrete.ResidualReduction.SourcePlane
