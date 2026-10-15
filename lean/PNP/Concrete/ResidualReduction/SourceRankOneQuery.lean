import PNP.Concrete.ResidualReduction.SourceMatrixStorage

namespace PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceDirections

structure LineWitness (n m : Nat) where
  weights : Point m
  beta : Point n
  direction : Point n

def LineGood {n : Nat} (F : Family n) (alpha : Affine n)
    (w : LineWitness n F.length) : Prop :=
  DirectionSpec F [alpha] w.direction ∧
  (∀ x y, weightedPolar F w.weights x y = wedge alpha w.beta x y) ∧
  pointDot w.beta w.direction = false ∧
  weightedActivity F w.weights w.direction = true

def lineRawQuery {n : Nat} (F : Family n) (alpha : Affine n) :
    Option (Point (n + F.length) × Point (directionSpace F [alpha]).parameters) :=
  let d := directionSpace F [alpha]
  let ra := matrixRows (bilinearCoefficients (m := n + F.length) (n := d.parameters)
    (fun w z => pointDot (splitPoint F.length w).2 (d.direction z)))
  let rc := matrixRows (bilinearCoefficients (m := n + F.length) (n := d.parameters)
    (fun w z => weightedActivity F (splitPoint F.length w).1 (d.direction z)))
  query (rankOneRows F alpha) []
    (fun i j => pointEntry (matrixRow ra i) j)
    (fun i j => pointEntry (matrixRow rc i) j)

theorem lineRawQuery_eq {n : Nat} (F : Family n) (alpha : Affine n) :
    lineRawQuery F alpha =
      query (rankOneRows F alpha) [] (normalQueryMatrix F alpha) (activityQueryMatrix F alpha) := by
  change query (rankOneRows F alpha) [] (storedMatrix (normalQueryMatrix F alpha))
    (storedMatrix (activityQueryMatrix F alpha)) = _
  rw [storedMatrix_eq, storedMatrix_eq]

def liftLine {n : Nat} (F : Family n) (alpha : Affine n)
    (p : Point (n + F.length) × Point (directionSpace F [alpha]).parameters) :
    LineWitness n F.length :=
  let parts := splitPoint F.length p.1
  ⟨parts.1, parts.2, (directionSpace F [alpha]).direction p.2⟩

/-- Every constraint and coefficient is derived from F and alpha. -/
def sourceLineQuery {n : Nat} (F : Family n) (alpha : Affine n) :
    Option (LineWitness n F.length) :=
  (lineRawQuery F alpha).map (liftLine F alpha)

theorem rawGood_iff {n : Nat} (F : Family n) (alpha : Affine n)
    (p : Point (n + F.length) × Point (directionSpace F [alpha]).parameters) :
    Good (rankOneRows F alpha) [] (normalQueryMatrix F alpha) (activityQueryMatrix F alpha) p ↔
      LineGood F alpha (liftLine F alpha p) := by
  constructor
  · rintro ⟨hs, _, hn, ha⟩
    refine ⟨directionSpace_sound F [alpha] p.2, (rankOneRows_iff F alpha p.1).mp hs, ?_, ?_⟩
    · exact (normalQueryMatrix_eval F alpha p.1 p.2).symm.trans hn
    · exact (activityQueryMatrix_eval F alpha p.1 p.2).symm.trans ha
  · rintro ⟨_, hp, hn, ha⟩
    refine ⟨(rankOneRows_iff F alpha p.1).mpr hp, rfl, ?_, ?_⟩
    · exact (normalQueryMatrix_eval F alpha p.1 p.2).trans hn
    · exact (activityQueryMatrix_eval F alpha p.1 p.2).trans ha

theorem sourceLineQuery_sound {n : Nat} (F : Family n) (alpha : Affine n)
    (w : LineWitness n F.length) (h : sourceLineQuery F alpha = some w) :
    LineGood F alpha w := by
  cases hq : lineRawQuery F alpha with
  | none => simp only [sourceLineQuery, hq, Option.map, reduceCtorEq] at h
  | some p =>
    have he : liftLine F alpha p = w := by
      simpa only [sourceLineQuery, hq, Option.map, Option.some.injEq] using h
    subst w
    have hplain : query (rankOneRows F alpha) [] (normalQueryMatrix F alpha)
        (activityQueryMatrix F alpha) = some p := by
      simpa only [lineRawQuery_eq] using hq
    exact (rawGood_iff F alpha p).mp
      (query_sound (rankOneRows F alpha) [] (normalQueryMatrix F alpha)
        (activityQueryMatrix F alpha) p hplain)

theorem sourceLineQuery_complete {n : Nat} (F : Family n) (alpha : Affine n)
    (h : ∃ w, LineGood F alpha w) :
    ∃ w, sourceLineQuery F alpha = some w := by
  obtain ⟨⟨lambda, beta, v⟩, hd, hp, hn, ha⟩ := h
  obtain ⟨z, hz⟩ := directionSpace_complete F [alpha] v hd
  let joint := appendPoint F.length lambda beta
  have hg : LineGood F alpha (liftLine F alpha (joint, z)) := by
    dsimp only [LineGood, liftLine, joint]
    rw [split_append, hz]
    exact ⟨hd, hp, hn, ha⟩
  obtain ⟨p, hq⟩ := query_complete (rankOneRows F alpha) []
    (normalQueryMatrix F alpha) (activityQueryMatrix F alpha)
    ⟨(joint, z), (rawGood_iff F alpha (joint, z)).mpr hg⟩
  exact ⟨liftLine F alpha p, by simp only [sourceLineQuery, lineRawQuery_eq, hq, Option.map]⟩

/-- Failure means no witness for the complete stated rank-one source condition.
    It is not a claim that the original input is unsatisfiable. -/
theorem sourceLineQuery_none_iff {n : Nat} (F : Family n) (alpha : Affine n) :
    sourceLineQuery F alpha = none ↔ ¬ ∃ w, LineGood F alpha w := by
  constructor
  · intro hn hg
    obtain ⟨w, hw⟩ := sourceLineQuery_complete F alpha hg
    simp only [hn, reduceCtorEq] at hw
  · intro hg
    cases h : sourceLineQuery F alpha with
    | none => rfl
    | some w => exact False.elim (hg ⟨w, sourceLineQuery_sound F alpha w h⟩)

theorem sourceLineQuery_exists_iff {n : Nat} (F : Family n) (alpha : Affine n) :
    (∃ w, sourceLineQuery F alpha = some w) ↔ ∃ w, LineGood F alpha w :=
  ⟨fun ⟨w, h⟩ => ⟨w, sourceLineQuery_sound F alpha w h⟩,
    sourceLineQuery_complete F alpha⟩

end PNP.Concrete.ResidualReduction.SourceLine
