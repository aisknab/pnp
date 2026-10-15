import PNP.Concrete.ResidualReduction.SourceQueryChart

namespace PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine PNP.Concrete.ResidualReduction.SourcePlane PNP.Concrete.ResidualReduction.SourceBalance

theorem weightedActivity_zero_weights {n : Nat} (F : Family n) (x : Point n) :
    weightedActivity F (zeroPoint F.length) x = false := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    simp only [List.length_cons, zeroPoint, weightedActivity,
      Bool.false_and, Bool.false_xor, ih]

theorem weightedActivity_additive_weights {n : Nat} (F : Family n)
    (u v : Point F.length) (x : Point n) :
    weightedActivity F (pXor u v) x =
      Bool.xor (weightedActivity F u x) (weightedActivity F v x) := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases u with ⟨a, u⟩
    rcases v with ⟨b, v⟩
    simp only [weightedActivity, pXor, xor_and, ih]
    exact xor_interchange _ _ _ _

private theorem weightedPolarStep : ∀ b a d p x y q : Bool,
    Bool.xor (b && Bool.xor (Bool.xor a d) p) (Bool.xor (Bool.xor x y) q) =
      Bool.xor (Bool.xor (Bool.xor (b && a) x) (Bool.xor (b && d) y))
        (Bool.xor (b && p) q) := by decide

theorem weightedActivity_polarization {n : Nat} (F : Family n) (w : Point F.length)
    (x y : Point n) :
    weightedActivity F w (pXor x y) =
      Bool.xor (Bool.xor (weightedActivity F w x) (weightedActivity F w y))
        (weightedPolar F w x y) := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    simp only [weightedActivity, weightedPolar, activity_polarization, ih]
    exact weightedPolarStep _ _ _ _ _ _ _

def AffineMask {n : Nat} (F : Family n) (w : Point F.length) : Prop :=
  ∀ x y, weightedPolar F w x y = false

theorem affineMask_activity_additive {n : Nat} (F : Family n) (w : Point F.length)
    (h : AffineMask F w) (x y : Point n) :
    weightedActivity F w (pXor x y) =
      Bool.xor (weightedActivity F w x) (weightedActivity F w y) := by
  rw [weightedActivity_polarization, h x y, Bool.xor_false]

theorem linearEval_const {n : Nat} (b : Bool) (x : Point n) :
    linearEval (aConst n b) x = false := by
  have hc : aConstant (aConst n b) = b := by
    rw [← eval_zero_constant, aConst_eval]
  rw [linearEval, homogeneousRow_eval, aConst_eval, hc, Bool.xor_self]

def affineMaskRows {n : Nat} (F : Family n) : System F.length :=
  PNP.Concrete.ResidualReduction.SourcePlane.planeRows F (aConst n false) (aConst n false)

theorem affineMaskRows_iff {n : Nat} (F : Family n) (w : Point F.length) :
    satisfies (affineMaskRows F) w = true ↔ AffineMask F w := by
  simp only [affineMaskRows, planeRows_iff, fixedWedge, linearEval_const,
    Bool.false_and, Bool.false_xor, AffineMask]

def affineSpaceQuery {n : Nat} (F : Family n) (s : Space F.length) :
    Option (Point F.length × Point n) :=
  firstTrue (fun p => weightedActivity F p.1 p.2) (affineTestPairs s n)

theorem affineSpaceQuery_sound {n : Nat} (F : Family n) (s : Space F.length)
    (p : Point F.length × Point n) (h : affineSpaceQuery F s = some p) :
    (∃ z, mapEval s.forms z = p.1) ∧ weightedActivity F p.1 p.2 = true := by
  obtain ⟨hm, hv⟩ := firstTrue_sound _ _ _ h
  obtain ⟨z, _, j, he⟩ := (affineTestPairs_mem s p).mp hm
  exact ⟨⟨z, congrArg Prod.fst he⟩, hv⟩

theorem affineSpaceQuery_none_zero {n : Nat} (F : Family n) (s : Space F.length)
    (hs : ∀ z, AffineMask F (mapEval s.forms z))
    (hq : affineSpaceQuery F s = none) (z : Point s.parameters) (v : Point n) :
    weightedActivity F (mapEval s.forms z) v = false := by
  have hnone := (firstTrue_none_iff
    (fun (p : Point F.length × Point n) => weightedActivity F p.1 p.2)
    (affineTestPairs s n)).mp hq
  apply additive_units_zero (weightedActivity F (mapEval s.forms z))
    (weightedActivity_zero F _) (affineMask_activity_additive F _ (hs z)) ?_ v
  intro j
  apply affine_units_zero (fun t => weightedActivity F (mapEval s.forms t) (unitPoint n j))
  · exact hnone _ ((affineTestPairs_mem s _).mpr
      ⟨zeroPoint s.parameters, affineParameters_zero _, j, rfl⟩)
  · intro x y
    simp only [mapEval_affine_xor, weightedActivity_additive_weights]
  · intro i
    exact hnone _ ((affineTestPairs_mem s _).mpr
      ⟨unitPoint s.parameters i, affineParameters_unit i, j, rfl⟩)

theorem affineSpaceQuery_complete {n : Nat} (F : Family n) (s : Space F.length)
    (hs : ∀ z, AffineMask F (mapEval s.forms z))
    (h : ∃ z v, weightedActivity F (mapEval s.forms z) v = true) :
    ∃ p, affineSpaceQuery F s = some p := by
  cases hq : affineSpaceQuery F s with
  | none =>
    obtain ⟨z, v, hv⟩ := h
    have hz := affineSpaceQuery_none_zero F s hs hq z v
    rw [hv] at hz
    cases hz
  | some p => exact ⟨p, rfl⟩

/-- The affine-mask phase uses arbitrary source directions, not a common-radical
    restriction: cancellation among selected rows can expose a linear equation. -/
def sourceAffineQuery {n : Nat} (F : Family n) : Option (Point F.length × Point n) :=
  match solve F.length (affineMaskRows F) with
  | none => none
  | some s => affineSpaceQuery F s

def AffineGood {n : Nat} (F : Family n) (w : Point F.length × Point n) : Prop :=
  AffineMask F w.1 ∧ weightedActivity F w.1 w.2 = true

theorem sourceAffineQuery_sound {n : Nat} (F : Family n)
    (w : Point F.length × Point n) (h : sourceAffineQuery F = some w) :
    AffineGood F w := by
  cases hs : solve F.length (affineMaskRows F) with
  | none => simp only [sourceAffineQuery, hs, reduceCtorEq] at h
  | some s =>
    have hq : affineSpaceQuery F s = some w := by simpa only [sourceAffineQuery, hs] using h
    obtain ⟨⟨z, hz⟩, hv⟩ := affineSpaceQuery_sound F s w hq
    refine ⟨?_, hv⟩
    have hr := solve_some_sound (affineMaskRows F) s hs z
    rw [hz] at hr
    exact (affineMaskRows_iff F w.1).mp hr

theorem sourceAffineQuery_complete {n : Nat} (F : Family n)
    (h : ∃ w, AffineGood F w) : ∃ w, sourceAffineQuery F = some w := by
  obtain ⟨⟨w, v⟩, hm, hv⟩ := h
  have hr := (affineMaskRows_iff F w).mpr hm
  cases hs : solve F.length (affineMaskRows F) with
  | none => exact False.elim ((solve_none_iff (affineMaskRows F)).mp hs ⟨w, hr⟩)
  | some s =>
    obtain ⟨z, hz⟩ := solve_some_complete (affineMaskRows F) s hs w hr
    have hall : ∀ z, AffineMask F (mapEval s.forms z) :=
      fun z => (affineMaskRows_iff F _).mp (solve_some_sound (affineMaskRows F) s hs z)
    obtain ⟨p, hp⟩ := affineSpaceQuery_complete F s hall ⟨z, v, by rw [hz]; exact hv⟩
    exact ⟨p, by simp only [sourceAffineQuery, hs, hp]⟩

theorem sourceAffineQuery_none_iff {n : Nat} (F : Family n) :
    sourceAffineQuery F = none ↔ ¬ ∃ w, AffineGood F w := by
  constructor
  · intro hn hh
    obtain ⟨w, hw⟩ := sourceAffineQuery_complete F hh
    simp only [hn, reduceCtorEq] at hw
  · intro hh
    cases h : sourceAffineQuery F with
    | none => rfl
    | some w => exact False.elim (hh ⟨w, sourceAffineQuery_sound F w h⟩)

theorem row_weight_supported {n : Nat} (F : Family n) (r : Row n) (hr : r ∈ F) :
    ∃ w : Point F.length,
      (∀ x, weightedActivity F w x = activity r x) ∧
      (∀ x y, weightedPolar F w x y = polar r x y) := by
  induction F with
  | nil => cases hr
  | cons q F ih =>
    rcases List.mem_cons.mp hr with he | ht
    · subst r
      refine ⟨(true, zeroPoint F.length), ?_, ?_⟩
      · intro x
        simp only [weightedActivity, weightedActivity_zero_weights, Bool.true_and, Bool.xor_false]
      · intro x y
        simp only [weightedPolar, weightedPolar_zero_weights, Bool.true_and, Bool.xor_false]
    · obtain ⟨w, ha, hp⟩ := ih ht
      refine ⟨(false, w), ?_, ?_⟩
      · intro x; simpa only [weightedActivity, Bool.false_and, Bool.false_xor] using ha x
      · intro x y; simpa only [weightedPolar, Bool.false_and, Bool.false_xor] using hp x y

/-- A failed complete affine prelude excludes each nonconstant affine source row;
    no caller supplies this exclusion as a correctness certificate. -/
theorem sourceAffineQuery_none_row_activity {n : Nat} (F : Family n)
    (hn : sourceAffineQuery F = none) (r : Row n) (hr : r ∈ F)
    (hp : ∀ x y, polar r x y = false) (v : Point n) : activity r v = false := by
  cases hv : activity r v with
  | false => rfl
  | true =>
    obtain ⟨w, ha, hw⟩ := row_weight_supported F r hr
    exact False.elim ((sourceAffineQuery_none_iff F).mp hn
      ⟨(w, v), (fun x y => (hw x y).trans (hp x y)), (ha v).trans hv⟩)

end PNP.Concrete.ResidualReduction.SourceClosure
