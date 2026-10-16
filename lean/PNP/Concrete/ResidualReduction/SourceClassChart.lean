import PNP.Concrete.ResidualReduction.SourceClassCompleteness

set_option autoImplicit false

namespace PNP.Concrete.ResidualReduction.SourceClass
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain

theorem functionPolar_zero_left {n : Nat} (f : Point n → Bool) (y : Point n) :
    functionPolar f (zeroPoint n) y = false := by
  simp only [functionPolar, point_zero_xor, Bool.xor_self]

/-- Construct coefficients from a vanishing third difference, rather than
    assuming an algebraic normal form or enumerating all assignments. -/
theorem quadratic_of_third_zero {n : Nat} (f : Point n → Bool)
    (hf : ∀ x y z, thirdDifference f x y z = false) :
    ∃ q : Quadratic n, ∀ x, qEval q x = f x := by
  induction n with
  | zero =>
    refine ⟨f (),?_⟩
    intro x
    cases x
    rfl
  | succ n ih =>
    let ft : Point n → Bool := fun x => f (false,x)
    have ht : ∀ x y z, thirdDifference ft x y z = false := by
      intro x y z
      simpa only [thirdDifference,functionPolar,pXor,zeroPoint,Bool.false_xor,ft]
        using hf (false,x) (false,y) (false,z)
    obtain ⟨qt,hqt⟩ := ih ft ht
    let e : Point (n+1) := (true,zeroPoint n)
    let l : Point n → Bool := fun x => functionPolar f (false,x) e
    have lz : l (zeroPoint n) = false := functionPolar_zero_left f e
    have la : ∀ x y, l (pXor x y) = Bool.xor (l x) (l y) := by
      intro x y
      apply (xor_false_iff _ _).mp
      exact hf (false,x) (false,y) e
    let a := aAdd (linearForm l)
      (aConst n (Bool.xor (f e) (f (false,zeroPoint n))))
    have he : ∀ x, aEval a x = Bool.xor (f (true,x)) (f (false,x)) := by
      intro x
      simp only [a,aAdd_eval,aConst_eval,linearForm_eval l lz la]
      simp only [l,e,functionPolar,pXor,Bool.false_xor,point_xor_zero,zeroPoint,
        Bool.xor_assoc,Bool.xor_self,Bool.xor_false]
    refine ⟨(a,qt),?_⟩
    rintro ⟨b,x⟩
    cases b <;>
      simp only [qEval,he,hqt,ft,Bool.and_true,Bool.and_false,Bool.false_xor,
        Bool.xor_assoc,Bool.xor_self,Bool.xor_false]

theorem third_zero_iff_quadratic {n : Nat} (f : Point n → Bool) :
    (∀ x y z, thirdDifference f x y z = false) ↔
      ∃ q : Quadratic n, ∀ x, qEval q x = f x := by
  constructor
  · exact quadratic_of_third_zero f
  · rintro ⟨q,hq⟩ x y z
    rw [← funext hq]
    exact thirdDifference_qEval q x y z

theorem coefficient_implies_semantic {n : Nat} (F : Family n)
    (w : Point F.length) (v : Point n) (h : CoefficientContraction F w v) :
    SemanticContraction F w v := by
  refine ⟨h.1,?_⟩
  intro r hr
  have ht : ∀ x y z,
      thirdDifference
        (fun t => weightedValue F w t && Bool.xor (activity r v) (polar r v t))
        x y z = false := by
    intro x y z
    rw [thirdDifference_weighted_product F w (activity r v) (polar r v)
      (polar_zero_right r v) (polar_additive_right r v)]
    exact h.2 r hr x y z
  obtain ⟨q,hq⟩ := quadratic_of_third_zero _ ht
  refine ⟨qAdd (qProduct r.left r.right) q,fun x => ?_⟩
  rw [qAdd_eval,qProduct_eval,hq,sourceRetraction_eval]
  rfl

theorem semantic_iff_coefficient {n : Nat} (F : Family n)
    (w : Point F.length) (v : Point n) :
    SemanticContraction F w v ↔ CoefficientContraction F w v :=
  ⟨semantic_implies_coefficient F w v,coefficient_implies_semantic F w v⟩

theorem quadratic_linear_pullback {m n : Nat} (q : Quadratic n)
    (L : Point m → Point n) (Lz : L (zeroPoint m) = zeroPoint n)
    (La : ∀ x y, L (pXor x y) = pXor (L x) (L y)) :
    ∃ r : Quadratic m, ∀ x, qEval r x = qEval q (L x) := by
  apply quadratic_of_third_zero
  have hp : ∀ x y, functionPolar (fun t => qEval q (L t)) x y =
      qPolar q (L x) (L y) := by
    intro x y
    simp only [functionPolar,qPolar,La,Lz]
  intro x y z
  simp only [thirdDifference,hp,La,qPolar_additive_left,Bool.xor_self]

private theorem xor_unit_toggle : ∀ a b : Bool,
    Bool.xor a b = true → a = !b := by decide

theorem sourceRetraction_shift {n : Nat} (F : Family n)
    (w : Point F.length) (v : Point n) (hb : Balanced F w v) (x : Point n) :
    sourceRetraction F w v (pXor x v) = sourceRetraction F w v x := by
  have hd : Bool.xor (weightedValue F w (pXor x v)) (weightedValue F w x) = true := by
    rw [weightedValue_derivative,hb.1,hb.2 x,Bool.xor_false]
  have ht := xor_unit_toggle _ _ hd
  simp only [sourceRetraction]
  rw [ht]
  cases hs : weightedValue F w x <;>
    simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,pXor_twice]

theorem pointXor_associative {n : Nat} (x y z : Point n) :
    pXor (pXor x y) z = pXor x (pXor y z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨a,x⟩
    rcases y with ⟨b,y⟩
    rcases z with ⟨c,z⟩
    simp only [pXor,ih,Bool.xor_assoc]

theorem pointXor_commutative {n : Nat} (x y : Point n) :
    pXor x y = pXor y x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨a,x⟩
    rcases y with ⟨b,y⟩
    simp only [pXor,ih,Bool.xor_comm]

theorem pointXor_left_commutative {n : Nat} (x y z : Point n) :
    pXor x (pXor y z) = pXor y (pXor x z) := by
  rw [← pointXor_associative,pointXor_commutative x y,pointXor_associative]

theorem pointXor_left_cancel {n : Nat} (x y : Point n) :
    pXor x (pXor x y) = y := by
  rw [← pointXor_associative,point_xor_self,point_zero_xor]

theorem shear_additive {n : Nat} (t : Point n) (x y : Point (n+1)) :
    shear t (pXor x y) = pXor (shear t x) (shear t y) := by
  rcases x with ⟨a,x⟩
  rcases y with ⟨b,y⟩
  cases a <;> cases b <;>
    simp only [shear,pXor,Bool.false_xor,Bool.xor_false,Bool.xor_self,
      Bool.false_eq_true,↓reduceIte,pointXor_commutative,
      pointXor_left_commutative,pointXor_left_cancel]

theorem encode_additive {n : Nat} (k : Fin (n+1)) (t : Point n)
    (x y : Point (n+1)) :
    encode k t (pXor x y) = pXor (encode k t x) (encode k t y) := by
  change (shear t (cut n k (pXor x y))).2 =
    pXor (shear t (cut n k x)).2 (shear t (cut n k y)).2
  rw [cut_xor,shear_additive]
  rfl

theorem encode_zero {n : Nat} (k : Fin (n+1)) (t : Point n) :
    encode k t (zeroPoint (n+1)) = zeroPoint n := by
  have h := encode_additive k t (zeroPoint (n+1)) (zeroPoint (n+1))
  rw [point_xor_self,point_xor_self] at h
  exact h

theorem unchart_false_base {n : Nat} (k : Fin (n+1)) (t z : Point n) :
    unchart k t (false,z) = basePoint k z := rfl

theorem decode_eq_retraction_base {n : Nat} (F : Family (n+1))
    (w : Point F.length) (v : Point (n+1)) (c : Fin (n+1) × Point n)
    (hc : chooseChart v = some c) (z : Point n) :
    decode (markSource F w) c.1 c.2 z =
      sourceRetraction F w v (basePoint c.1 z) := by
  rw [decode,source_tail_eval]
  cases hs : weightedValue F w (basePoint c.1 z) with
  | false =>
    simpa only [sourceRetraction,hs,Bool.false_eq_true,↓reduceIte] using
      (show unchart c.1 c.2 (false,z) = basePoint c.1 z from rfl)
  | true =>
    have h := unchart_flip c.1 c.2 z
    rw [chooseChart_sound v c hc,unchart_false_base] at h
    simpa only [sourceRetraction,hs,↓reduceIte] using h

/-- Equality on every ambient point, not only on source models. -/
theorem decode_encode_eq_retraction {n : Nat} (F : Family (n+1))
    (w : Point F.length) (v : Point (n+1)) (c : Fin (n+1) × Point n)
    (hc : chooseChart v = some c) (hb : Balanced F w v) (x : Point (n+1)) :
    decode (markSource F w) c.1 c.2 (encode c.1 c.2 x) =
      sourceRetraction F w v x := by
  have hall : ∀ b z,
      decode (markSource F w) c.1 c.2 (encode c.1 c.2 (unchart c.1 c.2 (b,z))) =
        sourceRetraction F w v (unchart c.1 c.2 (b,z)) := by
    intro b z
    simp only [encode,chart_unchart]
    rw [decode_eq_retraction_base F w v c hc z]
    cases b with
    | false => rfl
    | true =>
      rw [unchart_flip,chooseChart_sound v c hc,sourceRetraction_shift F w v hb,
        unchart_false_base]
  have h := hall (chart c.1 c.2 x).1 (chart c.1 c.2 x).2
  rw [show unchart c.1 c.2 ((chart c.1 c.2 x).1,(chart c.1 c.2 x).2) = x from
    unchart_chart c.1 c.2 x] at h
  exact h

/-- Exact degree closure through the actual computed quotient decoder. -/
def ChartQuadraticClosure {n : Nat} (F : Family (n+1))
    (w : Point F.length) (c : Fin (n+1) × Point n) : Prop :=
  ∀ r ∈ F, ∃ q : Quadratic n, ∀ z,
    qEval q z = r.eval (decode (markSource F w) c.1 c.2 z)

theorem semantic_iff_chart {n : Nat} (F : Family (n+1))
    (w : Point F.length) (v : Point (n+1)) (c : Fin (n+1) × Point n)
    (hc : chooseChart v = some c) :
    SemanticContraction F w v ↔ Balanced F w v ∧ ChartQuadraticClosure F w c := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    intro r hr
    obtain ⟨q,hq⟩ := h.2 r hr
    obtain ⟨qt,hqt⟩ := quadratic_linear_pullback q (basePoint c.1)
      (basePoint_zero c.1) (basePoint_additive c.1)
    refine ⟨qt,fun z => ?_⟩
    rw [hqt,hq,← decode_eq_retraction_base F w v c hc z]
  · rintro ⟨hb,hchart⟩
    refine ⟨hb,?_⟩
    intro r hr
    obtain ⟨q,hq⟩ := hchart r hr
    obtain ⟨qa,hqa⟩ := quadratic_linear_pullback q (encode c.1 c.2)
      (encode_zero c.1 c.2) (encode_additive c.1 c.2)
    refine ⟨qa,fun x => ?_⟩
    rw [hqa,hq,decode_encode_eq_retraction F w v c hc hb x]

theorem globalStep_complete_for_chart {n : Nat} (F : Family (n+1))
    (w : Point F.length) (v : Point (n+1)) (c : Fin (n+1) × Point n)
    (hc : chooseChart v = some c) (hb : Balanced F w v)
    (hq : ChartQuadraticClosure F w c) : ∃ s, globalStep F = some s :=
  globalStep_complete_for_semantic F
    ⟨w,v,(semantic_iff_chart F w v c hc).mpr ⟨hb,hq⟩⟩

end PNP.Concrete.ResidualReduction.SourceClass
