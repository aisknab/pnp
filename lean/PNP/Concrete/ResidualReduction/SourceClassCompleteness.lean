import PNP.Concrete.ResidualReduction.SourceContractionClass

set_option autoImplicit false

namespace PNP.Concrete.ResidualReduction.SourceClass
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain

theorem linearEval_of_zero_constant {n : Nat} (a : Affine n)
    (ha : aConstant a = false) (x : Point n) : linearEval a x = aEval a x := by
  rw [linearEval, homogeneousRow_eval, ha, Bool.xor_false]

theorem linear_nonzero_witness {n : Nat} (a : Affine n)
    (ha : aConstant a = false) (hn : a ≠ aConst n false) :
    ∃ p, linearEval a p = true := by
  cases hp : findUnit (linearEval a) with
  | some p => exact ⟨p,findUnit_sound _ p hp⟩
  | none =>
    apply False.elim (hn ?_)
    apply affine_eval_ext
    intro x
    rw [← linearEval_of_zero_constant a ha x, aConst_eval]
    exact findUnit_none_zero _ (linearEval_zero a) (linearEval_additive a) hp x

/-- A constructive dual basis for two distinct nonzero binary linear forms.
    Only the existing finite unit searches are used. -/
theorem independent_linear_basis {n : Nat} (a b : Affine n)
    (ha : aConstant a = false) (hb : aConstant b = false)
    (hna : a ≠ aConst n false) (hnb : b ≠ aConst n false) (hne : b ≠ a) :
    ∃ p q, linearEval a p = true ∧ linearEval b p = false ∧
      linearEval a q = false ∧ linearEval b q = true := by
  obtain ⟨p0,hap0⟩ := linear_nonzero_witness a ha hna
  let g : Point n → Bool :=
    fun x => Bool.xor (linearEval b x) (linearEval a x && linearEval b p0)
  have gz : g (zeroPoint n) = false := by
    simp only [g, linearEval_zero, Bool.false_and, Bool.false_xor]
  have ga : ∀ x y, g (pXor x y) = Bool.xor (g x) (g y) := by
    intro x y
    simp only [g, linearEval_additive, xor_and]
    exact xor_interchange _ _ _ _
  cases hq : findUnit g with
  | none =>
    have hg := findUnit_none_zero g gz ga hq
    have he : ∀ x, linearEval b x = (linearEval a x && linearEval b p0) :=
      fun x => (xor_false_iff _ _).mp (hg x)
    cases hbp : linearEval b p0 with
    | false =>
      apply False.elim (hnb ?_)
      apply affine_eval_ext
      intro x
      rw [← linearEval_of_zero_constant b hb x, aConst_eval, he, hbp,
        Bool.and_false]
    | true =>
      apply False.elim (hne ?_)
      apply affine_eval_ext
      intro x
      rw [← linearEval_of_zero_constant b hb x, ← linearEval_of_zero_constant a ha x,
        he, hbp, Bool.and_true]
  | some s =>
    let q := eraseAlong (linearEval a) p0 s
    have haq : linearEval a q = false :=
      eraseAlong_zero _ p0 s (linearEval_additive a) hap0
    have hbq : linearEval b q = true := by
      rw [show linearEval b q = g s from
        eraseAlong_eval _ _ p0 s (linearEval_additive b)]
      exact findUnit_sound g s hq
    let p := eraseAlong (linearEval b) q p0
    refine ⟨p,q,?_,eraseAlong_zero _ q p0 (linearEval_additive b) hbq,haq,hbq⟩
    change linearEval a (eraseAlong (linearEval b) q p0) = true
    rw [eraseAlong_eval _ _ q p0 (linearEval_additive a), hap0, haq,
      Bool.and_false, Bool.xor_false]

def coefficientPoint : {n : Nat} → Affine n → Point n
  | 0, _ => ()
  | _+1, (b,a) => (b,coefficientPoint a)

theorem coefficientPoint_eval {n : Nat} (a : Affine n) (x : Point n) :
    pointDot (coefficientPoint a) x = linearEval a x := by
  rw [linearEval, homogeneousRow_eval]
  induction n with
  | zero =>
    change false = Bool.xor a a
    exact (Bool.xor_self a).symm
  | succ n ih =>
    rcases a with ⟨b,a⟩
    rcases x with ⟨c,x⟩
    simp only [coefficientPoint, pointDot, aEval, aConstant, ih, Bool.xor_assoc]

theorem linear_function_covector {n : Nat} (f : Point n → Bool)
    (fz : f (zeroPoint n) = false)
    (fa : ∀ x y, f (pXor x y) = Bool.xor (f x) (f y)) :
    ∃ beta : Point n, ∀ x, pointDot beta x = f x := by
  refine ⟨coefficientPoint (linearForm f),fun x => ?_⟩
  rw [coefficientPoint_eval, linearEval_of_zero_constant _ (linearForm_constant f),
    linearForm_eval f fz fa]

theorem normalCode_injective_homogeneous {n : Nat} (a b : Affine n)
    (ha : aConstant a = false) (hb : aConstant b = false)
    (hc : normalCode a = normalCode b) : a = b := by
  induction n with
  | zero => exact ha.trans hb.symm
  | succ n ih =>
    rcases a with ⟨c,a⟩
    rcases b with ⟨d,b⟩
    change aConstant a = false at ha
    change aConstant b = false at hb
    cases c <;> cases d <;>
      simp only [normalCode, Bool.false_eq_true, ↓reduceIte] at hc
    all_goals first
      | exact Prod.ext rfl (ih a b ha hb (by omega))
      | exact False.elim (by omega)

private theorem finite_bool_partition {α : Type} (xs : List α) (p : α → Bool) :
    (∀ x ∈ xs, p x = true) ∨ ∃ x ∈ xs, p x = false := by
  induction xs with
  | nil => exact Or.inl (fun _ h => False.elim (List.not_mem_nil h))
  | cons x xs ih =>
    cases hx : p x with
    | false => exact Or.inr ⟨x,List.mem_cons_self,hx⟩
    | true =>
      rcases ih with ht | ⟨y,hy,hp⟩
      · apply Or.inl
        intro y hy
        rcases List.mem_cons.mp hy with he | hm
        · subst y; exact hx
        · exact ht y hm
      · exact Or.inr ⟨y,List.mem_cons_of_mem x hy,hp⟩

/-- Either all row derivatives lie on one specified line, or a row supplies
    a second distinct nonzero normal. The choice is derived from the source. -/
theorem derivative_line_cases {n : Nat} (F : Family n) (v : Point n) (a : Affine n) :
    (∀ r ∈ F, polarForm r v = aConst n false ∨ polarForm r v = a) ∨
      ∃ r ∈ F, polarForm r v ≠ aConst n false ∧ polarForm r v ≠ a := by
  rcases finite_bool_partition F
    (fun r => (aEq (polarForm r v) (aConst n false)) || (aEq (polarForm r v) a)) with
    hall | ⟨r,hr,hbad⟩
  · apply Or.inl
    intro r hr
    have hh := hall r hr
    simp only [Bool.or_eq_true] at hh
    rcases hh with hz | ha
    · exact Or.inl ((aEq_true_iff _ _).mp hz)
    · exact Or.inr ((aEq_true_iff _ _).mp ha)
  · refine Or.inr ⟨r,hr,?_,?_⟩
    · intro hz
      rw [(aEq_true_iff _ _).mpr hz, Bool.true_or] at hbad
      cases hbad
    · intro ha
      rw [(aEq_true_iff _ _).mpr ha, Bool.or_true] at hbad
      cases hbad

private theorem scalar_wedge_bool : ∀ ax bx ay byv k : Bool,
    Bool.xor (ax && (k && byv)) ((k && bx) && ay) =
      (k && Bool.xor (ax && byv) (bx && ay)) := by decide

theorem exterior_two_basis {α : Type} (B : α → α → Bool) (a b : α → Bool)
    (ha : ExteriorZero B a) (hb : ExteriorZero B b) (p q : α)
    (hap : a p = true) (hbp : b p = false) (hbq : b q = true) (x y : α) :
    B x y = (B p q && Bool.xor (a x && b y) (b x && a y)) := by
  have he : ∀ z, B z p = (B p q && b z) := by
    intro z
    have h := hb z p q
    simp only [hbp, hbq, Bool.and_true, Bool.and_false, Bool.false_xor] at h
    exact (xor_false_iff _ _).mp h
  rw [exterior_factor B a ha p hap x y, he x, he y]
  exact scalar_wedge_bool _ _ _ _ _

theorem exterior_kernel_zero {α : Type} (B : α → α → Bool) (a b g : α → Bool)
    (hg : ExteriorZero B g)
    (hB : ∀ x y, B x y = Bool.xor (a x && b y) (b x && a y))
    (p q : α) (hap : a p = true) (hbp : b p = false)
    (haq : a q = false) (hbq : b q = true) (x : α)
    (hax : a x = false) (hbx : b x = false) : g x = false := by
  have h := hg p q x
  rw [hB p q, hB p x, hB q x] at h
  simpa only [hap,hbp,haq,hbq,hax,hbx,Bool.true_and,Bool.false_and,
    Bool.and_true,Bool.and_false,Bool.xor_false,Bool.false_xor] using h

theorem single_kernel_iff {n : Nat} (a : Affine n) (x : Point n) :
    satisfies (homogeneous [a]) x = true ↔ linearEval a x = false := by
  change ((!linearEval a x) && true) = true ↔ linearEval a x = false
  cases linearEval a x <;> decide

theorem double_kernel_iff {n : Nat} (a b : Affine n) (x : Point n) :
    satisfies (homogeneous [a,b]) x = true ↔
      linearEval a x = false ∧ linearEval b x = false := by
  change ((!linearEval a x) && ((!linearEval b x) && true)) = true ↔
    linearEval a x = false ∧ linearEval b x = false
  cases linearEval a x <;> cases linearEval b x <;> decide

theorem polarForm_zero_value {n : Nat} (r : Row n) (v : Point n)
    (h : polarForm r v = aConst n false) (x : Point n) : polar r v x = false := by
  have he := congrArg (fun a => aEval a x) h
  simpa only [polarForm_eval, aConst_eval, polar_comm r x v] using he

theorem planeGood_swap {n : Nat} (F : Family n) (a b : Affine n)
    (u : Point F.length × Point n) (h : PlaneGood F a b u) :
    PlaneGood F b a u := by
  refine ⟨⟨?_,?_⟩,?_,h.2.2⟩
  · exact (double_kernel_iff b a u.2).mpr
      (And.symm ((double_kernel_iff a b u.2).mp h.1.1))
  · intro r hr x hx
    exact h.1.2 r hr x ((double_kernel_iff a b x).mpr
      (And.symm ((double_kernel_iff b a x).mp hx)))
  · intro x y
    rw [h.2.1 x y]
    simp only [fixedWedge, Bool.xor_comm]

/-- Every member of the full coefficient contraction class is covered by the
    computed source menu. No menu membership or coverage certificate is supplied.
    This does not assert that the class contains a contraction for every source. -/
theorem coefficient_implies_menu {n : Nat} (F : Family n)
    (w : Point F.length) (v : Point n) (h : CoefficientContraction F w v) :
    MenuEligible F := by
  cases haf : sourceAffineQuery F with
  | some u => exact Or.inl ⟨u,sourceAffineQuery_sound F u haf⟩
  | none =>
    have hmask : (∀ x y, weightedPolar F w x y = false) → False := by
      intro hm
      exact (sourceAffineQuery_none_iff F).mp haf ⟨(w,v),hm,h.1.1⟩
    have hnonzero : ∃ r ∈ F, polarForm r v ≠ aConst n false := by
      rcases derivative_line_cases F v (aConst n false) with hall | ⟨r,hr,hn,_⟩
      · have hd : ∀ r ∈ F, ∀ x, polar r v x = false := by
          intro r hr x
          exact polarForm_zero_value r v ((hall r hr).elim id id) x
        have bad := failedAffine_commonRadical_inactive F haf v hd w
        rw [h.1.1] at bad
        cases bad
      · exact ⟨r,hr,hn⟩
    obtain ⟨r0,hr0,hna⟩ := hnonzero
    let a := polarForm r0 v
    have ha : aConstant a = false := polarForm_constant r0 v
    have ham : a ∈ sourceMenu F := polarForm_mem_sourceMenu F r0 hr0 v hna
    have hav : linearEval a v = false := by
      rw [show a = polarForm r0 v from rfl, polarForm_linearEval, polar_diagonal]
    have hea : ExteriorZero (weightedPolar F w) (linearEval a) := by
      intro x y z
      simpa only [a,polarForm_linearEval] using h.2 r0 hr0 x y z
    rcases derivative_line_cases F v a with hline | ⟨r1,hr1,hnb,hne⟩
    · obtain ⟨p,hp⟩ := linear_nonzero_witness a ha hna
      obtain ⟨beta,hbeta⟩ := linear_function_covector (fun x => weightedPolar F w x p)
        (weightedPolar_zero_left F w p)
        (fun x y => weightedPolar_additive_left F w x y p)
      refine Or.inr (Or.inl ⟨a,ham,(⟨w,beta,v⟩ : LineWitness n F.length),?_⟩)
      refine ⟨⟨(single_kernel_iff a v).mpr hav,?_⟩,?_,?_,h.1.1⟩
      · intro r hr x hx
        have hax := (single_kernel_iff a x).mp hx
        rcases hline r hr with hz | he
        · exact polarForm_zero_value r v hz x
        · have heval := congrArg (fun f => linearEval f x) he
          rw [polarForm_linearEval] at heval
          exact heval.trans hax
      · intro x y
        simpa only [wedge,hbeta] using
          exterior_factor (weightedPolar F w) (linearEval a) hea p hp x y
      · rw [hbeta,weightedPolar_comm]
        exact h.1.2 p
    · let b := polarForm r1 v
      have hb : aConstant b = false := polarForm_constant r1 v
      have hbm : b ∈ sourceMenu F := polarForm_mem_sourceMenu F r1 hr1 v hnb
      have hbv : linearEval b v = false := by
        rw [show b = polarForm r1 v from rfl, polarForm_linearEval, polar_diagonal]
      have heb : ExteriorZero (weightedPolar F w) (linearEval b) := by
        intro x y z
        simpa only [b,polarForm_linearEval] using h.2 r1 hr1 x y z
      obtain ⟨p,q,hap,hbp,haq,hbq⟩ := independent_linear_basis a b ha hb hna hnb hne
      have hpq : weightedPolar F w p q = true := by
        cases hk : weightedPolar F w p q with
        | true => rfl
        | false =>
          apply False.elim (hmask ?_)
          intro x y
          rw [exterior_two_basis (weightedPolar F w) (linearEval a) (linearEval b)
            hea heb p q hap hbp hbq x y, hk, Bool.false_and]
      have hB : ∀ x y, weightedPolar F w x y =
          Bool.xor (linearEval a x && linearEval b y)
            (linearEval b x && linearEval a y) := by
        intro x y
        rw [exterior_two_basis (weightedPolar F w) (linearEval a) (linearEval b)
          hea heb p q hap hbp hbq x y, hpq, Bool.true_and]
      have hplane : PlaneGood F a b (w,v) := by
        refine ⟨⟨(double_kernel_iff a b v).mpr ⟨hav,hbv⟩,?_⟩,hB,h.1.1⟩
        intro r hr x hx
        obtain ⟨hax,hbx⟩ := (double_kernel_iff a b x).mp hx
        exact exterior_kernel_zero (weightedPolar F w) (linearEval a) (linearEval b)
          (polar r v) (h.2 r hr) hB p q hap hbp haq hbq x hax hbx
      have hcode : normalCode a ≠ normalCode b := by
        intro hc
        exact hne (normalCode_injective_homogeneous b a hb ha hc.symm)
      by_cases hlt : normalCode b < normalCode a
      · exact Or.inr (Or.inr ⟨(a,b),(planeMenu_mem _ _).mpr ⟨ham,hbm,hlt⟩,
          (w,v),hplane⟩)
      · have hgt : normalCode a < normalCode b := by omega
        exact Or.inr (Or.inr ⟨(b,a),(planeMenu_mem _ _).mpr ⟨hbm,ham,hgt⟩,
          (w,v),planeGood_swap F a b (w,v) hplane⟩)

theorem semantic_implies_menu {n : Nat} (F : Family n)
    (w : Point F.length) (v : Point n) (h : SemanticContraction F w v) :
    MenuEligible F :=
  coefficient_implies_menu F w v (semantic_implies_coefficient F w v h)

/-- Full ambient semantic class coverage, not merely menu-relative completeness.
    A useful contraction's existence is a premise, not a claim about all inputs. -/
theorem globalStep_complete_for_semantic {n : Nat} (F : Family (n+1))
    (h : ∃ w v, SemanticContraction F w v) : ∃ s, globalStep F = some s := by
  obtain ⟨w,v,h⟩ := h
  exact globalStep_complete F (semantic_implies_menu F w v h)

theorem globalStep_none_no_semantic {n : Nat} (F : Family (n+1))
    (hn : globalStep F = none) : ¬ ∃ w v, SemanticContraction F w v := by
  intro h
  obtain ⟨s,hs⟩ := globalStep_complete_for_semantic F h
  rw [hn] at hs
  cases hs

end PNP.Concrete.ResidualReduction.SourceClass
