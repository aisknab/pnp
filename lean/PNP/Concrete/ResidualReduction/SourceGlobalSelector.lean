import PNP.Concrete.ResidualReduction.SourceNormalMenu

namespace PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections PNP.Concrete.ResidualReduction.SourceLine PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceBalance PNP.Concrete.ResidualReduction.SourceClosure

def firstSome {α β : Type} (f : α → Option β) : List α → Option β
  | [] => none
  | a::as => match f a with
    | some b => some b
    | none => firstSome f as

theorem firstSome_some {α β : Type} (f : α → Option β) (as : List α) (b : β)
    (h : firstSome f as = some b) : ∃ a ∈ as, f a = some b := by
  induction as with
  | nil => simp only [firstSome,reduceCtorEq] at h
  | cons a as ih =>
    cases ha : f a with
    | none =>
      obtain ⟨x,hx,hf⟩ := ih (by simpa only [firstSome,ha] using h)
      exact ⟨x,List.mem_cons_of_mem a hx,hf⟩
    | some x =>
      have he : x = b := by simpa only [firstSome,ha,Option.some.injEq] using h
      subst x
      exact ⟨a,List.mem_cons_self,ha⟩

theorem firstSome_none_iff {α β : Type} (f : α → Option β) (as : List α) :
    firstSome f as = none ↔ ∀ a ∈ as, f a = none := by
  induction as with
  | nil =>
    constructor
    · intro _ a ha; cases ha
    · intro _; rfl
  | cons a as ih =>
    cases ha : f a with
    | none =>
      simp only [firstSome,ha]
      rw [ih]
      constructor
      · intro h x hx
        rcases List.mem_cons.mp hx with he | ht
        · subst x; exact ha
        · exact h x ht
      · intro h x hx; exact h x (List.mem_cons_of_mem a hx)
    | some b =>
      constructor
      · intro h; simp only [firstSome,ha,reduceCtorEq] at h
      · intro h
        have bad := h a List.mem_cons_self
        rw [ha] at bad
        cases bad

def lineCandidate {n : Nat} (F : Family (n+1)) (a : Affine (n+1)) :
    Option (ConstructedStep n F.length) :=
  (sourceLineQuery F a).bind fun w =>
    buildStep F w.weights w.direction (some (a,betaNormal w.beta))

def planeCandidate {n : Nat} (F : Family (n+1)) (p : Affine (n+1) × Affine (n+1)) :
    Option (ConstructedStep n F.length) :=
  (sourcePlaneQuery F p.1 p.2).bind fun w => buildStep F w.1 w.2 (some p)

theorem lineCandidate_sound {n : Nat} (F : Family (n+1)) (a : Affine (n+1))
    (s : ConstructedStep n F.length) (h : lineCandidate F a = some s) :
    StepSound F s := by
  cases hq : sourceLineQuery F a with
  | none => simp only [lineCandidate,hq,Option.bind,reduceCtorEq] at h
  | some w =>
    exact buildStep_sound F w.weights w.direction (some (a,betaNormal w.beta)) s
      (by simpa only [lineCandidate,hq,Option.bind] using h)

theorem planeCandidate_sound {n : Nat} (F : Family (n+1)) (p : Affine (n+1) × Affine (n+1))
    (s : ConstructedStep n F.length) (h : planeCandidate F p = some s) :
    StepSound F s := by
  cases hq : sourcePlaneQuery F p.1 p.2 with
  | none => simp only [planeCandidate,hq,Option.bind,reduceCtorEq] at h
  | some w =>
    exact buildStep_sound F w.1 w.2 (some p) s
      (by simpa only [planeCandidate,hq,Option.bind] using h)

theorem lineCandidate_none_iff {n : Nat} (F : Family (n+1))
    (hn : sourceAffineQuery F = none) (a : Affine (n+1)) :
    lineCandidate F a = none ↔ sourceLineQuery F a = none := by
  simpa only [lineStep,lineCandidate,hn,true_and] using lineStep_none_iff F a

theorem planeCandidate_none_iff {n : Nat} (F : Family (n+1))
    (hn : sourceAffineQuery F = none) (p : Affine (n+1) × Affine (n+1)) :
    planeCandidate F p = none ↔ sourcePlaneQuery F p.1 p.2 = none := by
  simpa only [planeStep,planeCandidate,hn,true_and] using planeStep_none_iff F p.1 p.2

/-- The source-derived menu is computed once, with the affine prelude first.
    The two candidate searches accept no supplied correctness certificates. -/
def globalStep {n : Nat} (F : Family (n+1)) : Option (ConstructedStep n F.length) :=
  match sourceAffineQuery F with
  | some w => buildStep F w.1 w.2 none
  | none =>
    let us := sourceMenu F
    match firstSome (lineCandidate F) us with
    | some s => some s
    | none => firstSome (planeCandidate F) (planeMenu us)

theorem globalStep_sound {n : Nat} (F : Family (n+1))
    (s : ConstructedStep n F.length) (h : globalStep F = some s) : StepSound F s := by
  cases hp : sourceAffineQuery F with
  | some w => exact buildStep_sound F w.1 w.2 none s (by simpa only [globalStep,hp] using h)
  | none =>
    cases hl : firstSome (lineCandidate F) (sourceMenu F) with
    | some t =>
      have he : t = s := by simpa only [globalStep,hp,hl,Option.some.injEq] using h
      subst t
      obtain ⟨a,_,ha⟩ := firstSome_some _ _ _ hl
      exact lineCandidate_sound F a s ha
    | none =>
      have hp' : firstSome (planeCandidate F) (planeMenu (sourceMenu F)) = some s := by
        simpa only [globalStep,hp,hl] using h
      obtain ⟨p,_,he⟩ := firstSome_some _ _ _ hp'
      exact planeCandidate_sound F p s he

theorem globalStep_none_iff {n : Nat} (F : Family (n+1)) :
    globalStep F = none ↔
      sourceAffineQuery F = none ∧
      (∀ a ∈ sourceMenu F, sourceLineQuery F a = none) ∧
      (∀ p ∈ planeMenu (sourceMenu F), sourcePlaneQuery F p.1 p.2 = none) := by
  cases hp : sourceAffineQuery F with
  | some w =>
    obtain ⟨s,hs⟩ := buildStep_affine_total F w (sourceAffineQuery_sound F w hp)
    simp only [globalStep,hp,hs,reduceCtorEq,false_and]
  | none =>
    cases hl : firstSome (lineCandidate F) (sourceMenu F) with
    | some s =>
      constructor
      · intro h; simp only [globalStep,hp,hl,reduceCtorEq] at h
      · rintro ⟨_,hline,_⟩
        have bad : firstSome (lineCandidate F) (sourceMenu F) = none :=
          (firstSome_none_iff _ _).mpr fun a ha =>
            (lineCandidate_none_iff F hp a).mpr (hline a ha)
        rw [hl] at bad
        cases bad
    | none =>
      constructor
      · intro h
        refine ⟨rfl,?_,?_⟩
        · intro a ha
          exact (lineCandidate_none_iff F hp a).mp ((firstSome_none_iff _ _).mp hl a ha)
        · intro p hm
          have hplanes : firstSome (planeCandidate F) (planeMenu (sourceMenu F)) = none := by
            simpa only [globalStep,hp,hl] using h
          exact (planeCandidate_none_iff F hp p).mp ((firstSome_none_iff _ _).mp hplanes p hm)
      · rintro ⟨_,_,hplanes⟩
        have h : firstSome (planeCandidate F) (planeMenu (sourceMenu F)) = none :=
          (firstSome_none_iff _ _).mpr fun p hm =>
            (planeCandidate_none_iff F hp p).mpr (hplanes p hm)
        simpa only [globalStep,hp,hl] using h

def MenuEligible {n : Nat} (F : Family n) : Prop :=
  (∃ w, AffineGood F w) ∨
  (∃ a ∈ sourceMenu F, ∃ w, LineGood F a w) ∨
  (∃ p ∈ planeMenu (sourceMenu F), ∃ w, PlaneGood F p.1 p.2 w)

theorem globalStep_none_iff_no_menu_witness {n : Nat} (F : Family (n+1)) :
    globalStep F = none ↔ ¬ MenuEligible F := by
  constructor
  · intro hn he
    obtain ⟨hp,hl,hr⟩ := (globalStep_none_iff F).mp hn
    rcases he with ha | ⟨a,hm,hw⟩ | ⟨p,hm,hw⟩
    · exact (sourceAffineQuery_none_iff F).mp hp ha
    · exact (sourceLineQuery_none_iff F a).mp (hl a hm) hw
    · exact (sourcePlaneQuery_none_iff F p.1 p.2).mp (hr p hm) hw
  · intro hn
    apply (globalStep_none_iff F).mpr
    refine ⟨(sourceAffineQuery_none_iff F).mpr (fun h => hn (Or.inl h)),?_,?_⟩
    · intro a ha
      exact (sourceLineQuery_none_iff F a).mpr
        (fun h => hn (Or.inr (Or.inl ⟨a,ha,h⟩)))
    · intro p hp
      exact (sourcePlaneQuery_none_iff F p.1 p.2).mpr
        (fun h => hn (Or.inr (Or.inr ⟨p,hp,h⟩)))

theorem globalStep_complete {n : Nat} (F : Family (n+1)) (h : MenuEligible F) :
    ∃ s, globalStep F = some s := by
  cases hs : globalStep F with
  | some s => exact ⟨s,rfl⟩
  | none => exact False.elim ((globalStep_none_iff_no_menu_witness F).mp hs h)

theorem weightedActivity_zero_of_rows {n : Nat} (F : Family n) (v : Point n)
    (h : ∀ r ∈ F, activity r v = false) (w : Point F.length) :
    weightedActivity F w v = false := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b,w⟩
    have hr := h r List.mem_cons_self
    have ht := ih (fun s hs => h s (List.mem_cons_of_mem r hs)) w
    simp only [weightedActivity,hr,ht,Bool.and_false,Bool.xor_false]

/-- A separate common-radical fallback cannot add an active source combination
    after the affine prelude failed on an affine-product input. -/
theorem failedAffine_commonRadical_inactive {n : Nat} (F : Family n)
    (hn : sourceAffineQuery F = none) (v : Point n)
    (hd : ∀ r ∈ F, ∀ x, polar r v x = false) (w : Point F.length) :
    weightedActivity F w v = false :=
  weightedActivity_zero_of_rows F v
    (fun r hr => failed_affine_common_radical_inactive F hn r hr v (hd r hr)) w

end PNP.Concrete.ResidualReduction.SourceChain
