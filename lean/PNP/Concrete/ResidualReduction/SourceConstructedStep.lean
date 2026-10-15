import PNP.Concrete.ResidualReduction.SourceComputedContract

namespace PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections PNP.Concrete.ResidualReduction.SourceLine PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceBalance

structure ConstructedStep (n m : Nat) where
  weights : Point m
  pivot : Fin (n+1)
  tail : Point n
  output : Family n

/-- Every coefficient and residual row is computed from the original input.
    This constructor accepts no correctness, balance or factor certificate. -/
def buildStep {n : Nat} (F : Family (n+1)) (w : Point F.length)
    (v : Point (n+1)) (normals : Option (Affine (n+1) × Affine (n+1))) :
    Option (ConstructedStep n F.length) :=
  (chooseChart v).bind fun c =>
    (contract (markSource F w) c.1 c.2 (computedTail F w c normals)).map
      fun out => ⟨w,c.1,c.2,out⟩

def StepSound {n : Nat} (F : Family (n+1)) (s : ConstructedStep n F.length) : Prop :=
  s.output.length = F.length ∧
  (∀ z, models s.output z = models F (decode (markSource F s.weights) s.pivot s.tail z)) ∧
  (∀ z, encode s.pivot s.tail (decode (markSource F s.weights) s.pivot s.tail z) = z) ∧
  (∀ x, models F x = true →
    decode (markSource F s.weights) s.pivot s.tail (encode s.pivot s.tail x) = x) ∧
  ((∃ x, models F x = true) ↔ ∃ z, models s.output z = true)

theorem buildStep_sound {n : Nat} (F : Family (n+1)) (w : Point F.length)
    (v : Point (n+1)) (normals : Option (Affine (n+1) × Affine (n+1)))
    (s : ConstructedStep n F.length) (h : buildStep F w v normals = some s) :
    StepSound F s := by
  cases hc : chooseChart v with
  | none => simp only [buildStep,hc,Option.bind,reduceCtorEq] at h
  | some c =>
    cases ho : contract (markSource F w) c.1 c.2 (computedTail F w c normals) with
    | none => simp only [buildStep,hc,Option.bind,ho,Option.map,reduceCtorEq] at h
    | some out =>
      have he : (⟨w,c.1,c.2,out⟩ : ConstructedStep n F.length) = s := by
        simpa only [buildStep,hc,Option.bind,ho,Option.map,Option.some.injEq] using h
      subst s
      have hs := contract_full_model_bijection (markSource F w) c.1 c.2
        (computedTail F w c normals) out ho
      simpa only [StepSound,markSource_length,markSource_models] using hs

theorem buildStep_total {n : Nat} (F : Family (n+1)) (w : Point F.length)
    (v : Point (n+1)) (normals : Option (Affine (n+1) × Affine (n+1)))
    (hb : Balanced F w v)
    (ht : ∀ c, chooseChart v = some c →
      ∃ out, contract (markSource F w) c.1 c.2 (computedTail F w c normals) = some out) :
    ∃ s, buildStep F w v normals = some s := by
  obtain ⟨c,hc⟩ := chooseChart_complete v (balanced_direction_nonzero F w v hb)
  obtain ⟨out,ho⟩ := ht c hc
  exact ⟨⟨w,c.1,c.2,out⟩, by simp only [buildStep,hc,Option.bind,ho,Option.map]⟩

theorem buildStep_affine_total {n : Nat} (F : Family (n+1))
    (w : Point F.length × Point (n+1)) (h : AffineGood F w) :
    ∃ s, buildStep F w.1 w.2 none = some s :=
  buildStep_total F w.1 w.2 none (affineGood_balanced F w h)
    (computed_affine_contract_total F w h)

theorem buildStep_line_total {n : Nat} (F : Family (n+1))
    (hn : sourceAffineQuery F = none) (alpha : Affine (n+1))
    (w : LineWitness (n+1) F.length) (h : LineGood F alpha w) :
    ∃ s, buildStep F w.weights w.direction (some (alpha,betaNormal w.beta)) = some s :=
  buildStep_total F w.weights w.direction (some (alpha,betaNormal w.beta))
    (line_good_balanced F alpha w h) (computed_line_contract_total F hn alpha w h)

theorem buildStep_plane_total {n : Nat} (F : Family (n+1))
    (hn : sourceAffineQuery F = none) (alpha beta : Affine (n+1))
    (w : Point F.length × Point (n+1)) (h : PlaneGood F alpha beta w) :
    ∃ s, buildStep F w.1 w.2 (some (alpha,beta)) = some s :=
  buildStep_total F w.1 w.2 (some (alpha,beta))
    (plane_good_balanced F alpha beta w h)
    (computed_ranktwo_contract_total F hn alpha beta w h)

/-- The affine prelude is essential: it excludes active affine guards that
    would otherwise obstruct full-source factored residual construction. -/
def lineStep {n : Nat} (F : Family (n+1)) (alpha : Affine (n+1)) :
    Option (ConstructedStep n F.length) :=
  match sourceAffineQuery F with
  | some w => buildStep F w.1 w.2 none
  | none =>
    (sourceLineQuery F alpha).bind fun w =>
      buildStep F w.weights w.direction (some (alpha,betaNormal w.beta))

def planeStep {n : Nat} (F : Family (n+1)) (alpha beta : Affine (n+1)) :
    Option (ConstructedStep n F.length) :=
  match sourceAffineQuery F with
  | some w => buildStep F w.1 w.2 none
  | none =>
    (sourcePlaneQuery F alpha beta).bind fun w =>
      buildStep F w.1 w.2 (some (alpha,beta))

theorem lineStep_sound {n : Nat} (F : Family (n+1)) (alpha : Affine (n+1))
    (s : ConstructedStep n F.length) (h : lineStep F alpha = some s) :
    StepSound F s := by
  cases hp : sourceAffineQuery F with
  | some w =>
    exact buildStep_sound F w.1 w.2 none s (by simpa only [lineStep,hp] using h)
  | none =>
    cases hq : sourceLineQuery F alpha with
    | none => simp only [lineStep,hp,hq,Option.bind,reduceCtorEq] at h
    | some w =>
      exact buildStep_sound F w.weights w.direction (some (alpha,betaNormal w.beta)) s
        (by simpa only [lineStep,hp,hq,Option.bind] using h)

theorem planeStep_sound {n : Nat} (F : Family (n+1)) (alpha beta : Affine (n+1))
    (s : ConstructedStep n F.length) (h : planeStep F alpha beta = some s) :
    StepSound F s := by
  cases hp : sourceAffineQuery F with
  | some w =>
    exact buildStep_sound F w.1 w.2 none s (by simpa only [planeStep,hp] using h)
  | none =>
    cases hq : sourcePlaneQuery F alpha beta with
    | none => simp only [planeStep,hp,hq,Option.bind,reduceCtorEq] at h
    | some w =>
      exact buildStep_sound F w.1 w.2 (some (alpha,beta)) s
        (by simpa only [planeStep,hp,hq,Option.bind] using h)

/-- Failure is exactly failure of both source searches. It cannot be caused by
    a lost pivot, an incorrect computed tail, or an unfactored retained row. -/
theorem lineStep_none_iff {n : Nat} (F : Family (n+1)) (alpha : Affine (n+1)) :
    lineStep F alpha = none ↔
      sourceAffineQuery F = none ∧ sourceLineQuery F alpha = none := by
  cases hp : sourceAffineQuery F with
  | some w =>
    obtain ⟨s,hs⟩ := buildStep_affine_total F w (sourceAffineQuery_sound F w hp)
    simp only [lineStep,hp,hs,reduceCtorEq,false_and]
  | none =>
    cases hq : sourceLineQuery F alpha with
    | none => simp only [lineStep,hp,hq,Option.bind,and_self]
    | some w =>
      obtain ⟨s,hs⟩ := buildStep_line_total F hp alpha w (sourceLineQuery_sound F alpha w hq)
      simp only [lineStep,hp,hq,Option.bind,hs,reduceCtorEq,and_false]

theorem planeStep_none_iff {n : Nat} (F : Family (n+1)) (alpha beta : Affine (n+1)) :
    planeStep F alpha beta = none ↔
      sourceAffineQuery F = none ∧ sourcePlaneQuery F alpha beta = none := by
  cases hp : sourceAffineQuery F with
  | some w =>
    obtain ⟨s,hs⟩ := buildStep_affine_total F w (sourceAffineQuery_sound F w hp)
    simp only [planeStep,hp,hs,reduceCtorEq,false_and]
  | none =>
    cases hq : sourcePlaneQuery F alpha beta with
    | none => simp only [planeStep,hp,hq,Option.bind,and_self]
    | some w =>
      obtain ⟨s,hs⟩ := buildStep_plane_total F hp alpha beta w
        (sourcePlaneQuery_sound F alpha beta w hq)
      simp only [planeStep,hp,hq,Option.bind,hs,reduceCtorEq,and_false]

end PNP.Concrete.ResidualReduction.SourceClosure
