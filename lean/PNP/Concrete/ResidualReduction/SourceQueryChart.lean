import PNP.Concrete.ResidualReduction.SourceWitnessBalance

namespace PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceLine PNP.Concrete.ResidualReduction.SourcePlane

structure ChartResult (n m : Nat) where
  weights : Point m
  pivot : Fin (n + 1)
  tail : Point n

def buildChart {n m : Nat} (w : Point m) (v : Point (n + 1)) :
    Option (ChartResult n m) :=
  (chooseChart v).map fun c => ⟨w, c.1, c.2⟩

def ChartSound {n : Nat} (F : Family (n + 1)) (c : ChartResult n F.length) : Prop :=
  (markSource F c.weights).length = F.length ∧
  (∀ x, models (markSource F c.weights) x = models F x) ∧
  (scalar (chartRows (markSource F c.weights) c.pivot c.tail)).1 = aConst n true ∧
  (∀ z, encode c.pivot c.tail (decode (markSource F c.weights) c.pivot c.tail z) = z) ∧
  (∀ x, models F x = true →
    decode (markSource F c.weights) c.pivot c.tail (encode c.pivot c.tail x) = x)

theorem buildChart_sound {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (v : Point (n + 1)) (c : ChartResult n F.length)
    (hb : Balanced F w v) (hc : buildChart w v = some c) : ChartSound F c := by
  cases h : chooseChart v with
  | none => simp only [buildChart, h, Option.map, reduceCtorEq] at hc
  | some kt =>
    have he : (⟨w, kt.1, kt.2⟩ : ChartResult n F.length) = c := by
      simpa only [buildChart, h, Option.map, Option.some.injEq] using hc
    subst c
    exact ⟨markSource_length F w, markSource_models F w,
      charted_source_head F w v kt h hb, encode_decode (markSource F w) kt.1 kt.2,
      fun x hx => charted_source_model_reconstruction F w v kt h hb x hx⟩

theorem buildChart_complete {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (v : Point (n + 1)) (hb : Balanced F w v) :
    ∃ c, buildChart w v = some c := by
  obtain ⟨kt, hk⟩ := chooseChart_complete v (balanced_direction_nonzero F w v hb)
  exact ⟨⟨w, kt.1, kt.2⟩, by simp only [buildChart, hk, Option.map]⟩

/-- The original-source line query computes all chart data; no balance premise is accepted. -/
def lineChart {n : Nat} (F : Family (n + 1)) (alpha : Affine (n + 1)) :
    Option (ChartResult n F.length) :=
  (sourceLineQuery F alpha).bind fun w => buildChart w.weights w.direction

/-- The original-source plane query computes all chart data; no balance premise is accepted. -/
def planeChart {n : Nat} (F : Family (n + 1)) (alpha beta : Affine (n + 1)) :
    Option (ChartResult n F.length) :=
  (sourcePlaneQuery F alpha beta).bind fun w => buildChart w.1 w.2

theorem lineChart_sound {n : Nat} (F : Family (n + 1)) (alpha : Affine (n + 1))
    (c : ChartResult n F.length) (hc : lineChart F alpha = some c) : ChartSound F c := by
  cases h : sourceLineQuery F alpha with
  | none => simp only [lineChart, h, Option.bind, reduceCtorEq] at hc
  | some w =>
    exact buildChart_sound F w.weights w.direction c (sourceLineQuery_balanced F alpha w h)
      (by simpa only [lineChart, h, Option.bind] using hc)

theorem planeChart_sound {n : Nat} (F : Family (n + 1)) (alpha beta : Affine (n + 1))
    (c : ChartResult n F.length) (hc : planeChart F alpha beta = some c) :
    ChartSound F c := by
  cases h : sourcePlaneQuery F alpha beta with
  | none => simp only [planeChart, h, Option.bind, reduceCtorEq] at hc
  | some w =>
    exact buildChart_sound F w.1 w.2 c (sourcePlaneQuery_balanced F alpha beta w h)
      (by simpa only [planeChart, h, Option.bind] using hc)

theorem lineChart_complete {n : Nat} (F : Family (n + 1)) (alpha : Affine (n + 1))
    (w : LineWitness (n + 1) F.length) (h : sourceLineQuery F alpha = some w) :
    ∃ c, lineChart F alpha = some c := by
  obtain ⟨c, hc⟩ := buildChart_complete F w.weights w.direction
    (sourceLineQuery_balanced F alpha w h)
  exact ⟨c, by simpa only [lineChart, h, Option.bind] using hc⟩

theorem planeChart_complete {n : Nat} (F : Family (n + 1)) (alpha beta : Affine (n + 1))
    (w : Point F.length × Point (n + 1)) (h : sourcePlaneQuery F alpha beta = some w) :
    ∃ c, planeChart F alpha beta = some c := by
  obtain ⟨c, hc⟩ := buildChart_complete F w.1 w.2 (sourcePlaneQuery_balanced F alpha beta w h)
  exact ⟨c, by simpa only [planeChart, h, Option.bind] using hc⟩

theorem lineChart_none_iff {n : Nat} (F : Family (n + 1)) (alpha : Affine (n + 1)) :
    lineChart F alpha = none ↔ sourceLineQuery F alpha = none := by
  cases h : sourceLineQuery F alpha with
  | none => simp only [lineChart, h, Option.bind]
  | some w =>
    obtain ⟨c, hc⟩ := lineChart_complete F alpha w h
    simp only [hc, reduceCtorEq]

theorem planeChart_none_iff {n : Nat} (F : Family (n + 1)) (alpha beta : Affine (n + 1)) :
    planeChart F alpha beta = none ↔ sourcePlaneQuery F alpha beta = none := by
  cases h : sourcePlaneQuery F alpha beta with
  | none => simp only [planeChart, h, Option.bind]
  | some w =>
    obtain ⟨c, hc⟩ := planeChart_complete F alpha beta w h
    simp only [hc, reduceCtorEq]

theorem lineChart_coefficient_check {n : Nat} (F : Family (n + 1)) (alpha : Affine (n + 1))
    (c : ChartResult n F.length) (hc : lineChart F alpha = some c) :
    aEq (scalar (chartRows (markSource F c.weights) c.pivot c.tail)).1 (aConst n true) = true :=
  (aEq_true_iff _ _).mpr (lineChart_sound F alpha c hc).2.2.1

theorem planeChart_coefficient_check {n : Nat} (F : Family (n + 1))
    (alpha beta : Affine (n + 1)) (c : ChartResult n F.length)
    (hc : planeChart F alpha beta = some c) :
    aEq (scalar (chartRows (markSource F c.weights) c.pivot c.tail)).1 (aConst n true) = true :=
  (aEq_true_iff _ _).mpr (planeChart_sound F alpha beta c hc).2.2.1

end PNP.Concrete.ResidualReduction.SourceBalance
