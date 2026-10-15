import PNP.Concrete.ResidualReduction.SourceSelectedScalar
import PNP.Concrete.ResidualReduction.SourceDirectionChart
import PNP.Concrete.ResidualReduction.CheckedContraction

namespace PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine PNP.Concrete.ResidualReduction.SourcePlane

def Balanced {n : Nat} (F : Family n) (w : Point F.length) (v : Point n) : Prop :=
  ∀ x, Bool.xor (weightedValue F w (pXor x v)) (weightedValue F w x) = true

theorem balanced_direction_nonzero {n : Nat} (F : Family n) (w : Point F.length)
    (v : Point n) (h : Balanced F w v) : v ≠ zeroPoint n := by
  intro hv
  have ht := h (zeroPoint n)
  rw [hv, point_xor_zero, Bool.xor_self] at ht
  cases ht

theorem direction_normal_zero {n : Nat} (F : Family n) (U : System n)
    (v : Point n) (h : DirectionSpec F U v) (alpha : Affine n) (ha : alpha ∈ U) :
    linearEval alpha v = false :=
  (satisfies_iff (homogeneous U) v).mp h.1 (homogeneousRow alpha)
    (List.mem_map.mpr ⟨alpha, ha, rfl⟩)

theorem line_good_balanced {n : Nat} (F : Family n) (alpha : Affine n)
    (w : LineWitness n F.length) (h : LineGood F alpha w) :
    Balanced F w.weights w.direction := by
  have hz := direction_normal_zero F [alpha] w.direction h.1 alpha List.mem_cons_self
  intro x
  rw [weightedValue_derivative, h.2.2.2, h.2.1 x w.direction]
  simp only [wedge, hz, h.2.2.1, Bool.and_false, Bool.xor_false]

theorem plane_good_balanced {n : Nat} (F : Family n) (alpha beta : Affine n)
    (w : Point F.length × Point n) (h : PlaneGood F alpha beta w) :
    Balanced F w.1 w.2 := by
  have ha := direction_normal_zero F [alpha, beta] w.2 h.1 alpha List.mem_cons_self
  have hb := direction_normal_zero F [alpha, beta] w.2 h.1 beta
    (List.mem_cons_of_mem alpha List.mem_cons_self)
  intro x
  rw [weightedValue_derivative, h.2.2, h.2.1 x w.2]
  simp only [fixedWedge, ha, hb, Bool.and_false, Bool.xor_false]

theorem sourceLineQuery_balanced {n : Nat} (F : Family n) (alpha : Affine n)
    (w : LineWitness n F.length) (h : sourceLineQuery F alpha = some w) :
    Balanced F w.weights w.direction :=
  line_good_balanced F alpha w (sourceLineQuery_sound F alpha w h)

theorem sourcePlaneQuery_balanced {n : Nat} (F : Family n) (alpha beta : Affine n)
    (w : Point F.length × Point n) (h : sourcePlaneQuery F alpha beta = some w) :
    Balanced F w.1 w.2 :=
  plane_good_balanced F alpha beta w (sourcePlaneQuery_sound F alpha beta w h)

/-- Translate a semantic unit derivative into the exact computed coefficient equality. -/
theorem charted_source_head {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (v : Point (n + 1)) (c : Fin (n + 1) × Point n)
    (hc : chooseChart v = some c) (hb : Balanced F w v) :
    (scalar (chartRows (markSource F w) c.1 c.2)).1 = aConst n true := by
  apply affine_eval_ext
  intro z
  rw [aConst_eval, ← qHead_derivative]
  rw [scalar_chart_eval, scalar_chart_eval, markSource_scalar_eval, markSource_scalar_eval]
  rw [unchart_flip, chooseChart_sound v c hc]
  exact hb (unchart c.1 c.2 (false, z))

theorem charted_source_head_check {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (v : Point (n + 1)) (c : Fin (n + 1) × Point n)
    (hc : chooseChart v = some c) (hb : Balanced F w v) :
    aEq (scalar (chartRows (markSource F w) c.1 c.2)).1 (aConst n true) = true :=
  (aEq_true_iff _ _).mpr (charted_source_head F w v c hc hb)

theorem charted_source_model_reconstruction {n : Nat} (F : Family (n + 1))
    (w : Point F.length) (v : Point (n + 1)) (c : Fin (n + 1) × Point n)
    (hc : chooseChart v = some c) (hb : Balanced F w v)
    (x : Point (n + 1)) (hx : models F x = true) :
    decode (markSource F w) c.1 c.2 (encode c.1 c.2 x) = x :=
  decode_encode_of_balance (markSource F w) c.1 c.2 (charted_source_head F w v c hc hb)
    x (by rw [markSource_models]; exact hx)

end PNP.Concrete.ResidualReduction.SourceBalance
