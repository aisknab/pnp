import PNP.Concrete.ResidualReduction.SourcePlaneClosure

namespace PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine PNP.Concrete.ResidualReduction.SourcePlane PNP.Concrete.ResidualReduction.SourceBalance

def computedTail {n : Nat} (F : Family (n+1)) (w : Point F.length)
    (c : Fin (n+1) × Point n) (normals : Option (Affine (n+1) × Affine (n+1))) :
    TailForm n :=
  let q := (scalar (chartRows (markSource F w) c.1 c.2)).2
  match normals with
  | none => .affine (affinePart q)
  | some (a,b) =>
    let alpha := tailNormal c.1 a
    let beta := tailNormal c.1 b
    .plane alpha beta (planeRemainder q alpha beta)

theorem contract_total_of_checks {n : Nat} (F : Family (n+1))
    (c : Fin (n+1) × Point n) (t : TailForm n)
    (hb : (scalar (chartRows F c.1 c.2)).1 = aConst n true)
    (ht : (scalar (chartRows F c.1 c.2)).2 = t.polynomial)
    (hr : ∃ out, t.reduce (chartRows F c.1 c.2) = some out) :
    ∃ out, contract F c.1 c.2 t = some out := by
  obtain ⟨out,ho⟩ := hr
  refine ⟨out, ?_⟩
  simp only [contract, (aEq_true_iff _ _).mpr hb, (qEq_true_iff _ _).mpr ht, ↓reduceIte]
  exact ho

theorem affineGood_balanced {n : Nat} (F : Family n) (w : Point F.length × Point n)
    (h : AffineGood F w) : Balanced F w.1 w.2 := by
  intro x
  rw [weightedValue_derivative, h.1 x w.2, h.2, Bool.xor_false]

theorem computed_affine_contract_total {n : Nat} (F : Family (n+1))
    (w : Point F.length × Point (n+1)) (h : AffineGood F w)
    (c : Fin (n+1) × Point n) (hc : chooseChart w.2 = some c) :
    ∃ out, contract (markSource F w.1) c.1 c.2 (computedTail F w.1 c none) = some out := by
  apply contract_total_of_checks
  · exact charted_source_head F w.1 w.2 c hc (affineGood_balanced F w h)
  · apply zero_polar_affine_coefficients
    intro x y
    rw [source_tail_polar, h.1]
  · exact ⟨_,rfl⟩

theorem computed_plane_contract_total {n : Nat} (F : Family (n+1))
    (hn : sourceAffineQuery F = none) (w : Point F.length) (v : Point (n+1))
    (c : Fin (n+1) × Point n) (hc : chooseChart v = some c)
    (a b : Affine (n+1)) (hb : Balanced F w v)
    (hp : ∀ x y, weightedPolar F w x y = fixedWedge a b x y)
    (hd : ∀ r ∈ F, ∀ x,
      linearEval a x = false → linearEval b x = false → polar r v x = false) :
    ∃ out, contract (markSource F w) c.1 c.2 (computedTail F w c (some (a,b))) = some out := by
  apply contract_total_of_checks
  · exact charted_source_head F w v c hc hb
  · exact source_tail_plane F w a b c.1 c.2 hp
  · exact source_chart_rows_total F hn w v c hc a b _ hd

def betaNormal {n : Nat} (beta : Point n) : Affine n :=
  linearForm (fun x => pointDot beta x)

theorem betaNormal_linearEval {n : Nat} (beta x : Point n) :
    linearEval (betaNormal beta) x = pointDot beta x := by
  rw [linearEval, homogeneousRow_eval, betaNormal, linearForm_constant, Bool.xor_false,
    linearForm_eval _ (pointDot_zero_right beta) (pointDot_additive_right beta)]

theorem computed_line_contract_total {n : Nat} (F : Family (n+1))
    (hn : sourceAffineQuery F = none) (alpha : Affine (n+1))
    (w : LineWitness (n+1) F.length) (h : LineGood F alpha w)
    (c : Fin (n+1) × Point n) (hc : chooseChart w.direction = some c) :
    ∃ out, contract (markSource F w.weights) c.1 c.2
      (computedTail F w.weights c (some (alpha,betaNormal w.beta))) = some out := by
  apply computed_plane_contract_total F hn w.weights w.direction c hc alpha
    (betaNormal w.beta) (line_good_balanced F alpha w h)
  · intro x y
    simpa only [wedge, fixedWedge, betaNormal_linearEval] using h.2.1 x y
  · intro r hr x ha _
    apply h.1.2 r hr x
    change ((!linearEval alpha x) && true) = true
    rw [ha]
    rfl

theorem computed_ranktwo_contract_total {n : Nat} (F : Family (n+1))
    (hn : sourceAffineQuery F = none) (alpha beta : Affine (n+1))
    (w : Point F.length × Point (n+1)) (h : PlaneGood F alpha beta w)
    (c : Fin (n+1) × Point n) (hc : chooseChart w.2 = some c) :
    ∃ out, contract (markSource F w.1) c.1 c.2
      (computedTail F w.1 c (some (alpha,beta))) = some out := by
  apply computed_plane_contract_total F hn w.1 w.2 c hc alpha beta
    (plane_good_balanced F alpha beta w h) h.2.1
  intro r hr x ha hb
  apply h.1.2 r hr x
  change ((!linearEval alpha x) && ((!linearEval beta x) && true)) = true
  rw [ha,hb]
  rfl

/-- On factored input, an active common-radical source row would already have
    been found by the complete affine prelude. -/
theorem failed_affine_common_radical_inactive {n : Nat} (F : Family n)
    (hn : sourceAffineQuery F = none) (r : Row n) (hr : r ∈ F) (v : Point n)
    (hd : ∀ x, polar r v x = false) : activity r v = false := by
  cases ha : activity r v with
  | false => rfl
  | true =>
    have hderiv : ∀ x, Bool.xor (r.eval (pXor x v)) (r.eval x) = true := by
      intro x
      rw [row_derivative, polar_comm, hd, ha, Bool.xor_false]
    have hp := product_unit_derivative_affine r v hderiv
    have hf := sourceAffineQuery_none_row_activity F hn r hr hp v
    rw [ha] at hf
    cases hf

end PNP.Concrete.ResidualReduction.SourceClosure
