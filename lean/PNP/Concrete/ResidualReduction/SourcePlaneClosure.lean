import PNP.Concrete.ResidualReduction.SourceRowDifference

namespace PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine PNP.Concrete.ResidualReduction.SourcePlane PNP.Concrete.ResidualReduction.SourceBalance

theorem planePartner_exists {n : Nat} (a b f : Affine n)
    (hm : f ∈ (planePairs a b).map Prod.fst) : ∃ t, planePartner a b f = some t := by
  obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
  subst f
  cases hfind : (planePairs a b).find? (fun q : Affine n × Affine n => aEq p.1 q.1) with
  | none =>
    have hf := List.find?_eq_none.mp hfind p hp
    rw [(aEq_true_iff _ _).mpr rfl] at hf
    exact False.elim (hf rfl)
  | some q => exact ⟨q.2, by simp only [planePartner, hfind, Option.map]⟩

theorem affine_span_plane_membership {n : Nat} (a b f : Affine n)
    (hn : f ≠ aConst n true) (e : Bool)
    (h : ∃ l m : Bool, ∀ z, aEval f z =
      Bool.xor (Bool.xor (l && aEval a z) (m && aEval b z)) e) :
    f ∈ (planePairs a b).map Prod.fst := by
  obtain ⟨l,m,h⟩ := h
  cases l <;> cases m <;> cases e
  · have hf : f = aConst n false := by
      apply affine_eval_ext
      intro z
      simpa only [Bool.false_and, Bool.true_and, Bool.false_xor, Bool.xor_false,
        aConst_eval, aAdd_eval] using h z
    rw [hf]
    simp only [planePairs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      true_or, or_false]
  · have hf : f = aConst n true := by
      apply affine_eval_ext
      intro z
      simpa only [Bool.false_and, Bool.false_xor, aConst_eval] using h z
    exact False.elim (hn hf)
  · have hf : f = b := by
      apply affine_eval_ext
      intro z
      simpa only [Bool.false_and, Bool.true_and, Bool.false_xor, Bool.xor_false,
        aConst_eval, aAdd_eval] using h z
    rw [hf]
    simp only [planePairs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      true_or, or_true, or_false]
  · have hf : f = aAdd b (aConst n true) := by
      apply affine_eval_ext
      intro z
      simpa only [Bool.false_and, Bool.true_and, Bool.false_xor, Bool.xor_false,
        aConst_eval, aAdd_eval] using h z
    rw [hf]
    simp only [planePairs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      true_or, or_true, or_false]
  · have hf : f = a := by
      apply affine_eval_ext
      intro z
      simpa only [Bool.false_and, Bool.true_and, Bool.false_xor, Bool.xor_false,
        aConst_eval, aAdd_eval] using h z
    rw [hf]
    simp only [planePairs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      true_or, or_true, or_false]
  · have hf : f = aAdd a (aConst n true) := by
      apply affine_eval_ext
      intro z
      simpa only [Bool.false_and, Bool.true_and, Bool.false_xor, Bool.xor_false,
        aConst_eval, aAdd_eval] using h z
    rw [hf]
    simp only [planePairs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      true_or, or_true, or_false]
  · have hf : f = aAdd a b := by
      apply affine_eval_ext
      intro z
      simpa only [Bool.false_and, Bool.true_and, Bool.false_xor, Bool.xor_false,
        aConst_eval, aAdd_eval] using h z
    rw [hf]
    simp only [planePairs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      true_or, or_true, or_false]
  · have hf : f = aAdd (aAdd a b) (aConst n true) := by
      apply affine_eval_ext
      intro z
      simpa only [Bool.false_and, Bool.true_and, Bool.false_xor, Bool.xor_false,
        aConst_eval, aAdd_eval] using h z
    rw [hf]
    simp only [planePairs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_true, or_false]

theorem planeRow_total_from_difference {n : Nat} (a b u : Affine n) (r : Row (n+1))
    (hm : rowDifference r ∈ (planePairs a b).map Prod.fst) :
    ∃ out, planeRow a b u r = some out := by
  rcases r with ⟨s, ⟨dl,f⟩, ⟨dr,g⟩⟩
  cases dl with
  | false =>
    cases dr with
    | false => exact ⟨⟨s,f,g⟩, rfl⟩
    | true =>
      obtain ⟨t,ht⟩ := planePartner_exists a b f hm
      exact ⟨⟨s,f,aAdd (aAdd g u) t⟩, by simp only [planeRow, assemble, ht, Option.map]⟩
  | true =>
    cases dr with
    | false =>
      obtain ⟨t,ht⟩ := planePartner_exists a b g hm
      exact ⟨⟨s,g,aAdd (aAdd f u) t⟩, by simp only [planeRow, assemble, ht, Option.map]⟩
    | true =>
      obtain ⟨t,ht⟩ := planePartner_exists a b (aAdd (aAdd f g) (aConst n true)) hm
      exact ⟨⟨s,aAdd (aAdd f g) (aConst n true),aAdd (aAdd f u) t⟩,
        by simp only [planeRow, assemble, ht, Option.map]⟩

theorem planeRows_total {n : Nat} (a b u : Affine n) (F : Family (n+1))
    (h : ∀ r ∈ F, ∃ out, planeRow a b u r = some out) :
    ∃ out, PNP.Concrete.ResidualReduction.FactoredContraction.planeRows a b u F = some out := by
  induction F with
  | nil => exact ⟨[],rfl⟩
  | cons r F ih =>
    obtain ⟨head,hh⟩ := h r List.mem_cons_self
    obtain ⟨tail,ht⟩ := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    exact ⟨head::tail, by simp only [PNP.Concrete.ResidualReduction.FactoredContraction.planeRows,
      hh, ht, Option.bind, Option.map]⟩

theorem markSource_all {n : Nat} (F : Family n) (w : Point F.length) (P : Row n → Prop)
    (h : ∀ r ∈ F, ∀ b, P {r with selected := b}) :
    ∀ r ∈ markSource F w, P r := by
  induction F with
  | nil => intro r hr; cases hr
  | cons q F ih =>
    rcases w with ⟨b,w⟩
    intro r hr
    rcases List.mem_cons.mp hr with he | ht
    · subst r; exact h q List.mem_cons_self b
    · exact ih w (fun r hr b => h r (List.mem_cons_of_mem _ hr) b) r ht

theorem source_chart_row_total {n : Nat} (F : Family (n+1))
    (hn : sourceAffineQuery F = none) (r : Row (n+1)) (hr : r ∈ F)
    (v : Point (n+1)) (c : Fin (n+1) × Point n) (hc : chooseChart v = some c)
    (a b : Affine (n+1)) (u : Affine n) (selected : Bool)
    (hd : ∀ x, linearEval a x = false → linearEval b x = false → polar r v x = false) :
    ∃ out, planeRow (tailNormal c.1 a) (tailNormal c.1 b) u
      (({r with selected := selected}.cut c.1).shear c.2) = some out := by
  have hm := affine_span_plane_membership (tailNormal c.1 a) (tailNormal c.1 b)
    (rowDifference ((r.cut c.1).shear c.2))
    (source_chart_difference_ne_one F hn r hr v c hc) (activity r v)
    (chart_difference_span r v a b c hc hd)
  exact planeRow_total_from_difference _ _ _ _ hm

theorem source_chart_rows_total {n : Nat} (F : Family (n+1))
    (hn : sourceAffineQuery F = none) (w : Point F.length) (v : Point (n+1))
    (c : Fin (n+1) × Point n) (hc : chooseChart v = some c)
    (a b : Affine (n+1)) (u : Affine n)
    (hd : ∀ r ∈ F, ∀ x,
      linearEval a x = false → linearEval b x = false → polar r v x = false) :
    ∃ out, PNP.Concrete.ResidualReduction.FactoredContraction.planeRows (tailNormal c.1 a)
      (tailNormal c.1 b) u (chartRows (markSource F w) c.1 c.2) = some out := by
  apply planeRows_total
  intro r hr
  obtain ⟨q,hq,he⟩ := List.mem_map.mp hr
  subst r
  exact markSource_all F w
    (fun q => ∃ out, planeRow (tailNormal c.1 a) (tailNormal c.1 b) u
      ((q.cut c.1).shear c.2) = some out)
    (fun q hq sel => source_chart_row_total F hn q hq v c hc a b u sel (hd q hq)) q hq

end PNP.Concrete.ResidualReduction.SourceClosure
