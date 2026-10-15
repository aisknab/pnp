import PNP.Concrete.ResidualReduction.SourceAffinePrelude

namespace PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceLine PNP.Concrete.ResidualReduction.SourcePlane

def findUnit {n : Nat} (f : Point n → Bool) : Option (Point n) :=
  firstTrue f ((List.finRange n).map (unitPoint n))

theorem findUnit_sound {n : Nat} (f : Point n → Bool) (p : Point n)
    (h : findUnit f = some p) : f p = true :=
  (firstTrue_sound f _ p h).2

theorem findUnit_none_zero {n : Nat} (f : Point n → Bool)
    (hz : f (zeroPoint n) = false)
    (ha : ∀ x y, f (pXor x y) = Bool.xor (f x) (f y))
    (hn : findUnit f = none) (x : Point n) : f x = false := by
  apply additive_units_zero f hz ha ?_ x
  intro i
  exact (firstTrue_none_iff f _).mp hn _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

def eraseAlong {n : Nat} (a : Point n → Bool) (p x : Point n) : Point n :=
  if a x then pXor x p else x

theorem eraseAlong_eval {n : Nat} (a f : Point n → Bool) (p x : Point n)
    (hf : ∀ x y, f (pXor x y) = Bool.xor (f x) (f y)) :
    f (eraseAlong a p x) = Bool.xor (f x) (a x && f p) := by
  cases h : a x <;>
    simp only [eraseAlong, h, Bool.false_eq_true, ↓reduceIte,
      Bool.false_and, Bool.true_and, Bool.xor_false, hf]

theorem eraseAlong_zero {n : Nat} (a : Point n → Bool) (p x : Point n)
    (ha : ∀ x y, a (pXor x y) = Bool.xor (a x) (a y)) (hp : a p = true) :
    a (eraseAlong a p x) = false := by
  rw [eraseAlong_eval a a p x ha, hp, Bool.and_true, Bool.xor_self]

theorem one_annihilator_span {n : Nat} (a f : Point n → Bool)
    (az : a (zeroPoint n) = false)
    (aa : ∀ x y, a (pXor x y) = Bool.xor (a x) (a y))
    (fa : ∀ x y, f (pXor x y) = Bool.xor (f x) (f y))
    (h : ∀ x, a x = false → f x = false) :
    ∃ c : Bool, ∀ x, f x = (c && a x) := by
  cases hp : findUnit a with
  | none =>
    refine ⟨false, fun x => ?_⟩
    exact h x (findUnit_none_zero a az aa hp x)
  | some p =>
    have hap := findUnit_sound a p hp
    refine ⟨f p, fun x => ?_⟩
    have hz := h (eraseAlong a p x) (eraseAlong_zero a p x aa hap)
    rw [eraseAlong_eval a f p x fa] at hz
    have he := (xor_false_iff _ _).mp hz
    exact he.trans (Bool.and_comm _ _)

private theorem two_annihilator_bool : ∀ value a b p q k : Bool,
    Bool.xor (Bool.xor value (a && p)) ((Bool.xor b (a && k)) && q) = false →
      value = Bool.xor ((Bool.xor p (k && q)) && a) (q && b) := by decide

/-- Constructive two-dimensional dual-span argument, using at most two unit
    searches rather than a supplied annihilator-span certificate. -/
theorem two_annihilator_span {n : Nat} (a b f : Point n → Bool)
    (az : a (zeroPoint n) = false) (bz : b (zeroPoint n) = false)
    (aa : ∀ x y, a (pXor x y) = Bool.xor (a x) (a y))
    (ba : ∀ x y, b (pXor x y) = Bool.xor (b x) (b y))
    (fa : ∀ x y, f (pXor x y) = Bool.xor (f x) (f y))
    (h : ∀ x, a x = false → b x = false → f x = false) :
    ∃ c d : Bool, ∀ x, f x = Bool.xor (c && a x) (d && b x) := by
  cases hp : findUnit a with
  | none =>
    have ha0 := findUnit_none_zero a az aa hp
    obtain ⟨d, hd⟩ := one_annihilator_span b f bz ba fa (fun x hx => h x (ha0 x) hx)
    exact ⟨false, d, fun x => by simpa only [Bool.false_and, Bool.false_xor] using hd x⟩
  | some p =>
    have hap := findUnit_sound a p hp
    let g : Point n → Bool := fun x => Bool.xor (b x) (a x && b p)
    have gz : g (zeroPoint n) = false := by
      simp only [g, az, bz, Bool.false_and, Bool.false_xor]
    have ga : ∀ x y, g (pXor x y) = Bool.xor (g x) (g y) := by
      intro x y
      simp only [g, aa, ba, xor_and]
      exact xor_interchange _ _ _ _
    cases hq : findUnit g with
    | none =>
      have hg0 := findUnit_none_zero g gz ga hq
      refine ⟨f p, false, fun x => ?_⟩
      have ha0 := eraseAlong_zero a p x aa hap
      have hb0 : b (eraseAlong a p x) = false := by
        have hh := hg0 (eraseAlong a p x)
        simpa only [g, ha0, Bool.false_and, Bool.xor_false] using hh
      have hf0 := h (eraseAlong a p x) ha0 hb0
      rw [eraseAlong_eval a f p x fa] at hf0
      simpa only [Bool.false_and, Bool.xor_false, Bool.and_comm] using
        (xor_false_iff _ _).mp hf0
    | some q =>
      let v := eraseAlong a p q
      have hav : a v = false := eraseAlong_zero a p q aa hap
      have hbv : b v = true := by
        rw [show b v = g q from eraseAlong_eval a b p q ba]
        exact findUnit_sound g q hq
      refine ⟨Bool.xor (f p) (b p && f v), f v, fun x => ?_⟩
      let z := eraseAlong a p x
      have haz : a z = false := eraseAlong_zero a p x aa hap
      have hat : a (eraseAlong b v z) = false := by
        rw [eraseAlong_eval b a v z aa, haz, hav, Bool.and_false, Bool.false_xor]
      have hbt := eraseAlong_zero b v z ba hbv
      have hft := h (eraseAlong b v z) hat hbt
      rw [eraseAlong_eval b f v z fa] at hft
      change Bool.xor (f (eraseAlong a p x)) (b (eraseAlong a p x) && f v) = false at hft
      rw [eraseAlong_eval a f p x fa, eraseAlong_eval a b p x ba] at hft
      exact two_annihilator_bool _ _ _ _ _ _ hft

end PNP.Concrete.ResidualReduction.SourceClosure
