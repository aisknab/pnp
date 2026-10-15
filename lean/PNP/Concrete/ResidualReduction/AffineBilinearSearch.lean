import PNP.Concrete.ResidualReduction.SourceLinearCoordinates

namespace PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceLine

def firstTrue {X : Type} (f : X → Bool) : List X → Option X
  | [] => none
  | x :: xs => match f x with
    | true => some x
    | false => firstTrue f xs

theorem firstTrue_sound {X : Type} (f : X → Bool) (xs : List X) (y : X)
    (h : firstTrue f xs = some y) : y ∈ xs ∧ f y = true := by
  induction xs with
  | nil => simp only [firstTrue, reduceCtorEq] at h
  | cons x xs ih =>
    cases hx : f x with
    | false =>
      have ht : firstTrue f xs = some y := by simpa only [firstTrue, hx] using h
      obtain ⟨hm, hf⟩ := ih ht
      exact ⟨List.mem_cons_of_mem x hm, hf⟩
    | true =>
      have he : x = y := by simpa only [firstTrue, hx, Option.some.injEq] using h
      subst y
      exact ⟨List.mem_cons_self, hx⟩

theorem firstTrue_none_iff {X : Type} (f : X → Bool) (xs : List X) :
    firstTrue f xs = none ↔ ∀ x ∈ xs, f x = false := by
  induction xs with
  | nil => simp only [firstTrue, List.not_mem_nil, false_implies, implies_true]
  | cons x xs ih =>
    cases hx : f x with
    | false =>
      constructor
      · intro h y hy
        have ht : firstTrue f xs = none := by simpa only [firstTrue, hx] using h
        rcases List.mem_cons.mp hy with he | hm
        · subst y; exact hx
        · exact ih.mp ht y hm
      · intro h
        have ht := ih.mpr (fun y hy => h y (List.mem_cons_of_mem x hy))
        simpa only [firstTrue, hx] using ht
    | true =>
      constructor
      · intro h
        simp only [firstTrue, hx, reduceCtorEq] at h
      · intro h
        have hf := h x List.mem_cons_self
        rw [hx] at hf
        cases hf

def affineParameters (n : Nat) : List (Point n) :=
  zeroPoint n :: (List.finRange n).map (unitPoint n)

theorem affineParameters_zero (n : Nat) : zeroPoint n ∈ affineParameters n :=
  List.mem_cons_self

theorem affineParameters_unit {n : Nat} (i : Fin n) :
    unitPoint n i ∈ affineParameters n :=
  List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

def affineTestPairs {m : Nat} (s : Space m) (n : Nat) : List (Point m × Point n) :=
  (affineParameters s.parameters).flatMap fun z =>
    (List.finRange n).map fun j => (mapEval s.forms z, unitPoint n j)

theorem affineTestPairs_mem {m n : Nat} (s : Space m) (p : Point m × Point n) :
    p ∈ affineTestPairs s n ↔
      ∃ z ∈ affineParameters s.parameters, ∃ j : Fin n,
        (mapEval s.forms z, unitPoint n j) = p := by
  constructor
  · intro h
    obtain ⟨z, hz, hp⟩ := List.mem_flatMap.mp h
    obtain ⟨j, _, he⟩ := List.mem_map.mp hp
    exact ⟨z, hz, j, he⟩
  · rintro ⟨z, hz, j, he⟩
    exact List.mem_flatMap.mpr ⟨z, hz, List.mem_map.mpr ⟨j, List.mem_finRange j, he⟩⟩

theorem affine_units_zero {n : Nat} (f : Point n → Bool)
    (hz : f (zeroPoint n) = false)
    (ha : ∀ x y, f (pXor x y) =
      Bool.xor (Bool.xor (f x) (f y)) (f (zeroPoint n)))
    (hu : ∀ i, f (unitPoint n i) = false) (x : Point n) : f x = false :=
  additive_units_zero f hz
    (fun a b => by simpa only [hz, Bool.xor_false] using ha a b) hu x

/-- The base point and shifted generators suffice for every affine parameter,
    and unit directions suffice for every linear parameter. -/
theorem affineTestPairs_zero {m n : Nat} (s : Space m) (M : Matrix m n)
    (h : ∀ p ∈ affineTestPairs s n, bilinearEval M p.1 p.2 = false)
    (z : Point s.parameters) (y : Point n) :
    bilinearEval M (mapEval s.forms z) y = false := by
  apply additive_units_zero (fun v => bilinearEval M (mapEval s.forms z) v)
    (bilinear_zero_right M _) (bilinear_additive_right M _) ?_ y
  intro j
  apply affine_units_zero (fun u => bilinearEval M (mapEval s.forms u) (unitPoint n j))
  · exact h _ ((affineTestPairs_mem s _).mpr
      ⟨zeroPoint s.parameters, affineParameters_zero _, j, rfl⟩)
  · intro a b
    simp only [mapEval_affine_xor, bilinear_additive_left]
  · intro i
    exact h _ ((affineTestPairs_mem s _).mpr
      ⟨unitPoint s.parameters i, affineParameters_unit i, j, rfl⟩)

def affineBilinearQuery {m n : Nat} (s : Space m) (M : Matrix m n) :
    Option (Point m × Point n) :=
  firstTrue (fun p => bilinearEval M p.1 p.2) (affineTestPairs s n)

theorem affineBilinearQuery_sound {m n : Nat} (s : Space m) (M : Matrix m n)
    (p : Point m × Point n) (h : affineBilinearQuery s M = some p) :
    (∃ z, mapEval s.forms z = p.1) ∧ bilinearEval M p.1 p.2 = true := by
  obtain ⟨hm, hv⟩ := firstTrue_sound _ _ _ h
  obtain ⟨z, _, j, he⟩ := (affineTestPairs_mem s p).mp hm
  exact ⟨⟨z, congrArg Prod.fst he⟩, hv⟩

theorem affineBilinearQuery_complete {m n : Nat} (s : Space m) (M : Matrix m n)
    (h : ∃ z y, bilinearEval M (mapEval s.forms z) y = true) :
    ∃ p, affineBilinearQuery s M = some p := by
  cases hq : affineBilinearQuery s M with
  | none =>
    have ht := (firstTrue_none_iff (fun (p : Point m × Point n) => bilinearEval M p.1 p.2)
      (affineTestPairs s n)).mp hq
    obtain ⟨z, y, hy⟩ := h
    have hz := affineTestPairs_zero s M ht z y
    rw [hy] at hz
    cases hz
  | some p => exact ⟨p, rfl⟩

theorem affineBilinearQuery_none_iff {m n : Nat} (s : Space m) (M : Matrix m n) :
    affineBilinearQuery s M = none ↔
      ¬ ∃ z y, bilinearEval M (mapEval s.forms z) y = true := by
  constructor
  · intro hn hg
    obtain ⟨p, hp⟩ := affineBilinearQuery_complete s M hg
    simp only [hn, reduceCtorEq] at hp
  · intro h
    cases hq : affineBilinearQuery s M with
    | none => rfl
    | some p =>
      obtain ⟨⟨z, hz⟩, hv⟩ := affineBilinearQuery_sound s M p hq
      exact False.elim (h ⟨z, p.2, by rw [hz]; exact hv⟩)

/-- Candidate count only; not a complete encoded runtime theorem. -/
theorem affineTestPairs_length {m : Nat} (s : Space m) (n : Nat) :
    (affineTestPairs s n).length = (s.parameters + 1) * n := by
  have aux : ∀ zs : List (Point s.parameters),
      (zs.flatMap (fun z => (List.finRange n).map
        (fun j => (mapEval s.forms z, unitPoint n j)))).length = zs.length * n := by
    intro zs
    induction zs with
    | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
    | cons z zs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_finRange, List.length_cons]
      rw [ih, Nat.succ_mul, Nat.add_comm]
  simpa only [affineTestPairs, affineParameters, List.length_cons,
    List.length_map, List.length_finRange] using aux (affineParameters s.parameters)

end PNP.Concrete.ResidualReduction.SourcePlane
