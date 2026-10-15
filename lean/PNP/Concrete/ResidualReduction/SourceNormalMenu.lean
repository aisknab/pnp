import PNP.Concrete.ResidualReduction.SourceConstructedStep

namespace PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections PNP.Concrete.ResidualReduction.SourceClosure

/-- Binary coefficient order; the affine constant is deliberately excluded. -/
def normalCode : {n : Nat} → Affine n → Nat
  | 0, _ => 0
  | _+1, (b,t) => (if b then 1 else 0) + 2 * normalCode t

/-- Zero, affine and repeated-normal products contribute no nonlinear plane.
    This agrees with taking triples after the reference row normalization. -/
def rowNormals {n : Nat} (r : Row n) : List (Affine n) :=
  let a := homogeneousRow r.left
  let b := homogeneousRow r.right
  if aEq a (aConst n false) then []
  else if aEq b (aConst n false) then []
  else if aEq a b then []
  else [a,b,aAdd a b]

def insertNormal {n : Nat} (a : Affine n) : List (Affine n) → List (Affine n)
  | [] => [a]
  | b::bs =>
    if aEq a b then b::bs
    else if normalCode a ≤ normalCode b then a::b::bs
    else b::insertNormal a bs

def sortedNormals {n : Nat} : List (Affine n) → List (Affine n)
  | [] => []
  | a::as => insertNormal a (sortedNormals as)

def sourceMenu {n : Nat} (F : Family n) : List (Affine n) :=
  sortedNormals (F.flatMap rowNormals)

def planeMenu {n : Nat} (us : List (Affine n)) : List (Affine n × Affine n) :=
  us.flatMap fun a =>
    ((us.filter fun b => decide (normalCode b < normalCode a)).map fun b => (a,b))

theorem mem_insertNormal {n : Nat} (a f : Affine n) (us : List (Affine n)) :
    f ∈ insertNormal a us ↔ f = a ∨ f ∈ us := by
  induction us with
  | nil => simp only [insertNormal,List.mem_cons,List.not_mem_nil,or_false]
  | cons b bs ih =>
    by_cases he : aEq a b = true
    · have hab := (aEq_true_iff a b).mp he
      subst a
      simp only [insertNormal,he,↓reduceIte,List.mem_cons,or_self_left]
    · by_cases hc : normalCode a ≤ normalCode b
      · simp only [insertNormal,he,hc,reduceCtorEq,↓reduceIte,List.mem_cons]
      · simp only [insertNormal,he,hc,reduceCtorEq,↓reduceIte,List.mem_cons,ih]
        constructor
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)

theorem mem_sortedNormals {n : Nat} (f : Affine n) (us : List (Affine n)) :
    f ∈ sortedNormals us ↔ f ∈ us := by
  induction us with
  | nil => rfl
  | cons a as ih =>
    simp only [sortedNormals,mem_insertNormal,List.mem_cons,ih]

theorem sourceMenu_mem {n : Nat} (F : Family n) (f : Affine n) :
    f ∈ sourceMenu F ↔ ∃ r ∈ F, f ∈ rowNormals r := by
  simp only [sourceMenu,mem_sortedNormals,List.mem_flatMap]

theorem insertNormal_length_le {n : Nat} (a : Affine n) (us : List (Affine n)) :
    (insertNormal a us).length ≤ us.length + 1 := by
  induction us with
  | nil => simp only [insertNormal,List.length_cons,List.length_nil,Nat.zero_add,Nat.le_refl]
  | cons b bs ih =>
    simp only [insertNormal]
    split
    · simp only [List.length_cons]; omega
    · split
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega

theorem sortedNormals_length_le {n : Nat} (us : List (Affine n)) :
    (sortedNormals us).length ≤ us.length := by
  induction us with
  | nil => exact Nat.le_refl 0
  | cons a as ih =>
    have h := insertNormal_length_le a (sortedNormals as)
    change (insertNormal a (sortedNormals as)).length ≤ as.length + 1
    omega

theorem rowNormals_length_le {n : Nat} (r : Row n) : (rowNormals r).length ≤ 3 := by
  simp only [rowNormals]
  split
  · simp only [List.length_nil]; omega
  · split
    · simp only [List.length_nil]; omega
    · split <;> simp only [List.length_nil,List.length_cons] <;> omega

theorem sourceMenu_length_le {n : Nat} (F : Family n) :
    (sourceMenu F).length ≤ 3 * F.length := by
  have hr : (F.flatMap rowNormals).length ≤ 3 * F.length := by
    induction F with
    | nil => exact Nat.le_refl 0
    | cons r F ih =>
      have h := rowNormals_length_le r
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega
  exact Nat.le_trans (sortedNormals_length_le _) hr

theorem planeMenu_mem {n : Nat} (us : List (Affine n)) (p : Affine n × Affine n) :
    p ∈ planeMenu us ↔
      p.1 ∈ us ∧ p.2 ∈ us ∧ normalCode p.2 < normalCode p.1 := by
  constructor
  · intro h
    obtain ⟨a,ha,hs⟩ := List.mem_flatMap.mp h
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hs
    have hb' := List.mem_filter.mp hb
    subst p
    exact ⟨ha,hb'.1,of_decide_eq_true hb'.2⟩
  · rintro ⟨ha,hb,hc⟩
    apply List.mem_flatMap.mpr
    exact ⟨p.1,ha,List.mem_map.mpr ⟨p.2,List.mem_filter.mpr ⟨hb,decide_eq_true hc⟩,rfl⟩⟩

theorem planeMenu_length_le {n : Nat} (us : List (Affine n)) :
    (planeMenu us).length ≤ us.length * us.length := by
  have h : ∀ xs : List (Affine n),
      (xs.flatMap fun a =>
        ((us.filter fun b => decide (normalCode b < normalCode a)).map fun b => (a,b))).length
        ≤ xs.length * us.length := by
    intro xs
    induction xs with
    | nil => simp only [List.flatMap_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
    | cons a xs ih =>
      have hf := List.length_filter_le (fun b : Affine n => decide (normalCode b < normalCode a)) us
      simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_cons,Nat.succ_mul]
      omega
  exact h us

end PNP.Concrete.ResidualReduction.SourceChain
