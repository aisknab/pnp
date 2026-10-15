import PNP.Concrete.ResidualReduction.BooleanCoefficients

namespace PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.FactoredContraction

abbrev System (n : Nat) := List (Affine n)

def satisfies {n : Nat} : System n → Point n → Bool
  | [], _ => true
  | f :: rs, x => (!aEval f x) && satisfies rs x

theorem satisfies_iff {n : Nat} (rs : System n) (x : Point n) :
    satisfies rs x = true ↔ ∀ f ∈ rs, aEval f x = false := by
  induction rs with
  | nil => simp [satisfies]
  | cons f rs ih => simp [satisfies, ih]

theorem affine_eval_cons {n : Nat} (f : Affine (n + 1)) (b : Bool)
    (x : Point n) :
    aEval f (b, x) = Bool.xor (f.1 && b) (aEval f.2 x) := by
  rcases f with ⟨d, f⟩
  rfl

theorem satisfies_map {m n : Nat} (rs : System m)
    (f : Affine m → Affine n) (g : Point n → Point m)
    (h : ∀ r x, aEval (f r) x = aEval r (g x)) (x : Point n) :
    satisfies (rs.map f) x = satisfies rs (g x) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [List.map_cons, satisfies, h, ih]

def choosePivot {n : Nat} : System (n + 1) → Option (Affine n)
  | [] => none
  | f :: rs => if f.1 then some f.2 else choosePivot rs

theorem choosePivot_mem {n : Nat} (rs : System (n + 1)) (p : Affine n)
    (h : choosePivot rs = some p) : (true, p) ∈ rs := by
  induction rs with
  | nil => simp [choosePivot] at h
  | cons f rs ih =>
    rcases f with ⟨b, f⟩
    cases b with
    | false =>
      have ht : choosePivot rs = some p := by simpa [choosePivot] using h
      exact List.mem_cons_of_mem _ (ih ht)
    | true =>
      have he : f = p := by simpa [choosePivot] using h
      cases he
      exact List.mem_cons_self

theorem choosePivot_none {n : Nat} (rs : System (n + 1))
    (h : choosePivot rs = none) : ∀ f ∈ rs, f.1 = false := by
  induction rs with
  | nil => simp
  | cons f rs ih =>
    rcases f with ⟨b, f⟩
    cases b with
    | false =>
      have ht : choosePivot rs = none := by simpa [choosePivot] using h
      intro g hg
      rcases List.mem_cons.mp hg with he | hm
      · cases he; rfl
      · exact ih ht g hm
    | true => simp [choosePivot] at h

def tails {n : Nat} (rs : System (n + 1)) : System n :=
  rs.map fun f => f.2

theorem tails_eval {n : Nat} (rs : System (n + 1))
    (h : ∀ f ∈ rs, f.1 = false) (b : Bool) (x : Point n) :
    satisfies (tails rs) x = satisfies rs (b, x) := by
  induction rs with
  | nil => rfl
  | cons f rs ih =>
    have hf : f.1 = false := h f List.mem_cons_self
    have ht : ∀ g ∈ rs, g.1 = false :=
      fun g hg => h g (List.mem_cons_of_mem _ hg)
    simp only [tails, List.map_cons, satisfies, affine_eval_cons, hf,
      Bool.false_and, Bool.false_xor]
    exact congrArg (fun t => (!aEval f.2 x) && t) (ih ht)

def substitute {n : Nat} (p : Affine n) (f : Affine (n + 1)) : Affine n :=
  aAdd (aScale f.1 p) f.2

theorem substitute_eval {n : Nat} (p : Affine n) (f : Affine (n + 1))
    (x : Point n) :
    aEval (substitute p f) x = aEval f (aEval p x, x) := by
  simp only [substitute, aAdd_eval, aScale_eval, affine_eval_cons]

def substituteRows {n : Nat} (p : Affine n) (rs : System (n + 1)) : System n :=
  rs.map (substitute p)

theorem substituteRows_eval {n : Nat} (p : Affine n)
    (rs : System (n + 1)) (x : Point n) :
    satisfies (substituteRows p rs) x = satisfies rs (aEval p x, x) :=
  satisfies_map rs (substitute p) (fun x => (aEval p x, x))
    (substitute_eval p) x

private theorem xor_zero_iff :
    ∀ a b : Bool, Bool.xor a b = false ↔ a = b := by
  decide

theorem pivot_equivalence {n : Nat} (rs : System (n + 1)) (p : Affine n)
    (hp : choosePivot rs = some p) (b : Bool) (x : Point n) :
    satisfies rs (b, x) = true ↔
      b = aEval p x ∧ satisfies (substituteRows p rs) x = true := by
  constructor
  · intro h
    have hz := (satisfies_iff rs (b, x)).mp h (true, p) (choosePivot_mem rs p hp)
    change Bool.xor b (aEval p x) = false at hz
    have hb := (xor_zero_iff b (aEval p x)).mp hz
    refine ⟨hb, ?_⟩
    rw [substituteRows_eval, ← hb]
    exact h
  · rintro ⟨hb, h⟩
    rw [hb]
    exact (substituteRows_eval p rs x).symm.trans h

end PNP.Concrete.ResidualReduction.BinaryLinear
