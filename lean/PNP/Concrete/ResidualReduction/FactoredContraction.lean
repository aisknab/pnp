import PNP.Concrete.ResidualReduction.BooleanCoefficients

namespace PNP.Concrete.ResidualReduction.FactoredContraction

structure Row (n : Nat) where
  selected : Bool
  left : Affine n
  right : Affine n

abbrev Family (n : Nat) := List (Row n)

def Row.eval {n : Nat} (r : Row n) (x : Point n) : Bool :=
  aEval r.left x && aEval r.right x

def models {n : Nat} : Family n → Point n → Bool
  | [], _ => true
  | r :: rs, x => (!r.eval x) && models rs x

def scalar {n : Nat} : Family n → Quadratic n
  | [] => qOfAffine (aConst n false)
  | r :: rs =>
    if r.selected then qAdd (qProduct r.left r.right) (scalar rs)
    else scalar rs

theorem scalar_zero_of_models {n : Nat} (rs : Family n) (x : Point n)
    (h : models rs x = true) : qEval (scalar rs) x = false := by
  induction rs with
  | nil => simp [scalar, qOfAffine_eval, aConst_eval]
  | cons r rs ih =>
    have hh : r.eval x = false ∧ models rs x = true := by
      simpa [models] using h
    have hz : (aEval r.left x && aEval r.right x) = false := hh.1
    have ht := ih hh.2
    cases hs : r.selected <;>
      simp [scalar, hs, qAdd_eval, qProduct_eval, hz, ht]

theorem models_map {m n : Nat} (rs : Family m)
    (f : Row m → Row n) (g : Point n → Point m)
    (h : ∀ r x, (f r).eval x = r.eval (g x)) (x : Point n) :
    models (rs.map f) x = models rs (g x) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [List.map_cons, models, h, ih]

def Row.cut {n : Nat} (k : Fin (n + 1)) (r : Row (n + 1)) : Row (n + 1) :=
  ⟨r.selected, FactoredContraction.cut n k r.left,
    FactoredContraction.cut n k r.right⟩

def Row.shear {n : Nat} (v : Point n) (r : Row (n + 1)) : Row (n + 1) :=
  ⟨r.selected, aShear v r.left, aShear v r.right⟩

def chart {n : Nat} (k : Fin (n + 1)) (v : Point n)
    (x : Point (n + 1)) : Point (n + 1) :=
  shear v (cut n k x)

def unchart {n : Nat} (k : Fin (n + 1)) (v : Point n)
    (x : Point (n + 1)) : Point (n + 1) :=
  insert n k (shear v x)

theorem chart_unchart {n : Nat} (k : Fin (n + 1)) (v : Point n)
    (x : Point (n + 1)) : chart k v (unchart k v x) = x := by
  simp only [chart, unchart, cut_insert, shear_involution]

theorem unchart_chart {n : Nat} (k : Fin (n + 1)) (v : Point n)
    (x : Point (n + 1)) : unchart k v (chart k v x) = x := by
  simp only [chart, unchart, shear_involution, insert_cut]

theorem Row.cut_eval {n : Nat} (k : Fin (n + 1)) (r : Row (n + 1))
    (x : Point (n + 1)) :
    (r.cut k).eval x = r.eval (insert n k x) := by
  have hl := aEval_cut n k r.left (insert n k x)
  have hr := aEval_cut n k r.right (insert n k x)
  simp only [cut_insert] at hl hr
  change (aEval (n := n + 1) (FactoredContraction.cut n k r.left) x &&
    aEval (n := n + 1) (FactoredContraction.cut n k r.right) x) =
      (aEval r.left (insert n k x) && aEval r.right (insert n k x))
  rw [hl, hr]

theorem Row.shear_eval {n : Nat} (v : Point n) (r : Row (n + 1))
    (x : Point (n + 1)) :
    (r.shear v).eval x = r.eval (FactoredContraction.shear v x) := by
  simp only [Row.shear, Row.eval, aShear_eval]

def chartRows {n : Nat} (rs : Family (n + 1)) (k : Fin (n + 1))
    (v : Point n) : Family (n + 1) :=
  rs.map fun r => (r.cut k).shear v

theorem chartRows_models {n : Nat} (rs : Family (n + 1))
    (k : Fin (n + 1)) (v : Point n) (x : Point (n + 1)) :
    models (chartRows rs k v) x = models rs (unchart k v x) := by
  apply models_map
  intro r x
  simp only [Row.shear_eval, Row.cut_eval, unchart]

def affineRow {n : Nat} (u : Affine n) (r : Row (n + 1)) : Row n :=
  ⟨r.selected, aAdd (aScale r.left.1 u) r.left.2,
    aAdd (aScale r.right.1 u) r.right.2⟩

theorem affineRow_eval {n : Nat} (u : Affine n) (r : Row (n + 1))
    (z : Point n) :
    (affineRow u r).eval z = r.eval (aEval u z, z) := by
  rcases r with ⟨s, ⟨dl, f⟩, ⟨dr, g⟩⟩
  simp only [affineRow, Row.eval, aAdd_eval, aScale_eval, aEval]

def planeValue {n : Nat} (a b u : Affine n) (z : Point n) : Bool :=
  Bool.xor (aEval a z && aEval b z) (aEval u z)

def planePairs {n : Nat} (a b : Affine n) : List (Affine n × Affine n) :=
  [(aConst n false, aConst n false),
   (a, b), (aAdd a (aConst n true), aConst n false),
   (b, a), (aAdd b (aConst n true), aConst n false),
   (aAdd a b, aConst n false),
   (aAdd (aAdd a b) (aConst n true), a)]

theorem planePairs_sound {n : Nat} (a b : Affine n)
    (p : Affine n × Affine n) (hp : p ∈ planePairs a b) (z : Point n) :
    (aEval p.1 z && (aEval a z && aEval b z)) =
      (aEval p.1 z && aEval p.2 z) := by
  simp only [planePairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [aConst_eval, aAdd_eval] <;>
    cases ha : aEval a z <;> cases hb : aEval b z <;> decide

def planePartner {n : Nat} (a b f : Affine n) : Option (Affine n) :=
  ((planePairs a b).find? (fun p : Affine n × Affine n => aEq f p.1)).map
    (fun p => p.2)

theorem planePartner_sound {n : Nat} (a b f t : Affine n)
    (h : planePartner a b f = some t) (z : Point n) :
    (aEval f z && (aEval a z && aEval b z)) = (aEval f z && aEval t z) := by
  unfold planePartner at h
  cases hp : (planePairs a b).find?
      (fun p : Affine n × Affine n => aEq f p.1) with
  | none => simp [hp] at h
  | some p =>
    have ht : p.2 = t := by simpa [hp] using h
    have hpval := List.find?_some hp
    have hf : f = p.1 := (aEq_true_iff f p.1).mp hpval
    rw [hf, ← ht]
    exact planePairs_sound a b p (List.mem_of_find?_eq_some hp) z

def assemble {n : Nat} (s : Bool) (a b u f g : Affine n) : Option (Row n) :=
  (planePartner a b f).map fun t =>
    ⟨s, f, aAdd (aAdd g u) t⟩

private theorem partnerReplacement :
    ∀ f g a b u t : Bool,
      (f && (a && b)) = (f && t) →
      (f && Bool.xor (Bool.xor g u) t) =
        (f && Bool.xor g (Bool.xor (a && b) u)) := by
  decide

theorem assemble_eval {n : Nat} (s : Bool) (a b u f g : Affine n)
    (r : Row n) (h : assemble s a b u f g = some r) (z : Point n) :
    r.eval z = (aEval f z && Bool.xor (aEval g z) (planeValue a b u z)) := by
  cases hp : planePartner a b f with
  | none => simp [assemble, hp] at h
  | some t =>
    have hr : (⟨s, f, aAdd (aAdd g u) t⟩ : Row n) = r := by
      simpa [assemble, hp] using h
    cases hr
    simp only [Row.eval, aAdd_eval, planeValue]
    exact partnerReplacement (aEval f z) (aEval g z) (aEval a z) (aEval b z)
      (aEval u z) (aEval t z) (planePartner_sound a b f t hp z)

def planeRow {n : Nat} (a b u : Affine n) (r : Row (n + 1)) : Option (Row n) :=
  match r.left.1, r.right.1 with
  | false, false => some ⟨r.selected, r.left.2, r.right.2⟩
  | false, true => assemble r.selected a b u r.left.2 r.right.2
  | true, false => assemble r.selected a b u r.right.2 r.left.2
  | true, true =>
    assemble r.selected a b u
      (aAdd (aAdd r.left.2 r.right.2) (aConst n true)) r.left.2

private theorem inactiveLeft :
    ∀ f g h : Bool,
      (f && Bool.xor g h) =
        ((Bool.xor (false && h) f) && (Bool.xor (true && h) g)) := by
  decide

private theorem inactiveRight :
    ∀ f g h : Bool,
      (g && Bool.xor f h) =
        ((Bool.xor (true && h) f) && (Bool.xor (false && h) g)) := by
  decide

private theorem bothActive :
    ∀ f g h : Bool,
      ((Bool.xor (Bool.xor f g) true) && Bool.xor f h) =
        ((Bool.xor (true && h) f) && (Bool.xor (true && h) g)) := by
  decide

theorem planeRow_eval {n : Nat} (a b u : Affine n)
    (r : Row (n + 1)) (out : Row n)
    (h : planeRow a b u r = some out) (z : Point n) :
    out.eval z = r.eval (planeValue a b u z, z) := by
  rcases r with ⟨s, l, r⟩
  rcases l with ⟨dl, f⟩
  rcases r with ⟨dr, g⟩
  cases dl with
  | false =>
    cases dr with
    | false =>
      have hh : (⟨s, f, g⟩ : Row n) = out := by simpa [planeRow] using h
      cases hh
      simp [Row.eval, aEval]
    | true =>
      have hh : assemble s a b u f g = some out := by simpa [planeRow] using h
      rw [assemble_eval s a b u f g out hh z]
      simpa only [Row.eval, aEval] using
        inactiveLeft (aEval f z) (aEval g z) (planeValue a b u z)
  | true =>
    cases dr with
    | false =>
      have hh : assemble s a b u g f = some out := by simpa [planeRow] using h
      rw [assemble_eval s a b u g f out hh z]
      simpa only [Row.eval, aEval] using
        inactiveRight (aEval f z) (aEval g z) (planeValue a b u z)
    | true =>
      have hh : assemble s a b u (aAdd (aAdd f g) (aConst n true)) f =
          some out := by simpa [planeRow] using h
      rw [assemble_eval s a b u (aAdd (aAdd f g) (aConst n true)) f out hh z]
      simpa only [Row.eval, aEval, aAdd_eval, aConst_eval] using
        bothActive (aEval f z) (aEval g z) (planeValue a b u z)

def planeRows {n : Nat} (a b u : Affine n) :
    Family (n + 1) → Option (Family n)
  | [] => some []
  | r :: rs => (planeRow a b u r).bind fun head =>
      (planeRows a b u rs).map fun tail => head :: tail

theorem planeRows_sound {n : Nat} (a b u : Affine n)
    (rs : Family (n + 1)) (out : Family n)
    (h : planeRows a b u rs = some out) :
    out.length = rs.length ∧
      ∀ z, models out z = models rs (planeValue a b u z, z) := by
  induction rs generalizing out with
  | nil =>
    have hh : ([] : Family n) = out := by simpa [planeRows] using h
    cases hh
    exact ⟨rfl, fun _ => rfl⟩
  | cons r rs ih =>
    cases hr : planeRow a b u r with
    | none => simp [planeRows, hr] at h
    | some head =>
      cases ht : planeRows a b u rs with
      | none => simp [planeRows, hr, ht] at h
      | some tail =>
        have hh : head :: tail = out := by simpa [planeRows, hr, ht] using h
        cases hh
        obtain ⟨hlen, hmodels⟩ := ih tail ht
        refine ⟨by simp only [List.length_cons, hlen], ?_⟩
        intro z
        simp only [models, planeRow_eval a b u r head hr z, hmodels]

end PNP.Concrete.ResidualReduction.FactoredContraction
