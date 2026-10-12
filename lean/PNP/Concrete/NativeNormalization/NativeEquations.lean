import PNP.Concrete.NativeNormalization.NativeSource

namespace PNP.Concrete.NativeNormalization.NativeEquations

open NativeBasis NativeSource

local infixl:65 " ⊕ᵦ " => Bool.xor

abbrev Row (c : Nat) := Fin c × Bool
abbrev RowValues (c : Nat) := Row c → Bool

/-- The other factor in the same native pair; no factor is discarded. -/
def companion (S : Selection n c) (w : Values n c) (r : Row c) : Bool :=
  if r.2 then
    match S.mode r.1 with
    | some .last => w.t r.1
    | _ => falseForm S r.1 .last w
  else
    match S.mode r.1 with
    | some .middle | some .last => falseForm S r.1 .first w
    | _ => falseForm S r.1 .middle w ⊕ᵦ w.t r.1

def factor (S : Selection n c) (w : Values n c) (r : Row c) : Bool :=
  if r.2 then w.t r.1 && falseForm S r.1 .last w
  else falseForm S r.1 .first w && (falseForm S r.1 .middle w ⊕ᵦ w.t r.1)

theorem selected_companion (S : Selection n c) (w : Values n c) (r : Row c) :
    (selected S w r && companion S w r) = factor S w r := by
  rcases r with ⟨i, b⟩
  cases b <;> cases hm : S.mode i with
  | none => simp [selected, companion, factor, hm]
  | some s => cases s <;> simp [selected, companion, factor, hm, Bool.and_comm]

def NativeSatisfied (S : Selection n c) (w : Values n c) : Prop :=
  w.e = true ∧ ∀ r, factor S w r = false

theorem falseForm_zero (S : Selection n c) (w : Values n c)
    (he : w.e = true) (i : Fin c) (s : Slot) :
    falseForm S i s w = false ↔ w.x (S.literal i s).index = (S.literal i s).positive := by
  cases hx : w.x (S.literal i s).index <;>
    cases hp : (S.literal i s).positive <;> simp [falseForm, he, hx, hp]

private theorem factor_sound (a b c t : Bool)
    (h₁ : (a && (b ⊕ᵦ t)) = false) (h₂ : (t && c) = false) :
    a = false ∨ b = false ∨ c = false := by
  cases a <;> cases b <;> cases c <;> cases t <;> simp_all

private theorem factor_complete (a b c : Bool)
    (h : a = false ∨ b = false ∨ c = false) :
    ((a && (b ⊕ᵦ (a && b))) = false) ∧ (((a && b) && c) = false) := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem native_clause (S : Selection n c) (w : Values n c)
    (h : NativeSatisfied S w) (i : Fin c) : clauseTrue S w.x i = true := by
  have hf := factor_sound (falseForm S i .first w) (falseForm S i .middle w)
    (falseForm S i .last w) (w.t i) (h.2 (i,false)) (h.2 (i,true))
  apply (clauseTrue_iff _ _ _).mpr
  rcases hf with h₁ | h₂ | h₃
  · exact ⟨.first, (falseForm_zero S w h.1 i .first).mp h₁⟩
  · exact ⟨.middle, (falseForm_zero S w h.1 i .middle).mp h₂⟩
  · exact ⟨.last, (falseForm_zero S w h.1 i .last).mp h₃⟩

/-- A direct auxiliary assignment, not a search over possible witnesses. -/
def extend (S : Selection n c) (x : Fin n → Bool) : Values n c :=
  { e := true
    x := x
    t := fun i =>
      (x (S.literal i .first).index ⊕ᵦ (S.literal i .first).positive) &&
      (x (S.literal i .middle).index ⊕ᵦ (S.literal i .middle).positive) }

theorem extend_satisfied (S : Selection n c) (x : Fin n → Bool)
    (h : ∀ i, clauseTrue S x i = true) : NativeSatisfied S (extend S x) := by
  refine ⟨rfl, ?_⟩
  rintro ⟨i, b⟩
  have hz : falseForm S i .first (extend S x) = false ∨
      falseForm S i .middle (extend S x) = false ∨
      falseForm S i .last (extend S x) = false := by
    obtain ⟨s, hs⟩ := (clauseTrue_iff S x i).mp (h i)
    have hh := (falseForm_zero S (extend S x) rfl i s).mpr hs
    cases s
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr hh)
  have hc := factor_complete _ _ _ hz
  have ht : (extend S x).t i =
      (falseForm S i .first (extend S x) && falseForm S i .middle (extend S x)) := by
    simp [extend, falseForm]
  cases b
  · change (falseForm S i .first (extend S x) &&
      (falseForm S i .middle (extend S x) ⊕ᵦ (extend S x).t i)) = false
    rw [ht]
    exact hc.1
  · change ((extend S x).t i && falseForm S i .last (extend S x)) = false
    rw [ht]
    exact hc.2

theorem native_satisfiable_iff (S : Selection n c) :
    (∃ w, NativeSatisfied S w) ↔ ∃ x, ∀ i, clauseTrue S x i = true := by
  constructor
  · rintro ⟨w, h⟩
    exact ⟨w.x, native_clause S w h⟩
  · rintro ⟨x, h⟩
    exact ⟨extend S x, extend_satisfied S x h⟩

def recovered (S : Selection n c) (failed : Fin c) (u : RowValues c) : Values n c :=
  decode S failed (pick S failed u)

def bRow (S : Selection n c) (failed : Fin c) (u : RowValues c) : Bool :=
  (recovered S failed u).e

def imageRow (S : Selection n c) (failed : Fin c) (u : RowValues c) (r : Row c) : Bool :=
  u r ⊕ᵦ selected S (recovered S failed u) r

def aRow (S : Selection n c) (failed : Fin c) (u : RowValues c) (r : Row c) : Bool :=
  u r ⊕ᵦ companion S (recovered S failed u) r

def qRow (S : Selection n c) (failed : Fin c) (u : RowValues c) (r : Row c) : Bool :=
  u r && !(aRow S failed u r)

/-- Every nonbasis row retains its image equation. Basis equations are proved
identities; they are not assumed or silently discarded. -/
def ImageEquations (S : Selection n c) (failed : Fin c) (u : RowValues c) : Prop :=
  ∀ r, (∀ k, row S failed k ≠ r) → imageRow S failed u r = false

def NormalizedSatisfied (S : Selection n c) (failed : Fin c) (u : RowValues c) : Prop :=
  bRow S failed u = true ∧ ImageEquations S failed u ∧ ∀ r, qRow S failed u r = false

theorem pick_value (S : Selection n c) (failed : Fin c)
    (u : RowValues c) (k : Label n c) :
    value (pick S failed u) k = u (row S failed k) :=
  value_fromFn _ k

theorem basis_consistency (S : Selection n c) (failed : Fin c)
    (unmatched : S.mode failed = none)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive)
    (u : RowValues c) (k : Label n c) :
    selected S (recovered S failed u) (row S failed k) = u (row S failed k) := by
  have h := congrArg (fun v => value v k)
    (selected_basis_surjective S failed unmatched bad (pick S failed u))
  simpa only [recovered, pick_value] using h

private theorem xor_zero (a b : Bool) : (a ⊕ᵦ b = false) ↔ a = b := by
  cases a <;> cases b <;> decide

theorem image_equations_iff (S : Selection n c) (failed : Fin c)
    (unmatched : S.mode failed = none)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive)
    (u : RowValues c) :
    ImageEquations S failed u ↔ ∀ r, u r = selected S (recovered S failed u) r := by
  constructor
  · intro h r
    let labels : List (Label n c) :=
      (List.finRange n).map Sum.inl ++
        ((List.finRange c).map (fun i => Sum.inr (Sum.inl i)) ++ [Sum.inr (Sum.inr ())])
    have complete (k : Label n c) : k ∈ labels := by
      cases k with
      | inl j =>
          exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))
      | inr k =>
          cases k with
          | inl i =>
              exact List.mem_append.mpr (Or.inr (List.mem_append.mpr
                (Or.inl (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))))
          | inr marker =>
              cases marker
              exact List.mem_append.mpr (Or.inr (List.mem_append.mpr
                (Or.inr (by simp only [List.mem_singleton]))))
    letI : Decidable (r ∈ labels.map (row S failed)) := inferInstance
    by_cases hb : r ∈ labels.map (row S failed)
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hb
      exact (basis_consistency S failed unmatched bad u k).symm
    · apply (xor_zero _ _).mp
      apply h r
      intro k eq
      exact hb (List.mem_map.mpr ⟨k, complete k, eq⟩)
  · intro h r _
    exact (xor_zero _ _).mpr (h r)

theorem image_characterization (S : Selection n c) (failed : Fin c)
    (unmatched : S.mode failed = none)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive)
    (u : RowValues c) :
    ImageEquations S failed u ↔ ∃ w, selected S w = u := by
  rw [image_equations_iff S failed unmatched bad u]
  constructor
  · intro h
    exact ⟨recovered S failed u, funext (fun r => (h r).symm)⟩
  · rintro ⟨w, rfl⟩ r
    unfold recovered
    rw [reconstruct_selected S failed unmatched bad]

private theorem q_boolean (u k : Bool) : (u && !(u ⊕ᵦ k)) = (u && k) := by
  cases u <;> cases k <;> rfl

theorem q_agrees (S : Selection n c) (failed : Fin c) (u : RowValues c)
    (r : Row c) (h : u r = selected S (recovered S failed u) r) :
    qRow S failed u r = factor S (recovered S failed u) r := by
  unfold qRow aRow
  rw [q_boolean, h, selected_companion]

theorem native_to_normalized (S : Selection n c) (failed : Fin c)
    (unmatched : S.mode failed = none)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive)
    (w : Values n c) (h : NativeSatisfied S w) :
    NormalizedSatisfied S failed (selected S w) := by
  have hr : recovered S failed (selected S w) = w :=
    reconstruct_selected S failed unmatched bad w
  have hi : ImageEquations S failed (selected S w) :=
    (image_characterization S failed unmatched bad _).mpr ⟨w, rfl⟩
  refine ⟨?_, hi, ?_⟩
  · simpa only [bRow, hr] using h.1
  · intro r
    rw [q_agrees S failed _ r (by rw [hr]), hr]
    exact h.2 r

theorem normalized_to_native (S : Selection n c) (failed : Fin c)
    (unmatched : S.mode failed = none)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive)
    (u : RowValues c) (h : NormalizedSatisfied S failed u) :
    NativeSatisfied S (recovered S failed u) := by
  refine ⟨h.1, ?_⟩
  intro r
  rw [← q_agrees S failed u r
    ((image_equations_iff S failed unmatched bad u).mp h.2.1 r)]
  exact h.2.2 r

theorem normalized_satisfiable_iff (S : Selection n c) (failed : Fin c)
    (unmatched : S.mode failed = none)
    (bad : sigma S (anchor S failed) ≠ (S.literal failed .first).positive) :
    (∃ u, NormalizedSatisfied S failed u) ↔ ∃ x, ∀ i, clauseTrue S x i = true := by
  rw [← native_satisfiable_iff S]
  constructor
  · rintro ⟨u, h⟩
    exact ⟨recovered S failed u, normalized_to_native S failed unmatched bad u h⟩
  · rintro ⟨w, h⟩
    exact ⟨selected S w, native_to_normalized S failed unmatched bad w h⟩


end PNP.Concrete.NativeNormalization.NativeEquations
