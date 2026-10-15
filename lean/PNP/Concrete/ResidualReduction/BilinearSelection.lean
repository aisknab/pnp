import Std

/-!
A complete, source-only selector for one Boolean bilinear separation query.
This standalone research module is not imported by the public PNP root.
The local matrix-query bound is not a full encoded SAT runtime theorem.
-/

namespace PNP.Concrete.ResidualReduction.BilinearSelection

universe u v

def rowEval {I : Type u} {J : Type v}
    (M : I → J → Bool) (i : I) : List J → Bool
  | [] => false
  | j :: js => Bool.xor (M i j) (rowEval M i js)

def eval {I : Type u} {J : Type v}
    (M : I → J → Bool) : List I → List J → Bool
  | [], _ => false
  | i :: is, js => Bool.xor (rowEval M i js) (eval M is js)

def good (a c : Bool) : Bool := (!a) && c

def accepts {I : Type u} {J : Type v}
    (A C : I → J → Bool) (w : List I × List J) : Bool :=
  good (eval A w.1 w.2) (eval C w.1 w.2)

def scan {T : Type u} (p : T → Bool) : List T → Option T × Nat
  | [] => (none, 0)
  | x :: xs =>
    if p x then (some x, 1)
    else
      let r := scan p xs
      (r.1, r.2 + 1)

theorem scan_sound {T : Type u} (p : T → Bool) {xs : List T} {x : T}
    (h : (scan p xs).1 = some x) : x ∈ xs ∧ p x = true := by
  induction xs with
  | nil => simp [scan] at h
  | cons a xs ih =>
    cases hp : p a with
    | false =>
      have hh : (scan p xs).1 = some x := by simpa [scan, hp] using h
      obtain ⟨hm, ht⟩ := ih hh
      exact ⟨List.mem_cons_of_mem a hm, ht⟩
    | true =>
      have ha : a = x := by simpa [scan, hp] using h
      subst x
      exact ⟨by simp, hp⟩

theorem scan_none_iff {T : Type u} (p : T → Bool) (xs : List T) :
    (scan p xs).1 = none ↔ ∀ x ∈ xs, p x = false := by
  induction xs with
  | nil => simp [scan]
  | cons a xs ih =>
    cases hp : p a <;> simp [scan, hp, ih]

theorem scan_some_iff {T : Type u} (p : T → Bool) (xs : List T) :
    (∃ x, (scan p xs).1 = some x) ↔ xs.any p = true := by
  induction xs with
  | nil => simp [scan]
  | cons a xs ih =>
    cases hp : p a with
    | false => simpa [scan, hp] using ih
    | true => simp [scan, hp]

theorem scan_steps_le {T : Type u} (p : T → Bool) (xs : List T) :
    (scan p xs).2 ≤ xs.length := by
  induction xs with
  | nil => simp [scan]
  | cons a xs ih =>
    cases hp : p a with
    | false => simpa [scan, hp] using Nat.add_le_add_right ih 1
    | true => simp [scan, hp]

def candidates {I : Type u} {J : Type v}
    (i k : I) (j l : J) : List (List I × List J) :=
  [([i], [j]), ([i], [l]), ([i], [j, l]),
   ([k], [j]), ([k], [l]), ([k], [j, l]),
   ([i, k], [j]), ([i, k], [l]), ([i, k], [j, l])]

theorem candidates_small {I : Type u} {J : Type v}
    {i k : I} {j l : J} {w : List I × List J}
    (h : w ∈ candidates i k j l) :
    w.1.length ≤ 2 ∧ w.2.length ≤ 2 := by
  simp only [candidates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem xor_true_iff_ne (a b : Bool) :
    Bool.xor a b = true ↔ a ≠ b := by
  cases a <;> cases b <;> decide

private theorem xor_false_iff_eq (a b : Bool) :
    Bool.xor a b = false ↔ a = b := by
  cases a <;> cases b <;> decide

private theorem rectangleTruth :
    ∀ a b c d e f g h : Bool,
      e = true → h ≠ d →
      [good a e, good b f, good (Bool.xor a b) (Bool.xor e f),
       good c g, good d h, good (Bool.xor c d) (Bool.xor g h),
       good (Bool.xor a c) (Bool.xor e g),
       good (Bool.xor b d) (Bool.xor f h),
       good (Bool.xor (Bool.xor a b) (Bool.xor c d))
            (Bool.xor (Bool.xor e f) (Bool.xor g h))].any id = true := by
  decide

theorem candidates_succeed {I : Type u} {J : Type v}
    (A C : I → J → Bool) (i k : I) (j l : J)
    (hz : C i j = true) (hd : C k l ≠ A k l) :
    (candidates i k j l).any (accepts A C) = true := by
  simpa [candidates, accepts, eval, rowEval, good] using
    rectangleTruth (A i j) (A i l) (A k j) (A k l)
      (C i j) (C i l) (C k j) (C k l) hz hd

theorem bounded_support_witness {I : Type u} {J : Type v}
    (A C : I → J → Bool)
    (hz : ∃ i j, C i j = true)
    (hd : ∃ i j, C i j ≠ A i j) :
    ∃ w : List I × List J,
      w.1.length ≤ 2 ∧ w.2.length ≤ 2 ∧
      eval A w.1 w.2 = false ∧ eval C w.1 w.2 = true := by
  obtain ⟨i, j, hi⟩ := hz
  obtain ⟨k, l, hk⟩ := hd
  obtain ⟨w, hw⟩ := (scan_some_iff (accepts A C) (candidates i k j l)).mpr
    (candidates_succeed A C i k j l hi hk)
  obtain ⟨hm, ha⟩ := scan_sound (accepts A C) hw
  obtain ⟨hr, hc⟩ := candidates_small hm
  have hv : eval A w.1 w.2 = false ∧ eval C w.1 w.2 = true := by
    simpa [accepts, good] using ha
  exact ⟨w, hr, hc, hv⟩

abbrev Matrix (m n : Nat) := Fin m → Fin n → Bool
abbrev Witness (m n : Nat) := List (Fin m) × List (Fin n)

def entries (m n : Nat) : List (Fin m × Fin n) :=
  (List.finRange m).flatMap fun i =>
    (List.finRange n).map fun j => (i, j)

theorem mem_entries {m n : Nat} (i : Fin m) (j : Fin n) :
    (i, j) ∈ entries m n := by
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, ?_⟩
  exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩

private theorem grid_length {I : Type u} {J : Type v}
    (is : List I) (js : List J) :
    (is.flatMap fun i => js.map fun j => (i, j)).length =
      is.length * js.length := by
  induction is with
  | nil => simp
  | cons i is ih => simp [List.flatMap_cons, ih, Nat.succ_mul, Nat.add_comm]

theorem entries_length (m n : Nat) : (entries m n).length = m * n := by
  simp only [entries, grid_length, List.length_finRange]

structure Result (m n : Nat) where
  witness : Option (Witness m n)
  nonzeroChecks : Nat
  differenceChecks : Nat
  candidateChecks : Nat
  deriving Repr

def Result.matrixReadCharge {m n : Nat} (r : Result m n) : Nat :=
  r.nonzeroChecks + 2 * r.differenceChecks + 8 * r.candidateChecks

def select {m n : Nat} (A C : Matrix m n) : Result m n :=
  let nz := scan (fun p : Fin m × Fin n => C p.1 p.2) (entries m n)
  match nz.1 with
  | none => ⟨none, nz.2, 0, 0⟩
  | some e =>
    let df := scan (fun p : Fin m × Fin n => Bool.xor (C p.1 p.2) (A p.1 p.2)) (entries m n)
    match df.1 with
    | none => ⟨none, nz.2, df.2, 0⟩
    | some f =>
      let hit := scan (accepts A C) (candidates e.1 f.1 e.2 f.2)
      ⟨hit.1, nz.2, df.2, hit.2⟩

def Viable {m n : Nat} (A C : Matrix m n) : Prop :=
  (∃ i j, C i j = true) ∧ (∃ i j, C i j ≠ A i j)

theorem select_sound {m n : Nat} (A C : Matrix m n) {w : Witness m n}
    (h : (select A C).witness = some w) :
    w.1.length ≤ 2 ∧ w.2.length ≤ 2 ∧
      eval A w.1 w.2 = false ∧ eval C w.1 w.2 = true := by
  cases hn : (scan (fun p : Fin m × Fin n => C p.1 p.2) (entries m n)).1 with
  | none => simp [select, hn] at h
  | some e =>
    cases hd : (scan (fun p : Fin m × Fin n => Bool.xor (C p.1 p.2) (A p.1 p.2))
        (entries m n)).1 with
    | none => simp [select, hn, hd] at h
    | some f =>
      have hh : (scan (accepts A C) (candidates e.1 f.1 e.2 f.2)).1 = some w := by
        simpa [select, hn, hd] using h
      obtain ⟨hm, ht⟩ := scan_sound (accepts A C) hh
      obtain ⟨hr, hc⟩ := candidates_small hm
      have hv : eval A w.1 w.2 = false ∧ eval C w.1 w.2 = true := by
        simpa [accepts, good] using ht
      exact ⟨hr, hc, hv⟩

theorem select_complete {m n : Nat} (A C : Matrix m n)
    (h : Viable A C) : ∃ w, (select A C).witness = some w := by
  obtain ⟨⟨i, j, hz⟩, ⟨k, l, hdiff⟩⟩ := h
  cases hn : (scan (fun p : Fin m × Fin n => C p.1 p.2) (entries m n)).1 with
  | none =>
    have hh := (scan_none_iff (fun p : Fin m × Fin n => C p.1 p.2) (entries m n)).mp hn
      (i, j) (mem_entries i j)
    simp [hz] at hh
  | some e =>
    have he : C e.1 e.2 = true :=
      (scan_sound (fun p : Fin m × Fin n => C p.1 p.2) hn).2
    cases hd : (scan (fun p : Fin m × Fin n => Bool.xor (C p.1 p.2) (A p.1 p.2))
        (entries m n)).1 with
    | none =>
      have hh := (scan_none_iff
        (fun p : Fin m × Fin n => Bool.xor (C p.1 p.2) (A p.1 p.2)) (entries m n)).mp hd
          (k, l) (mem_entries k l)
      exact False.elim (hdiff ((xor_false_iff_eq _ _).mp hh))
    | some f =>
      have hf : C f.1 f.2 ≠ A f.1 f.2 :=
        (xor_true_iff_ne _ _).mp
          (scan_sound (fun p : Fin m × Fin n => Bool.xor (C p.1 p.2) (A p.1 p.2)) hd).2
      obtain ⟨w, hw⟩ :=
        (scan_some_iff (accepts A C) (candidates e.1 f.1 e.2 f.2)).mpr
          (candidates_succeed A C e.1 f.1 e.2 f.2 he hf)
      exact ⟨w, by simpa [select, hn, hd] using hw⟩

theorem select_viable {m n : Nat} (A C : Matrix m n)
    (h : ∃ w, (select A C).witness = some w) : Viable A C := by
  obtain ⟨w, hw⟩ := h
  cases hn : (scan (fun p : Fin m × Fin n => C p.1 p.2) (entries m n)).1 with
  | none => simp [select, hn] at hw
  | some e =>
    have he : C e.1 e.2 = true :=
      (scan_sound (fun p : Fin m × Fin n => C p.1 p.2) hn).2
    cases hd : (scan (fun p : Fin m × Fin n => Bool.xor (C p.1 p.2) (A p.1 p.2))
        (entries m n)).1 with
    | none => simp [select, hn, hd] at hw
    | some f =>
      have hf : C f.1 f.2 ≠ A f.1 f.2 :=
        (xor_true_iff_ne _ _).mp
          (scan_sound (fun p : Fin m × Fin n => Bool.xor (C p.1 p.2) (A p.1 p.2)) hd).2
      exact ⟨⟨e.1, e.2, he⟩, ⟨f.1, f.2, hf⟩⟩

theorem select_iff {m n : Nat} (A C : Matrix m n) :
    (∃ w, (select A C).witness = some w) ↔ Viable A C :=
  ⟨select_viable A C, select_complete A C⟩

theorem matrix_read_charge_bound {m n : Nat} (A C : Matrix m n) :
    (select A C).matrixReadCharge ≤ 3 * (m * n) + 72 := by
  have h0 : (scan (fun p : Fin m × Fin n => C p.1 p.2) (entries m n)).2 ≤ m * n := by
    simpa only [entries_length] using
      scan_steps_le (fun p : Fin m × Fin n => C p.1 p.2) (entries m n)
  have h1 : (scan (fun p : Fin m × Fin n => Bool.xor (C p.1 p.2) (A p.1 p.2))
      (entries m n)).2 ≤ m * n := by
    simpa only [entries_length] using
      scan_steps_le (fun p : Fin m × Fin n => Bool.xor (C p.1 p.2) (A p.1 p.2)) (entries m n)
  cases hn : (scan (fun p : Fin m × Fin n => C p.1 p.2) (entries m n)).1 with
  | none =>
    simp only [select, hn, Result.matrixReadCharge]
    omega
  | some e =>
    cases hd : (scan (fun p : Fin m × Fin n => Bool.xor (C p.1 p.2) (A p.1 p.2))
        (entries m n)).1 with
    | none =>
      simp only [select, hn, hd, Result.matrixReadCharge]
      omega
    | some f =>
      have h2 : (scan (accepts A C) (candidates e.1 f.1 e.2 f.2)).2 ≤ 9 := by
        simpa only [candidates, List.length_cons, List.length_nil] using
          scan_steps_le (accepts A C) (candidates e.1 f.1 e.2 f.2)
      simp only [select, hn, hd, Result.matrixReadCharge]
      omega


private theorem xor_ne_splits (a b c d : Bool) :
    Bool.xor a b ≠ Bool.xor c d → a ≠ c ∨ b ≠ d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem rowEval_true_entry {I : Type u} {J : Type v}
    (M : I → J → Bool) (i : I) (js : List J)
    (h : rowEval M i js = true) : ∃ j, M i j = true := by
  induction js with
  | nil => simp [rowEval] at h
  | cons j js ih =>
    cases hj : M i j with
    | false => exact ih (by simpa [rowEval, hj] using h)
    | true => exact ⟨j, hj⟩

theorem eval_true_entry {I : Type u} {J : Type v}
    (M : I → J → Bool) (is : List I) (js : List J)
    (h : eval M is js = true) : ∃ i j, M i j = true := by
  induction is with
  | nil => simp [eval] at h
  | cons i is ih =>
    cases hr : rowEval M i js with
    | false => exact ih (by simpa [eval, hr] using h)
    | true =>
      obtain ⟨j, hj⟩ := rowEval_true_entry M i js hr
      exact ⟨i, j, hj⟩

theorem rowEval_ne_entry {I : Type u} {J : Type v}
    (M N : I → J → Bool) (i : I) (js : List J)
    (h : rowEval M i js ≠ rowEval N i js) : ∃ j, M i j ≠ N i j := by
  induction js with
  | nil => simp [rowEval] at h
  | cons j js ih =>
    rcases xor_ne_splits (M i j) (rowEval M i js) (N i j) (rowEval N i js) h with
      hc | ht
    · exact ⟨j, hc⟩
    · exact ih ht

theorem eval_ne_entry {I : Type u} {J : Type v}
    (M N : I → J → Bool) (is : List I) (js : List J)
    (h : eval M is js ≠ eval N is js) : ∃ i j, M i j ≠ N i j := by
  induction is with
  | nil => simp [eval] at h
  | cons i is ih =>
    rcases xor_ne_splits (rowEval M i js) (eval M is js)
      (rowEval N i js) (eval N is js) h with hr | ht
    · obtain ⟨j, hj⟩ := rowEval_ne_entry M N i js hr
      exact ⟨i, j, hj⟩
    · exact ih ht

theorem bilinear_existence_iff {I : Type u} {J : Type v}
    (A C : I → J → Bool) :
    (∃ is js, eval A is js = false ∧ eval C is js = true) ↔
      (∃ i j, C i j = true) ∧ (∃ i j, C i j ≠ A i j) := by
  constructor
  · rintro ⟨is, js, ha, hc⟩
    refine ⟨eval_true_entry C is js hc, ?_⟩
    apply eval_ne_entry C A is js
    rw [hc, ha]
    decide
  · rintro ⟨hz, hd⟩
    obtain ⟨w, _, _, ha, hc⟩ := bounded_support_witness A C hz hd
    exact ⟨w.1, w.2, ha, hc⟩

theorem select_complete_for_any_witness {m n : Nat} (A C : Matrix m n)
    (h : ∃ is js, eval A is js = false ∧ eval C is js = true) :
    ∃ w, (select A C).witness = some w :=
  select_complete A C ((bilinear_existence_iff A C).mp h)

theorem select_none_iff {m n : Nat} (A C : Matrix m n) :
    (select A C).witness = none ↔
      ¬ ∃ is js, eval A is js = false ∧ eval C is js = true := by
  constructor
  · intro hn hw
    obtain ⟨w, hh⟩ := select_complete_for_any_witness A C hw
    simp [hn] at hh
  · intro h
    cases hs : (select A C).witness with
    | none => rfl
    | some w =>
      obtain ⟨_, _, ha, hc⟩ := select_sound A C hs
      exact False.elim (h ⟨w.1, w.2, ha, hc⟩)

end PNP.Concrete.ResidualReduction.BilinearSelection
