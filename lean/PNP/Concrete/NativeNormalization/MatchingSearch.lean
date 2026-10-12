import PNP.Concrete.NativeNormalization.MatchingReach
import PNP.Concrete.NormalizerVertexEquality
import PNP.Concrete.NormalizerConstructiveLists

namespace PNP.Concrete.NativeNormalization.Matching

abbrev Vertex (c n : Nat) := Sum (Fin c) (Fin n)

/-- Constructive equality law; the finite equality computation is unchanged. -/
instance vertexLawfulBEq : LawfulBEq (Vertex c n) :=
  PNP.Concrete.NormalizerBlocks.ConstructiveVertexEquality.lawful c n

def vertices (c n : Nat) : List (Vertex c n) :=
  (List.finRange c).map Sum.inl ++ (List.finRange n).map Sum.inr

theorem vertices_all (v : Vertex c n) : v ∈ vertices c n := by
  cases v with
  | inl i => simp [vertices]
  | inr j => simp [vertices]

def owner (m : Fin c → Option (Fin n)) (v : Fin n) : Option (Fin c) :=
  (List.finRange c).find? (fun i => m i == some v)

theorem owner_some (m : Fin c → Option (Fin n)) (v : Fin n)
    (h : owner m v = some i) : m i = some v := by
  have he := List.find?_some (p := fun j => m j == some v) h
  simpa using he

theorem owner_none (m : Fin c → Option (Fin n)) (v : Fin n) :
    owner m v = none ↔ ∀ i, m i ≠ some v := by
  simp [owner, List.find?_eq_none]

def roots (m : Fin c → Option (Fin n)) : Vertex c n → Bool
  | .inl i => (m i).isNone
  | .inr _ => false

def alternating (incidence : Fin c → Fin n → Bool)
    (m : Fin c → Option (Fin n)) : Vertex c n → Vertex c n → Bool
  | .inl i, .inr v => incidence i v && !(m i == some v)
  | .inr v, .inl i => m i == some v
  | _, _ => false

def scan (incidence : Fin c → Fin n → Bool) (m : Fin c → Option (Fin n)) :
    Trace (Vertex c n) :=
  explore (roots m) (alternating incidence m) (c + n) (vertices c n) []

theorem scan_valid (incidence : Fin c → Fin n → Bool) (m : Fin c → Option (Fin n)) :
    Valid (roots m) (alternating incidence m) (scan incidence m) :=
  explore_valid _ _ _ _ _ Valid.nil

theorem scan_closed (incidence : Fin c → Fin n → Bool) (m : Fin c → Option (Fin n)) :
    Closed (roots m) (alternating incidence m) (scan incidence m) := by
  apply explore_closed
  · simp [vertices]
  · intro v
    exact Or.inl (vertices_all v)

theorem scan_reachable (incidence : Fin c → Fin n → Bool) (m : Fin c → Option (Fin n))
    (v : Vertex c n) :
    v ∈ nodes (scan incidence m) ↔ Reach (roots m) (alternating incidence m) v := by
  constructor
  · exact (scan_valid incidence m).sound v
  · intro h
    induction h with
    | root hs => exact (scan_closed incidence m).1 _ hs
    | step _ he ih => exact (scan_closed incidence m).2 _ _ ih he

theorem scan_length (incidence : Fin c → Fin n → Bool) (m : Fin c → Option (Fin n)) :
    (scan incidence m).length ≤ c + n := by
  simpa [scan] using explore_length (roots m) (alternating incidence m)
    (c + n) (vertices c n) []

theorem matched_partner_reachable (incidence : Fin c → Fin n → Bool)
    (m : Fin c → Option (Fin n)) (i : Fin c) (v : Fin n)
    (hi : Reach (roots m) (alternating incidence m) (.inl i))
    (hm : m i = some v) :
    Reach (roots m) (alternating incidence m) (.inr v) := by
  have general : ∀ w, Reach (roots m) (alternating incidence m) w →
      match w with
      | .inl j => ∀ u, m j = some u → Reach (roots m) (alternating incidence m) (.inr u)
      | .inr _ => True := by
    intro w hw
    induction hw with
    | @root w hs =>
      cases w with
      | inl j =>
        intro u hu
        simp [roots, hu] at hs
      | inr u => trivial
    | @step a b ha he ih =>
      cases b with
      | inr u => trivial
      | inl j =>
        intro u hu
        cases a with
        | inl k => simp [alternating] at he
        | inr v =>
          have hv : m j = some v := by simpa [alternating] using he
          have eq : u = v := Option.some.inj (hu.symm.trans hv)
          subst v
          exact ha
  exact general (.inl i) hi v hm

def freeCandidate (incidence : Fin c → Fin n → Bool)
    (m : Fin c → Option (Fin n)) : Option (Fin n) :=
  (List.finRange n).find? (fun v =>
    (owner m v).isNone && decide (Sum.inr v ∈ nodes (scan incidence m)))

theorem freeCandidate_some (incidence : Fin c → Fin n → Bool)
    (m : Fin c → Option (Fin n)) (h : freeCandidate incidence m = some v) :
    owner m v = none ∧ Sum.inr v ∈ nodes (scan incidence m) := by
  have he := List.find?_some (p := fun w =>
    (owner m w).isNone && decide (Sum.inr w ∈ nodes (scan incidence m))) h
  simpa using he

theorem freeCandidate_none (incidence : Fin c → Fin n → Bool)
    (m : Fin c → Option (Fin n)) (h : freeCandidate incidence m = none)
    (v : Fin n) (hv : Sum.inr v ∈ nodes (scan incidence m)) :
    ∃ i, owner m v = some i := by
  have he := List.find?_eq_none.mp h v (List.mem_finRange v)
  cases ho : owner m v with
  | none => simp [ho, hv] at he
  | some i => exact ⟨i, rfl⟩

/-- The residual region is computed by the search, not supplied by a caller. -/
def Cut (incidence : Fin c → Fin n → Bool) (m : Fin c → Option (Fin n))
    (tr : Trace (Vertex c n)) : Prop :=
  (∀ i, m i = none → Sum.inl i ∈ nodes tr) ∧
  (∀ i v, Sum.inl i ∈ nodes tr → incidence i v = true → Sum.inr v ∈ nodes tr) ∧
  (∀ v, Sum.inr v ∈ nodes tr → ∃ i, m i = some v ∧ Sum.inl i ∈ nodes tr) ∧
  (∀ i v, m i = some v → (Sum.inl i ∈ nodes tr ↔ Sum.inr v ∈ nodes tr)) ∧
  (∀ i, Sum.inl i ∉ nodes tr → ∃ v, m i = some v ∧ Sum.inr v ∉ nodes tr)

theorem scan_cut (incidence : Fin c → Fin n → Bool)
    (m : Fin c → Option (Fin n)) (h : freeCandidate incidence m = none) :
    Cut incidence m (scan incidence m) := by
  have closed := scan_closed incidence m
  have paired : ∀ i v, m i = some v →
      (Sum.inl i ∈ nodes (scan incidence m) ↔ Sum.inr v ∈ nodes (scan incidence m)) := by
    intro i v hm
    constructor
    · intro hi
      apply (scan_reachable incidence m (.inr v)).mpr
      exact matched_partner_reachable incidence m i v
        ((scan_reachable incidence m (.inl i)).mp hi) hm
    · intro hv
      exact closed.2 _ _ hv (by
        change (m i == some v) = true
        rw [hm]
        change decide (v = v) = true
        exact decide_eq_true rfl)
  refine ⟨?_, ?_, ?_, paired, ?_⟩
  · intro i hi
    exact closed.1 (.inl i) (by simp [roots, hi])
  · intro i v hi he
    by_cases hm : m i = some v
    · exact (paired i v hm).mp hi
    · exact closed.2 _ _ hi (by
        change (incidence i v && !(m i == some v)) = true
        have different : (m i == some v) = false := by
          cases found : m i with
          | none => rfl
          | some u =>
            change decide (u = v) = false
            apply decide_eq_false
            intro same
            exact hm (found.trans (congrArg some same))
        rw [he, different]
        rfl)
  · intro v hv
    obtain ⟨i, ho⟩ := freeCandidate_none incidence m h v hv
    have hm := owner_some m v ho
    exact ⟨i, hm, (paired i v hm).mpr hv⟩
  · intro i hi
    cases hm : m i with
    | none => exact False.elim (hi (closed.1 (.inl i) (by simp [roots, hm])))
    | some v =>
      exact ⟨v, rfl, fun hv => hi ((paired i v hm).mpr hv)⟩

inductive SearchOutput (c n : Nat)
  | augment (v : Fin n) (path : List (Vertex c n))
  | terminal (trace : Trace (Vertex c n))
  deriving Repr

def search (incidence : Fin c → Fin n → Bool) (m : Fin c → Option (Fin n)) :
    SearchOutput c n :=
  match freeCandidate incidence m with
  | none => .terminal (scan incidence m)
  | some v => .augment v ((pathTo (scan incidence m) (.inr v)).getD [])

def SearchCorrect (incidence : Fin c → Fin n → Bool)
    (m : Fin c → Option (Fin n)) : SearchOutput c n → Prop
  | .augment v path =>
      owner m v = none ∧ ReversePath (roots m) (alternating incidence m) (.inr v) path ∧
      path.Nodup ∧ path.length ≤ c + n
  | .terminal tr =>
      tr = scan incidence m ∧ Valid (roots m) (alternating incidence m) tr ∧ Cut incidence m tr

theorem search_correct (incidence : Fin c → Fin n → Bool)
    (m : Fin c → Option (Fin n)) : SearchCorrect incidence m (search incidence m) := by
  cases h : freeCandidate incidence m with
  | none =>
    simp only [search, h, SearchCorrect]
    exact ⟨True.intro, scan_valid incidence m, scan_cut incidence m h⟩
  | some v =>
    obtain ⟨free, member⟩ := freeCandidate_some incidence m h
    obtain ⟨path, hp, hr, hn, hl, _⟩ := (scan_valid incidence m).path (.inr v) member
    simp only [search, h, hp, Option.getD_some, SearchCorrect]
    exact ⟨free, hr, hn, Nat.le_trans hl (scan_length incidence m)⟩


end PNP.Concrete.NativeNormalization.Matching
