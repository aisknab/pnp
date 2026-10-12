import PNP.Concrete.NativeNormalization.MatchingSearch

namespace PNP.Concrete.NativeNormalization.Matching

structure IsMatching (incidence : Fin c → Fin n → Bool)
    (m : Fin c → Option (Fin n)) : Prop where
  incident : ∀ i v, m i = some v → incidence i v = true
  injective : ∀ i j v, m i = some v → m j = some v → i = j

def Free (m : Fin c → Option (Fin n)) (v : Fin n) : Prop :=
  ∀ i, m i ≠ some v

def put (m : Fin c → Option (Fin n)) (i : Fin c) (v : Fin n) :
    Fin c → Option (Fin n) :=
  fun j => if j = i then some v else m j

theorem put_valid (incidence : Fin c → Fin n → Bool)
    (m : Fin c → Option (Fin n)) (i : Fin c) (v : Fin n)
    (valid : IsMatching incidence m) (free : Free m v) (edge : incidence i v = true) :
    IsMatching incidence (put m i v) := by
  constructor
  · intro j w h
    by_cases eq : j = i
    · subst j
      have vw : v = w := Option.some.inj (by simpa [put] using h)
      subst w
      exact edge
    · exact valid.incident j w (by simpa [put, eq] using h)
  · intro a b w ha hb
    by_cases ai : a = i
    · subst a
      have vw : v = w := Option.some.inj (by simpa [put] using ha)
      subst w
      by_cases bi : b = i
      · exact bi.symm
      · have old : m b = some v := by simpa [put, bi] using hb
        exact False.elim (free b old)
    · by_cases bi : b = i
      · subst b
        have vw : v = w := Option.some.inj (by simpa [put] using hb)
        subst w
        have old : m a = some v := by simpa [put, ai] using ha
        exact False.elim (free a old)
      · exact valid.injective a b w (by simpa [put, ai] using ha) (by simpa [put, bi] using hb)

theorem put_frees_previous (incidence : Fin c → Fin n → Bool)
    (m : Fin c → Option (Fin n)) (i : Fin c) (v old : Fin n)
    (valid : IsMatching incidence m) (free : Free m v) (previous : m i = some old) :
    Free (put m i v) old := by
  intro j h
  by_cases eq : j = i
  · subst j
    have same : v = old := Option.some.inj (by simpa [put] using h)
    subst old
    exact free i previous
  · have hj : m j = some old := by simpa [put, eq] using h
    exact eq (valid.injective j i old hj previous)

theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ]
    apply List.nodup_cons.mpr
    constructor
    · intro h
      obtain ⟨i, _, eq⟩ := List.mem_map.mp h
      have hv := congrArg Fin.val eq
      change i.val + 1 = 0 at hv
      omega
    · exact List.Pairwise.map Fin.succ (fun a b ne eq => ne (by
        apply Fin.ext
        have hv := congrArg Fin.val eq
        change a.val + 1 = b.val + 1 at hv
        omega)) ih

theorem countP_promote {α : Type} [DecidableEq α] (xs : List α)
    (p : α → Bool) (i : α) (nd : xs.Nodup) (mem : i ∈ xs) (off : p i = false) :
    xs.countP (fun j => if j = i then true else p j) = xs.countP p + 1 := by
  induction xs with
  | nil => simp at mem
  | cons a xs ih =>
    have tail := List.nodup_cons.mp nd
    by_cases eq : a = i
    · subst a
      have same : xs.countP (fun j => if j = i then true else p j) = xs.countP p := by
        apply List.countP_congr
        intro j hj
        have ne : j ≠ i := by intro e; subst j; exact tail.1 hj
        simp [ne]
      simp only [List.countP_cons, off,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero, same]
    · have hin : i ∈ xs := (List.mem_cons.mp mem).resolve_left (Ne.symm eq)
      have ht := ih tail.2 hin
      simp only [List.countP_cons, if_neg eq]
      rw [ht]
      omega

def size (m : Fin c → Option (Fin n)) : Nat :=
  (List.finRange c).countP (fun i => (m i).isSome)

theorem size_le (m : Fin c → Option (Fin n)) : size m ≤ c := by
  simpa [size] using (List.countP_le_length (p := fun i => (m i).isSome) (l := List.finRange c))

theorem put_size_matched (m : Fin c → Option (Fin n)) (i : Fin c) (v old : Fin n)
    (h : m i = some old) : size (put m i v) = size m := by
  apply List.countP_congr
  intro j _
  by_cases eq : j = i
  · subst j
    simp [put, h]
  · simp [put, eq]

theorem put_size_free (m : Fin c → Option (Fin n)) (i : Fin c) (v : Fin n)
    (h : m i = none) : size (put m i v) = size m + 1 := by
  have funEq : (fun j => (put m i v j).isSome) =
      (fun j => if j = i then true else (m j).isSome) := by
    funext j
    by_cases eq : j = i <;> simp [put, eq]
  unfold size
  rw [funEq]
  apply countP_promote
  · exact finRange_nodup c
  · exact List.mem_finRange i
  · simp [h]

/-- Pairs run backwards from the current free variable to the unmatched root clause. -/
inductive Chain (incidence : Fin c → Fin n → Bool) (m : Fin c → Option (Fin n)) :
    Fin n → List (Fin c × Fin n) → Prop
  | root {i v} : m i = none → incidence i v = true → Chain incidence m v [(i, v)]
  | step {i v old pairs} : Chain incidence m old pairs →
      m i = some old → incidence i v = true → Chain incidence m v ((i, v) :: pairs)

def augment : List (Fin c × Fin n) → (Fin c → Option (Fin n)) → (Fin c → Option (Fin n))
  | [], m => m
  | (i, v) :: pairs, m => augment pairs (put m i v)

theorem Chain.congr {incidence : Fin c → Fin n → Bool}
    {m m' : Fin c → Option (Fin n)} {v : Fin n} {pairs : List (Fin c × Fin n)}
    (h : Chain incidence m v pairs)
    (agree : ∀ i, i ∈ pairs.map Prod.fst → m' i = m i) :
    Chain incidence m' v pairs := by
  induction h with
  | @root i v hm he =>
    apply Chain.root
    · exact (agree i (by simp)).trans hm
    · exact he
  | @step i v old pairs chain hm he ih =>
    apply Chain.step
    · apply ih
      intro j hj
      exact agree j (List.mem_cons_of_mem i hj)
    · exact (agree i (by simp)).trans hm
    · exact he

/-- Each supplied internal chain is realized by the executable update.
    The caller-facing search constructs this chain from its proved source path. -/
theorem augment_valid_gain (incidence : Fin c → Fin n → Bool)
    (pairs : List (Fin c × Fin n)) :
    ∀ (m : Fin c → Option (Fin n)) (v : Fin n),
      Chain incidence m v pairs → IsMatching incidence m → Free m v →
      (pairs.map Prod.fst).Nodup →
      IsMatching incidence (augment pairs m) ∧ size (augment pairs m) = size m + 1 := by
  induction pairs with
  | nil =>
    intro m v chain
    cases chain
  | cons pair pairs ih =>
    rcases pair with ⟨i, v⟩
    intro m endpoint chain valid free nd
    cases chain with
    | root unmatched edge =>
      simp only [augment]
      exact ⟨put_valid incidence m i v valid free edge, put_size_free m i v unmatched⟩
    | @step _ _ old _ chain previous edge =>
      have parts := List.nodup_cons.mp nd
      have updated := put_valid incidence m i v valid free edge
      have freeOld := put_frees_previous incidence m i v old valid free previous
      have tailChain : Chain incidence (put m i v) old pairs := chain.congr (by
        intro j hj
        have ne : j ≠ i := by intro eq; subst j; exact parts.1 hj
        simp [put, ne])
      have result := ih (put m i v) old tailChain updated freeOld parts.2
      simpa only [augment, put_size_matched m i v old previous] using result


def flattenPairs : List (Fin c × Fin n) → List (Vertex c n)
  | [] => []
  | (i, v) :: pairs => .inr v :: .inl i :: flattenPairs pairs

def readPairs : List (Vertex c n) → List (Fin c × Fin n)
  | .inr v :: .inl i :: rest => (i, v) :: readPairs rest
  | _ => []

theorem readPairs_flatten (pairs : List (Fin c × Fin n)) :
    readPairs (flattenPairs pairs) = pairs := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
    rcases pair with ⟨i, v⟩
    simp [flattenPairs, readPairs, ih]

def PathShape (incidence : Fin c → Fin n → Bool) (m : Fin c → Option (Fin n))
    (target : Vertex c n) (path : List (Vertex c n)) : Prop :=
  match target with
  | .inr v => ∃ pairs, path = flattenPairs pairs ∧ Chain incidence m v pairs
  | .inl i =>
      (path = [.inl i] ∧ m i = none) ∨
      ∃ old pairs, path = .inl i :: flattenPairs pairs ∧
        m i = some old ∧ Chain incidence m old pairs

theorem reversePath_shape (incidence : Fin c → Fin n → Bool)
    (m : Fin c → Option (Fin n)) (target : Vertex c n) (path : List (Vertex c n))
    (h : ReversePath (roots m) (alternating incidence m) target path) :
    PathShape incidence m target path := by
  induction h with
  | @root v hs =>
    cases v with
    | inl i =>
      exact Or.inl ⟨rfl, by simpa [roots] using hs⟩
    | inr v => simp [roots] at hs
  | @step a b path h he ih =>
    cases a with
    | inl i =>
      cases b with
      | inl j => simp [alternating] at he
      | inr v =>
        have edge : incidence i v = true := by
          cases e : incidence i v with
          | false => simp [alternating, e] at he
          | true => rfl
        rcases ih with ⟨eq, unmatched⟩ | ⟨old, pairs, eq, matched, chain⟩
        · subst path
          exact ⟨[(i, v)], rfl, Chain.root unmatched edge⟩
        · subst path
          exact ⟨(i, v) :: pairs, rfl, Chain.step chain matched edge⟩
    | inr old =>
      cases b with
      | inr v => simp [alternating] at he
      | inl i =>
        have matched : m i = some old := by simpa [alternating] using he
        obtain ⟨pairs, eq, chain⟩ := ih
        exact Or.inr ⟨old, pairs, by simp [eq], matched, chain⟩

theorem inl_mem_flatten (pairs : List (Fin c × Fin n)) (i : Fin c) :
    Sum.inl i ∈ flattenPairs pairs ↔ i ∈ pairs.map Prod.fst := by
  induction pairs with
  | nil => simp [flattenPairs]
  | cons pair pairs ih =>
    rcases pair with ⟨j, v⟩
    simp [flattenPairs, ih]

theorem flatten_left_nodup (pairs : List (Fin c × Fin n))
    (h : (flattenPairs pairs).Nodup) : (pairs.map Prod.fst).Nodup := by
  induction pairs with
  | nil => simp
  | cons pair pairs ih =>
    rcases pair with ⟨i, v⟩
    have first := List.nodup_cons.mp h
    have second := List.nodup_cons.mp first.2
    exact List.nodup_cons.mpr
      ⟨fun hi => second.1 ((inl_mem_flatten pairs i).mpr hi), ih second.2⟩

theorem search_augment_valid_gain (incidence : Fin c → Fin n → Bool)
    (m : Fin c → Option (Fin n)) (v : Fin n) (path : List (Vertex c n))
    (valid : IsMatching incidence m) (h : search incidence m = .augment v path) :
    IsMatching incidence (augment (readPairs path) m) ∧
      size (augment (readPairs path) m) = size m + 1 := by
  have correct := search_correct incidence m
  rw [h] at correct
  obtain ⟨free, route, nodup, _⟩ := correct
  obtain ⟨pairs, eq, chain⟩ := reversePath_shape incidence m (.inr v) path route
  have nd : (pairs.map Prod.fst).Nodup :=
    flatten_left_nodup pairs (by simpa [eq] using nodup)
  rw [eq, readPairs_flatten]
  exact augment_valid_gain incidence pairs m v chain valid ((owner_none m v).mp free) nd

/-- The only recursion counter is the clause count plus one, not a search over matchings. -/
def finish (incidence : Fin c → Fin n → Bool) :
    Nat → (Fin c → Option (Fin n)) → (Fin c → Option (Fin n))
  | 0, m => m
  | fuel + 1, m =>
    match search incidence m with
    | .terminal _ => m
    | .augment _ path => finish incidence fuel (augment (readPairs path) m)

theorem finish_valid_terminal (incidence : Fin c → Fin n → Bool)
    (fuel : Nat) (m : Fin c → Option (Fin n))
    (valid : IsMatching incidence m) (budget : c < size m + fuel) :
    IsMatching incidence (finish incidence fuel m) ∧
      freeCandidate incidence (finish incidence fuel m) = none := by
  induction fuel generalizing m with
  | zero =>
    have bound := size_le m
    have impossible : False := by omega
    exact impossible.elim
  | succ fuel ih =>
    cases h : search incidence m with
    | terminal tr =>
      have none : freeCandidate incidence m = none := by
        cases e : freeCandidate incidence m with
        | none => rfl
        | some v => simp [search, e] at h
      simpa only [finish, h] using (And.intro valid none)
    | augment v path =>
      have gain := search_augment_valid_gain incidence m v path valid h
      have nextBudget : c < size (augment (readPairs path) m) + fuel := by
        rw [gain.2]
        omega
      simpa only [finish, h] using ih (augment (readPairs path) m) gain.1 nextBudget

def fullMatching (incidence : Fin c → Fin n → Bool) : Fin c → Option (Fin n) :=
  finish incidence (c + 1) (fun _ => none)

theorem fullMatching_valid_terminal (incidence : Fin c → Fin n → Bool) :
    IsMatching incidence (fullMatching incidence) ∧
      freeCandidate incidence (fullMatching incidence) = none := by
  apply finish_valid_terminal
  · constructor
    · intro i v h; cases h
    · intro i j v h; cases h
  · omega

theorem fullMatching_cut (incidence : Fin c → Fin n → Bool) :
    Cut incidence (fullMatching incidence) (scan incidence (fullMatching incidence)) :=
  scan_cut incidence (fullMatching incidence) (fullMatching_valid_terminal incidence).2


end PNP.Concrete.NativeNormalization.Matching
