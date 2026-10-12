import PNP.Concrete.CNFToNAND
import PNP.Concrete.NativeNormalization.NativeSourceEquations

namespace PNP.Concrete.NativeNormalization.NativeTseitin

open PNP PNP.Concrete PNP.DirectWire PNP.DirectWire.LockedNANDTrace

/-- Absolute source indices preserve every prefix of a typed NAND program. -/
def sourceIndex {n g : Nat} : Source n g → Nat
  | .input i => i.val
  | .constant false => n
  | .constant true => n + 1
  | .gate j => n + 2 + j.val

def clauseHolds (v : Nat → Bool) (ls : List CNFLiteral) : Prop :=
  ∃ l ∈ ls, v l.variableIndex = l.positive

def holds (v : Nat → Bool) (cs : List (List CNFLiteral)) : Prop :=
  ∀ ls ∈ cs, clauseHolds v ls

def unitClause (i : Nat) (value : Bool) : List CNFLiteral :=
  [⟨value, i⟩, ⟨value, i⟩, ⟨value, i⟩]

/-- Exactly three clauses for z = NAND(x,y); repeated literals are retained. -/
def gateClauses {n g : Nat} (gate : Gate n g) : List (List CNFLiteral) :=
  [[⟨false, sourceIndex gate.left⟩, ⟨false, sourceIndex gate.right⟩,
      ⟨false, n + 2 + g⟩],
   [⟨true, sourceIndex gate.left⟩, ⟨true, n + 2 + g⟩,
      ⟨true, n + 2 + g⟩],
   [⟨true, sourceIndex gate.right⟩, ⟨true, n + 2 + g⟩,
      ⟨true, n + 2 + g⟩]]

def programClauses {n : Nat} : {g : Nat} → Program n g → List (List CNFLiteral)
  | _, .empty => []
  | _, .snoc p gate => programClauses p ++ gateClauses gate

theorem holds_append (v : Nat → Bool) (a b : List (List CNFLiteral)) :
    holds v (a ++ b) ↔ holds v a ∧ holds v b := by
  simp [holds, List.mem_append, or_imp, forall_and]

theorem unit_iff (v : Nat → Bool) (i : Nat) (b : Bool) :
    clauseHolds v (unitClause i b) ↔ v i = b := by
  simp [clauseHolds, unitClause]

theorem gate_iff {n g : Nat} (gate : Gate n g) (v : Nat → Bool) :
    holds v (gateClauses gate) ↔
      v (n + 2 + g) = boolNand (v (sourceIndex gate.left)) (v (sourceIndex gate.right)) := by
  simp [holds, gateClauses, clauseHolds]
  cases v (sourceIndex gate.left) <;> cases v (sourceIndex gate.right) <;>
    cases v (n + 2 + g) <;> decide

theorem source_eval {n g : Nat} (s : Source n g) (v : Nat → Bool)
    (hf : v n = false) (ht : v (n + 1) = true) :
    v (sourceIndex s) = s.eval (fun i => v i.val) (fun j => v (n + 2 + j.val)) := by
  cases s with
  | input i => rfl
  | gate j => rfl
  | constant b => cases b <;> simp [sourceIndex, Source.eval, hf, ht]

theorem snoc_values_iff {n g : Nat} (p : Program n g) (gate : Gate n g)
    (v : Nat → Bool) :
    (∀ j : Fin (g + 1), v (n + 2 + j.val) =
      (p.snoc gate).eval (fun i => v i.val) j) ↔
    (∀ j : Fin g, v (n + 2 + j.val) = p.eval (fun i => v i.val) j) ∧
      v (n + 2 + g) = gate.eval (fun i => v i.val) (p.eval (fun i => v i.val)) := by
  constructor
  · intro h
    constructor
    · intro j
      simpa only [Fin.val_castSucc, Program.eval_snoc_castSucc] using h j.castSucc
    · simpa only [Fin.val_last, Program.eval_snoc_last] using h (Fin.last g)
  · rintro ⟨hp, hg⟩ j
    by_cases hj : j.val < g
    · have eq : j = (⟨j.val, hj⟩ : Fin g).castSucc := Fin.ext rfl
      rw [eq, Program.eval_snoc_castSucc]
      exact hp ⟨j.val, hj⟩
    · have eq : j = Fin.last g := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [eq, Program.eval_snoc_last]
      exact hg

/-- The gate constraints force every gate value, not only the output bit. -/
theorem program_iff {n g : Nat} (p : Program n g) (v : Nat → Bool)
    (hf : v n = false) (ht : v (n + 1) = true) :
    holds v (programClauses p) ↔
      ∀ j : Fin g, v (n + 2 + j.val) = p.eval (fun i => v i.val) j := by
  induction p with
  | empty => simp [programClauses, holds]
  | @snoc g p gate ih =>
      rw [programClauses, holds_append, ih, gate_iff, snoc_values_iff]
      constructor
      · rintro ⟨hp, hg⟩
        refine ⟨hp, ?_⟩
        have he : (fun j : Fin g => v (n + 2 + j.val)) =
            p.eval (fun i => v i.val) := funext hp
        rw [source_eval gate.left v hf ht, source_eval gate.right v hf ht, he] at hg
        exact hg
      · rintro ⟨hp, hg⟩
        refine ⟨hp, ?_⟩
        have he : (fun j : Fin g => v (n + 2 + j.val)) =
            p.eval (fun i => v i.val) := funext hp
        rw [source_eval gate.left v hf ht, source_eval gate.right v hf ht, he]
        exact hg

theorem sourceIndex_bound {n g : Nat} (s : Source n g) :
    sourceIndex s < n + 2 + g := by
  cases s with
  | input i => simp only [sourceIndex]; omega
  | constant b => cases b <;> simp only [sourceIndex] <;> omega
  | gate j => simp only [sourceIndex]; omega

theorem gateClauses_shape {n g : Nat} (gate : Gate n g) :
    (gateClauses gate).length = 3 ∧
    ∀ ls ∈ gateClauses gate, ls.length = 3 ∧
      ∀ l ∈ ls, l.variableIndex < n + 2 + (g + 1) := by
  have leftBound : sourceIndex gate.left < n + 2 + (g + 1) := by
    have checked := sourceIndex_bound gate.left
    omega
  have rightBound : sourceIndex gate.right < n + 2 + (g + 1) := by
    have checked := sourceIndex_bound gate.right
    omega
  have outputBound : n + 2 + g < n + 2 + (g + 1) := by omega
  have triple (a b c : CNFLiteral)
      (ha : a.variableIndex < n + 2 + (g + 1))
      (hb : b.variableIndex < n + 2 + (g + 1))
      (hc : c.variableIndex < n + 2 + (g + 1)) :
      [a,b,c].length = 3 ∧ ∀ l ∈ [a,b,c], l.variableIndex < n + 2 + (g + 1) := by
    refine ⟨rfl, ?_⟩
    intro l member
    rcases List.mem_cons.mp member with equal | tail
    · subst l
      exact ha
    · rcases List.mem_cons.mp tail with equal | tail
      · subst l
        exact hb
      · rcases List.mem_cons.mp tail with equal | tail
        · subst l
          exact hc
        · cases tail
  refine ⟨rfl, ?_⟩
  intro ls member
  unfold gateClauses at member
  rcases List.mem_cons.mp member with equal | tail
  · subst ls
    exact triple _ _ _ leftBound rightBound outputBound
  · rcases List.mem_cons.mp tail with equal | tail
    · subst ls
      exact triple _ _ _ leftBound outputBound outputBound
    · rcases List.mem_cons.mp tail with equal | tail
      · subst ls
        exact triple _ _ _ rightBound outputBound outputBound
      · cases tail

theorem programClauses_shape {n g : Nat} (p : Program n g) :
    (programClauses p).length = 3 * g ∧
    ∀ ls ∈ programClauses p, ls.length = 3 ∧
      ∀ l ∈ ls, l.variableIndex < n + 2 + g := by
  induction p with
  | empty => simp [programClauses]
  | @snoc g p gate ih =>
      obtain ⟨hg, hs⟩ := gateClauses_shape gate
      constructor
      · simp only [programClauses, List.length_append, ih.1, hg]
        omega
      · intro ls hls
        rcases List.mem_append.mp hls with old | fresh
        · obtain ⟨hl, hi⟩ := ih.2 ls old
          exact ⟨hl, fun l hm => Nat.lt_trans (hi l hm) (by omega)⟩
        · exact hs ls fresh


end PNP.Concrete.NativeNormalization.NativeTseitin
