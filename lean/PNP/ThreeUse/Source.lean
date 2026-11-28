import PNP.ThreeUse.Gates
import PNP.ThreeUse.OccurrenceSplit
import PNP.Concrete.CNF

/-!
# Interpreting strict encoded CNF

Decode source bytes using the ordinary concrete language. Out-of-width literals of either polarity do not satisfy a clause; invalid byte strings map to an impossible system.
-/

set_option autoImplicit false

namespace PNP.ThreeUse
open PNP.Concrete

def emit : Nat → (Nat → Bool) → BitString
  | 0, _ => []
  | n+1, h => h 0 :: emit n (fun j => h (j+1))

theorem emit_len (n : Nat) (h : Nat → Bool) : (emit n h).length = n := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => rw [emit, List.length_cons, ih]

theorem emit_at (n : Nat) (h : Nat → Bool) (j : Nat) :
    assignmentAt (emit n h) j = if j<n then some (h j) else none := by
  induction n generalizing h j with
  | zero => rfl
  | succ n ih =>
    cases j with
    | zero => rw [if_pos (Nat.zero_lt_succ _)]; rfl
    | succ j =>
      change assignmentAt (emit n (fun x => h (x+1))) j = _
      rw [ih]
      by_cases e : j<n
      · rw [if_pos e, if_pos (by omega : j+1<n+1)]
      · rw [if_neg e, if_neg (by omega : ¬j+1<n+1)]

theorem emit_all (w : BitString) : ∃ h : Nat → Bool, emit w.length h = w := by
  induction w with
  | nil => exact ⟨fun _ => false, rfl⟩
  | cons a w ih =>
    obtain ⟨h, e⟩ := ih
    let f : Nat → Bool := fun i => match i with | 0 => a | j+1 => h j
    exact ⟨f, congrArg (List.cons a) e⟩

def normalize (n : Nat) : List CNFLiteral → List Lit
  | [] => []
  | l :: ls => if l.variableIndex<n then ⟨l.variableIndex, l.positive⟩ :: normalize n ls else normalize n ls

theorem norm_row (n : Nat) (h : Nat → Bool) (c : List CNFLiteral) : ClauseSatisfied c (emit n h) ↔
    bads h (normalize n c) = false := by
  induction c with
  | nil => constructor <;> intro x <;> contradiction
  | cons l ls ih =>
    change (assignmentAt (emit n h) l.variableIndex = some l.positive ∨ ClauseSatisfied ls (emit n h)) ↔ _
    rw [emit_at, ih, normalize]
    by_cases e : l.variableIndex<n
    · rw [if_pos e, if_pos e, bads]
      change (some (h l.variableIndex) = some l.positive ∨ _) ↔
        (((h l.variableIndex ^^ l.positive) && bads h (normalize n ls)) = false)
      cases h l.variableIndex <;> cases l.positive <;> cases bads h (normalize n ls) <;> decide
    · rw [if_neg e, if_neg e]; constructor
      · rintro (x|x)
        · contradiction
        · exact x
      · exact Or.inr

theorem norm_all (n : Nat) (h : Nat → Bool) (cs : List (List CNFLiteral)) :
    ClausesSatisfied cs (emit n h) ↔ source h (cs.map (normalize n)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => exact and_congr (norm_row _ _ _) ih

def normalized (bits : BitString) : List (List Lit) :=
  match decodeEncodedCNF bits with
  | none => [[]]
  | some f => f.clauses.map (normalize f.variableCount)

def targetRows (bits : BitString) : List (Row (Port Name)) := splitRows (macroRows (normalized bits))

def sourceWord (bits : BitString) (v : Port Name → G) : BitString :=
  match decodeEncodedCNF bits with
  | none => []
  | some f => emit f.variableCount (project (collapse (labels (tagged (macroRows (normalized bits)))) v))

theorem original_replay (bits : BitString) (v : Port Name → G) (ok : holds v (targetRows bits)) :
    ∃ f, decodeEncodedCNF bits = some f ∧ f.Satisfied (sourceWord bits v) := by
  have hit := macro_sound _ _ (split_project _ _ ok)
  cases e : decodeEncodedCNF bits with
  | none =>
    unfold normalized at hit; rw [e] at hit
    have no : true = false := hit.1; contradiction
  | some f =>
    refine ⟨f, rfl, ?_⟩
    unfold sourceWord; rw [e]
    constructor
    · exact emit_len _ _
    · apply (norm_all _ _ _).mpr
      have key : normalized bits = f.clauses.map (normalize f.variableCount) := by unfold normalized; rw [e]
      exact key ▸ hit

theorem raw_iff (bits : BitString) : CNFSAT bits ↔ feasible (targetRows bits) := by
  constructor
  · rintro ⟨f, hf, w, hw⟩
    obtain ⟨h, e⟩ := emit_all w
    have ew : emit f.variableCount h = w := hw.1 ▸ e
    have hh := hw.2
    rw [←ew] at hh
    have src : source h (normalized bits) := by
      unfold normalized; rw [hf]; exact (norm_all _ _ _).mp hh
    exact ⟨_, split_lift _ _ (macro_complete h _ src)⟩
  · rintro ⟨v, hv⟩; obtain ⟨f, hd, hw⟩ := original_replay _ _ hv
    exact ⟨f, hd, sourceWord bits v, hw⟩

end PNP.ThreeUse
