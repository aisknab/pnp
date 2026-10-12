import PNP.Concrete.NativeNormalization.MeasuredExplore
import PNP.Concrete.NativeNormalization.MatchingCache
import PNP.Concrete.NativeNormalization.CNFCore

namespace PNP.Concrete.NativeNormalization.MeasuredMatching

open PNP.Concrete Matching MatchingCache MeasuredReach

/-- Each recursive list visit is charged; index-word representation is a later boundary. -/
def lookup : List α → Nat → Measured (Option α)
  | [], _ => ⟨none,1⟩
  | a::_, 0 => ⟨some a,1⟩
  | _::xs, k+1 =>
      let tail := lookup xs k
      ⟨tail.value,tail.cost+1⟩

theorem lookup_value (xs : List α) (k : Nat) :
    (lookup xs k).value = xs[k]? := by
  induction xs generalizing k with
  | nil => rfl
  | cons a xs ih =>
      cases k with
      | zero => rfl
      | succ k => simpa [lookup] using ih k

theorem lookup_cost (xs : List α) (k : Nat) :
    (lookup xs k).cost ≤ xs.length+1 := by
  induction xs generalizing k with
  | nil => simp [lookup]
  | cons a xs ih =>
      cases k with
      | zero => simp [lookup]
      | succ k =>
          have h := ih k
          simp only [lookup, List.length_cons]
          omega

def readMatching (T : Table c n) (i : Fin c) : Measured (Option (Fin n)) :=
  let found := lookup T.entries i.val
  ⟨found.value.getD none, found.cost+1⟩

theorem readMatching_value (T : Table c n) (i : Fin c) :
    (readMatching T i).value = T.get i := by
  have hi : i.val < T.entries.length := by rw [T.length_eq]; exact i.isLt
  simp [readMatching, lookup_value, List.getElem?_eq_getElem hi, Table.get]

theorem readMatching_cost (T : Table c n) (i : Fin c) :
    (readMatching T i).cost ≤ c+2 := by
  have h := lookup_cost T.entries i.val
  rw [T.length_eq] at h
  simp only [readMatching]
  omega

def readClause (F : CNFFormula) (i : Fin F.clauses.length) : Measured (List CNFLiteral) :=
  let found := lookup F.clauses i.val
  ⟨found.value.getD [],found.cost+1⟩

theorem readClause_value (F : CNFFormula) (i : Fin F.clauses.length) :
    (readClause F i).value = CNFCore.clause F i := by
  simp [readClause, lookup_value, CNFCore.clause]

theorem readClause_cost (F : CNFFormula) (i : Fin F.clauses.length) :
    (readClause F i).cost ≤ F.clauses.length+2 := by
  have h := lookup_cost F.clauses i.val
  simp only [readClause]
  omega

def incidence (F : CNFFormula) (i : Fin F.clauses.length) (v : Fin F.variableCount) :
    Measured Bool :=
  let clause := readClause F i
  let found := MeasuredReach.find (fun l : CNFLiteral => ⟨l.variableIndex == v.val,1⟩) clause.value
  ⟨found.value.isSome,clause.cost+found.cost+1⟩

theorem incidence_value (F : CNFFormula) (i : Fin F.clauses.length) (v : Fin F.variableCount) :
    (incidence F i v).value = CNFCore.incidence F i v := by
  simp only [incidence, MeasuredReach.find_value, readClause_value,
    CNFCore.incidence, CNFCore.occurrence]

theorem incidence_cost (F : CNFFormula) (i : Fin F.clauses.length)
    (v : Fin F.variableCount) (L : Nat)
    (hl : (CNFCore.clause F i).length ≤ L) :
    (incidence F i v).cost ≤ F.clauses.length+2*L+4 := by
  have hc := readClause_cost F i
  have hf := MeasuredReach.find_cost
    (fun l : CNFLiteral => (⟨l.variableIndex == v.val,1⟩ : Measured Bool))
    (readClause F i).value 1 (fun _ => Nat.le_refl _)
  rw [readClause_value] at hf
  simp only [incidence, readClause_value]
  omega

def seed (T : Table c n) : Vertex c n → Measured Bool
  | .inl i =>
      let entry := readMatching T i
      ⟨entry.value.isNone,entry.cost+1⟩
  | .inr _ => ⟨false,1⟩

theorem seed_value (T : Table c n) (v : Vertex c n) :
    (seed T v).value = Matching.roots T.get v := by
  cases v <;> simp [seed, readMatching_value, Matching.roots]

theorem seed_cost (T : Table c n) (v : Vertex c n) : (seed T v).cost ≤ c+3 := by
  cases v with
  | inl i =>
      have h := readMatching_cost T i
      simp only [seed]
      omega
  | inr v => simp [seed]

def edge (F : CNFFormula) (T : Table F.clauses.length F.variableCount) :
    Vertex F.clauses.length F.variableCount → Vertex F.clauses.length F.variableCount → Measured Bool
  | .inl i, .inr v =>
      let incident := incidence F i v
      let entry := readMatching T i
      ⟨incident.value && !(entry.value == some v),incident.cost+entry.cost+3⟩
  | .inr v, .inl i =>
      let entry := readMatching T i
      ⟨entry.value == some v,entry.cost+1⟩
  | _, _ => ⟨false,1⟩

theorem edge_value (F : CNFFormula) (T : Table F.clauses.length F.variableCount)
    (a b : Vertex F.clauses.length F.variableCount) :
    (edge F T a b).value = Matching.alternating (CNFCore.incidence F) T.get a b := by
  cases a <;> cases b <;>
    simp only [edge, incidence_value, readMatching_value, Matching.alternating]

theorem edge_cost (F : CNFFormula) (T : Table F.clauses.length F.variableCount)
    (hl : ∀ i, (CNFCore.clause F i).length ≤ 3)
    (a b : Vertex F.clauses.length F.variableCount) :
    (edge F T a b).cost ≤ 2*F.clauses.length+15 := by
  cases a with
  | inl i =>
      cases b with
      | inl j => simp [edge]
      | inr v =>
          have hi := incidence_cost F i v 3 (hl i)
          have hm := readMatching_cost T i
          simp only [edge]
          omega
  | inr v =>
      cases b with
      | inl i =>
          have hm := readMatching_cost T i
          simp only [edge]
          omega
      | inr w => simp [edge]

def scan (F : CNFFormula) (T : Table F.clauses.length F.variableCount) :
    Measured (Trace (Vertex F.clauses.length F.variableCount)) :=
  MeasuredReach.explore (seed T) (edge F T) (F.clauses.length+F.variableCount)
    (Matching.vertices F.clauses.length F.variableCount) []

theorem scan_value (F : CNFFormula) (T : Table F.clauses.length F.variableCount) :
    (scan F T).value = Matching.scan (CNFCore.incidence F) T.get := by
  simp only [scan, MeasuredReach.explore_value, seed_value, edge_value, Matching.scan]

/-- Complete graph-pass source work, including linear matching and literal lookups.
It excludes construction of the input table, word encoding and concrete machine simulation. -/
theorem scan_cost (F : CNFFormula) (T : Table F.clauses.length F.variableCount)
    (hl : ∀ i, (CNFCore.clause F i).length ≤ 3) :
    (scan F T).cost ≤
      (F.clauses.length+F.variableCount) *
        ((((2*F.clauses.length+15+3)*(F.clauses.length+F.variableCount)+
          (F.clauses.length+3)+7)*(F.clauses.length+F.variableCount))+2)+1 := by
  apply MeasuredReach.explore_cost (seed T) (edge F T)
    (F.clauses.length+3) (2*F.clauses.length+15)
    (seed_cost T) (edge_cost F T hl)
  · simp [Matching.vertices]
  · simp


end PNP.Concrete.NativeNormalization.MeasuredMatching
