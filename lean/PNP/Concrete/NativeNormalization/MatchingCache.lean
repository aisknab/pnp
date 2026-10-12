import PNP.Concrete.NativeNormalization.MatchingUpdate

namespace PNP.Concrete.NativeNormalization.MatchingCache

open Matching

/-- Materialized matchings prevent repeating an entire search when a function is read. -/
structure Table (c n : Nat) where
  entries : List (Option (Fin n))
  length_eq : entries.length = c

def Table.get (T : Table c n) (i : Fin c) : Option (Fin n) :=
  T.entries[i.val]'(by rw [T.length_eq]; exact i.isLt)

def Table.ofFunction (m : Fin c → Option (Fin n)) : Table c n :=
  ⟨List.ofFn m, List.length_ofFn⟩

theorem Table.get_ofFunction (m : Fin c → Option (Fin n)) :
    (Table.ofFunction m).get = m := by
  funext i
  simp [Table.get, Table.ofFunction]

def finishTable (incidence : Fin c → Fin n → Bool) : Nat → Table c n → Table c n
  | 0, T => T
  | fuel + 1, T =>
      match search incidence T.get with
      | .terminal _ => T
      | .augment _ path =>
          finishTable incidence fuel (Table.ofFunction (augment (readPairs path) T.get))

theorem finishTable_eq (incidence : Fin c → Fin n → Bool) (fuel : Nat)
    (T : Table c n) :
    (finishTable incidence fuel T).get = finish incidence fuel T.get := by
  induction fuel generalizing T with
  | zero => rfl
  | succ fuel ih =>
      simp only [finishTable, finish]
      split
      · rename_i tr h
        rw [h]
      · rename_i v path h
        rw [h, ih, Table.get_ofFunction]

def fullTable (incidence : Fin c → Fin n → Bool) : Table c n :=
  finishTable incidence (c+1) (Table.ofFunction (fun _ => none))

theorem fullTable_get (incidence : Fin c → Fin n → Bool) :
    (fullTable incidence).get = fullMatching incidence := by
  simp only [fullTable, finishTable_eq, Table.get_ofFunction, fullMatching]

theorem fullTable_entries (incidence : Fin c → Fin n → Bool) :
    (fullTable incidence).entries = List.ofFn (fullMatching incidence) := by
  apply List.ext_getElem
  · rw [(fullTable incidence).length_eq, List.length_ofFn]
  · intro i hi hj
    have bound : i < c := by simpa only [List.length_ofFn] using hj
    have eq := congrFun (fullTable_get incidence) (⟨i,bound⟩ : Fin c)
    simpa only [Table.get, List.getElem_ofFn] using eq


end PNP.Concrete.NativeNormalization.MatchingCache
