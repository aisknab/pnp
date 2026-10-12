/-
Copyright (c) 2026 PNP Labs.

A matching update never adds rows or introduces an index outside the
generated search universe. These bounds hold for any number of rounds;
they are not obtained by iterating a growing per-call size estimate.
-/
import PNP.Concrete.NormalizerMatchingRange

namespace PNP.Concrete.NormalizerBlocks.MatchingLoop
open ExplorationData

theorem path_range (limit : Nat) (trace : List TraceData.Row)
    (rows : TraceBound limit trace) (target : CNFLiteral) (path : List CNFLiteral)
    (selected : TracePath.value trace target = some path) :
    VerticesBound limit path ∧ path.length ≤ trace.length := by
  induction trace generalizing target path with
  | nil => cases selected
  | cons entry rest ih =>
      have older : TraceBound limit rest := fun row member => rows row (List.mem_cons_of_mem entry member)
      cases same : TraceMember.same entry.1 target with
      | false =>
          have prior := ih older target path (by
            simpa only [TracePath.value, same, Bool.false_eq_true, ite_false] using selected)
          exact ⟨prior.1, Nat.le_trans prior.2 (Nat.le_succ _)⟩
      | true =>
          have targetEq := (TraceMember.same_true_iff entry.1 target).1 same
          have headBound : target.variableIndex ≤ limit := by
            rw [← targetEq]
            exact (rows entry List.mem_cons_self).1
          cases parent : entry.2 with
          | none =>
              have shape : [target] = path := Option.some.inj (by
                simpa only [TracePath.value, same, ite_true, parent] using selected)
              rw [← shape]
              refine ⟨?_, ?_⟩
              · intro vertex member
                have equal : vertex = target := List.mem_singleton.mp member
                rw [equal]
                exact headBound
              · simp only [List.length_cons, List.length_nil]; omega
          | some next =>
              cases found : TracePath.value rest next with
              | none =>
                  simp only [TracePath.value, same, ite_true, parent, found, Option.map_none] at selected
                  cases selected
              | some suffix =>
                  have shape : target :: suffix = path := Option.some.inj (by
                    simpa only [TracePath.value, same, ite_true, parent, found, Option.map_some] using selected)
                  have prior := ih older next suffix found
                  rw [← shape]
                  refine ⟨?_, Nat.succ_le_succ prior.2⟩
                  intro vertex member
                  cases List.mem_cons.mp member with
                  | inl equal => rw [equal]; exact headBound
                  | inr tail => exact prior.1 vertex tail

theorem path_default_range (limit : Nat) (trace : List TraceData.Row)
    (rows : TraceBound limit trace) (target : CNFLiteral) :
    VerticesBound limit ((TracePath.value trace target).getD []) ∧
      ((TracePath.value trace target).getD []).length ≤ trace.length := by
  cases found : TracePath.value trace target with
  | none =>
      constructor
      · intro vertex member; cases member
      · exact Nat.zero_le _
  | some path => exact path_range limit trace rows target path found

private theorem pairs_range_aux (fuel limit : Nat) (xs : List CNFLiteral)
    (size : xs.length ≤ fuel) (vertices : VerticesBound limit xs) :
    ∀ pair, pair ∈ PathPairs.value xs → pair.2 ≤ limit := by
  induction fuel generalizing xs with
  | zero =>
      cases xs with
      | nil => intro pair member; cases member
      | cons first rest => simp only [List.length_cons] at size; omega
  | succ fuel ih =>
      cases xs with
      | nil => intro pair member; cases member
      | cons first rest =>
          rcases first with ⟨tag, index⟩
          cases tag with
          | true => intro pair member; cases member
          | false =>
              cases rest with
              | nil => intro pair member; cases member
              | cons second tail =>
                  rcases second with ⟨tag, other⟩
                  cases tag with
                  | false => intro pair member; cases member
                  | true =>
                      have headBound := vertices ⟨false,index⟩ List.mem_cons_self
                      have tailBound : VerticesBound limit tail := fun vertex member =>
                        vertices vertex (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
                      have tailSize : tail.length ≤ fuel := by
                        simp only [List.length_cons] at size
                        omega
                      have prior := ih tail tailSize tailBound
                      intro pair member
                      cases List.mem_cons.mp member with
                      | inl equal => rw [equal]; exact headBound
                      | inr member => exact prior pair member

theorem pairs_range (limit : Nat) (xs : List CNFLiteral) (vertices : VerticesBound limit xs) :
    ∀ pair, pair ∈ PathPairs.value xs → pair.2 ≤ limit :=
  pairs_range_aux xs.length limit xs (Nat.le_refl _) vertices

def EntriesBound (limit : Nat) (entries : MatchingTable.Entries) : Prop :=
  ∀ value, some value ∈ entries → value ≤ limit

theorem empty_bound (count limit : Nat) : EntriesBound limit (List.replicate count none) := by
  intro value member
  have same : some value = (none : Option Nat) := (List.mem_replicate.mp member).2
  cases same

theorem write_bound (limit : Nat) (entries : MatchingTable.Entries) (index value : Nat)
    (bounded : EntriesBound limit entries) (newBound : value ≤ limit) :
    EntriesBound limit (MatchingTable.write entries index value) := by
  induction entries generalizing index with
  | nil => intro found member; cases member
  | cons first rest ih =>
      have tailBound : EntriesBound limit rest := fun found member =>
        bounded found (List.mem_cons_of_mem first member)
      cases index with
      | zero =>
          intro found member
          cases List.mem_cons.mp member with
          | inl same => rw [Option.some.inj same]; exact newBound
          | inr tail => exact tailBound found tail
      | succ index =>
          have prior := ih index tailBound
          intro found member
          cases List.mem_cons.mp member with
          | inl same => exact bounded found (List.mem_cons.mpr (Or.inl same))
          | inr tail => exact prior found tail

theorem writeAll_bound (limit : Nat) (entries : MatchingTable.Entries)
    (updates : List (Nat × Nat)) (bounded : EntriesBound limit entries)
    (newBounds : ∀ pair, pair ∈ updates → pair.2 ≤ limit) :
    EntriesBound limit (MatchingTable.writeAll entries updates) := by
  induction updates generalizing entries with
  | nil => exact bounded
  | cons pair rest ih =>
      exact ih (MatchingTable.write entries pair.1 pair.2)
        (write_bound limit entries pair.1 pair.2 bounded (newBounds pair List.mem_cons_self))
        (fun item member => newBounds item (List.mem_cons_of_mem pair member))

theorem search_augmentation_bound (variables : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (index : Nat) (path : List CNFLiteral)
    (bounded : EntriesBound (clauses.length + variables) entries)
    (selected : Search.value variables clauses entries = .augment index path) :
    EntriesBound (clauses.length + variables) (MatchingTable.writeAll entries (PathPairs.value path)) ∧
      (MatchingTable.writeAll entries (PathPairs.value path)).length = entries.length ∧
      path.length ≤ clauses.length + variables := by
  have trace := search_trace_range variables clauses entries
  cases candidate : Candidate.selectFrom entries (SeenTrace.value (Search.traceValue variables clauses entries)) variables 0 with
  | none =>
      simp only [Search.value, candidate] at selected
      cases selected
  | some chosen =>
      have shape : (TracePath.value (Search.traceValue variables clauses entries) ⟨false,chosen⟩).getD [] = path := by
        have eq : Search.Output.augment chosen
            ((TracePath.value (Search.traceValue variables clauses entries) ⟨false,chosen⟩).getD []) =
            Search.Output.augment index path := by simpa only [Search.value, candidate] using selected
        exact Search.Output.augment.inj eq |>.2
      have route := path_default_range (clauses.length + variables)
        (Search.traceValue variables clauses entries) trace.1 ⟨false,chosen⟩
      rw [shape] at route
      exact ⟨writeAll_bound _ entries _ bounded (pairs_range _ path route.1),
        MatchingTable.writeAll_length entries _, Nat.le_trans route.2 trace.2⟩

end PNP.Concrete.NormalizerBlocks.MatchingLoop
