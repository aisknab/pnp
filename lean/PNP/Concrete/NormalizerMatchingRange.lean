/-
Copyright (c) 2026 PNP Labs.

The generated search trace stays in the original finite vertex universe.
This invariant does not depend on the current table's byte length and
therefore remains useful across every round of the matching driver.
-/
import PNP.Concrete.NormalizerSearchPolynomial
import PNP.Concrete.NormalizerAugmentationPolynomial

namespace PNP.Concrete.NormalizerBlocks.MatchingLoop
open ExplorationData

private theorem find_member {α : Type} (test : α → Bool) (xs : List α) (found : α)
    (chosen : xs.find? test = some found) : found ∈ xs := by
  induction xs with
  | nil => cases chosen
  | cons first rest ih =>
      cases selected : test first with
      | true =>
          have same : first = found := Option.some.inj (by
            simpa only [List.find?, selected] using chosen)
          rw [← same]
          exact List.mem_cons_self
      | false =>
          have tail : rest.find? test = some found := by
            simpa only [List.find?, selected] using chosen
          exact List.mem_cons_of_mem first (ih tail)

theorem parent_within (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) (parent : Option CNFLiteral)
    (selected : ParentQuery.value target clauses entries trace = some parent) :
    Extraction.ParentWithin trace parent := by
  intro vertex same
  cases root : RootKinds.value target entries with
  | true =>
      have absent : none = parent := Option.some.inj (by
        simpa only [ParentQuery.value, root, ite_true] using selected)
      rw [← absent] at same
      cases same
  | false =>
      cases choice : trace.find? (fun entry => EdgeKinds.value entry.1 target clauses entries) with
      | none =>
          simp only [ParentQuery.value, root, Bool.false_eq_true, ite_false, choice,
            Option.map_none] at selected
          cases selected
      | some entry =>
          have parentEq : some entry.1 = parent := Option.some.inj (by
            simpa only [ParentQuery.value, root, Bool.false_eq_true, ite_false, choice,
              Option.map_some] using selected)
          exact ⟨entry, find_member _ trace entry choice, Option.some.inj (parentEq.trans same)⟩

theorem eligibility_within (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) (parent : Option CNFLiteral)
    (selected : Eligibility.value target clauses entries trace = some parent) :
    Extraction.ParentWithin trace parent := by
  cases seen : TraceMember.value target trace with
  | true =>
      simp only [Eligibility.value, seen, ite_true] at selected
      cases selected
  | false =>
      exact parent_within target clauses entries trace parent (by
        simpa only [Eligibility.value, seen, Bool.false_eq_true, ite_false] using selected)

theorem extraction_range (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (trace : List TraceData.Row) (unseen : List CNFLiteral)
    (vertex : CNFLiteral) (parent : Option CNFLiteral) (rest : List CNFLiteral)
    (selected : Extraction.value clauses entries trace unseen = some ((vertex, parent), rest)) :
    Removes vertex unseen rest ∧ Extraction.ParentWithin trace parent := by
  induction unseen generalizing vertex parent rest with
  | nil => cases selected
  | cons first tail ih =>
      cases eligible : Eligibility.value first clauses entries trace with
      | some ancestor =>
          have same : ((first, ancestor), tail) = ((vertex, parent), rest) := Option.some.inj (by
            simpa only [Extraction.value, eligible] using selected)
          have origin := eligibility_within first clauses entries trace ancestor eligible
          have removed : Removes first (first :: tail) tail := .head tail
          cases same
          exact ⟨removed, origin⟩
      | none =>
          cases next : Extraction.value clauses entries trace tail with
          | none =>
              simp only [Extraction.value, eligible, next, Option.map_none] at selected
              cases selected
          | some found =>
              rcases found with ⟨⟨node, ancestor⟩, suffix⟩
              have same : ((node, ancestor), first :: suffix) = ((vertex, parent), rest) :=
                Option.some.inj (by
                  simpa only [Extraction.value, eligible, next, Option.map_some] using selected)
              have prior := ih node ancestor suffix next
              have removed := Removes.skip first prior.1
              have origin := prior.2
              cases same
              exact ⟨removed, origin⟩

theorem exploration_range (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (fuel limit : Nat) (unseen : List CNFLiteral) (trace : List TraceData.Row)
    (vertices : VerticesBound limit unseen) (rows : TraceBound limit trace) :
    TraceBound limit (Exploration.value clauses entries fuel unseen trace) ∧
      (Exploration.value clauses entries fuel unseen trace).length ≤ trace.length + fuel := by
  induction fuel generalizing unseen trace with
  | zero => exact ⟨rows, Nat.le_refl _⟩
  | succ fuel ih =>
      cases choice : Extraction.value clauses entries trace unseen with
      | none =>
          simp only [Exploration.value, choice]
          exact ⟨rows, Nat.le_add_right _ _⟩
      | some found =>
          rcases found with ⟨⟨vertex, parent⟩, rest⟩
          have range := extraction_range clauses entries trace unseen vertex parent rest choice
          have nextRows := Exploration.trace_cons_bound vertices rows range.1 range.2
          have next := ih rest ((vertex, parent) :: trace) (range.1.bounds limit vertices).2 nextRows
          simp only [Exploration.value, choice]
          refine ⟨next.1, ?_⟩
          have length := next.2
          rw [List.length_cons] at length
          omega

theorem search_trace_range (variables : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) :
    TraceBound (clauses.length + variables) (Search.traceValue variables clauses entries) ∧
      (Search.traceValue variables clauses entries).length ≤ clauses.length + variables := by
  simpa only [Search.traceValue, List.length_nil, Nat.zero_add] using
    exploration_range clauses entries (clauses.length + variables) (clauses.length + variables)
    (SearchVertices.vertices clauses.length variables) []
    (Exploration.range_vertices_bound clauses.length variables)
    (by intro entry member; cases member)

end PNP.Concrete.NormalizerBlocks.MatchingLoop
