/-
Copyright (c) 2026 PNP Labs.

Exact arbitrary-path semantics for the pair decoder. The accumulator
invariant retains source order and proves stopping at the first invalid
pair, including a final unmatched variable.
-/
import PNP.Concrete.NormalizerPairScan

namespace PNP.Concrete.NormalizerBlocks.PathPairs

def nextVertices : List CNFLiteral → List CNFLiteral
  | ⟨false, _⟩ :: ⟨true, _⟩ :: rest => rest
  | _ => []
def headUpdates : List CNFLiteral → List (Nat × Nat)
  | ⟨false, variableIndex⟩ :: ⟨true, clauseIndex⟩ :: _ => [(clauseIndex, variableIndex)]
  | _ => []

theorem value_split (xs : List CNFLiteral) : value xs = headUpdates xs ++ value (nextVertices xs) := by
  cases xs with
  | nil => rfl
  | cons first rest =>
      rcases first with ⟨tag, index⟩
      cases tag with
      | true => rfl
      | false =>
          cases rest with
          | nil => rfl
          | cons second tail =>
              rcases second with ⟨tag, index⟩
              cases tag <;> rfl

theorem encodeUpdates_append (first second : List (Nat × Nat)) :
    TableBatch.encodeUpdates (first ++ second) =
      TableBatch.encodeUpdates first ++ TableBatch.encodeUpdates second := by
  induction first with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨index, value⟩
      simp only [List.cons_append, TableBatch.encodeUpdates, TableBatch.encodePair, ih,
        List.append_assoc, List.cons_append]

theorem body_canonical (r : State) (xs : List CNFLiteral) (nonempty : xs ≠ [])
    (pending : r.pending = PathData.encode xs) :
    (bodyResult r).pending = PathData.encode (nextVertices xs) ∧
      (bodyResult r).buffer = (TableBatch.encodeUpdates (headUpdates xs)).reverse ++ r.buffer := by
  cases xs with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      rcases first with ⟨tag, index⟩
      cases tag with
      | true =>
          have stopRead : bodyResult r = stopped r := by unfold bodyResult; rw [pending]; rfl
          rw [stopRead]
          exact ⟨rfl, rfl⟩
      | false =>
          have firstReadFields := firstRead_canonical r ⟨false, index⟩ (PathData.encode rest) pending
          have firstCase : bodyResult r = firstProcessed r := by unfold bodyResult; rw [pending]; rfl
          rw [firstCase]
          cases rest with
          | nil =>
              have tagRead : ForwardEdge.present (firstRead r).core.input = false := by rw [firstReadFields.1]; rfl
              simp only [firstProcessed, secondChosen, tagRead, Bool.false_eq_true, ite_false]
              exact ⟨rfl, firstReadFields.2.2⟩
          | cons second tail =>
              rcases second with ⟨tag, clause⟩
              cases tag with
              | false =>
                  have tagRead : ForwardEdge.present (firstRead r).core.input = false := by rw [firstReadFields.1]; rfl
                  simp only [firstProcessed, secondChosen, tagRead, Bool.false_eq_true, ite_false]
                  exact ⟨rfl, firstReadFields.2.2⟩
              | true =>
                  have tagRead : ForwardEdge.present (firstRead r).core.input = true := by rw [firstReadFields.1]; rfl
                  simp only [firstProcessed, secondChosen, tagRead, ite_true]
                  have pair := pairProcessed_canonical (firstRead r) clause index (PathData.encode tail)
                    firstReadFields.1 firstReadFields.2.1
                  exact ⟨pair.1, pair.2.trans (congrArg
                    (fun b => (TableBatch.encodePair clause index []).reverse ++ b) firstReadFields.2.2)⟩

theorem encode_empty (xs : List CNFLiteral) (empty : PathData.encode xs = []) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons first rest => cases empty

theorem scan_buffer (fuel : Nat) (r : State) (xs : List CNFLiteral)
    (pending : r.pending = PathData.encode xs)
    (enough : r.pending.length < fuel ∨ r.pending = []) :
    (scan fuel r).state.buffer = (TableBatch.encodeUpdates (value xs)).reverse ++ r.buffer := by
  induction fuel generalizing r xs with
  | zero =>
      have empty := enough.resolve_left (Nat.not_lt_zero _)
      have sourceEmpty := encode_empty xs (pending.symm.trans empty)
      subst xs
      rfl
  | succ fuel ih =>
      cases xs with
      | nil =>
          have empty : r.pending = [] := pending
          rw [scan_empty _ r empty]
          rfl
      | cons first rest =>
          have nonempty : r.pending ≠ [] := by rw [pending]; intro h; cases h
          have size : r.pending.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => exact False.elim (nonempty h)
          have nextEnough := Nat.lt_of_lt_of_le (body_shorter r nonempty) size
          have current := body_canonical r (first :: rest) (by intro h; cases h) pending
          have tail := ih (bodyResult r) (nextVertices (first :: rest)) current.1 (Or.inl nextEnough)
          rw [scan_step _ r nonempty]
          change (scan fuel (bodyResult r)).state.buffer = _
          rw [tail, current.2, value_split (first :: rest), encodeUpdates_append, List.reverse_append, List.append_assoc]

theorem whole_buffer (r : State) (xs : List CNFLiteral) (pending : r.pending = PathData.encode xs) :
    (whole r).state.buffer = (TableBatch.encodeUpdates (value xs)).reverse ++ r.buffer :=
  scan_buffer _ r xs pending (Or.inl (Nat.lt_succ_self _))

end PNP.Concrete.NormalizerBlocks.PathPairs
