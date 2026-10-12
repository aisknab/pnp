/-
Copyright (c) 2026 PNP Labs.

Complete correctness of suffix-based path reconstruction. The theorem
covers arbitrary finite traces, including duplicates and dangling parents,
without assuming acyclicity, a supplied path, or a successful search.
-/
import PNP.Concrete.NormalizerPathSemantics

namespace PNP.Concrete.NormalizerBlocks.TracePath

theorem accumulated_follow (prior : List CNFLiteral) (target : CNFLiteral) (path : Option (List CNFLiteral)) :
    PathData.answer (path.map (fun route => (prior ++ [target]) ++ route)) =
      PathData.answer ((path.map (List.cons target)).map (fun route => prior ++ route)) := by
  cases path <;> simp only [Option.map_none, Option.map_some, List.append_assoc, List.cons_append, List.nil_append]

theorem scan_canonical (fuel : Nat) (r : State) (target : CNFLiteral) (trace : List TraceData.Row)
    (prior : List CNFLiteral)
    (indexRead : r.core.targetIndex = List.replicate target.variableIndex true)
    (tagRead : ForwardEdge.present r.core.targetTag = target.positive)
    (traceRead : r.core.pending = TraceData.encode trace)
    (initialAnswer : r.core.output = [false])
    (bufferRead : r.buffer = (PathData.encode prior).reverse)
    (enough : r.core.pending.length < fuel) :
    observation (scan fuel r).state =
      PathData.answer ((value trace target).map (fun route => prior ++ route)) := by
  induction trace generalizing fuel r target prior with
  | nil =>
      rw [scan_empty fuel r traceRead]
      unfold observation
      rw [initialAnswer]
      rfl
  | cons entry rest ih =>
      have nonempty : r.core.pending ≠ [] := by
        rw [traceRead]
        change (entry.1.positive :: _) ≠ []
        intro h
        cases h
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          rw [scan_step fuel r nonempty]
          have remaining : (bodyResult r).core.pending.length < fuel := by
            have shorter := body_shorter r nonempty
            omega
          cases found : TraceMember.same entry.1 target with
          | false =>
              have same : bodyResult r = probed r := by
                rw [body_on_row r target entry (TraceData.encode rest) indexRead tagRead traceRead, found]
                rfl
              have row := probed_canonical r target entry (TraceData.encode rest) indexRead tagRead traceRead
              have preserved := probed_preserves r
              have targetIndex : (bodyResult r).core.targetIndex = List.replicate target.variableIndex true := by
                rw [same, preserved.1, indexRead]
              have targetTag : ForwardEdge.present (bodyResult r).core.targetTag = target.positive := by
                rw [same, preserved.2.1, tagRead]
              have next : (bodyResult r).core.pending = TraceData.encode rest := by rw [same, row.2.1]
              have answer : (bodyResult r).core.output = [false] := by rw [same, preserved.2.2.1, initialAnswer]
              have buffer : (bodyResult r).buffer = (PathData.encode prior).reverse := by rw [same, preserved.2.2.2.2.2, bufferRead]
              have checked := ih fuel (bodyResult r) target prior targetIndex targetTag next answer buffer remaining
              simpa only [value, found, Bool.false_eq_true, ite_false] using checked
          | true =>
              have nodeEqual : entry.1 = target := (TraceMember.same_true_iff _ _).1 found
              rcases entry with ⟨node, parent⟩
              change node = target at nodeEqual
              subst node
              cases parent with
              | none =>
                  have row := body_row_root r target (TraceData.encode rest) indexRead tagRead traceRead
                  rw [scan_empty fuel (bodyResult r) row.1]
                  unfold observation
                  rw [row.2.1]
                  change true :: (bodyResult r).buffer.reverse = _
                  rw [row.2.2, bufferRead, append_accumulator, List.reverse_reverse]
                  simp only [value, found, ite_true, Option.map_some, PathData.answer]
              | some parent =>
                  have row := body_row_parent r target parent (TraceData.encode rest) indexRead tagRead traceRead
                  have answer := row.2.2.2.1.trans initialAnswer
                  have buffer : (bodyResult r).buffer = (PathData.encode (prior ++ [target])).reverse := by
                    rw [row.2.2.2.2, bufferRead, append_accumulator]
                  have checked := ih fuel (bodyResult r) parent (prior ++ [target]) row.2.1 row.2.2.1 row.1 answer buffer remaining
                  rw [accumulated_follow] at checked
                  simpa only [value, found, ite_true] using checked

theorem whole_canonical (r : State) (target : CNFLiteral) (trace : List TraceData.Row)
    (indexRead : r.core.targetIndex = List.replicate target.variableIndex true)
    (tagRead : ForwardEdge.present r.core.targetTag = target.positive)
    (traceRead : r.core.pending = TraceData.encode trace)
    (initialAnswer : r.core.output = [false]) (bufferRead : r.buffer = []) :
    observation (whole r).state = PathData.answer (value trace target) := by
  have checked := scan_canonical _ r target trace [] indexRead tagRead traceRead initialAnswer bufferRead (Nat.lt_succ_self _)
  cases result : value trace target <;>
    simpa only [whole, result, Option.map_none, Option.map_some, List.nil_append] using checked

end PNP.Concrete.NormalizerBlocks.TracePath
