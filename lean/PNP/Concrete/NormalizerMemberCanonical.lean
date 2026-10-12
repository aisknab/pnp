/-
Copyright (c) 2026 PNP Labs.

Complete signed-node membership in arbitrary finite predecessor traces.
The finite loop matches the source node-membership operation, including
duplicate nodes and rows carrying optional predecessor metadata.
-/

import PNP.Concrete.NormalizerMemberScan

namespace PNP.Concrete.NormalizerBlocks.TraceMember

open BitRegister

def value (target : CNFLiteral) (trace : List TraceData.Row) : Bool :=
  trace.any (fun entry => same entry.1 target)

theorem scan_canonical (fuel : Nat) (r : State) (target : CNFLiteral) (trace : List TraceData.Row)
    (indexRead : r.targetIndex = List.replicate target.variableIndex true)
    (tagRead : ForwardEdge.present r.targetTag = target.positive)
    (traceRead : r.pending = TraceData.encode trace)
    (initialAnswer : r.output = [false]) (enough : r.pending.length < fuel) :
    (scan fuel r).state.output = [value target trace] := by
  induction trace generalizing fuel r with
  | nil =>
      rw [scan_empty fuel r traceRead]
      exact initialAnswer
  | cons entry rest ih =>
      have nonempty : r.pending ≠ [] := by
        rw [traceRead]
        change (entry.1.positive :: _) ≠ []
        intro h
        cases h
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          rw [scan_step fuel r nonempty]
          have row := body_row r target entry (TraceData.encode rest) indexRead tagRead traceRead
          cases found : same entry.1 target with
          | false =>
              have next : (bodyResult r).pending = TraceData.encode rest := by
                simpa only [found, Bool.false_eq_true, ite_false] using row.1
              have answerRead : (bodyResult r).output = [false] := by
                have sameOutput : (bodyResult r).output = r.output := by
                  simpa only [found, Bool.false_eq_true, ite_false] using row.2
                exact sameOutput.trans initialAnswer
              have shorter : (bodyResult r).pending.length < r.pending.length := by
                rw [next, ← TraceData.next_canonical entry (TraceData.encode rest)]
                change (TraceData.next (TraceData.encode (entry :: rest))).length < _
                rw [← traceRead]
                exact TraceData.next_shorter _ nonempty
              have remaining : (bodyResult r).pending.length < fuel := by omega
              have targetIndex := (body_preserves r).1.trans indexRead
              have targetTag : ForwardEdge.present (bodyResult r).targetTag = target.positive := by
                rw [(body_preserves r).2.1]
                exact tagRead
              have checked := ih fuel (bodyResult r) targetIndex targetTag next answerRead remaining
              simpa only [value, List.any_cons, found, Bool.false_or] using checked
          | true =>
              have stopped : (bodyResult r).pending = [] := by simpa only [found, ite_true] using row.1
              rw [scan_empty fuel (bodyResult r) stopped]
              simpa only [value, List.any_cons, found, Bool.true_or, ite_true] using row.2

theorem whole_canonical (r : State) (target : CNFLiteral) (trace : List TraceData.Row)
    (indexRead : r.targetIndex = List.replicate target.variableIndex true)
    (tagRead : ForwardEdge.present r.targetTag = target.positive)
    (traceRead : r.pending = TraceData.encode trace) (initialAnswer : r.output = [false]) :
    (whole r).state.output = [value target trace] :=
  scan_canonical _ r target trace indexRead tagRead traceRead initialAnswer (Nat.lt_succ_self _)

def phase : Block 21 := .seq ParentQuery.defaultAnswer loop
def phaseResult (r : State) : State := (whole (ParentQuery.defaulted r)).state
def phaseFuel (r : State) : Nat := 2 + (whole (ParentQuery.defaulted r)).fuel

theorem phase_exec (r : State) : Exec phase r.store (phaseFuel r) (phaseResult r).store :=
  Exec.seq (ParentQuery.defaultAnswer_exec r) (whole_exec (ParentQuery.defaulted r))
theorem phaseFuel_bound (r : State) :
    phaseFuel r ≤ (28 * r.pending.length + 81) * (r.pending.length + 1) + 3 := by
  have bound := whole_fuel_bound (ParentQuery.defaulted r)
  change (whole (ParentQuery.defaulted r)).fuel ≤ (28 * r.pending.length + 81) * (r.pending.length + 1) + 1 at bound
  unfold phaseFuel
  omega
theorem phase_stopped (r : State) : (phaseResult r).pending = [] := whole_stopped (ParentQuery.defaulted r)
theorem phase_preserves (r : State) :
    (phaseResult r).targetIndex = r.targetIndex ∧ (phaseResult r).targetTag = r.targetTag ∧
      (phaseResult r).graph.core.formula = r.graph.core.formula ∧
        (phaseResult r).graph.core.matching = r.graph.core.matching :=
  scan_preserves _ (ParentQuery.defaulted r)
theorem phase_canonical (r : State) (target : CNFLiteral) (trace : List TraceData.Row)
    (indexRead : r.targetIndex = List.replicate target.variableIndex true)
    (tagRead : ForwardEdge.present r.targetTag = target.positive)
    (traceRead : r.pending = TraceData.encode trace) :
    (phaseResult r).output = [value target trace] :=
  whole_canonical (ParentQuery.defaulted r) target trace indexRead tagRead traceRead rfl

end PNP.Concrete.NormalizerBlocks.TraceMember
