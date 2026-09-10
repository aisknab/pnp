/-
Copyright (c) 2026 PNP Labs.

A fixed finite table lookup over the newest unary register. Only the immutable
table and first key determine the program; the actual key is read from tape.
Every key, including absent keys, has an exact terminating physical run.
The selected row is written literally, and rejection restores the entire tape.

This is a compiler component for the fixed verifier's control-action table.
It must not be instantiated with a table depending on the source input.
-/

import PNP.Concrete.CookLevinBuilderRegisterPack
import PNP.Concrete.CookLevinBuilderUnaryTagMatch

namespace PNP.Concrete.CookLevin.BuilderRegisterTable

open BuilderUnaryPolynomial WorkMachineProgramGraph WorkMachineProgramPath
open BuilderDividerOperands (endTape)

def fields (row : List Nat) : List (BuilderRegisterPack.Field 0) :=
  row.map .constant

def emptyEnvironment : Fin 0 → Nat := Fin.elim0

theorem fields_values (row : List Nat) :
    BuilderRegisterPack.values (fields row) emptyEnvironment = row := by
  induction row with
  | nil => rfl
  | cons value rest ih =>
      simp only [fields, List.map_cons, BuilderRegisterPack.values, List.map_cons,
        BuilderRegisterPack.Field.eval, BuilderRegisterPack.Field.expression, BuilderRegisterExpression.eval]
      exact congrArg (List.cons value) ih

def rowMachine (row : List Nat) : WorkMachine := BuilderRegisterPack.machine (fields row) 0
def rowSteps (row : List Nat) : Nat := BuilderRegisterPack.workSteps (fields row) emptyEnvironment []
def rowSpan (row : List Nat) : Nat := (registerWord row).length

theorem row_workRunExact (row older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (rowMachine row) (rowSteps row)
      (workStartConfiguration (rowMachine row) (endTape older inside outside)) =
      some {
        state := (rowMachine row).acceptState
        tape := endTape (older ++ row) inside (outside.drop (rowSpan row)) } := by
  have h := BuilderRegisterPack.workRunExact (fields row) 0 older emptyEnvironment [] inside outside rfl
  have hEmpty : List.ofFn emptyEnvironment = [] := rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    hEmpty, List.append_nil, fields_values, rowMachine, rowSteps, rowSpan] using h

def writerNode (row : List Nat) : Node :=
  { name := 1, program := rowMachine row, onAccept := .accept, onReject := .dead }

def tailNode (next : WorkMachine) : Node :=
  { name := 2, program := next, onAccept := .accept, onReject := .reject }

def testNode (first : Nat) (row : List Nat) (next : WorkMachine) : Node :=
  { name := 0
    program := BuilderUnaryTagMatch.machine first
    onAccept := .node (writerNode row).reference
    onReject := .node (tailNode next).reference }

def branchGraph (first : Nat) (row : List Nat) (next : WorkMachine) : Graph :=
  { nodes := [testNode first row next, writerNode row, tailNode next]
    entry := (testNode first row next).reference }

def rejectMachine : WorkMachine :=
  { rules := [], startState := 1, acceptState := 0, rejectState := 1 }

def machine : List (List Nat) → Nat → WorkMachine
  | [], _ => rejectMachine
  | row :: rest, first => WorkMachineProgramGraph.machine (branchGraph first row (machine rest (first + 1)))

/-- Specification only. Runtime selection is the physical sequence of tag tests. -/
def lookup : List (List Nat) → Nat → Nat → Option (List Nat)
  | [], _, _ => none
  | row :: rest, first, actual => if actual = first then some row else lookup rest (first + 1) actual

def workSteps : List (List Nat) → Nat → Nat → Nat
  | [], _, _ => 0
  | row :: rest, first, actual =>
      BuilderUnaryTagMatch.workSteps first actual + 1 +
        ((if actual = first then rowSteps row else workSteps rest (first + 1) actual) + 1)

def resultEndpoint : Option (List Nat) → Endpoint
  | none => .reject
  | some _ => .accept

def resultState (program : WorkMachine) : Option (List Nat) → Nat
  | none => program.rejectState
  | some _ => program.acceptState

def resultTape (selected : Option (List Nat)) (older : List Nat) (actual : Nat)
    (inside outside : List WorkSymbol) : WorkTape :=
  match selected with
  | none => endTape (older ++ [actual]) inside outside
  | some row => endTape (older ++ [actual] ++ row) inside (outside.drop (rowSpan row))

def initialConfiguration (rows : List (List Nat)) (first actual : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine rows first) (endTape (older ++ [actual]) inside outside)

def finalConfiguration (rows : List (List Nat)) (first actual : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  { state := resultState (machine rows first) (lookup rows first actual)
    tape := resultTape (lookup rows first actual) older actual inside outside }

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise QueryDistinct ∧ NoRuleAt program program.acceptState ∧
    NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState

private theorem row_good (row : List Nat) : Good (rowMachine row) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct (fields row) 0,
    BuilderRegisterPack.noRuleAtAccept (fields row) 0,
    BuilderRegisterPack.noRuleAtReject (fields row) 0,
    BuilderRegisterPack.acceptState_ne_rejectState (fields row) 0⟩

private theorem branch_wellFormed (first : Nat) (row : List Nat) (next : WorkMachine)
    (hNext : Good next) : (branchGraph first row next).WellFormed := by
  have hTest : Good (BuilderUnaryTagMatch.machine first) :=
    ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct first,
      BuilderUnaryTagMatch.noRuleAtAccept first, BuilderUnaryTagMatch.noRuleAtReject first,
      BuilderUnaryTagMatch.acceptState_ne_rejectState first⟩
  have hNames : ((branchGraph first row next).nodes.map Node.name).Pairwise
      (fun left right : Nat => left ≠ right) := by
    change ([0, 1, 2] : List Nat).Pairwise (fun left right => left ≠ right)
    decide
  have hTestMem : testNode first row next ∈ (branchGraph first row next).nodes := List.Mem.head _
  have hWriterMem : writerNode row ∈ (branchGraph first row next).nodes := List.Mem.tail _ (List.Mem.head _)
  have hTailMem : tailNode next ∈ (branchGraph first row next).nodes :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [branchGraph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact hTest
    · exact row_good row
    · exact hNext
  · exact ⟨testNode first row next, hTestMem, rfl, rfl⟩
  · intro node hMem
    simp only [branchGraph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact ⟨⟨writerNode row, hWriterMem, rfl, rfl⟩, ⟨tailNode next, hTailMem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

private theorem good (rows : List (List Nat)) (first : Nat) : Good (machine rows first) := by
  induction rows generalizing first with
  | nil =>
      change Good rejectMachine
      refine ⟨List.Pairwise.nil, ?_, ?_, by decide⟩
      · intro rule hMem; cases hMem
      · intro rule hMem; cases hMem
  | cons row rest ih =>
      have h := branch_wellFormed first row (machine rest (first + 1)) (ih (first + 1))
      refine ⟨WorkMachineProgramGraph.rules_pairwise _ h,
        WorkMachineProgramGraph.noRuleAt_globalAccept _,
        WorkMachineProgramGraph.noRuleAt_globalReject _, ?_⟩
      change (0 : Nat) ≠ 1
      decide

private theorem graph_run (graph : Graph) (hGood : graph.WellFormed)
    (selected : Option (List Nat)) (steps : Nat) (initial final : WorkTape)
    (hPath : AcceptPath graph (.node graph.entry) (resultEndpoint selected) steps initial final) :
    workRunExact? (WorkMachineProgramGraph.machine graph) steps
      (workStartConfiguration (WorkMachineProgramGraph.machine graph) initial) =
      some { state := resultState (WorkMachineProgramGraph.machine graph) selected, tape := final } := by
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ hGood hPath
  have hInitial : endpointConfiguration (.node graph.entry) initial =
      workStartConfiguration (WorkMachineProgramGraph.machine graph) initial := rfl
  have hFinal : endpointConfiguration (resultEndpoint selected) final =
      { state := resultState (WorkMachineProgramGraph.machine graph) selected, tape := final } := by
    cases selected <;> rfl
  rw [hInitial, hFinal] at h
  exact h

theorem workRunExact (rows : List (List Nat)) (first actual : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? (machine rows first) (workSteps rows first actual)
      (initialConfiguration rows first actual older inside outside) =
      some (finalConfiguration rows first actual older inside outside) := by
  induction rows generalizing first with
  | nil => rfl
  | cons row rest ih =>
      let next := machine rest (first + 1)
      have hGood := branch_wellFormed first row next (good rest (first + 1))
      have hTestMem : testNode first row next ∈ (branchGraph first row next).nodes := List.Mem.head _
      have hWriterMem : writerNode row ∈ (branchGraph first row next).nodes := List.Mem.tail _ (List.Mem.head _)
      have hTailMem : tailNode next ∈ (branchGraph first row next).nodes :=
        List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      by_cases hEqual : actual = first
      · subst actual
        have hTest : LocalAcceptRun (testNode first row next) (BuilderUnaryTagMatch.workSteps first first)
            (endTape (older ++ [first]) inside outside) (endTape (older ++ [first]) inside outside) :=
          BuilderUnaryTagMatch.accept_workRunExact first older inside outside
        have hRow : LocalAcceptRun (writerNode row) (rowSteps row)
            (endTape (older ++ [first]) inside outside)
            (resultTape (some row) older first inside outside) :=
          row_workRunExact row (older ++ [first]) inside outside
        have hWriter := AcceptPath.step (writerNode row) .accept _ 0 _ _ _ hWriterMem hRow
          (AcceptPath.terminal .accept (resultTape (some row) older first inside outside))
        have hPath := AcceptPath.step (testNode first row next) .accept _ _ _ _ _ hTestMem hTest hWriter
        have hRun := graph_run (branchGraph first row next) hGood (some row) _ _ _ hPath
        simpa only [machine, next, workSteps, lookup, if_pos rfl, ite_true, Nat.add_zero,
          initialConfiguration, finalConfiguration, resultState] using hRun
      · have hTest : LocalRejectRun (testNode first row next) (BuilderUnaryTagMatch.workSteps first actual)
            (endTape (older ++ [actual]) inside outside) (endTape (older ++ [actual]) inside outside) :=
          BuilderUnaryTagMatch.reject_workRunExact first actual older inside outside hEqual
        have hNext := ih (first + 1)
        cases hSelected : lookup rest (first + 1) actual with
        | none =>
            have hLocal : LocalRejectRun (tailNode next) (workSteps rest (first + 1) actual)
                (endTape (older ++ [actual]) inside outside) (resultTape none older actual inside outside) := by
              simpa only [LocalRejectRun, tailNode, next, initialConfiguration, workStartConfiguration,
                finalConfiguration, hSelected, resultState] using hNext
            have hTail := AcceptPath.stepReject (tailNode next) .reject _ 0 _ _ _ hTailMem hLocal
              (AcceptPath.terminal .reject (resultTape none older actual inside outside))
            have hPath := AcceptPath.stepReject (testNode first row next) .reject _ _ _ _ _ hTestMem hTest hTail
            have hRun := graph_run (branchGraph first row next) hGood none _ _ _ hPath
            simpa only [machine, next, workSteps, lookup, if_neg hEqual, hSelected, Nat.add_zero,
              initialConfiguration, finalConfiguration, resultState] using hRun
        | some selected =>
            have hLocal : LocalAcceptRun (tailNode next) (workSteps rest (first + 1) actual)
                (endTape (older ++ [actual]) inside outside) (resultTape (some selected) older actual inside outside) := by
              simpa only [LocalAcceptRun, tailNode, next, initialConfiguration, workStartConfiguration,
                finalConfiguration, hSelected, resultState] using hNext
            have hTail := AcceptPath.step (tailNode next) .accept _ 0 _ _ _ hTailMem hLocal
              (AcceptPath.terminal .accept (resultTape (some selected) older actual inside outside))
            have hPath := AcceptPath.stepReject (testNode first row next) .accept _ _ _ _ _ hTestMem hTest hTail
            have hRun := graph_run (branchGraph first row next) hGood (some selected) _ _ _ hPath
            simpa only [machine, next, workSteps, lookup, if_neg hEqual, hSelected, Nat.add_zero,
              initialConfiguration, finalConfiguration, resultState] using hRun

theorem run_compile_exact (rows : List (List Nat)) (first actual : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine rows first)) (6 * workSteps rows first actual)
      (encodeWorkConfiguration (initialConfiguration rows first actual older inside outside)) =
      encodeWorkConfiguration (finalConfiguration rows first actual older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact rows first actual older inside outside)

theorem lookup_at (rows : List (List Nat)) (first index : Nat) (hIndex : index < rows.length) :
    lookup rows first (first + index) = some rows[index] := by
  induction rows generalizing first index with
  | nil => simp only [List.length_nil] at hIndex; omega
  | cons row rest ih =>
      cases index with
      | zero => simp only [Nat.add_zero, lookup, if_pos rfl, ite_true, List.getElem_cons_zero]
      | succ index =>
          have hRest : index < rest.length := by
            simp only [List.length_cons] at hIndex; omega
          have hNe : first + (index + 1) ≠ first := by omega
          simp only [lookup, if_neg hNe, List.getElem_cons_succ]
          rw [show first + (index + 1) = (first + 1) + index by omega]
          exact ih (first + 1) index hRest

theorem lookup_outside (rows : List (List Nat)) (first actual : Nat)
    (hOutside : actual < first ∨ first + rows.length ≤ actual) :
    lookup rows first actual = none := by
  induction rows generalizing first with
  | nil => rfl
  | cons row rest ih =>
      have hNe : actual ≠ first := by
        simp only [List.length_cons] at hOutside; omega
      rw [lookup, if_neg hNe]
      apply ih (first + 1)
      simp only [List.length_cons] at hOutside
      omega

theorem selected_workRunExact (rows : List (List Nat)) (first index : Nat) (hIndex : index < rows.length)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine rows first) (workSteps rows first (first + index))
      (initialConfiguration rows first (first + index) older inside outside) =
      some {
        state := (machine rows first).acceptState
        tape := endTape (older ++ [first + index] ++ rows[index]) inside (outside.drop (rowSpan rows[index])) } := by
  simpa only [finalConfiguration, lookup_at rows first index hIndex, resultState, resultTape] using
    workRunExact rows first (first + index) older inside outside

theorem rejected_workRunExact (rows : List (List Nat)) (first actual : Nat)
    (hOutside : actual < first ∨ first + rows.length ≤ actual)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine rows first) (workSteps rows first actual)
      (initialConfiguration rows first actual older inside outside) =
      some {
        state := (machine rows first).rejectState
        tape := endTape (older ++ [actual]) inside outside } := by
  simpa only [finalConfiguration, lookup_outside rows first actual hOutside, resultState, resultTape] using
    workRunExact rows first actual older inside outside

/-- A fixed table gives one input-independent finite runtime ceiling. -/
def workBound : List (List Nat) → Nat → Nat
  | [], _ => 0
  | row :: rest, first => (2 * first + 3) + 2 + rowSteps row + workBound rest (first + 1)

def tableSpan : List (List Nat) → Nat
  | [] => 0
  | row :: rest => rowSpan row + tableSpan rest

theorem workSteps_le (rows : List (List Nat)) (first actual : Nat) :
    workSteps rows first actual ≤ workBound rows first := by
  induction rows generalizing first with
  | nil => exact Nat.le_refl 0
  | cons row rest ih =>
      have hTest := BuilderUnaryTagMatch.workSteps_le first actual
      have hRest := ih (first + 1)
      simp only [workSteps, workBound]
      split <;> omega

theorem selected_span_le (rows : List (List Nat)) (first actual : Nat) :
    rowSpan ((lookup rows first actual).getD []) ≤ tableSpan rows := by
  induction rows generalizing first with
  | nil => exact Nat.le_refl 0
  | cons row rest ih =>
      have hRest := ih (first + 1)
      simp only [lookup, tableSpan]
      split
      · simp only [Option.getD_some]; omega
      · omega

def spanPolynomial (rows : List (List Nat)) (bound : NatPolynomial) : NatPolynomial :=
  .add bound (.constant (tableSpan rows))

def rawTimePolynomial (rows : List (List Nat)) (first : Nat) : NatPolynomial :=
  .constant (6 * workBound rows first)

theorem source_polynomial_bounds (rows : List (List Nat)) (first actual : Nat)
    (older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [actual])).length ≤ bound.eval inputLength) :
    (registerWord (older ++ [actual] ++ (lookup rows first actual).getD [])).length ≤
        (spanPolynomial rows bound).eval inputLength ∧
      6 * workSteps rows first actual ≤ (rawTimePolynomial rows first).eval inputLength := by
  have hOutput := selected_span_le rows first actual
  have hTime := workSteps_le rows first actual
  simp only [spanPolynomial, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant,
    registerWord_append, List.length_append] at *
  constructor <;> unfold rowSpan at hOutput <;> omega

theorem final_exterior_length_le (rows : List (List Nat)) (first actual : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration rows first actual older inside outside).tape.left.length ≤ outside.length := by
  cases h : lookup rows first actual <;>
    simp only [finalConfiguration, h, resultTape, endTape, List.length_drop] <;> omega

theorem rules_pairwise_query_distinct (rows : List (List Nat)) (first : Nat) :
    (machine rows first).rules.Pairwise QueryDistinct := (good rows first).1

theorem noRuleAtAccept (rows : List (List Nat)) (first : Nat) :
    NoRuleAt (machine rows first) (machine rows first).acceptState := (good rows first).2.1

theorem noRuleAtReject (rows : List (List Nat)) (first : Nat) :
    NoRuleAt (machine rows first) (machine rows first).rejectState := (good rows first).2.2.1

theorem acceptState_ne_rejectState (rows : List (List Nat)) (first : Nat) :
    (machine rows first).acceptState ≠ (machine rows first).rejectState := (good rows first).2.2.2

end PNP.Concrete.CookLevin.BuilderRegisterTable
