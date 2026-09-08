/-
Copyright (c) 2026 PNP Labs.

Erase every discarded register after a fixed retained root prefix, regardless of
the length or values of the computed history. The existing source-root locator
marks the actual boundary; a fixed four-rule eraser stops at that marker.
The retained registers and arbitrary interior survive. Exactly the discarded
word is replaced by exterior blanks. This is scratch recovery, not a token
selector, complete source loop, or packaged Cook-Levin reduction.
-/
import PNP.Concrete.CookLevinBuilderRegisterRootCopy

namespace PNP.Concrete.CookLevin.BuilderRegisterRootErase

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderRegisterCountdownControl (counterMarker markedTape)

private def rule (source target : Nat) (read write : WorkSymbol) (move : HeadMove) : WorkRule :=
  {sourceState := source, targetState := target, readSymbol := read, writeSymbol := write, move := move}

def eraser : WorkMachine :=
  {rules := [rule 0 1 scratchEndSymbol .blank .right,
    rule 1 1 unitSymbol .blank .right, rule 1 1 separatorSymbol .blank .right,
    rule 1 2 counterMarker scratchEndSymbol .stay], startState := 0, acceptState := 2, rejectState := 3}

theorem eraser_rules_length : eraser.rules.length = 4 := rfl

private def scanTape (word inside outside : List WorkSymbol) : WorkTape :=
  match word with
  | [] => {left := outside, head := counterMarker, right := inside}
  | symbol :: rest => {left := outside, head := symbol, right := rest ++ counterMarker :: inside}

private theorem compose {program : WorkMachine} {n m : Nat} {a b c : WorkConfiguration}
    (first : workRunExact? program n a = some b) (second : workRunExact? program m b = some c) :
    workRunExact? program (n + m) a = some c :=
  PipelineMachineSimulation.workRunExact?_compose program n m a b c first second
private theorem one_step {program : WorkMachine} {a b : WorkConfiguration}
    (step : workStep? program a = some b) : workRunExact? program 1 a = some b := by
  simp only [workRunExact?, step]

private theorem scan_run (word : List WorkSymbol)
    (hSymbols : ∀ symbol ∈ word, symbol = unitSymbol ∨ symbol = separatorSymbol)
    (inside outside : List WorkSymbol) :
    workRunExact? eraser (word.length + 1) {state := 1, tape := scanTape word inside outside} =
      some {state := eraser.acceptState,
            tape := {left := List.replicate word.length WorkSymbol.blank ++ outside,
                     head := scratchEndSymbol, right := inside}} := by
  induction word generalizing outside with
  | nil => rfl
  | cons symbol rest ih =>
      have hSymbol := hSymbols symbol (List.Mem.head _)
      have hRest : ∀ next ∈ rest, next = unitSymbol ∨ next = separatorSymbol := by
        intro next hNext
        exact hSymbols next (List.Mem.tail _ hNext)
      have hStep : workStep? eraser {state := 1, tape := scanTape (symbol :: rest) inside outside} =
          some {state := 1, tape := scanTape rest inside (WorkSymbol.blank :: outside)} := by
        rcases hSymbol with rfl | rfl <;> cases rest <;> rfl
      have hTail := ih hRest (WorkSymbol.blank :: outside)
      have h := compose (one_step hStep) hTail
      have hClock : 1 + (rest.length + 1) = (symbol :: rest).length + 1 := by
        simp only [List.length_cons]
        omega
      rw [hClock] at h
      simpa only [List.length_cons, List.replicate_succ', List.replicate_one,
        List.append_assoc, List.cons_append, List.nil_append] using h

def discardedSpan (value : Nat) (after : List Nat) : Nat := (registerWord ([value] ++ after)).length
def eraseSteps (value : Nat) (after : List Nat) : Nat := discardedSpan value after + 1

theorem discardedSpan_eq (value : Nat) (after : List Nat) :
    discardedSpan value after = value + (registerWord after).length + 1 := by
  simp only [discardedSpan, registerWord_append, List.length_append, registerWord,
    List.length_cons, List.length_nil, List.length_replicate, List.length_append]
  omega

theorem eraser_workRunExact (value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? eraser (eraseSteps value after)
      (workStartConfiguration eraser (markedTape 0 value after inside outside)) =
      some {state := eraser.acceptState,
            tape := {left := List.replicate (discardedSpan value after) WorkSymbol.blank ++ outside,
                     head := scratchEndSymbol, right := inside}} := by
  let word := (registerWord after).reverse ++ List.replicate value unitSymbol
  have hStart : workStep? eraser (workStartConfiguration eraser (markedTape 0 value after inside outside)) =
      some {state := 1, tape := scanTape word inside (WorkSymbol.blank :: outside)} := by
    have hTape : markedTape 0 value after inside outside =
        {left := outside, head := scratchEndSymbol, right := word ++ counterMarker :: inside} := by
      simp only [markedTape, word, List.replicate_zero, List.append_nil, List.append_assoc]
    rw [hTape]
    cases hWord : word <;> rfl
  have hSymbols : ∀ symbol ∈ word, symbol = unitSymbol ∨ symbol = separatorSymbol := by
    intro symbol hSymbol
    simp only [word, List.mem_append, List.mem_reverse] at hSymbol
    rcases hSymbol with hWord | hUnit
    · exact BuilderRegisterAccess.registerWord_symbols after symbol hWord
    · exact Or.inl (List.eq_of_mem_replicate hUnit)
  have hTail := scan_run word hSymbols inside (WorkSymbol.blank :: outside)
  have h := compose (one_step hStart) hTail
  have hLength : word.length + 1 = discardedSpan value after := by
    simp only [word, List.length_append, List.length_reverse, List.length_replicate, discardedSpan_eq]
    omega
  have hClock : 1 + (word.length + 1) = eraseSteps value after := by
    rw [eraseSteps, ← hLength]
    omega
  rw [hClock] at h
  have hOutside : List.replicate word.length WorkSymbol.blank ++ WorkSymbol.blank :: outside =
      List.replicate (discardedSpan value after) WorkSymbol.blank ++ outside := by
    rw [← hLength, List.replicate_succ']
    simp only [List.replicate_one, List.append_assoc, List.cons_append, List.nil_append]
  rw [hOutside] at h
  exact h

theorem eraser_control :
    eraser.rules.Pairwise WorkMachineChain.QueryDistinct ∧ WorkMachineChain.NoRuleAtAccept eraser ∧
      WorkMachineProgramGraph.NoRuleAt eraser eraser.rejectState ∧ eraser.acceptState ≠ eraser.rejectState := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · unfold WorkMachineChain.QueryDistinct
    decide
  · intro item h
    decide +revert
  · intro item h
    decide +revert

def machine (beforeCount : Nat) : WorkMachine :=
  WorkMachineChain.machine (BuilderRegisterRootCopy.markProgram beforeCount) eraser
def workSteps (before : List Nat) (value : Nat) (after : List Nat) : Nat :=
  BuilderRegisterRootCopy.markSteps before value after + 1 + eraseSteps value after
def initialConfiguration (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine beforeCount) (endTape (before ++ [value] ++ after) (leftMarker :: inside) outside)
def finalConfiguration (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  {state := (machine beforeCount).acceptState,
   tape := endTape before (leftMarker :: inside) (List.replicate (discardedSpan value after) WorkSymbol.blank ++ outside)}

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

theorem workRunExact (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) (hLength : before.length = beforeCount) :
    workRunExact? (machine beforeCount) (workSteps before value after)
      (initialConfiguration beforeCount before value after inside outside) =
      some (finalConfiguration beforeCount before value after inside outside) := by
  have hMark := BuilderRegisterRootCopy.mark_workRunExact beforeCount before value after inside outside hLength
  have hErase := eraser_workRunExact value after ((registerWord before).reverse ++ leftMarker :: inside) outside
  have h := chain_run (BuilderRegisterRootCopy.markProgram beforeCount) eraser
    (BuilderRegisterRootCopy.markSteps before value after) (eraseSteps value after) _ _ _ hMark hErase
  exact h

theorem run_compile_exact (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) (hLength : before.length = beforeCount) :
    run (compileWorkMachine (machine beforeCount)) (6 * workSteps before value after)
      (encodeWorkConfiguration (initialConfiguration beforeCount before value after inside outside)) =
      encodeWorkConfiguration (finalConfiguration beforeCount before value after inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact beforeCount before value after inside outside hLength)

theorem final_tape (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration beforeCount before value after inside outside).tape =
      endTape before (leftMarker :: inside) (List.replicate (discardedSpan value after) WorkSymbol.blank ++ outside) := rfl
theorem final_accept (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration beforeCount before value after inside outside).state = (machine beforeCount).acceptState := rfl
theorem final_span_eq (before : List Nat) (value : Nat) (after : List Nat) (outside : List WorkSymbol) :
    (registerWord before).length + (List.replicate (discardedSpan value after) WorkSymbol.blank ++ outside).length =
      (registerWord (before ++ [value] ++ after)).length + outside.length := by
  simp only [discardedSpan, registerWord_append, List.length_append, List.length_replicate]
  omega

theorem workSteps_le (before : List Nat) (value : Nat) (after : List Nat) (bound : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length ≤ bound) :
    workSteps before value after ≤ 4 * bound + 7 := by
  have hBefore : before.length ≤ (registerWord before).length := by
    rw [registerWord_length]
    omega
  have hSpan' := hSpan
  simp only [registerWord_append, List.length_append, registerWord, List.length_cons,
    List.length_nil, List.length_replicate, List.length_append] at hSpan'
  have hBeforeWord := registerWord_length before
  simp only [workSteps, BuilderRegisterRootCopy.markSteps, BuilderRegisterRootCopy.skipSteps_closed,
    eraseSteps, discardedSpan_eq, registerWord_append, List.length_append, registerWord,
    List.length_cons, List.length_nil, List.length_replicate, List.length_append]
  omega

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 6) (.add (.mul (.constant 4) bound) (.constant 7))

theorem source_polynomial_bounds (before : List Nat) (value : Nat) (after : List Nat) (outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length + outside.length ≤ bound.eval input) :
    (registerWord before).length + (List.replicate (discardedSpan value after) WorkSymbol.blank ++ outside).length ≤
        bound.eval input ∧
      6 * workSteps before value after ≤ (rawTimePolynomial bound).eval input := by
  have hTime := workSteps_le before value after (bound.eval input) (by omega)
  constructor
  · rw [final_span_eq]
    exact hSpan
  · simp only [rawTimePolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

private theorem good (beforeCount : Nat) :
    (machine beforeCount).rules.Pairwise WorkMachineChain.QueryDistinct ∧
      WorkMachineChain.NoRuleAtAccept (machine beforeCount) ∧
      WorkMachineProgramGraph.NoRuleAt (machine beforeCount) (machine beforeCount).rejectState ∧
      (machine beforeCount).acceptState ≠ (machine beforeCount).rejectState :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ (BuilderRegisterRootCopy.mark_control beforeCount).1
      eraser_control.1 (BuilderRegisterRootCopy.mark_control beforeCount).2.1,
   WorkMachineChain.noRuleAtAccept _ _ eraser_control.2.1,
   WorkMachineChain.noRuleAtAccept (BuilderRegisterRootCopy.markProgram beforeCount)
     {eraser with acceptState := eraser.rejectState} eraser_control.2.2.1,
   WorkMachineChain.machine_acceptState_ne_rejectState _ _ eraser_control.2.2.2⟩
theorem rules_pairwise_query_distinct (beforeCount : Nat) :
    (machine beforeCount).rules.Pairwise WorkMachineChain.QueryDistinct := (good beforeCount).1
theorem noRuleAtAccept (beforeCount : Nat) : WorkMachineChain.NoRuleAtAccept (machine beforeCount) := (good beforeCount).2.1
theorem noRuleAtReject (beforeCount : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine beforeCount) (machine beforeCount).rejectState := (good beforeCount).2.2.1
theorem acceptState_ne_rejectState (beforeCount : Nat) :
    (machine beforeCount).acceptState ≠ (machine beforeCount).rejectState := (good beforeCount).2.2.2

end PNP.Concrete.CookLevin.BuilderRegisterRootErase
