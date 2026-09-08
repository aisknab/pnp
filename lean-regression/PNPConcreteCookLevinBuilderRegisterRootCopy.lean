import PNP.Concrete.CookLevinBuilderRegisterRootCopy

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderRegisterRootCopy
open BuilderUnaryPolynomial (registerWord unitSymbol separatorSymbol scratchEndSymbol)
open BuilderDividerOperands (endTape)

-- Fixed root ordinals; arbitrary runtime register values and newer histories.
example : skipSteps [] = 0 := rfl
example : skipSteps [0] = 3 := rfl
example : skipSteps [2, 0, 3] = 14 := rfl
example (before : List Nat) : skipSteps before = before.sum + 3 * before.length := skipSteps_closed before
example : workSteps [] 0 [] = 19 := rfl
example : workSteps [] 1 [] = 38 := rfl
example : workSteps [0] 0 [] = 23 := rfl
example : workSteps [2] 1 [3] = 70 := rfl
example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) (hBefore : before.length = beforeCount) :
    workRunExact? (machine beforeCount) (workSteps before value after)
      (initialConfiguration beforeCount before value after inside outside) =
      some (finalConfiguration beforeCount before value after inside outside) :=
  workRunExact beforeCount before value after inside outside hBefore
example (value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine 0) (workSteps [] value after) (initialConfiguration 0 [] value after inside outside) =
      some (finalConfiguration 0 [] value after inside outside) :=
  workRunExact 0 [] value after inside outside rfl
example (first value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine 1) (workSteps [first] value after)
      (initialConfiguration 1 [first] value after inside outside) =
      some (finalConfiguration 1 [first] value after inside outside) :=
  workRunExact 1 [first] value after inside outside rfl
example (first second value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine 2) (workSteps [first, second] value after)
      (initialConfiguration 2 [first, second] value after inside outside) =
      some (finalConfiguration 2 [first, second] value after inside outside) :=
  workRunExact 2 [first, second] value after inside outside rfl
example (before : List Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine before.length) (workSteps before 0 after)
      (initialConfiguration before.length before 0 after inside outside) =
      some (finalConfiguration before.length before 0 after inside outside) :=
  workRunExact before.length before 0 after inside outside rfl
example (before : List Nat) (value : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine before.length) (workSteps before value [])
      (initialConfiguration before.length before value [] inside outside) =
      some (finalConfiguration before.length before value [] inside outside) :=
  workRunExact before.length before value [] inside outside rfl
example (before : List Nat) (value extra : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine before.length) (workSteps before value (List.replicate extra 0))
      (initialConfiguration before.length before value (List.replicate extra 0) inside outside) =
      some (finalConfiguration before.length before value (List.replicate extra 0) inside outside) :=
  workRunExact before.length before value (List.replicate extra 0) inside outside rfl
example (before : List Nat) (value : Nat) (after : List Nat) :
    workRunExact? (machine before.length) (workSteps before value after)
      (initialConfiguration before.length before value after [scratchEndSymbol, separatorSymbol]
        [unitSymbol, PipelineTape.leftMarker, .blank]) =
      some (finalConfiguration before.length before value after [scratchEndSymbol, separatorSymbol]
        [unitSymbol, PipelineTape.leftMarker, .blank]) :=
  workRunExact before.length before value after _ _ rfl
example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) (hBefore : before.length = beforeCount) :
    run (compileWorkMachine (machine beforeCount)) (6 * workSteps before value after)
      (encodeWorkConfiguration (initialConfiguration beforeCount before value after inside outside)) =
      encodeWorkConfiguration (finalConfiguration beforeCount before value after inside outside) :=
  run_compile_exact beforeCount before value after inside outside hBefore
example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration beforeCount before value after inside outside).tape =
      endTape (before ++ [value] ++ after ++ [value]) (PipelineTape.leftMarker :: inside) (outside.drop (value + 1)) :=
  final_tape beforeCount before value after inside outside
example (beforeCount : Nat) (before : List Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration beforeCount before 0 after inside outside).tape.left = outside.drop 1 := rfl
example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration beforeCount before value after inside []).tape.left = [] := rfl
example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration beforeCount before value after inside outside).state = (machine beforeCount).acceptState := rfl
example : workStep? seekMachine {state := 0, tape := {left := [], head := unitSymbol, right := []}} = none := rfl
example : workStep? skipOneMachine {state := 0, tape := {left := [], head := unitSymbol, right := []}} = none := rfl
example (beforeCount : Nat) : (machine beforeCount).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct beforeCount
example (beforeCount : Nat) : WorkMachineChain.NoRuleAtAccept (machine beforeCount) := noRuleAtAccept beforeCount
example (beforeCount : Nat) : WorkMachineProgramGraph.NoRuleAt (machine beforeCount) (machine beforeCount).rejectState :=
  noRuleAtReject beforeCount
example (beforeCount : Nat) : (machine beforeCount).acceptState ≠ (machine beforeCount).rejectState :=
  acceptState_ne_rejectState beforeCount
example (before : List Nat) (value : Nat) (after : List Nat) (bound : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length ≤ bound) :
    workSteps before value after ≤ workBound bound := workSteps_le before value after bound hSpan
example (before : List Nat) (value : Nat) (after : List Nat) (outside : List WorkSymbol) (bound : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length + outside.length ≤ bound) :
    (registerWord (before ++ [value] ++ after ++ [value])).length + (outside.drop (value + 1)).length ≤ 2 * bound + 1 :=
  final_span_le before value after outside bound hSpan
example (before : List Nat) (value : Nat) (after : List Nat) (outside : List WorkSymbol)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length + outside.length ≤ bound.eval inputLength) :
    (registerWord (before ++ [value] ++ after ++ [value])).length + (outside.drop (value + 1)).length ≤
        (spanPolynomial bound).eval inputLength ∧
      6 * workSteps before value after ≤ (rawTimePolynomial bound).eval inputLength :=
  source_polynomial_bounds before value after outside bound inputLength hSpan

-- Boundary marking is shared with general scratch recovery.
example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) (hLength : before.length = beforeCount) :
    workRunExact? (markProgram beforeCount) (markSteps before value after)
      (workStartConfiguration (markProgram beforeCount)
        (endTape (before ++ [value] ++ after) (PipelineTape.leftMarker :: inside) outside)) =
      some {state := (markProgram beforeCount).acceptState,
            tape := BuilderRegisterCountdownControl.markedTape 0 value after
              ((registerWord before).reverse ++ PipelineTape.leftMarker :: inside) outside} :=
  mark_workRunExact beforeCount before value after inside outside hLength
example (beforeCount : Nat) :
    (markProgram beforeCount).rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept (markProgram beforeCount) ∧
    WorkMachineProgramGraph.NoRuleAt (markProgram beforeCount) (markProgram beforeCount).rejectState ∧
    (markProgram beforeCount).acceptState ≠ (markProgram beforeCount).rejectState := mark_control beforeCount
