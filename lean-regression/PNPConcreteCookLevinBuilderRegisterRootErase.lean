import PNP.Concrete.CookLevinBuilderRegisterRootErase

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderRegisterRootErase
open BuilderUnaryPolynomial (registerWord unitSymbol separatorSymbol scratchEndSymbol)
open BuilderDividerOperands (endTape)

-- Numerical cases are fixtures; the execution contract below has an unbounded tail.
example : eraser.rules.length = 4 := eraser_rules_length
example : discardedSpan 0 [] = 1 := rfl
example : discardedSpan 3 [0, 2] = 8 := rfl
example (value : Nat) (after : List Nat) :
    discardedSpan value after = value + (registerWord after).length + 1 := discardedSpan_eq value after
example : workSteps [] 0 [] = 10 := rfl
example : workSteps [] 1 [] = 13 := rfl
example : workSteps [0] 0 [] = 14 := rfl
example : workSteps [2] 1 [3] = 33 := rfl
example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) (hLength : before.length = beforeCount) :
    workRunExact? (machine beforeCount) (workSteps before value after)
      (initialConfiguration beforeCount before value after inside outside) =
      some (finalConfiguration beforeCount before value after inside outside) :=
  workRunExact beforeCount before value after inside outside hLength
example (value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine 0) (workSteps [] value after)
      (initialConfiguration 0 [] value after inside outside) =
      some (finalConfiguration 0 [] value after inside outside) :=
  workRunExact 0 [] value after inside outside rfl
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
example (before : List Nat) (value count repeated : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine before.length) (workSteps before value (List.replicate count repeated))
      (initialConfiguration before.length before value (List.replicate count repeated) inside outside) =
      some (finalConfiguration before.length before value (List.replicate count repeated) inside outside) :=
  workRunExact before.length before value (List.replicate count repeated) inside outside rfl
example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (inside outside : List WorkSymbol) (hLength : before.length = beforeCount) :
    run (compileWorkMachine (machine beforeCount)) (6 * workSteps before value after)
      (encodeWorkConfiguration (initialConfiguration beforeCount before value after inside outside)) =
      encodeWorkConfiguration (finalConfiguration beforeCount before value after inside outside) :=
  run_compile_exact beforeCount before value after inside outside hLength
example (value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? eraser (eraseSteps value after)
      (workStartConfiguration eraser (BuilderRegisterCountdownControl.markedTape 0 value after inside outside)) =
      some {state := eraser.acceptState,
            tape := {left := List.replicate (discardedSpan value after) WorkSymbol.blank ++ outside,
                     head := scratchEndSymbol, right := inside}} :=
  eraser_workRunExact value after inside outside
example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration beforeCount before value after inside outside).tape =
      endTape before (PipelineTape.leftMarker :: inside) (List.replicate (discardedSpan value after) WorkSymbol.blank ++ outside) :=
  final_tape beforeCount before value after inside outside
example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration beforeCount before value after inside outside).tape.right =
      (registerWord before).reverse ++ PipelineTape.leftMarker :: inside := rfl
example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration beforeCount before value after inside outside).state = (machine beforeCount).acceptState :=
  final_accept beforeCount before value after inside outside
example (before : List Nat) (value : Nat) (after : List Nat) (outside : List WorkSymbol) :
    (registerWord before).length + (List.replicate (discardedSpan value after) WorkSymbol.blank ++ outside).length =
      (registerWord (before ++ [value] ++ after)).length + outside.length :=
  final_span_eq before value after outside
example (before : List Nat) (value : Nat) (after : List Nat) (bound : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length ≤ bound) :
    workSteps before value after ≤ 4 * bound + 7 := workSteps_le before value after bound hSpan
example (before : List Nat) (value : Nat) (after : List Nat) (outside : List WorkSymbol)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length + outside.length ≤ bound.eval inputLength) :
    (registerWord before).length + (List.replicate (discardedSpan value after) WorkSymbol.blank ++ outside).length ≤
        bound.eval inputLength ∧
      6 * workSteps before value after ≤ (rawTimePolynomial bound).eval inputLength :=
  source_polynomial_bounds before value after outside bound inputLength hSpan

-- The machine has no valid unmarked-stop rule or hidden acceptance transition.
example : workStep? eraser {state := 1, tape := {left := [], head := PipelineTape.leftMarker, right := []}} = none := rfl
example : workStep? eraser {state := 0, tape := {left := [], head := unitSymbol, right := []}} = none := rfl
example : eraser.rules.Pairwise WorkMachineChain.QueryDistinct ∧ WorkMachineChain.NoRuleAtAccept eraser ∧
    WorkMachineProgramGraph.NoRuleAt eraser eraser.rejectState ∧ eraser.acceptState ≠ eraser.rejectState := eraser_control
example (beforeCount : Nat) : (machine beforeCount).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct beforeCount
example (beforeCount : Nat) : WorkMachineChain.NoRuleAtAccept (machine beforeCount) := noRuleAtAccept beforeCount
example (beforeCount : Nat) : WorkMachineProgramGraph.NoRuleAt (machine beforeCount) (machine beforeCount).rejectState :=
  noRuleAtReject beforeCount
example (beforeCount : Nat) : (machine beforeCount).acceptState ≠ (machine beforeCount).rejectState :=
  acceptState_ne_rejectState beforeCount
