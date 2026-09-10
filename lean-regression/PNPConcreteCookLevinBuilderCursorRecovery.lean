/- Regression contracts for actual root erasure and return-to-cursor execution. -/
import PNP.Concrete.CookLevinBuilderCursorRecovery

namespace PNP.Concrete.CookLevin.BuilderCursorRecoveryRegression

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderRequestedPairLookup (BlankExterior storedCells)
open BuilderCursorRecovery

example : returnMachine.rules.length = 4 :=
  BuilderCursorRecovery.return_rules_length

example (before : List Nat) (head : WorkSymbol) (tail outside : List WorkSymbol) :
    workRunExact? returnMachine ((registerWord before).length + 2)
      (workStartConfiguration returnMachine (endTape before (leftMarker :: head :: tail) outside)) =
      some {
        state := returnMachine.acceptState
        tape := BuilderRegisterAccess.sourceTape head tail (registerWord before) outside
      } :=
  BuilderCursorRecovery.return_workRunExact before head tail outside

example :
    returnMachine.rules.Pairwise WorkMachineChain.QueryDistinct ∧
      WorkMachineChain.NoRuleAtAccept returnMachine ∧
      WorkMachineProgramGraph.NoRuleAt returnMachine returnMachine.rejectState ∧
      returnMachine.acceptState ≠ returnMachine.rejectState :=
  BuilderCursorRecovery.return_control

example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside : List WorkSymbol) (hLength : before.length = beforeCount) :
    workRunExact? (machine beforeCount) (workSteps before value after)
      (initialConfiguration beforeCount before value after head tail outside) =
      some (finalConfiguration beforeCount before value after head tail outside) :=
  BuilderCursorRecovery.workRunExact beforeCount before value after head tail outside hLength

example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside : List WorkSymbol) (hLength : before.length = beforeCount) :
    run (compileWorkMachine (machine beforeCount)) (6 * workSteps before value after)
      (encodeWorkConfiguration (initialConfiguration beforeCount before value after head tail outside)) =
      encodeWorkConfiguration (finalConfiguration beforeCount before value after head tail outside) :=
  BuilderCursorRecovery.run_compile_exact beforeCount before value after head tail outside hLength

example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside : List WorkSymbol) :
    (finalConfiguration beforeCount before value after head tail outside).tape.head = head ∧
      (finalConfiguration beforeCount before value after head tail outside).tape.right = tail :=
  BuilderCursorRecovery.final_head_and_tail beforeCount before value after head tail outside

example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside : List WorkSymbol) :
    storedCells (finalConfiguration beforeCount before value after head tail outside).tape =
      storedCells (initialConfiguration beforeCount before value after head tail outside).tape :=
  BuilderCursorRecovery.final_storedCells beforeCount before value after head tail outside

example (value : Nat) (after : List Nat) (outside : List WorkSymbol)
    (hBlank : BlankExterior outside) : BlankExterior (clearedOutside value after outside) :=
  BuilderCursorRecovery.clearedOutside_blank value after outside hBlank

example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside expectedOutside : List WorkSymbol)
    (hBlank : BlankExterior outside) (hExpected : BlankExterior expectedOutside) :
    WorkTape.BlankEquivalent (finalConfiguration beforeCount before value after head tail outside).tape
      (BuilderRegisterAccess.sourceTape head tail (registerWord before) expectedOutside) :=
  BuilderCursorRecovery.final_blankEquivalent beforeCount before value after head tail outside expectedOutside hBlank hExpected

example (before : List Nat) (value : Nat) (after : List Nat) (bound : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length ≤ bound) :
    workSteps before value after ≤ 5 * bound + 10 :=
  BuilderCursorRecovery.workSteps_le before value after bound hSpan

example (beforeCount : Nat) (before : List Nat) (value : Nat) (after : List Nat)
    (head : WorkSymbol) (tail outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (before ++ [value] ++ after)).length + outside.length ≤ bound.eval input) :
    storedCells (finalConfiguration beforeCount before value after head tail outside).tape ≤
        tail.length + 2 + bound.eval input ∧
      6 * workSteps before value after ≤ (rawTimePolynomial bound).eval input :=
  BuilderCursorRecovery.source_polynomial_bounds beforeCount before value after head tail outside bound input hSpan

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    (BuilderOperandRegisters.retainedValues problem index remaining).length = rootCount problem.verifier :=
  BuilderCursorRecovery.retainedValues_length problem index remaining

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    recoveredCursorTape problem index remaining output (BuilderCursorSource.preservedTail problem) =
      BuilderCursorSource.cursorTape problem index remaining output :=
  BuilderCursorRecovery.recovered_original_cursor problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (value : Nat) (after : List Nat) (outside : List WorkSymbol) :
    workRunExact? (machine (rootCount problem.verifier))
      (workSteps (BuilderOperandRegisters.retainedValues problem index remaining) value after)
      (workStartConfiguration (machine (rootCount problem.verifier))
        (endTape (BuilderOperandRegisters.retainedValues problem index remaining ++ [value] ++ after)
          (BuilderDividerOperands.inside problem.input output) outside)) =
      some {
        state := (machine (rootCount problem.verifier)).acceptState
        tape := recoveredCursorTape problem index remaining output (clearedOutside value after outside)
      } :=
  BuilderCursorRecovery.source_workRunExact problem index remaining output value after outside

example (beforeCount : Nat) :
    (machine beforeCount).rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderCursorRecovery.rules_pairwise_query_distinct beforeCount

example (beforeCount : Nat) : WorkMachineChain.NoRuleAtAccept (machine beforeCount) :=
  BuilderCursorRecovery.noRuleAtAccept beforeCount

example (beforeCount : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine beforeCount) (machine beforeCount).rejectState :=
  BuilderCursorRecovery.noRuleAtReject beforeCount

example (beforeCount : Nat) :
    (machine beforeCount).acceptState ≠ (machine beforeCount).rejectState :=
  BuilderCursorRecovery.acceptState_ne_rejectState beforeCount

-- Independent boundary fixtures: empty retained roots, zero scratch values,
-- arbitrary input symbols, nonblank exterior data and the actual return direction.
example : returnMachine.rules.length = 4 := rfl

example (head : WorkSymbol) (tail outside : List WorkSymbol) :
    workRunExact? returnMachine 2
      (workStartConfiguration returnMachine (endTape [] (leftMarker :: head :: tail) outside)) =
      some {
        state := returnMachine.acceptState
        tape := BuilderRegisterAccess.sourceTape head tail [] outside
      } :=
  return_workRunExact [] head tail outside

example : clearedOutside 0 [] [] = [WorkSymbol.blank] := rfl

example : clearedOutside 2 [] [WorkSymbol.oneBlank] =
    [WorkSymbol.blank, WorkSymbol.blank, WorkSymbol.blank, WorkSymbol.oneBlank] := rfl

example (before : List Nat) (value : Nat) (after : List Nat) (tail outside : List WorkSymbol) :
    (finalConfiguration before.length before value after WorkSymbol.zeroBlank tail outside).tape.head =
      WorkSymbol.zeroBlank := rfl

example (before : List Nat) (value : Nat) (after : List Nat) (tail outside : List WorkSymbol) :
    (finalConfiguration before.length before value after WorkSymbol.oneBlank tail outside).tape.head =
      WorkSymbol.oneBlank := rfl

example : WorkSymbol.zeroBlank ≠ WorkSymbol.oneBlank := by decide

example (before : List Nat) (value : Nat) (after : List Nat) (head : WorkSymbol) (tail outside : List WorkSymbol) :
    workRunExact? (machine before.length) (workSteps before value after)
      (initialConfiguration before.length before value after head tail outside) =
      some (finalConfiguration before.length before value after head tail outside) :=
  workRunExact before.length before value after head tail outside rfl

example (before : List Nat) (head : WorkSymbol) (tail outside : List WorkSymbol) :
    workRunExact? (machine before.length) (workSteps before 0 [])
      (initialConfiguration before.length before 0 [] head tail outside) =
      some (finalConfiguration before.length before 0 [] head tail outside) :=
  workRunExact before.length before 0 [] head tail outside rfl

example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * (5 * bound.eval input + 10) := rfl

end PNP.Concrete.CookLevin.BuilderCursorRecoveryRegression
