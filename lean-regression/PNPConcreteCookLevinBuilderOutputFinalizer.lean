/-
Copyright (c) 2026 PNP Labs.
Prepared external-output adapter contracts for M230.
-/
import PNP.Concrete.CookLevinBuilderOutputFinalizer

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderOutputFinalizer

example :
    machine.rules.Pairwise WorkMachineChain.QueryDistinct := by
  exact rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept machine := by
  exact noRuleAtAccept

example : machine.acceptState ≠ machine.rejectState := by
  exact acceptState_ne_rejectState

example (input : BitString) (outside : List WorkSymbol)
    (output : List CNFToken) :
    workRunExact? machine (workSteps input output)
      (workStartConfiguration machine (BuilderTokenAppender.workspaceTape input outside output)) =
        some (finalConfiguration input outside output) := by
  exact workRun_exact input outside output

example (input : BitString) (outside : List WorkSymbol)
    (output : List CNFToken) :
    (encodeWorkTape (finalTape input outside output)).outputBits =
      encodeTokenPairs output ++ [false] := by
  exact output_eq input outside output

example (input : BitString) (outside : List WorkSymbol)
    (output : List CNFToken) :
    machine.isHalted (finalConfiguration input outside output) = true := by
  exact final_isHalted input outside output

example (input : BitString) (output : List CNFToken) :
    6 * workSteps input output ≤ 12 * input.length + 12 * output.length + 30 := by
  exact rawTime_le input output

example {language : Language} (problem : VerifierTableauProblem language) :
    workRunExact? machine (workSteps problem.input (encodeCNFTokens problem.formula))
      (workStartConfiguration machine
        (BuilderCursorSource.cursorTape problem (BuilderFullScheduleCursorController.bodySlotCount problem) 0
          (encodeCNFTokens problem.formula))) =
      some (finalConfiguration problem.input (canonicalOutside problem) (encodeCNFTokens problem.formula)) := by
  exact canonical_workRun_exact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (encodeWorkTape (finalTape problem.input (canonicalOutside problem) (encodeCNFTokens problem.formula))).outputBits =
      problem.encodedFormula := by
  exact canonical_output_eq problem

example {language : Language} (problem : VerifierTableauProblem language) :
    6 * workSteps problem.input (encodeCNFTokens problem.formula) ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  exact canonical_rawTime_le problem

example : machine.rules.length = 17 := rfl

example : workSteps [] [] = 5 := rfl

example : workSteps [true, false, true] [.t, .finish] = 14 := rfl

example (outside : List WorkSymbol) :
    (encodeWorkTape (finalTape [] outside [])).outputBits = [false] := by
  exact output_eq [] outside []

example (input : BitString) (outside : List WorkSymbol) :
    (encodeWorkTape (finalTape input outside [.f, .t, .sep, .finish])).outputBits =
      [false, false, true, true, false, true, true, false, false] := by
  rw [output_eq]
  rfl

example (input : BitString) (first second : List WorkSymbol) (output : List CNFToken) :
    (encodeWorkTape (finalTape input first output)).outputBits =
      (encodeWorkTape (finalTape input second output)).outputBits := by
  rw [output_eq, output_eq]

example (left right : List WorkSymbol) :
    workStep? machine {state := 1, tape := {left := left, head := .zeroZero, right := right}} = none := by
  rfl

example (input : BitString) (outside : List WorkSymbol) (output : List CNFToken) :
    ((encodeWorkTape (finalTape input outside output)).outputBits).length =
      (encodeTokenPairs output).length + 1 := by
  rw [output_eq, List.length_append]
  rfl
