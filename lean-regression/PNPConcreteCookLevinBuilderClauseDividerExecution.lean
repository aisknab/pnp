import PNP.Concrete.CookLevinBuilderClauseDividerExecution

namespace PNP.Concrete.CookLevinBuilderClauseDividerExecutionRegression

open CookLevin CookLevin.BuilderClauseDividerExecution PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count width)
open BuilderClauseDividerOperands (clauseWidth quotient dividerOlder)
open BuilderDividerSourceExecution (sourceSpan)

example : divisionMachine.rules.length = 119 := by decide
example : divisionMachine.rules.Pairwise WorkMachineChain.QueryDistinct := division_rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept divisionMachine := division_noRuleAtAccept
example : divisionMachine.acceptState ≠ divisionMachine.rejectState := division_acceptState_ne_rejectState

example :
    workRunExact? divisionMachine (divisionSteps 0 0 1) (divisionInitial 0 0 1 [] []) =
      some (divisionFinal 0 0 1 [] []) := by decide
example :
    workRunExact? divisionMachine (divisionSteps 4 1 3)
        (divisionInitial 4 1 3 [2, 0] [leftMarker, scratchEndSymbol, .blank]) =
      some (divisionFinal 4 1 3 [2, 0] [leftMarker, scratchEndSymbol, .blank]) := by decide
example :
    workRunExact? divisionMachine (divisionSteps 8 5 2)
        (divisionInitial 8 5 2 [4, 1] [rightMarker]) =
      some (divisionFinal 8 5 2 [4, 1] [rightMarker]) := by decide
example :
    workRunExact? divisionMachine (divisionSteps 6 4 2)
        (divisionInitial 6 4 2 [0] [separatorSymbol]) =
      some (divisionFinal 6 4 2 [0] [separatorSymbol]) := by decide

example : (divisionFinal 8 5 2 [4, 1] [rightMarker]).tape.left =
    List.replicate 2 BuilderPostHeaderRawDivider.quotientMark := by decide
example : ((divisionFinal 8 5 2 [4, 1] [rightMarker]).tape.right.drop 3).take 1 = [unitSymbol] := by decide
example : ((divisionFinal 8 5 2 [4, 1] [rightMarker]).tape.right.drop 4).headD .blank =
    BuilderPostHeaderRawDivider.consumedDividend := by decide

example :
    workRunExact? divisionMachine (divisionSteps 8 5 2 - 1) (divisionInitial 8 5 2 [4, 1] []) ≠
      some (divisionFinal 8 5 2 [4, 1] []) := by decide

/-- The positive divisor premise cannot be dropped at the literal execution boundary. -/
example :
    workRunExact? divisionMachine (divisionSteps 2 1 0) (divisionInitial 2 1 0 [] []) ≠
      some (divisionFinal 2 1 0 [] []) := by decide

example (count dividend divisor : Nat) (older : List Nat) (workspace : List WorkSymbol)
    (hPositive : 0 < divisor) :
    workRunExact? divisionMachine (divisionSteps count dividend divisor)
        (divisionInitial count dividend divisor older workspace) =
      some (divisionFinal count dividend divisor older workspace) :=
  division_workRunExact count dividend divisor older workspace hPositive

example (count dividend divisor : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (divisionFinal count dividend divisor older workspace).tape =
      {
        left := List.replicate (dividend / divisor) BuilderPostHeaderRawDivider.quotientMark
        head := scratchEndSymbol
        right := List.replicate divisor unitSymbol ++ separatorSymbol ::
          (List.replicate (dividend % divisor) unitSymbol ++
            List.replicate ((dividend / divisor) * divisor) BuilderPostHeaderRawDivider.consumedDividend ++
            leftMarker :: leftMarker :: (List.replicate count unitSymbol ++
              scratchEndSymbol :: ((registerWord older).reverse ++ workspace)))
      } := division_final_tape_layout count dividend divisor older workspace

example (count dividend divisor bound : Nat)
    (hCount : count ≤ bound) (hDividend : dividend ≤ bound) (hDivisor : divisor ≤ bound)
    (hPositive : 0 < divisor) :
    divisionSteps count dividend divisor ≤ 4 * bound + 8 + 20 * (2 * bound + 1) * (2 * bound + 1) :=
  divisionSteps_le count dividend divisor bound hCount hDividend hDivisor hPositive

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderClauseDividerOperands.finalConfiguration problem index remaining output).tape =
      (divisionInitial (count problem) (quotient problem index) (clauseWidth problem)
        (dividerOlder problem index remaining) (inside problem.input output)).tape :=
  operand_division_handoff problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := workRunExact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compile_exact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState :=
  finalConfiguration_state problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      {
        left := List.replicate (constraintIndex problem index) BuilderPostHeaderRawDivider.quotientMark
        head := scratchEndSymbol
        right := List.replicate (clauseWidth problem) unitSymbol ++ separatorSymbol ::
          (List.replicate (clauseIndex problem index) unitSymbol ++
            List.replicate (constraintIndex problem index * clauseWidth problem)
              BuilderPostHeaderRawDivider.consumedDividend ++ leftMarker :: leftMarker ::
                (List.replicate (count problem) unitSymbol ++ scratchEndSymbol ::
                  ((registerWord (dividerOlder problem index remaining)).reverse ++ inside problem.input output)))
      } := final_tape_layout problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape.left.length = constraintIndex problem index :=
  constraint_mark_count problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    clauseIndex problem index < problem.formulaClauseSlotsPerConstraint := clauseIndex_lt problem index

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    constraintIndex problem index * clauseWidth problem + clauseIndex problem index = quotient problem index :=
  coordinate_reconstruction problem index

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hBody : quotient problem index < count problem) :
    constraintIndex problem index < problem.formulaConstraintSlotCount := constraintIndex_lt problem index hBody

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (constraintIndex problem index * clauseWidth problem + clauseIndex problem index) * width problem +
      index % width problem = index := source_coordinate_reconstruction problem index

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * divisionSteps (count problem) (quotient problem index) (clauseWidth problem) ≤
      (divisionRawTimeBound problem.verifier).eval problem.input.length :=
  divisionRawTimeBound_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  rawTimeBound_le problem index remaining hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := machine_acceptState_ne_rejectState verifier

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (bodyMachine problem.verifier) (bodySteps problem index remaining)
        (bodyInitial problem index remaining output) = some (finalConfiguration problem index remaining output) :=
  body_workRunExact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (bodyMachine problem.verifier)) (6 * bodySteps problem index remaining)
        (encodeWorkConfiguration (bodyInitial problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  body_run_compile_exact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (bodyMachine problem.verifier).acceptState :=
  body_finalConfiguration_state problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * bodySteps problem index remaining ≤ (bodyRawTimeBound problem.verifier).eval problem.input.length :=
  body_rawTimeBound_le problem index remaining hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := body_rules_pairwise_query_distinct verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (bodyMachine verifier) := body_noRuleAtAccept verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).acceptState ≠ (bodyMachine verifier).rejectState := body_acceptState_ne_rejectState verifier

end PNP.Concrete.CookLevinBuilderClauseDividerExecutionRegression
