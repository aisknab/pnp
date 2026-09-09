import PNP.Concrete.CookLevinBuilderLiteralSearchAdvance

open PNP.Concrete PNP.Concrete.CookLevin
open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLiteralSearchFrame (valueHistory widthHistory comparisonHistory comparisonResult chunk residual)
open BuilderLiteralSearchAdvance

-- Independent layout, last-item and boundary fixtures; general contracts follow.
example : (ordinalSuffix 1 2 5 3).length = 16 := ordinalSuffix_length _ _ _ _
example : (countSuffix 1 5 3).length = 16 := countSuffix_length _ _ _
example : (finalValues [9,8] 1 0 5 3).length = 22 := final_frame_length _ _ _ _ _
example : residual 5 3 = 0 := rfl
example : residual 8 3 = 3 := rfl
example : residual 4 3 = 4 := rfl
example (older : List Nat) :
    finalValues older 1 0 5 3 = initialValues older 1 0 5 3 ++ [2,0,0] := rfl
example (older : List Nat) :
    finalValues older 1 2 8 3 = initialValues older 1 2 8 3 ++ [2,2,3] := rfl
example (ordinal remaining position value : Nat) : finalOutside ordinal remaining position value [] = [] := by
  simp only [finalOutside_eq, countOutside, incrementOutside, ordinalOutside, List.drop_nil]
example : spanBound 0 = 4 := rfl
example : copyBound 0 = 18 := rfl
example : workBound 0 = 323 := rfl

example (ordinal count position value : Nat) :
    (ordinalSuffix ordinal count position value).length = 16 :=
  BuilderLiteralSearchAdvance.ordinalSuffix_length ordinal count position value

example (ordinal position value : Nat) :
    (countSuffix ordinal position value).length = 16 :=
  BuilderLiteralSearchAdvance.countSuffix_length ordinal position value

example (ordinal count position value : Nat) :
    chunk ordinal count position value = [ordinal] ++ ordinalSuffix ordinal count position value :=
  BuilderLiteralSearchAdvance.chunk_ordinal ordinal count position value

example (ordinal count position value : Nat) :
    chunk ordinal count position value ++ [ordinal + 1] =
      [ordinal, count] ++ countSuffix ordinal position value :=
  BuilderLiteralSearchAdvance.chunk_count ordinal count position value

example (ordinal count position value : Nat) :
    chunk ordinal count position value = beforeResidual ordinal count position value ++ [residual position value] :=
  BuilderLiteralSearchAdvance.chunk_residual ordinal count position value

example (older : List Nat) (ordinal remaining position value : Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps ordinal remaining position value)
      (initialConfiguration older ordinal remaining position value inside outside) =
      some (finalConfiguration older ordinal remaining position value inside outside) :=
  BuilderLiteralSearchAdvance.workRunExact older ordinal remaining position value inside outside

example (older : List Nat) (ordinal remaining position value : Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps ordinal remaining position value)
      (encodeWorkConfiguration (initialConfiguration older ordinal remaining position value inside outside)) =
      encodeWorkConfiguration (finalConfiguration older ordinal remaining position value inside outside) :=
  BuilderLiteralSearchAdvance.run_compile_exact older ordinal remaining position value inside outside

example (older : List Nat) (ordinal remaining position value : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration older ordinal remaining position value inside outside).tape =
      endTape (finalValues older ordinal remaining position value) inside
        (finalOutside ordinal remaining position value outside) :=
  BuilderLiteralSearchAdvance.final_tape older ordinal remaining position value inside outside

example (ordinal remaining position value : Nat) (outside : List WorkSymbol) :
    finalOutside ordinal remaining position value outside =
      (countOutside ordinal remaining outside).drop (residual position value) :=
  BuilderLiteralSearchAdvance.finalOutside_eq ordinal remaining position value outside

example (ordinal remaining position value : Nat) (outside : List WorkSymbol) :
    (finalOutside ordinal remaining position value outside).length ≤ outside.length :=
  BuilderLiteralSearchAdvance.finalOutside_length_le ordinal remaining position value outside

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderLiteralSearchAdvance.rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept machine :=
  BuilderLiteralSearchAdvance.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  BuilderLiteralSearchAdvance.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState :=
  BuilderLiteralSearchAdvance.acceptState_ne_rejectState

example (older : List Nat) (ordinal remaining position value : Nat) :
    (finalValues older ordinal remaining position value).length = older.length + 20 :=
  BuilderLiteralSearchAdvance.final_frame_length older ordinal remaining position value

example (prior : List Nat) (ordinal remaining position value : Nat)
    (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * ordinal) :
    (prior ++ chunk ordinal (remaining + 1) position value).length =
      BuilderLiteralSearchFrame.historyStride * (ordinal + 1) :=
  BuilderLiteralSearchAdvance.next_history_length prior ordinal remaining position value hPrior

example (older : List Nat) (ordinal remaining position value : Nat) (hMiss : value + 2 ≤ position) :
    finalValues older ordinal remaining position value =
      initialValues older ordinal remaining position value ++ [ordinal + 1, remaining, position - (value + 2)] :=
  BuilderLiteralSearchAdvance.miss_next_frame older ordinal remaining position value hMiss

example (older : List Nat) (ordinal remaining position value bound : Nat)
    (outside : List WorkSymbol)
    (hSpan : (registerWord (initialValues older ordinal remaining position value)).length + outside.length ≤ bound) :
    (registerWord (finalValues older ordinal remaining position value)).length +
      (finalOutside ordinal remaining position value outside).length ≤ spanBound bound ∧
    workSteps ordinal remaining position value ≤ workBound bound :=
  BuilderLiteralSearchAdvance.space_time_bounds older ordinal remaining position value bound outside hSpan

example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) :=
  BuilderLiteralSearchAdvance.rawTimePolynomial_eval bound input

example (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial bound).eval input = spanBound (bound.eval input) :=
  BuilderLiteralSearchAdvance.spanPolynomial_eval bound input

example (older : List Nat) (ordinal remaining position value : Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues older ordinal remaining position value)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues older ordinal remaining position value)).length +
      (finalOutside ordinal remaining position value outside).length ≤ (spanPolynomial bound).eval input ∧
    6 * workSteps ordinal remaining position value ≤ (rawTimePolynomial bound).eval input :=
  BuilderLiteralSearchAdvance.source_polynomial_bounds older ordinal remaining position value outside bound input hSpan
