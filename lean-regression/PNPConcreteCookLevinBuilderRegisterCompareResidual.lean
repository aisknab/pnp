import PNP.Concrete.CookLevinBuilderRegisterCompareResidual

namespace PNP.Concrete.CookLevin.BuilderRegisterCompareResidualRegression

open BuilderArbitrarySlotHeaderRouter BuilderRegisterCompareResidual
open BuilderDividerOperands (endTape)
open BuilderUnaryPolynomial (registerWord)

example : graph.nodes.length = 8 := rfl
example : graph.WellFormed := graph_wellFormed
example : outputValues (.less 2 2) = [2, 0, 5, 5, 2] := by decide
example : outputValues (.equal 3) = [3, 0, 3, 3, 0] := by decide
example : outputValues (.greater 2 2) = [3, 2, 2, 2, 3] := by decide
example : outputValues (RawRouter.compareResult 0 0 0) = [0, 0, 0, 0, 0] := by decide
example : outputValues (RawRouter.compareResult 0 0 4) = [0, 0, 4, 4, 0] := by decide
example : outputValues (RawRouter.compareResult 0 1 0) = [1, 0, 0, 0, 1] := by decide
example : outputValues (RawRouter.compareResult 0 4 3) = [4, 0, 3, 3, 1] := by decide
example : outputValues (RawRouter.compareResult 0 4 3) ≠ [4, 0, 3, 3, 0] := by decide
example : resultCoordinate (RawRouter.compareResult 0 2 5) = 2 := by decide
example : resultCoordinate (RawRouter.compareResult 0 5 2) = 3 := by decide
example : resultCoordinate (RawRouter.compareResult 0 3 3) = 0 := by decide
example : resultBoundary (RawRouter.compareResult 0 5 2) = 2 := by decide
example : allocatedCells (RawRouter.compareResult 0 0 0) = 3 := by decide
example : allocatedCells (RawRouter.compareResult 0 1 0) = 4 := by decide
example : allocatedCells (RawRouter.compareResult 0 2 5) = 10 := by decide
example : allocatedCells (RawRouter.compareResult 0 5 2) = 8 := by decide
example : extraSteps (.less 2 2) = 0 := rfl
example : extraSteps (.equal 3) = 0 := rfl
example : extraSteps (.greater 3 0) = 3 := rfl

example (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps 0 0) (initialConfiguration 0 0 older inside outside) =
      some {
        state := machine.rejectState
        tape := endTape (older ++ [0, 0, 0, 0, 0]) inside (outside.drop 3)} := by
  exact workRunExact 0 0 older inside outside

example (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps 0 4) (initialConfiguration 0 4 older inside outside) =
      some {
        state := machine.acceptState
        tape := endTape (older ++ [0, 0, 4, 4, 0]) inside (outside.drop 7)} := by
  exact workRunExact 0 4 older inside outside

example (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps 1 0) (initialConfiguration 1 0 older inside outside) =
      some {
        state := machine.rejectState
        tape := endTape (older ++ [1, 0, 0, 0, 1]) inside (outside.drop 4)} := by
  exact workRunExact 1 0 older inside outside

example (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps 2 5) (initialConfiguration 2 5 older inside outside) =
      some {
        state := machine.acceptState
        tape := endTape (older ++ [2, 0, 5, 5, 2]) inside (outside.drop 10)} := by
  exact workRunExact 2 5 older inside outside

example (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps 3 3) (initialConfiguration 3 3 older inside outside) =
      some {
        state := machine.rejectState
        tape := endTape (older ++ [3, 0, 3, 3, 0]) inside (outside.drop 6)} := by
  exact workRunExact 3 3 older inside outside

example (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps 5 2) (initialConfiguration 5 2 older inside outside) =
      some {
        state := machine.rejectState
        tape := endTape (older ++ [3, 2, 2, 2, 3]) inside (outside.drop 8)} := by
  exact workRunExact 5 2 older inside outside

example :
    workRunExact? machine (workSteps 4 3)
      (initialConfiguration 4 3 [7, 1] [.oneBlank, .blank]
        (List.replicate 20 .oneOne ++ [.zeroOne, .oneBlank])) =
      some {
        state := machine.rejectState
        tape := endTape [7, 1, 4, 0, 3, 3, 1] [.oneBlank, .blank]
          (List.replicate 13 .oneOne ++ [.zeroOne, .oneBlank])} := by
  let inside : List WorkSymbol := [.oneBlank, .blank]
  let outside : List WorkSymbol := List.replicate 20 .oneOne ++ [.zeroOne, .oneBlank]
  have hTail : outside.drop 7 = List.replicate 13 .oneOne ++ [.zeroOne, .oneBlank] := by
    dsimp only [outside] <;> decide
  have hState := (final_reject_iff 4 3 [7, 1] inside outside).mpr (by decide)
  have hTape := final_tape 4 3 [7, 1] inside outside
  change (finalConfiguration 4 3 [7, 1] inside outside).tape =
    endTape [7, 1, 4, 0, 3, 3, 1] inside (outside.drop 7) at hTape
  rw [hTail] at hTape
  have hFields (config : WorkConfiguration) (state : Nat) (tape : WorkTape)
      (hs : config.state = state) (ht : config.tape = tape) :
      config = {state := state, tape := tape} := by
    cases config with
    | mk currentState currentTape =>
        change currentState = state at hs
        change currentTape = tape at ht
        subst currentState
        subst currentTape
        rfl
  calc
    _ = some (finalConfiguration 4 3 [7, 1] inside outside) :=
      workRunExact 4 3 [7, 1] inside outside
    _ = _ := congrArg some (hFields _ _ _ hState hTape)

example (coordinate boundary : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps coordinate boundary)
      (initialConfiguration coordinate boundary older inside outside) =
      some (finalConfiguration coordinate boundary older inside outside) :=
  workRunExact coordinate boundary older inside outside

example (coordinate boundary : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps coordinate boundary)
      (encodeWorkConfiguration (initialConfiguration coordinate boundary older inside outside)) =
      encodeWorkConfiguration (finalConfiguration coordinate boundary older inside outside) :=
  run_compile_exact coordinate boundary older inside outside

example (coordinate boundary : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).state = machine.acceptState ↔
      coordinate < boundary := final_accept_iff coordinate boundary older inside outside

example (coordinate boundary : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).state = machine.rejectState ↔
      boundary ≤ coordinate := final_reject_iff coordinate boundary older inside outside

example (coordinate boundary : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).tape =
      endTape (older ++ BuilderRegisterLessThan.resultValues (RawRouter.compareResult 0 coordinate boundary) ++
        [boundary, if coordinate < boundary then coordinate else coordinate - boundary])
        inside (outside.drop (boundary +
          (if coordinate < boundary then coordinate else coordinate - boundary) + 3)) :=
  final_tape coordinate boundary older inside outside

example (coordinate boundary : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).tape.left =
      outside.drop (boundary + (if coordinate < boundary then coordinate else coordinate - boundary) + 3) :=
  final_exterior coordinate boundary older inside outside

example (coordinate boundary : Nat) (older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [coordinate, boundary])).length ≤ bound.eval inputLength) :
    (registerWord (older ++ outputValues (RawRouter.compareResult 0 coordinate boundary))).length ≤
        (spanPolynomial bound).eval inputLength ∧
      6 * workSteps coordinate boundary ≤ (rawTimePolynomial bound).eval inputLength :=
  source_polynomial_bounds coordinate boundary older bound inputLength hSpan

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderRegisterCompareResidualRegression
