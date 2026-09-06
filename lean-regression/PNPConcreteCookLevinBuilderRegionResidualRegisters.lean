import PNP.Concrete.CookLevinBuilderRegionResidualRegisters

namespace PNP.Concrete.CookLevin.RegionResidualRegistersRegression

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderRegionResidualRegisters
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter

example : rules.length = 42 := rules_length
example : rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

example (view : RestoreView) (workspace tail : List WorkSymbol)
    (hBlank : tail.headD .blank = .blank) :
    workRunExact? machine (workSteps view) (initialConfiguration view workspace tail) =
      some (finalConfiguration view workspace tail) :=
  workRunExact view workspace tail hBlank

example (view : RestoreView) (workspace tail : List WorkSymbol)
    (hBlank : tail.headD .blank = .blank) :
    run (compileWorkMachine machine) (6 * workSteps view)
      (encodeWorkConfiguration (initialConfiguration view workspace tail)) =
      encodeWorkConfiguration (finalConfiguration view workspace tail) :=
  run_compile_exact view workspace tail hBlank

example (view : RestoreView) (workspace tail : List WorkSymbol) :
    (finalConfiguration view workspace tail).tape.left = tail.drop 1 := rfl

example (view : RestoreView) (workspace tail : List WorkSymbol) :
    (finalConfiguration view workspace tail).tape.right =
      (registerWord (restoredValues view)).reverse ++ workspace := rfl

example (view : RestoreView) (workspace tail : List WorkSymbol) :
    workRunExact? machine 0 (initialConfiguration view workspace tail) =
      some (initialConfiguration view workspace tail) := rfl

example : workRunExact? machine 13 (initialConfiguration ⟨0, 0, 0, 0⟩ [] []) =
    some { state := 16, tape := endTape [0, 0, 0] [] [] } := by decide

example : workRunExact? machine 19 (initialConfiguration ⟨0, 1, 0, 1⟩ [] []) =
    some { state := 16, tape := endTape [1, 0, 1] [] [] } := by decide

example : workRunExact? machine 25 (initialConfiguration ⟨0, 2, 0, 2⟩ [] []) =
    some { state := 16, tape := endTape [2, 0, 2] [] [] } := by decide

example : workRunExact? machine 15 (initialConfiguration ⟨0, 0, 0, 1⟩ [] []) =
    some { state := 17, tape := endTape [1, 0, 0] [] [] } := by decide

example : workRunExact? machine 21 (initialConfiguration ⟨0, 1, 0, 2⟩ [] []) =
    some { state := 17, tape := endTape [2, 0, 1] [] [] } := by decide

example : workRunExact? machine 39 (initialConfiguration ⟨0, 2, 3, 3⟩ [] []) =
    some { state := 17, tape := endTape [3, 3, 2] [] [] } := by decide

example : workRunExact? machine 18 (initialConfiguration ⟨1, 0, 0, 0⟩ [] []) =
    some { state := 16, tape := endTape [0, 0, 1] [] [] } := by decide

example : workRunExact? machine 35 (initialConfiguration ⟨2, 2, 0, 2⟩ [] []) =
    some { state := 16, tape := endTape [2, 0, 4] [] [] } := by decide

example : workRunExact? machine 46 (initialConfiguration ⟨1, 2, 3, 4⟩ [] []) =
    some { state := 16, tape := endTape [4, 3, 3] [] [] } := by decide

example : workRunExact? machine 35 (initialConfiguration ⟨2, 1, 1, 2⟩ [] []) =
    some { state := 17, tape := endTape [2, 1, 3] [] [] } := by decide

example : workRunExact? machine 15
    (initialConfiguration ⟨0, 0, 0, 1⟩ [leftMarker, coordinateMark, scratchEndSymbol]
      [.blank, boundaryMark, unitSymbol]) =
    some {
      state := 17
      tape := endTape [1, 0, 0] [leftMarker, coordinateMark, scratchEndSymbol]
        [boundaryMark, unitSymbol]
    } := by decide

example : workRunExact? machine 12 (initialConfiguration ⟨0, 0, 0, 0⟩ [] []) =
    some { state := 14, tape := endTape [0, 0, 0] [] [] } := by decide

example : workRunExact? machine 14 (initialConfiguration ⟨0, 0, 0, 0⟩ [] []) =
    none := by decide

example : workRunExact? machine 13 (initialConfiguration ⟨0, 0, 0, 0⟩ [] [unitSymbol]) =
    none := by decide

example : workStep? machine {
      state := 0
      tape := { left := [], head := .blank, right := [] }
    } = none := by decide

example : workStep? machine {
      state := 2
      tape := { left := [], head := boundaryMark, right := [] }
    } = none := by decide

example (result : RawRouter.ComparisonResult) :
    markedParity (ofComparison result) = isGreater result := ofComparison_markedParity result

example (processed remaining : Nat) :
    markedParity (ofComparison (.less processed remaining)) = false :=
  ofComparison_markedParity _

example (processed : Nat) :
    markedParity (ofComparison (.equal processed)) = false :=
  ofComparison_markedParity _

example (processed remaining : Nat) :
    markedParity (ofComparison (.greater processed remaining)) = true :=
  ofComparison_markedParity _

example (result : RawRouter.ComparisonResult) (workspace : List WorkSymbol) :
    inputTape (ofComparison result) workspace [] =
      BuilderPhysicalClassifierFinishMirroredDispatch.mirrorTape
        (BuilderPostDividerRawRouteClassifier.appendExteriorTape
          (RawRouter.resultConfiguration result).tape workspace) :=
  inputTape_ofComparison result workspace

example (result : RawRouter.ComparisonResult) (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps (ofComparison result))
      (workStartConfiguration machine
        (BuilderPhysicalClassifierFinishMirroredDispatch.mirrorTape
          (BuilderPostDividerRawRouteClassifier.appendExteriorTape
            (RawRouter.resultConfiguration result).tape workspace))) =
      some (finalConfiguration (ofComparison result) workspace []) :=
  comparison_workRunExact result workspace

example (result : RawRouter.ComparisonResult) (workspace : List WorkSymbol) :
    (finalConfiguration (ofComparison result) workspace []).state = terminalState (isGreater result) :=
  comparison_final_state result workspace

example (view : RestoreView) (bound : Nat)
    (hA : view.boundaryRest ≤ bound) (hB : view.boundaryMarked ≤ bound)
    (hC : view.coordinateRest ≤ bound) (hD : view.coordinateMarked ≤ bound) :
    workSteps view ≤ 15 * bound + 13 := workSteps_le view bound hA hB hC hD

example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 90 * bound.eval input + 78 :=
  rawTimePolynomial_eval bound input

example (view : RestoreView) (bound : NatPolynomial) (input : Nat)
    (hA : view.boundaryRest ≤ bound.eval input) (hB : view.boundaryMarked ≤ bound.eval input)
    (hC : view.coordinateRest ≤ bound.eval input) (hD : view.coordinateMarked ≤ bound.eval input) :
    6 * workSteps view ≤ (rawTimePolynomial bound).eval input :=
  rawTimePolynomial_le view bound input hA hB hC hD

end PNP.Concrete.CookLevin.RegionResidualRegistersRegression
