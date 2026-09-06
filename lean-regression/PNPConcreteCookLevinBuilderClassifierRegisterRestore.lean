import PNP.Concrete.CookLevinBuilderClassifierRegisterRestore

namespace PNP.Concrete.CookLevinBuilderClassifierRegisterRestoreRegression

open CookLevin CookLevin.BuilderClassifierRegisterRestore PipelineTape BuilderUnaryPolynomial

private def zeroView : RestoreView :=
  {
    countRest := 0
    countMarked := 0
    quotientRest := 0
    quotientMarked := 0
    consumed := 0
    remainder := 0
    width := 0
    sidecarCount := 0
  }

private def bodyView : RestoreView :=
  {
    countRest := 1
    countMarked := 1
    quotientRest := 0
    quotientMarked := 1
    consumed := 2
    remainder := 1
    width := 2
    sidecarCount := 2
  }

private def equalView : RestoreView :=
  {
    countRest := 0
    countMarked := 2
    quotientRest := 0
    quotientMarked := 2
    consumed := 4
    remainder := 0
    width := 2
    sidecarCount := 2
  }

private def greaterView : RestoreView :=
  {
    countRest := 0
    countMarked := 2
    quotientRest := 0
    quotientMarked := 3
    consumed := 6
    remainder := 0
    width := 2
    sidecarCount := 2
  }

example : rules.length = 19 := rules_length
example : rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

example : workSteps zeroView = 13 := by decide
example : workSteps bodyView = 34 := by decide
example : workSteps equalView = 37 := by decide
example : workSteps greaterView = 43 := by decide

example : restoredValues bodyView = [2, 0, 3, 2, 1, 2] := by decide
example : restoredValues equalView = [2, 0, 4, 2, 2, 2] := by decide
example : restoredValues greaterView = [2, 0, 6, 2, 3, 2] := by decide

example :
    workRunExact? machine 13 (initialConfiguration zeroView [] []) =
      some (finalConfiguration zeroView [] []) := by decide

example :
    workRunExact? machine 34
        (initialConfiguration bodyView [leftMarker, .oneZero, rightMarker] [.blank, leftMarker]) =
      some (finalConfiguration bodyView [leftMarker, .oneZero, rightMarker] [.blank, leftMarker]) := by decide

example :
    workRunExact? machine 37 (initialConfiguration equalView [rightMarker] []) =
      some (finalConfiguration equalView [rightMarker] []) := by decide

example :
    workRunExact? machine 43 (initialConfiguration greaterView [] [.blank, .blank]) =
      some (finalConfiguration greaterView [] [.blank, .blank]) := by decide

example :
    workRunExact? machine 12 (initialConfiguration zeroView [] []) ≠
      some (finalConfiguration zeroView [] []) := by decide

/-- The second protective boundary must be a real boundary, not a separator. -/
example :
    workStep? machine
      { state := 5, tape := { left := [], head := separatorSymbol, right := [] } } = none := by decide

/-- Count-comparison markers are not valid first-divider consumed markers. -/
example :
    workStep? machine
      { state := 4, tape := { left := [], head := boundaryMark, right := [] } } = none := by decide

example (view : RestoreView) (workspace tail : List WorkSymbol) :
    workRunExact? machine (workSteps view) (initialConfiguration view workspace tail) =
      some (finalConfiguration view workspace tail) := workRunExact view workspace tail

example (view : RestoreView) (workspace tail : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps view)
        (encodeWorkConfiguration (initialConfiguration view workspace tail)) =
      encodeWorkConfiguration (finalConfiguration view workspace tail) :=
  run_compile_exact view workspace tail

example (view : RestoreView) (workspace tail : List WorkSymbol) :
    (finalConfiguration view workspace tail).state = machine.acceptState :=
  finalConfiguration_state view workspace tail

example (view : RestoreView) (workspace tail : List WorkSymbol) :
    (finalConfiguration view workspace tail).tape =
      {
        left := tail
        head := scratchEndSymbol
        right := (registerWord (restoredValues view)).reverse ++ workspace
      } := final_tape_layout view workspace tail

example (view : RestoreView) (bound : Nat)
    (hCount : view.countTotal ≤ bound) (hQuotient : view.quotientTotal ≤ bound)
    (hWidth : view.width ≤ bound) (hDividend : view.dividend ≤ bound)
    (hSidecar : view.sidecarCount ≤ bound) :
    workSteps view ≤ 11 * bound + 13 :=
  workSteps_le view bound hCount hQuotient hWidth hDividend hSidecar

end PNP.Concrete.CookLevinBuilderClassifierRegisterRestoreRegression
