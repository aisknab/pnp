import PNP.Concrete.CookLevinBuilderDividerCoordinateRegisters

namespace PNP.Concrete.CookLevinBuilderDividerCoordinateRegistersRegression

open CookLevin CookLevin.BuilderDividerCoordinateRegisters PipelineTape BuilderUnaryPolynomial

private def zeroView : RestoreView :=
  { quotient := 0, width := 0, remainder := 0, consumed := 0, sidecarCount := 0 }

private def mixedView : RestoreView :=
  { quotient := 2, width := 2, remainder := 1, consumed := 4, sidecarCount := 2 }

private def exactView : RestoreView :=
  { quotient := 2, width := 2, remainder := 0, consumed := 4, sidecarCount := 2 }

private def noConsumedView : RestoreView :=
  { quotient := 0, width := 2, remainder := 1, consumed := 0, sidecarCount := 2 }

example : rules.length = 41 := rules_length
example : rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

example : workSteps zeroView = 19 := by decide
example : workSteps mixedView = 49 := by decide
example : workSteps exactView = 45 := by decide
example : workSteps noConsumedView = 35 := by decide

example : restoredValues mixedView = [2, 0, 4, 1, 2, 2] := by decide
example : restoredValues noConsumedView = [2, 0, 0, 1, 2, 0] := by decide
example : (registerWord (restoredValues mixedView)).length = 17 := by decide

example :
    workRunExact? machine 19 (initialConfiguration zeroView [] []) =
      some (finalConfiguration zeroView [] []) := by decide

example :
    workRunExact? machine 49
        (initialConfiguration mixedView [leftMarker, .oneZero, rightMarker] []) =
      some (finalConfiguration mixedView [leftMarker, .oneZero, rightMarker] []) := by decide

example :
    workRunExact? machine 45 (initialConfiguration exactView [rightMarker] [.blank]) =
      some (finalConfiguration exactView [rightMarker] [.blank]) := by decide

example :
    workRunExact? machine 35
        (initialConfiguration noConsumedView [scratchEndSymbol, separatorSymbol]
          [.blank, .blank, leftMarker, quotientMark]) =
      some (finalConfiguration noConsumedView [scratchEndSymbol, separatorSymbol]
        [.blank, .blank, leftMarker, quotientMark]) := by decide

example :
    (finalConfiguration noConsumedView [rightMarker]
      [.blank, .blank, leftMarker, quotientMark]).tape.left = [leftMarker, quotientMark] := by decide

example :
    workRunExact? machine 48 (initialConfiguration mixedView [] []) ≠
      some (finalConfiguration mixedView [] []) := by decide

/-- The shift may not overwrite a nonblank first outer cell. -/
example :
    workRunExact? machine 49 (initialConfiguration mixedView [] [.oneZero, .blank]) ≠
      some (finalConfiguration mixedView [] [.oneZero, .blank]) := by decide

/-- Allocating the new end also needs its own blank cell. -/
example :
    workRunExact? machine 49 (initialConfiguration mixedView [] [.blank, .oneZero]) ≠
      some (finalConfiguration mixedView [] [.blank, .oneZero]) := by decide

/-- Ordinary units are not consumed-divider markers. -/
example :
    workStep? machine { state := 11, tape := { left := [], head := unitSymbol, right := [] } } =
      none := by decide

/-- The second protective boundary must remain a real boundary. -/
example :
    workStep? machine { state := 12, tape := { left := [], head := separatorSymbol, right := [] } } =
      none := by decide

example (view : RestoreView) (workspace tail : List WorkSymbol)
    (hFirst : tail.headD .blank = .blank) (hSecond : (tail.drop 1).headD .blank = .blank) :
    workRunExact? machine (workSteps view) (initialConfiguration view workspace tail) =
      some (finalConfiguration view workspace tail) :=
  workRunExact view workspace tail hFirst hSecond

example (view : RestoreView) (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps view) (initialConfiguration view workspace []) =
      some (finalConfiguration view workspace []) :=
  workRunExact view workspace [] rfl rfl

example (view : RestoreView) (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps view) (initialConfiguration view workspace [.blank]) =
      some (finalConfiguration view workspace [.blank]) :=
  workRunExact view workspace [.blank] rfl rfl

example (view : RestoreView) (workspace exterior : List WorkSymbol) :
    workRunExact? machine (workSteps view)
        (initialConfiguration view workspace (.blank :: .blank :: exterior)) =
      some (finalConfiguration view workspace (.blank :: .blank :: exterior)) :=
  workRunExact view workspace (.blank :: .blank :: exterior) rfl rfl

example (view : RestoreView) (workspace tail : List WorkSymbol)
    (hFirst : tail.headD .blank = .blank) (hSecond : (tail.drop 1).headD .blank = .blank) :
    run (compileWorkMachine machine) (6 * workSteps view)
        (encodeWorkConfiguration (initialConfiguration view workspace tail)) =
      encodeWorkConfiguration (finalConfiguration view workspace tail) :=
  run_compile_exact view workspace tail hFirst hSecond

example (view : RestoreView) (workspace tail : List WorkSymbol) :
    (finalConfiguration view workspace tail).state = machine.acceptState :=
  finalConfiguration_state view workspace tail

example (view : RestoreView) (workspace tail : List WorkSymbol) :
    (finalConfiguration view workspace tail).tape =
      { left := tail.drop 2, head := scratchEndSymbol,
        right := (registerWord (restoredValues view)).reverse ++ workspace } :=
  final_tape_layout view workspace tail

example (view : RestoreView) : (restoredValues view)[3]? = some view.remainder :=
  restored_remainder view

example (view : RestoreView) : (restoredValues view)[5]? = some view.quotient :=
  restored_quotient view

example (view : RestoreView) (bound : Nat)
    (hQuotient : view.quotient ≤ bound) (hWidth : view.width ≤ bound)
    (hRemainder : view.remainder ≤ bound) (hConsumed : view.consumed ≤ bound)
    (hSidecar : view.sidecarCount ≤ bound) :
    workSteps view ≤ 15 * bound + 19 :=
  workSteps_le view bound hQuotient hWidth hRemainder hConsumed hSidecar

end PNP.Concrete.CookLevinBuilderDividerCoordinateRegistersRegression
