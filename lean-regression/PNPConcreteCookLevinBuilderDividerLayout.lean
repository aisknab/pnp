import PNP.Concrete.CookLevinBuilderDividerLayout

namespace PNP.Concrete.CookLevinBuilderDividerLayoutRegression

open CookLevin CookLevin.BuilderDividerLayout PipelineTape BuilderUnaryPolynomial

example : rules.length = 11 := rules_length
example : rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

example : workSteps 0 0 0 = 7 := by decide
example : workSteps 2 1 3 = 15 := by decide

example :
    workRunExact? machine 7 (initialConfiguration 0 0 0 [] [] []) =
      some (finalConfiguration 0 0 0 [] [] []) := by decide

example :
    workRunExact? machine 15
      (initialConfiguration 2 1 3 [1, 0] [leftMarker, .oneBlank, rightMarker] [.zeroOne, .blank]) =
    some (finalConfiguration 2 1 3 [1, 0] [leftMarker, .oneBlank, rightMarker] [.zeroOne, .blank]) := by decide

example :
    workRunExact? machine 12 (initialConfiguration 2 0 1 [0] [rightMarker] []) =
      some (finalConfiguration 2 0 1 [0] [rightMarker] []) := by decide

example :
    workStep? machine { state := 0, tape := { left := [], head := .blank, right := [] } } = none := by decide

/-- The boundary slot must really be empty; it cannot be a copied nonzero index. -/
example :
    workRunExact? machine 15
      (workStartConfiguration machine (BuilderDividerOperands.endTape [2, 1, 1, 3] [] [])) = none := by decide

example (count index width : Nat) (older : List Nat) (inside tail : List WorkSymbol) :
    (initialConfiguration count index width older inside tail).tape =
      {
        left := tail
        head := scratchEndSymbol
        right := List.replicate width unitSymbol ++ separatorSymbol ::
          (List.replicate index unitSymbol ++ separatorSymbol :: separatorSymbol ::
            (List.replicate count unitSymbol ++ separatorSymbol ::
              ((registerWord older).reverse ++ inside)))
      } := initial_tape_layout count index width older inside tail

example (count index width : Nat) (older : List Nat) (inside tail : List WorkSymbol) :
    workRunExact? machine (workSteps count index width)
        (initialConfiguration count index width older inside tail) =
      some (finalConfiguration count index width older inside tail) :=
  workRunExact count index width older inside tail

example (count index width : Nat) (older : List Nat) (inside tail : List WorkSymbol) :
    (finalConfiguration count index width older inside tail).state = machine.acceptState :=
  finalConfiguration_state count index width older inside tail

example (count index width : Nat) (older : List Nat) (inside tail : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps count index width)
        (encodeWorkConfiguration (initialConfiguration count index width older inside tail)) =
      encodeWorkConfiguration (finalConfiguration count index width older inside tail) :=
  run_compile_exact count index width older inside tail

example (count index width bound : Nat)
    (hCount : count ≤ bound) (hIndex : index ≤ bound) (hWidth : width ≤ bound) :
    workSteps count index width ≤ 4 * bound + 7 := workSteps_le count index width bound hCount hIndex hWidth

example (count index width : Nat) (older : List Nat) (inside tail : List WorkSymbol) :
    (finalConfiguration count index width older inside tail).tape =
      leftFocus (dividerWord index width ++ tail)
        (leftMarker :: leftMarker :: (List.replicate count unitSymbol ++ scratchEndSymbol ::
          ((registerWord older).reverse ++ inside))) := rfl

end PNP.Concrete.CookLevinBuilderDividerLayoutRegression
