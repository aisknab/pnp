import PNP.Concrete.CookLevinBuilderRegionResidualSelection

namespace PNP.Concrete.CookLevin.RegionResidualSelectionRegression

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderRegionResidualSelection
open BuilderArbitrarySlotHeaderRouter

example : graph.WellFormed := graph_wellFormed
example : machine.rules.length = 602 := rules_length
example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps coordinate boundary) (initialConfiguration coordinate boundary older workspace) =
      some (finalConfiguration coordinate boundary older workspace) :=
  workRunExact coordinate boundary older workspace

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps coordinate boundary)
      (encodeWorkConfiguration (initialConfiguration coordinate boundary older workspace)) =
      encodeWorkConfiguration (finalConfiguration coordinate boundary older workspace) :=
  run_compile_exact coordinate boundary older workspace

example (coordinate boundary : Nat) :
    nextCoordinate coordinate boundary =
      if coordinate < boundary then coordinate else coordinate - boundary :=
  nextCoordinate_eq coordinate boundary

example (coordinate boundary : Nat) :
    let view := BuilderRegionResidualRegisters.ofComparison (RawRouter.compareResult 0 coordinate boundary)
    view.boundaryRest + view.boundaryMarked = boundary :=
  restoredBoundary_eq coordinate boundary

example (result : RawRouter.ComparisonResult) : (scratchValues result).length = 4 :=
  scratchValues_length result

example (result : RawRouter.ComparisonResult) :
    (scratchValues result).getLast? = some (resultCoordinate result) := scratchValues_last result

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).state = machine.acceptState ↔
      coordinate < boundary := final_accept_iff coordinate boundary older workspace

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).state = machine.rejectState ↔
      boundary ≤ coordinate := final_reject_iff coordinate boundary older workspace

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).tape.right =
      (registerWord (scratchValues (RawRouter.compareResult 0 coordinate boundary))).reverse ++
        ((registerWord older).reverse ++ workspace) :=
  final_exterior_preserved coordinate boundary older workspace

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).tape.left = [] :=
  final_outer_empty coordinate boundary older workspace

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    workRunExact? machine 0 (initialConfiguration coordinate boundary older workspace) =
      some (initialConfiguration coordinate boundary older workspace) := rfl

section LiteralRuns

-- The fixed materialized graph has 602 rules. Keep kernel-checked literal
-- reduction, with a bounded evaluator depth for its longer lookup chains.
set_option maxRecDepth 4096

example : workRunExact? machine 31 (initialConfiguration 0 0 [] []) =
    some { state := 1, tape := endTape [0, 0, 0, 0] [] [] } := by decide

example : workRunExact? machine 41 (initialConfiguration 0 1 [] []) =
    some { state := 0, tape := endTape [0, 0, 1, 0] [] [] } := by decide

example : workRunExact? machine 38 (initialConfiguration 1 0 [] []) =
    some { state := 1, tape := endTape [1, 0, 0, 1] [] [] } := by decide

example : workRunExact? machine 49 (initialConfiguration 1 1 [] []) =
    some { state := 1, tape := endTape [1, 0, 1, 0] [] [] } := by decide

example : workRunExact? machine 78 (initialConfiguration 1 2 [] []) =
    some { state := 0, tape := endTape [1, 0, 2, 1] [] [] } := by decide

example : workRunExact? machine 58 (initialConfiguration 2 1 [] []) =
    some { state := 1, tape := endTape [2, 0, 1, 1] [] [] } := by decide

example : workRunExact? machine 73 (initialConfiguration 2 2 [] []) =
    some { state := 1, tape := endTape [2, 0, 2, 0] [] [] } := by decide

example : workRunExact? machine 81 (initialConfiguration 3 1 [] []) =
    some { state := 1, tape := endTape [2, 1, 1, 2] [] [] } := by decide

example : workRunExact? machine 57 (initialConfiguration 0 3 [] []) =
    some { state := 0, tape := endTape [0, 0, 3, 0] [] [] } := by decide

example : workRunExact? machine 80 (initialConfiguration 3 0 [] []) =
    some { state := 1, tape := endTape [1, 2, 0, 3] [] [] } := by decide

example : workRunExact? machine 129 (initialConfiguration 2 3 [] []) =
    some { state := 0, tape := endTape [2, 0, 3, 2] [] [] } := by decide

example : workRunExact? machine 58
    (initialConfiguration 2 1 [3, 1] [leftMarker, scratchEndSymbol, separatorSymbol]) =
    some {
      state := 1
      tape := endTape [3, 1, 2, 0, 1, 1] [leftMarker, scratchEndSymbol, separatorSymbol] []
    } := by decide

example : workRunExact? machine 30 (initialConfiguration 0 0 [] []) =
    some {
      state := WorkMachineProgramGraph.nodeState 4 (RegisterCopy.machine 1).acceptState
      tape := endTape [0, 0, 0, 0] [] []
    } := by decide

example : workRunExact? machine 40 (initialConfiguration 0 1 [] []) =
    some {
      state := WorkMachineProgramGraph.nodeState 3 (RegisterCopy.machine 2).acceptState
      tape := endTape [0, 0, 1, 0] [] []
    } := by decide

example : workRunExact? machine 37 (initialConfiguration 1 0 [] []) =
    some {
      state := WorkMachineProgramGraph.nodeState 6 BuilderConstraintRegionAssembly.Increment.machine.acceptState
      tape := endTape [1, 0, 0, 1] [] []
    } := by decide

example : workRunExact? machine 32 (initialConfiguration 0 0 [] []) = none := by decide
example : workRunExact? machine 42 (initialConfiguration 0 1 [] []) = none := by decide

example : workStep? machine {
      state := machine.startState
      tape := { left := [], head := .blank, right := [] }
    } = none := by decide

end LiteralRuns

example (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound) :
    workSteps coordinate boundary ≤ workBound bound :=
  workSteps_le coordinate boundary bound hCoordinate hBoundary

example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) :=
  rawTimePolynomial_eval bound input

example (coordinate boundary : Nat) (bound : NatPolynomial) (input : Nat)
    (hCoordinate : coordinate ≤ bound.eval input) (hBoundary : boundary ≤ bound.eval input) :
    6 * workSteps coordinate boundary ≤ (rawTimePolynomial bound).eval input :=
  rawTimePolynomial_le coordinate boundary bound input hCoordinate hBoundary

end PNP.Concrete.CookLevin.RegionResidualSelectionRegression
