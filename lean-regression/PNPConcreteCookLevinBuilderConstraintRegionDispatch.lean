import PNP.Concrete.CookLevinBuilderConstraintRegionDispatch

namespace PNP.Concrete.CookLevinBuilderConstraintRegionDispatchRegression

open CookLevin PipelineTape
open BuilderConstraintRegionDispatch
open BuilderDividerOperands (endTape)
open BuilderConstraintRegionRegisters (Region)

example (tag : Nat) (values : List Nat) (workspace tail : List WorkSymbol) :
    workRunExact? (Tag.machine tag) (Tag.steps tag)
      (workStartConfiguration (Tag.machine tag) (endTape values workspace tail)) =
      some {
        state := (Tag.machine tag).acceptState
        tape := endTape (values ++ [tag]) workspace (tail.drop (tag + 1))
      } :=
  Tag.workRunExact tag values workspace tail

example (tag : Nat) : (Tag.machine tag).rules.length = 18 + 27 * tag := Tag.rules_length tag
example (tag : Nat) : (Tag.machine tag).rules.Pairwise WorkMachineChain.QueryDistinct :=
  Tag.rules_pairwise_query_distinct tag
example (tag : Nat) : WorkMachineChain.NoRuleAtAccept (Tag.machine tag) := Tag.noRuleAtAccept tag
example (tag : Nat) : WorkMachineProgramGraph.NoRuleAt (Tag.machine tag) (Tag.machine tag).rejectState :=
  Tag.noRuleAtReject tag
example (tag : Nat) : (Tag.machine tag).acceptState ≠ (Tag.machine tag).rejectState :=
  Tag.acceptState_ne_rejectState tag

example : graph.nodes.map WorkMachineProgramGraph.Node.name = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
example : graph.WellFormed := graph_wellFormed
example : machine.rules.length = 5080 := rules_length
example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

example (lengths : Lengths) (coordinate : Nat) (region : Region) :
    (newerValues lengths coordinate region).length = 5 * regionTag region := newer_length lengths coordinate region

example (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps lengths coordinate)
      (workStartConfiguration machine (endTape (older ++ frame lengths ++ [coordinate]) workspace [])) =
      some (finalConfiguration lengths coordinate older workspace) :=
  workRunExact lengths coordinate older workspace

example (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps lengths coordinate)
      (encodeWorkConfiguration (initialConfiguration lengths coordinate older workspace)) =
      encodeWorkConfiguration (finalConfiguration lengths coordinate older workspace) :=
  run_compile_exact lengths coordinate older workspace

example (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration lengths coordinate older workspace).state = machine.acceptState ↔
      coordinate < total lengths := final_accept_iff lengths coordinate older workspace

example (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration lengths coordinate older workspace).state = machine.rejectState ↔
      total lengths ≤ coordinate := final_reject_iff lengths coordinate older workspace

example (lengths : Lengths) (coordinate : Nat) (region : Region)
    (hRegion : selectedRegion lengths coordinate = some region) :
    remaining lengths coordinate region < boundary lengths region :=
  selectedRegion_local_valid lengths coordinate region hRegion

example (lengths : Lengths) (coordinate : Nat) :
    selectedRegion lengths coordinate = none ↔ total lengths ≤ coordinate :=
  selectedRegion_none_iff lengths coordinate

example (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol)
    (region : Region) (hRegion : selectedRegion lengths coordinate = some region) :
    (finalConfiguration lengths coordinate older workspace).tape =
      endTape ((stageInput lengths coordinate older region ++
        restored (remaining lengths coordinate region) (boundary lengths region)) ++
        [remaining lengths coordinate region, regionTag region]) workspace [] :=
  final_selected_tape lengths coordinate older workspace region hRegion

example (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol)
    (region : Region) (hRegion : selectedRegion lengths coordinate = some region) :
    (finalConfiguration lengths coordinate older workspace).tape =
      endTape (initialValues lengths coordinate older ++
        (prefixScratch lengths coordinate region ++
          restored (remaining lengths coordinate region) (boundary lengths region) ++
          [remaining lengths coordinate region, regionTag region])) workspace [] :=
  final_selected_preserves_frame lengths coordinate older workspace region hRegion

example (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration lengths coordinate older workspace).tape.left = [] :=
  final_outer_empty lengths coordinate older workspace

example (lengths : Lengths) (coordinate : Nat) (region : Region) :
    remaining lengths coordinate region ≤ coordinate := remaining_le lengths coordinate region

example (lengths : Lengths) (coordinate bound : Nat) (region : Region)
    (hq : coordinate ≤ bound) (hb : ∀ region, boundary lengths region ≤ bound) :
    (newerValues lengths coordinate region).length + (newerValues lengths coordinate region).sum ≤
      24 * bound + 20 := newer_size_le lengths coordinate bound region hq hb

example (lengths : Lengths) (coordinate bound : Nat)
    (hq : coordinate ≤ bound) (hb : ∀ region, boundary lengths region ≤ bound) :
    workSteps lengths coordinate ≤ workBound bound := workSteps_le lengths coordinate bound hq hb

example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := rawTimePolynomial_eval bound input

example (lengths : Lengths) (coordinate input : Nat) (bound : NatPolynomial)
    (hq : coordinate ≤ bound.eval input) (hb : ∀ region, boundary lengths region ≤ bound.eval input) :
    6 * workSteps lengths coordinate ≤ (rawTimePolynomial bound).eval input :=
  rawTimePolynomial_le lengths coordinate input bound hq hb

-- Independent semantic boundary fixtures: equality proceeds to the next region.
example : selectedRegion ⟨1, 1, 1, 1, 1⟩ 0 = some .shape := by decide
example : selectedRegion ⟨1, 1, 1, 1, 1⟩ 1 = some .initial := by decide
example : selectedRegion ⟨1, 1, 1, 1, 1⟩ 2 = some .control := by decide
example : selectedRegion ⟨1, 1, 1, 1, 1⟩ 3 = some .preservation := by decide
example : selectedRegion ⟨1, 1, 1, 1, 1⟩ 4 = some .accepting := by decide
example : selectedRegion ⟨1, 1, 1, 1, 1⟩ 5 = none := by decide
example : selectedRegion ⟨0, 0, 0, 0, 0⟩ 0 = none := by decide
example : selectedRegion ⟨0, 0, 0, 0, 1⟩ 0 = some .accepting := by decide
example : selectedRegion ⟨0, 2, 0, 1, 1⟩ 2 = some .preservation := by decide
example : remaining ⟨0, 2, 0, 1, 1⟩ 2 .preservation = 0 := by decide

-- Each literal schedule has all preceding regions empty. A rejection costs
-- 51 + 10*i, the selected comparison costs 76 + 20*j, each comparison bridge
-- costs one, and the tag plus its bridge costs 3 + 3*j.

example : workSteps ⟨1, 0, 0, 0, 0⟩ 0 = 80 := by decide

example :
    workRunExact? machine 80 (initialConfiguration ⟨1, 0, 0, 0, 0⟩ 0 [2] [.oneBlank]) =
      some {
        state := machine.acceptState
        tape := endTape [2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0] [.oneBlank] []
      } := by
  exact workRunExact ⟨1, 0, 0, 0, 0⟩ 0 [2] [.oneBlank]

example : workSteps ⟨0, 1, 0, 0, 0⟩ 0 = 155 := by decide

example :
    workRunExact? machine 155 (initialConfiguration ⟨0, 1, 0, 0, 0⟩ 0 [2] [.oneBlank]) =
      some {
        state := machine.acceptState
        tape := endTape [2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1] [.oneBlank] []
      } := by
  exact workRunExact ⟨0, 1, 0, 0, 0⟩ 0 [2] [.oneBlank]

example : workSteps ⟨0, 0, 1, 0, 0⟩ 0 = 240 := by decide

example :
    workRunExact? machine 240 (initialConfiguration ⟨0, 0, 1, 0, 0⟩ 0 [2] [.oneBlank]) =
      some {
        state := machine.acceptState
        tape := endTape [2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2] [.oneBlank] []
      } := by
  exact workRunExact ⟨0, 0, 1, 0, 0⟩ 0 [2] [.oneBlank]

example : workSteps ⟨0, 0, 0, 1, 0⟩ 0 = 335 := by decide

example :
    workRunExact? machine 335 (initialConfiguration ⟨0, 0, 0, 1, 0⟩ 0 [2] [.oneBlank]) =
      some {
        state := machine.acceptState
        tape := endTape [2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3] [.oneBlank] []
      } := by
  exact workRunExact ⟨0, 0, 0, 1, 0⟩ 0 [2] [.oneBlank]

example : workSteps ⟨0, 0, 0, 0, 1⟩ 0 = 440 := by decide

example :
    workRunExact? machine 440 (initialConfiguration ⟨0, 0, 0, 0, 1⟩ 0 [2] [.oneBlank]) =
      some {
        state := machine.acceptState
        tape := endTape [2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4] [.oneBlank] []
      } := by
  exact workRunExact ⟨0, 0, 0, 0, 1⟩ 0 [2] [.oneBlank]

example : workSteps ⟨0, 0, 0, 0, 0⟩ 0 = 360 := by decide

example :
    workRunExact? machine 360 (initialConfiguration ⟨0, 0, 0, 0, 0⟩ 0 [] [.zeroOne]) =
      some {
        state := machine.rejectState
        tape := endTape [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [.zeroOne] []
      } := by
  exact workRunExact ⟨0, 0, 0, 0, 0⟩ 0 [] [.zeroOne]

section LiteralTransitions
set_option maxRecDepth 4096

example :
    workRunExact? (Tag.machine 4) 14
      (workStartConfiguration (Tag.machine 4) (endTape [1] [.zeroOne] [.blank, .oneBlank])) =
      some {
        state := (Tag.machine 4).acceptState
        tape := endTape [1, 4] [.zeroOne] []
      } := by decide

-- Malformed input follows the explicit dead transition, then has no rule.
-- This literal 5,080-rule negative lookup needs deeper structural reduction.
set_option maxRecDepth 16384 in
example :
    workRunExact? machine 2
      (workStartConfiguration machine { left := [], head := .blank, right := [] }) = none := by decide

-- A missing graph transition is not an accept result.
example :
    workRunExact? machine 0 (initialConfiguration ⟨1, 0, 0, 0, 0⟩ 0 [] []) ≠
      some (finalConfiguration ⟨1, 0, 0, 0, 0⟩ 0 [] []) := by decide

end LiteralTransitions
end PNP.Concrete.CookLevinBuilderConstraintRegionDispatchRegression
