import PNP.Concrete.CookLevinBuilderRegionRadixSource

namespace PNP.Concrete.CookLevinBuilderRegionRadixSourceRegression

open CookLevin PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPolynomialRegisterCopies (Address)

namespace Structural
open BuilderPolynomialRegisterCopies

example (polynomial : NatPolynomial) : (Address.root polynomial).selected = polynomial := rfl
example : (Address.addLeft (right := .constant 7) (.root .variable)).newerCount = 2 := rfl
example : (Address.addRight (left := .variable) (.root (.constant 7))).newerCount = 1 := rfl
example : (Address.mulLeft (right := .constant 7) (.root .variable)).newer 3 = [7, 21] := rfl
example : (Address.mulRight (left := .variable) (.root (.constant 7))).older 3 = [3] := rfl

example {polynomial : NatPolynomial} (address : Address polynomial) (input : Nat) :
    registerValues polynomial input =
      address.older input ++ [address.selected.eval input] ++ address.newer input :=
  address.layout input
example {polynomial : NatPolynomial} (address : Address polynomial) (input : Nat) :
    (address.newer input).length = address.newerCount := address.newer_length input
example {polynomial : NatPolynomial} (address : Address polynomial) (input : Nat) (before after : List Nat) :
    inputValues polynomial input before after =
      (before ++ address.older input) ++ [address.selected.eval input] ++ (address.newer input ++ after) :=
  inputValues_selection address input before after
example {polynomial : NatPolynomial} (address : Address polynomial) (afterCount : Nat) :
    copyMachine address afterCount = RegisterCopy.machine (address.newerCount + afterCount) := rfl

example {polynomial : NatPolynomial} (address : Address polynomial) (afterCount input : Nat)
    (before after : List Nat) (workspace : List WorkSymbol) (hCount : after.length = afterCount) :
    workRunExact? (copyMachine address afterCount) (copySteps address input after)
      (workStartConfiguration (copyMachine address afterCount)
        (endTape (inputValues polynomial input before after) workspace [])) =
      some {
        state := (copyMachine address afterCount).acceptState
        tape := endTape (inputValues polynomial input before after ++ [address.selected.eval input]) workspace []
      } := copy_workRunExact address afterCount input before after workspace hCount

example {polynomial : NatPolynomial} (addresses : List (Address polynomial))
    (afterCount input : Nat) (before after : List Nat) (workspace : List WorkSymbol) (hCount : after.length = afterCount) :
    workRunExact? (machine addresses afterCount) (workSteps addresses input after)
      (workStartConfiguration (machine addresses afterCount)
        (endTape (inputValues polynomial input before after) workspace [])) =
      some {
        state := (machine addresses afterCount).acceptState
        tape := endTape (inputValues polynomial input before after ++ values addresses input) workspace []
      } := workRunExact addresses afterCount input before after workspace hCount

example {polynomial : NatPolynomial} (addresses : List (Address polynomial))
    (afterCount input : Nat) (before after : List Nat) (workspace : List WorkSymbol) (hCount : after.length = afterCount) :
    run (compileWorkMachine (machine addresses afterCount)) (6 * workSteps addresses input after)
      (encodeWorkConfiguration (workStartConfiguration (machine addresses afterCount)
        (endTape (inputValues polynomial input before after) workspace []))) =
      encodeWorkConfiguration {
        state := (machine addresses afterCount).acceptState
        tape := endTape (inputValues polynomial input before after ++ values addresses input) workspace []
      } := run_compile_exact addresses afterCount input before after workspace hCount

example : values [Address.addLeft (right := .constant 7) (.root .variable),
    Address.addRight (left := .variable) (.root (.constant 7)),
    Address.root (.add .variable (.constant 7))] 3 = [3, 7, 10] := rfl
example : inputValues (.add .variable (.constant 7)) 3 [99] [5] = [99, 3, 7, 10, 5] := rfl
example (polynomial : NatPolynomial) (afterCount : Nat) :
    machine ([] : List (Address polynomial)) afterCount = BuilderRegionRadixDecoder.doneMachine := rfl

example {polynomial : NatPolynomial} (address : Address polynomial)
    (input : Nat) (before after : List Nat) (bound : Nat)
    (hSpan : (registerWord (inputValues polynomial input before after)).length ≤ bound) :
    address.selected.eval input ≤ bound ∧
      (address.newer input ++ after).length + (address.newer input ++ after).sum ≤ bound :=
  selection_bounds address input before after bound hSpan
example {polynomial : NatPolynomial} (address : Address polynomial)
    (input : Nat) (before after : List Nat) (bound : Nat)
    (hSpan : (registerWord (inputValues polynomial input before after)).length ≤ bound) :
    copySteps address input after ≤ copyBound bound := copySteps_le address input before after bound hSpan
example {polynomial : NatPolynomial} (addresses : List (Address polynomial))
    (input : Nat) (before after : List Nat) (bound : Nat)
    (hSpan : (registerWord (inputValues polynomial input before after)).length ≤ bound) :
    workSteps addresses input after ≤ workBound addresses.length bound :=
  workSteps_le addresses input before after bound hSpan
example {polynomial : NatPolynomial} (addresses : List (Address polynomial))
    (input : Nat) (before after : List Nat) (bound : Nat)
    (hSpan : (registerWord (inputValues polynomial input before after)).length ≤ bound) :
    (registerWord (inputValues polynomial input before after ++ values addresses input)).length ≤ spanBound addresses.length bound :=
  final_span_le addresses input before after bound hSpan
example (count bound : Nat) : bound ≤ spanBound count bound := spanBound_ge count bound
example (count : Nat) (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial count bound).eval input = spanBound count (bound.eval input) := spanPolynomial_eval count bound input
example (count : Nat) (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial count bound).eval input = 6 * workBound count (bound.eval input) := rawTimePolynomial_eval count bound input
example {polynomial : NatPolynomial} (addresses : List (Address polynomial))
    (input : Nat) (before after : List Nat) (bound : NatPolynomial)
    (hSpan : (registerWord (inputValues polynomial input before after)).length ≤ bound.eval input) :
    6 * workSteps addresses input after ≤ (rawTimePolynomial addresses.length bound).eval input :=
  rawTimePolynomial_le addresses input before after bound hSpan
example {polynomial : NatPolynomial} (addresses : List (Address polynomial)) (afterCount : Nat) :
    (machine addresses afterCount).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct addresses afterCount
example {polynomial : NatPolynomial} (addresses : List (Address polynomial)) (afterCount : Nat) :
    WorkMachineChain.NoRuleAtAccept (machine addresses afterCount) := noRuleAtAccept addresses afterCount
example {polynomial : NatPolynomial} (addresses : List (Address polynomial)) (afterCount : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine addresses afterCount) (machine addresses afterCount).rejectState := noRuleAtReject addresses afterCount
example {polynomial : NatPolynomial} (addresses : List (Address polynomial)) (afterCount : Nat) :
    (machine addresses afterCount).acceptState ≠ (machine addresses afterCount).rejectState := acceptState_ne_rejectState addresses afterCount

end Structural

namespace Source
open BuilderRegionRadixSource
open BuilderConstraintRegionRegisters (Region)
open BuilderConstraintRegionDispatch (regionTag)

example {language : Language} (verifier : PolynomialTimeVerifier language) (field : Field) :
    (fieldAddress verifier field).selected = fieldPolynomial verifier field := fieldAddress_selected verifier field
example {language : Language} (problem : VerifierTableauProblem language) (field : Field) :
    0 < fieldValue problem field := fieldValue_positive problem field
example : radixFields .shape = [.shapeWidth] := rfl
example : radixFields .initial = [] := rfl
example : radixFields .control = [.three, .three, .states, .tapeWidth] := rfl
example : radixFields .preservation = [.three, .tapeWidth, .tapeWidth] := rfl
example : radixFields .accepting = [] := rfl
example {language : Language} (problem : VerifierTableauProblem language) :
    radices problem .shape = [problem.dimensions.tapeWidth problem.tableauInputMode + 2] := shape_radices problem
example {language : Language} (problem : VerifierTableauProblem language) :
    radices problem .control = [3, 3, problem.dimensions.stateBound, problem.dimensions.tapeWidth problem.tableauInputMode] := control_radices problem
example {language : Language} (problem : VerifierTableauProblem language) :
    radices problem .preservation = [3, problem.dimensions.tapeWidth problem.tableauInputMode,
      problem.dimensions.tapeWidth problem.tableauInputMode] := preservation_radices problem
example {language : Language} (problem : VerifierTableauProblem language) (region : Region) :
    BuilderPolynomialRegisterCopies.values (addresses problem.verifier region) problem.input.length =
      (radices problem region).reverse := written_radices problem region
example {language : Language} (problem : VerifierTableauProblem language) (region : Region) :
    ∀ radix ∈ radices problem region, 0 < radix := radices_positive problem region

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderClauseCoordinateRegisters.finalValues problem index remaining =
      registerValues (formulaClauseCountPolynomial problem.verifier) problem.input.length ++
        sourceAfter problem index remaining := source_layout problem index remaining
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (region : Region) :
    (BuilderConstraintRegionSource.selectedScratch problem index region).length = 4 * regionTag region + 5 :=
  selectedScratch_length problem index region
example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (region : Region) :
    (sourceSuffix problem index remaining region).length = sourceCount problem.verifier region :=
  sourceSuffix_length problem index remaining region
example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (region : Region) :
    selectedValues problem index remaining region =
      BuilderPolynomialRegisterCopies.inputValues (formulaClauseCountPolynomial problem.verifier)
        problem.input.length [] (sourceSuffix problem index remaining region) := selectedValues_layout problem index remaining region

example {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    machine verifier region = WorkMachineChain.machine (prepareMachine verifier region)
      (BuilderRegionRadixDecoder.machine (radixFields region).length 0) := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    prepareMachine verifier region = WorkMachineChain.machine
      (BuilderPolynomialRegisterCopies.machine (addresses verifier region) (sourceCount verifier region))
      (RegisterCopy.machine ((radixFields region).length + 1)) := rfl

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (workspace : List WorkSymbol) (region : Region) :
    workRunExact? (prepareMachine problem.verifier region) (prepareSteps problem index remaining region)
      (workStartConfiguration (prepareMachine problem.verifier region)
        (endTape (selectedValues problem index remaining region) workspace [])) =
      some {
        state := (prepareMachine problem.verifier region).acceptState
        tape := endTape (preparedValues problem index remaining region) workspace []
      } := prepare_workRunExact problem index remaining workspace region

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (workspace : List WorkSymbol) (region : Region) :
    workRunExact? (machine problem.verifier region) (workSteps problem index remaining region)
      (workStartConfiguration (machine problem.verifier region)
        (endTape (selectedValues problem index remaining region) workspace [])) =
      some {
        state := (machine problem.verifier region).acceptState
        tape := endTape (finalValues problem index remaining region) workspace []
      } := workRunExact problem index remaining workspace region

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    workRunExact? (machine problem.verifier region) (workSteps problem index remaining region)
      (workStartConfiguration (machine problem.verifier region)
        (BuilderConstraintRegionSource.finalConfiguration problem index remaining output).tape) =
      some {
        state := (machine problem.verifier region).acceptState
        tape := endTape (finalValues problem index remaining region) (BuilderDividerOperands.inside problem.input output) []
      } := source_workRunExact problem index remaining output region hRegion

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    run (compileWorkMachine (machine problem.verifier region)) (6 * workSteps problem index remaining region)
      (encodeWorkConfiguration (workStartConfiguration (machine problem.verifier region)
        (BuilderConstraintRegionSource.finalConfiguration problem index remaining output).tape)) =
      encodeWorkConfiguration {
        state := (machine problem.verifier region).acceptState
        tape := endTape (finalValues problem index remaining region) (BuilderDividerOperands.inside problem.input output) []
      } := run_compile_exact problem index remaining output region hRegion

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (region : Region) :
    finalValues problem index remaining region = preparedValues problem index remaining region ++
      BuilderRegionRadixDecoder.extraValues (radices problem region)
        (BuilderConstraintRegionSource.localCoordinate problem index region) := finalValues_preserve_source problem index remaining region
example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (region : Region) :
    BuilderRegionRadixDecoder.reconstruct (radices problem region)
      (BuilderRegionRadixDecoder.packetDigits
        (BuilderRegionRadixDecoder.extraValues (radices problem region)
          (BuilderConstraintRegionSource.localCoordinate problem index region)))
      ((finalValues problem index remaining region).reverse.headD 0) = BuilderConstraintRegionSource.localCoordinate problem index region :=
  written_coordinate_reconstruct problem index remaining region

example {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (machine verifier region).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier region
example {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    WorkMachineChain.NoRuleAtAccept (machine verifier region) := noRuleAtAccept verifier region
example {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier region) (machine verifier region).rejectState := noRuleAtReject verifier region
example {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (machine verifier region).acceptState ≠ (machine verifier region).rejectState := acceptState_ne_rejectState verifier region

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (region : Region)
    (bound : Nat) (hSpan : (registerWord (selectedValues problem index remaining region)).length ≤ bound) :
    workSteps problem index remaining region ≤ workBound (radixFields region).length bound := workSteps_le problem index remaining region bound hSpan
example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (region : Region)
    (bound : Nat) (hSpan : (registerWord (selectedValues problem index remaining region)).length ≤ bound) :
    (registerWord (finalValues problem index remaining region)).length ≤ preparedBound (radixFields region).length bound +
      (radixFields region).length * (3 * preparedBound (radixFields region).length bound + 6) :=
  final_span_le problem index remaining region bound hSpan
example (splitCount : Nat) (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial splitCount bound).eval input = 6 * workBound splitCount (bound.eval input) := rawTimePolynomial_eval splitCount bound input
example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (region : Region)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    6 * workSteps problem index remaining region ≤ (rawTimeBound problem.verifier region).eval problem.input.length :=
  rawTimeBound_le problem index remaining region hBody hBalance hRegion

-- The empty schemas do not pretend to implement initial/acceptance constraint semantics.
example {language : Language} (problem : VerifierTableauProblem language) : radices problem .initial = [] := rfl
example {language : Language} (problem : VerifierTableauProblem language) : radices problem .accepting = [] := rfl
example {language : Language} (problem : VerifierTableauProblem language) :
    ¬ (0 ∈ radices problem .control) := by
  intro h
  exact Nat.lt_irrefl 0 (radices_positive problem .control 0 h)

end Source
end PNP.Concrete.CookLevinBuilderRegionRadixSourceRegression
