/-
Copyright (c) 2026 PNP Labs.

One literal runtime graph reads the source-derived region tag and enters one
of five fixed radix programs. The source assembly and selection run only once.
Semantic region decoding specifies the result; it never constructs the runtime
program. Local constraints, input reads, emission and the complete loop remain
separate obligations.
-/

import PNP.Concrete.CookLevinBuilderRegionRadixSource
import PNP.Concrete.CookLevinBuilderUnaryTagMatch

namespace PNP.Concrete.CookLevin.BuilderRegionRadixDispatch

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count)
open BuilderClauseDividerOperands (quotient)
open BuilderClauseDividerExecution (constraintIndex)
open BuilderConstraintRegionRegisters (Region regionLength)
open BuilderConstraintRegionDispatch (regionTag)
open WorkMachineProgramGraph (Node NodeRef Graph Endpoint)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)

def checkRef (region : Region) : NodeRef := { name := regionTag region, startState := 0 }

def entryNode {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) : Node :=
  { name := 5 + regionTag region
    program := BuilderRegionRadixSource.machine verifier region
    onAccept := .accept
    onReject := .dead }

def rejectTarget : Region → Endpoint
  | .shape => .node (checkRef .initial)
  | .initial => .node (checkRef .control)
  | .control => .node (checkRef .preservation)
  | .preservation => .node (checkRef .accepting)
  | .accepting => .reject

def checkNode {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) : Node :=
  { name := regionTag region
    program := BuilderUnaryTagMatch.machine (regionTag region)
    onAccept := .node (entryNode verifier region).reference
    onReject := rejectTarget region }

theorem checkNode_reference {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (checkNode verifier region).reference = checkRef region := rfl

/-- All programs and bridge destinations are fixed by the verifier, not the input. -/
def graph {language : Language} (verifier : PolynomialTimeVerifier language) : Graph :=
  { nodes := [checkNode verifier .shape, checkNode verifier .initial, checkNode verifier .control,
      checkNode verifier .preservation, checkNode verifier .accepting,
      entryNode verifier .shape, entryNode verifier .initial, entryNode verifier .control,
      entryNode verifier .preservation, entryNode verifier .accepting]
    entry := checkRef .shape }

def dispatchMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph verifier)

private theorem check_mem {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    checkNode verifier region ∈ (graph verifier).nodes := by
  cases region with
  | shape => exact List.Mem.head _
  | initial => exact List.Mem.tail _ (List.Mem.head _)
  | control => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | preservation => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | accepting => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

private theorem entry_mem {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    entryNode verifier region ∈ (graph verifier).nodes := by
  cases region with
  | shape => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  | initial => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  | control => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  | preservation => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  | accepting => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

private theorem check_good {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (checkNode verifier region).WellFormed :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct _, BuilderUnaryTagMatch.noRuleAtAccept _, BuilderUnaryTagMatch.noRuleAtReject _,
    BuilderUnaryTagMatch.acceptState_ne_rejectState _⟩

private theorem entry_good {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (entryNode verifier region).WellFormed :=
  ⟨BuilderRegionRadixSource.rules_pairwise_query_distinct _ _, BuilderRegionRadixSource.noRuleAtAccept _ _, BuilderRegionRadixSource.noRuleAtReject _ _,
    BuilderRegionRadixSource.acceptState_ne_rejectState _ _⟩

private theorem check_resolves {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    Endpoint.Resolves (graph verifier).nodes (.node (checkRef region)) :=
  ⟨checkNode verifier region, check_mem verifier region, rfl, rfl⟩

private theorem entry_resolves {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    Endpoint.Resolves (graph verifier).nodes (.node (entryNode verifier region).reference) :=
  ⟨entryNode verifier region, entry_mem verifier region, rfl, rfl⟩

private theorem targets_resolve {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    Endpoint.Resolves (graph verifier).nodes (checkNode verifier region).onAccept ∧
      Endpoint.Resolves (graph verifier).nodes (checkNode verifier region).onReject := by
  refine ⟨entry_resolves verifier region, ?_⟩
  cases region with
  | shape => exact check_resolves verifier .initial
  | initial => exact check_resolves verifier .control
  | control => exact check_resolves verifier .preservation
  | preservation => exact check_resolves verifier .accepting
  | accepting => exact True.intro

theorem graph_wellFormed {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).WellFormed := by
  have hNames : ((graph verifier).nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List Nat).Pairwise (fun left right => left ≠ right)
    decide
  refine ⟨?_, ?_, check_resolves verifier .shape, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact check_good verifier .shape
    · exact check_good verifier .initial
    · exact check_good verifier .control
    · exact check_good verifier .preservation
    · exact check_good verifier .accepting
    · exact entry_good verifier .shape
    · exact entry_good verifier .initial
    · exact entry_good verifier .control
    · exact entry_good verifier .preservation
    · exact entry_good verifier .accepting
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact targets_resolve verifier .shape
    · exact targets_resolve verifier .initial
    · exact targets_resolve verifier .control
    · exact targets_resolve verifier .preservation
    · exact targets_resolve verifier .accepting
    all_goals exact ⟨True.intro, True.intro⟩

theorem graph_nodes_length {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).nodes.length = 10 := rfl

theorem dispatch_rules_pairwise {language : Language} (verifier : PolynomialTimeVerifier language) :
    (dispatchMachine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise (graph verifier) (graph_wellFormed verifier)

theorem dispatch_noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (dispatchMachine verifier) :=
  WorkMachineProgramGraph.noRuleAt_globalAccept (graph verifier)

theorem dispatch_noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (dispatchMachine verifier) (dispatchMachine verifier).rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject (graph verifier)

theorem dispatch_accept_ne_reject {language : Language} (verifier : PolynomialTimeVerifier language) :
    (dispatchMachine verifier).acceptState ≠ (dispatchMachine verifier).rejectState := by
  change 0 ≠ 1
  decide

def beforeTag {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) : List Nat :=
  BuilderConstraintRegionAssembly.finalValues problem index remaining ++
    BuilderConstraintRegionDispatch.prefixScratch (BuilderConstraintRegionSource.lengths problem) (constraintIndex problem index) region ++
    BuilderConstraintRegionDispatch.restored (BuilderConstraintRegionSource.localCoordinate problem index region) (regionLength problem region) ++
    [BuilderConstraintRegionSource.localCoordinate problem index region]

theorem selectedValues_tag {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) :
    BuilderRegionRadixSource.selectedValues problem index remaining region =
      beforeTag problem index remaining region ++ [regionTag region] := by
  simp only [BuilderRegionRadixSource.selectedValues, BuilderConstraintRegionSource.selectedScratch, beforeTag,
    List.append_assoc, List.cons_append, List.nil_append]

private theorem check_accept {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (older : List Nat) (workspace tail : List WorkSymbol) :
    LocalAcceptRun (checkNode verifier region) (BuilderUnaryTagMatch.workSteps (regionTag region) (regionTag region))
      (endTape (older ++ [regionTag region]) workspace tail)
      (endTape (older ++ [regionTag region]) workspace tail) :=
  BuilderUnaryTagMatch.accept_workRunExact (regionTag region) older workspace tail

private theorem check_reject {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (actual : Nat) (older : List Nat) (workspace tail : List WorkSymbol)
    (hNe : actual ≠ regionTag region) :
    LocalRejectRun (checkNode verifier region) (BuilderUnaryTagMatch.workSteps (regionTag region) actual)
      (endTape (older ++ [actual]) workspace tail) (endTape (older ++ [actual]) workspace tail) :=
  BuilderUnaryTagMatch.reject_workRunExact (regionTag region) actual older workspace tail hNe

private theorem reject_prefix {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (actual : Nat) (older : List Nat) (workspace tail : List WorkSymbol)
    (endpoint : Endpoint) (tailSteps : Nat) (finalTape : WorkTape)
    (hNe : actual ≠ regionTag region)
    (hTail : AcceptPath (graph verifier) (rejectTarget region) endpoint tailSteps
      (endTape (older ++ [actual]) workspace tail) finalTape) :
    AcceptPath (graph verifier) (.node (checkRef region)) endpoint
      (BuilderUnaryTagMatch.workSteps (regionTag region) actual + 1 + tailSteps)
      (endTape (older ++ [actual]) workspace tail) finalTape :=
  AcceptPath.stepReject (checkNode verifier region) endpoint _ _ _ _ _
    (check_mem verifier region) (check_reject verifier region actual older workspace tail hNe) hTail

private theorem selected_path {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (workspace : List WorkSymbol) :
    AcceptPath (graph problem.verifier) (.node (checkRef region)) .accept
      (BuilderUnaryTagMatch.workSteps (regionTag region) (regionTag region) + 1 + (BuilderRegionRadixSource.workSteps problem index remaining region + 1))
      (endTape (BuilderRegionRadixSource.selectedValues problem index remaining region) workspace [])
      (endTape (BuilderRegionRadixSource.finalValues problem index remaining region) workspace []) := by
  have hEntry := AcceptPath.step (entryNode problem.verifier region) .accept
    (BuilderRegionRadixSource.workSteps problem index remaining region) 0 _ _ _ (entry_mem problem.verifier region)
    (BuilderRegionRadixSource.workRunExact problem index remaining workspace region)
    (AcceptPath.terminal .accept _)
  have hCheck : LocalAcceptRun (checkNode problem.verifier region)
      (BuilderUnaryTagMatch.workSteps (regionTag region) (regionTag region))
      (endTape (BuilderRegionRadixSource.selectedValues problem index remaining region) workspace [])
      (endTape (BuilderRegionRadixSource.selectedValues problem index remaining region) workspace []) := by
    rw [selectedValues_tag]
    exact check_accept problem.verifier region (beforeTag problem index remaining region) workspace []
  simpa only [Nat.add_zero, checkNode_reference] using AcceptPath.step (checkNode problem.verifier region) .accept
    (BuilderUnaryTagMatch.workSteps (regionTag region) (regionTag region)) (BuilderRegionRadixSource.workSteps problem index remaining region + 1)
    _ _ _ (check_mem problem.verifier region) hCheck hEntry

def routeSteps (region : Region) : Nat := (regionTag region + 1) * (regionTag region + 4)

def dispatchSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) : Nat :=
  routeSteps region + BuilderRegionRadixSource.workSteps problem index remaining region + 1

private theorem path_steps {graph : Graph} {start finish : Endpoint} {steps expected : Nat}
    {initial final : WorkTape} (path : AcceptPath graph start finish steps initial final)
    (hSteps : steps = expected) : AcceptPath graph start finish expected initial final :=
  hSteps ▸ path

private theorem dispatch_path {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (workspace : List WorkSymbol) :
    AcceptPath (graph problem.verifier) (.node (checkRef .shape)) .accept
      (dispatchSteps problem index remaining region)
      (endTape (BuilderRegionRadixSource.selectedValues problem index remaining region) workspace [])
      (endTape (BuilderRegionRadixSource.finalValues problem index remaining region) workspace []) := by
  have h := selected_path problem index remaining region workspace
  rw [selectedValues_tag] at h ⊢
  cases region with
  | shape =>
      apply path_steps h
      simp only [dispatchSteps, routeSteps, regionTag, BuilderUnaryTagMatch.workSteps]
      omega
  | initial =>
      have h0 := reject_prefix problem.verifier .shape 1 _ workspace [] .accept _ _ (by decide) h
      apply path_steps h0
      simp only [dispatchSteps, routeSteps, regionTag, BuilderUnaryTagMatch.workSteps]
      omega
  | control =>
      have h1 := reject_prefix problem.verifier .initial 2 _ workspace [] .accept _ _ (by decide) h
      have h0 := reject_prefix problem.verifier .shape 2 _ workspace [] .accept _ _ (by decide) h1
      apply path_steps h0
      simp only [dispatchSteps, routeSteps, regionTag, BuilderUnaryTagMatch.workSteps]
      omega
  | preservation =>
      have h2 := reject_prefix problem.verifier .control 3 _ workspace [] .accept _ _ (by decide) h
      have h1 := reject_prefix problem.verifier .initial 3 _ workspace [] .accept _ _ (by decide) h2
      have h0 := reject_prefix problem.verifier .shape 3 _ workspace [] .accept _ _ (by decide) h1
      apply path_steps h0
      simp only [dispatchSteps, routeSteps, regionTag, BuilderUnaryTagMatch.workSteps]
      omega
  | accepting =>
      have h3 := reject_prefix problem.verifier .preservation 4 _ workspace [] .accept _ _ (by decide) h
      have h2 := reject_prefix problem.verifier .control 4 _ workspace [] .accept _ _ (by decide) h3
      have h1 := reject_prefix problem.verifier .initial 4 _ workspace [] .accept _ _ (by decide) h2
      have h0 := reject_prefix problem.verifier .shape 4 _ workspace [] .accept _ _ (by decide) h1
      apply path_steps h0
      simp only [dispatchSteps, routeSteps, regionTag, BuilderUnaryTagMatch.workSteps]
      omega

theorem dispatch_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (workspace : List WorkSymbol) :
    workRunExact? (dispatchMachine problem.verifier) (dispatchSteps problem index remaining region)
      (workStartConfiguration (dispatchMachine problem.verifier)
        (endTape (BuilderRegionRadixSource.selectedValues problem index remaining region) workspace [])) =
      some { state := (dispatchMachine problem.verifier).acceptState,
             tape := endTape (BuilderRegionRadixSource.finalValues problem index remaining region) workspace [] } :=
  WorkMachineProgramPath.runEntryToAccept (graph problem.verifier) _ _ _
    (graph_wellFormed problem.verifier) (dispatch_path problem index remaining region workspace)

theorem reject_invalid_tag {language : Language} (verifier : PolynomialTimeVerifier language)
    (actual : Nat) (older : List Nat) (workspace tail : List WorkSymbol) (hInvalid : 5 ≤ actual) :
    workRunExact? (dispatchMachine verifier) 40
      (workStartConfiguration (dispatchMachine verifier) (endTape (older ++ [actual]) workspace tail)) =
      some { state := (dispatchMachine verifier).rejectState, tape := endTape (older ++ [actual]) workspace tail } := by
  have h4 := reject_prefix verifier .accepting actual older workspace tail .reject 0 _ (by change actual ≠ 4; omega)
    (AcceptPath.terminal .reject _)
  have h3 := reject_prefix verifier .preservation actual older workspace tail .reject _ _ (by change actual ≠ 3; omega) h4
  have h2 := reject_prefix verifier .control actual older workspace tail .reject _ _ (by change actual ≠ 2; omega) h3
  have h1 := reject_prefix verifier .initial actual older workspace tail .reject _ _ (by change actual ≠ 1; omega) h2
  have h0 := reject_prefix verifier .shape actual older workspace tail .reject _ _ (by change actual ≠ 0; omega) h1
  have hSteps (tag : Nat) (hTag : tag ≤ 4) : BuilderUnaryTagMatch.workSteps tag actual = 2 * tag + 3 := by
    unfold BuilderUnaryTagMatch.workSteps
    have hMin : min actual tag = tag := by omega
    rw [hMin]
  have hPath : AcceptPath (graph verifier) (.node (checkRef .shape)) .reject 40
      (endTape (older ++ [actual]) workspace tail) (endTape (older ++ [actual]) workspace tail) := by
    apply path_steps h0
    simp only [regionTag, hSteps 0 (by omega), hSteps 1 (by omega), hSteps 2 (by omega),
      hSteps 3 (by omega), hSteps 4 (by omega)]
  exact WorkMachineProgramPath.runEntryToReject (graph verifier) 40 _ _ (graph_wellFormed verifier) hPath

theorem routeSteps_le (region : Region) : routeSteps region ≤ 40 := by cases region <;> decide

/-- A result specification only. The runtime machine never calls this function. -/
def selectedRegion {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Region :=
  (BuilderConstraintRegionSource.selectedRegion problem index).getD .shape

theorem selectedRegion_correct {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    BuilderConstraintRegionSource.selectedRegion problem index = some (selectedRegion problem index) := by
  rcases BuilderConstraintRegionSource.selectedRegion_some_of_body problem index hBody with ⟨region, hRegion⟩
  simpa only [selectedRegion, hRegion, Option.getD_some] using hRegion

/-- Source assembly/selection occurs exactly once before the fixed tag graph. -/
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderConstraintRegionSource.machine verifier) (dispatchMachine verifier)

def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderConstraintRegionSource.workSteps problem index remaining + 1 +
    dispatchSteps problem index remaining (selectedRegion problem index)

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (BuilderCursorSource.cursorTape problem index remaining output)

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  BuilderRegionRadixSource.finalValues problem index remaining (selectedRegion problem index)

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  { state := (machine problem.verifier).acceptState
    tape := endTape (finalValues problem index remaining) (inside problem.input output) [] }

private theorem chain_run (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some { state := first.acceptState, tape := middle })
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some { state := second.acceptState, tape := final }) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some { state := (WorkMachineChain.machine first second).acceptState, tape := final } :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

private theorem configuration_eq (configuration : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : configuration.state = state) (hTape : configuration.tape = tape) :
    configuration = { state := state, tape := tape } := by
  cases configuration
  cases hState
  cases hTape
  rfl

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := by
  have hRegion := selectedRegion_correct problem index hBody
  have hSource := BuilderConstraintRegionSource.workRunExact problem index remaining output hBody
  have hFinal := configuration_eq (BuilderConstraintRegionSource.finalConfiguration problem index remaining output)
    (BuilderConstraintRegionSource.machine problem.verifier).acceptState
    (endTape (BuilderRegionRadixSource.selectedValues problem index remaining (selectedRegion problem index))
      (inside problem.input output) [])
    (BuilderConstraintRegionSource.final_accept_of_body problem index remaining output hBody)
    (BuilderRegionRadixSource.selected_source_handoff problem index remaining output (selectedRegion problem index) hRegion)
  rw [hFinal] at hSource
  exact chain_run (BuilderConstraintRegionSource.machine problem.verifier) (dispatchMachine problem.verifier)
    (BuilderConstraintRegionSource.workSteps problem index remaining)
    (dispatchSteps problem index remaining (selectedRegion problem index)) _ _ _ hSource
    (dispatch_workRunExact problem index remaining (selectedRegion problem index) (inside problem.input output))

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output hBody)

theorem final_tape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      endTape (finalValues problem index remaining) (inside problem.input output) [] := rfl

theorem final_accept {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState := rfl

theorem finalValues_preserve_source {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem) :
    ∃ suffix, finalValues problem index remaining = BuilderConstraintRegionSource.finalValues problem index remaining ++ suffix := by
  let region := selectedRegion problem index
  refine ⟨(BuilderRegionRadixSource.radices problem region).reverse ++ [BuilderConstraintRegionSource.localCoordinate problem index region] ++
    BuilderRegionRadixDecoder.extraValues (BuilderRegionRadixSource.radices problem region)
      (BuilderConstraintRegionSource.localCoordinate problem index region), ?_⟩
  have hRegion := selectedRegion_correct problem index hBody
  have hPrefix := BuilderConstraintRegionSource.finalValues_of_region problem index remaining region hRegion
  have hFinal := BuilderRegionRadixSource.finalValues_preserve_source problem index remaining region
  simpa only [finalValues, region, BuilderRegionRadixSource.preparedValues, BuilderRegionRadixSource.selectedValues,
    hPrefix, List.append_assoc] using hFinal

theorem written_coordinate_reconstruct {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    BuilderRegionRadixDecoder.reconstruct (BuilderRegionRadixSource.radices problem (selectedRegion problem index))
      (BuilderRegionRadixDecoder.packetDigits
        (BuilderRegionRadixDecoder.extraValues (BuilderRegionRadixSource.radices problem (selectedRegion problem index))
          (BuilderConstraintRegionSource.localCoordinate problem index (selectedRegion problem index))))
      ((finalValues problem index remaining).reverse.headD 0) =
        BuilderConstraintRegionSource.localCoordinate problem index (selectedRegion problem index) :=
  BuilderRegionRadixSource.written_coordinate_reconstruct problem index remaining (selectedRegion problem index)

def entryTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderRegionRadixSource.rawTimeBound verifier .shape)
    (.add (BuilderRegionRadixSource.rawTimeBound verifier .initial)
      (.add (BuilderRegionRadixSource.rawTimeBound verifier .control)
        (.add (BuilderRegionRadixSource.rawTimeBound verifier .preservation) (BuilderRegionRadixSource.rawTimeBound verifier .accepting))))

theorem entryTimeBound_le {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (inputLength : Nat) :
    (BuilderRegionRadixSource.rawTimeBound verifier region).eval inputLength ≤ (entryTimeBound verifier).eval inputLength := by
  cases region <;> simp only [entryTimeBound, NatPolynomial.eval_add] <;> omega

/-- Includes the entire source execution, all tag tests and every new bridge. -/
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderConstraintRegionSource.rawTimeBound verifier) (.add (.constant 252) (entryTimeBound verifier))

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hRegion := selectedRegion_correct problem index hBody
  have hSource := BuilderConstraintRegionSource.rawTimeBound_le problem index remaining hBalance
  have hEntry := BuilderRegionRadixSource.rawTimeBound_le problem index remaining (selectedRegion problem index) hBody hBalance hRegion
  have hSum := entryTimeBound_le problem.verifier (selectedRegion problem index) problem.input.length
  have hRoute := routeSteps_le (selectedRegion problem index)
  simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant, workSteps, dispatchSteps]
  omega


/-- Only generated registers are charged here; an arbitrary prior output prefix
is preserved in the workspace and is not claimed as newly bounded output. -/
def entrySpanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) : NatPolynomial :=
  let splits := (BuilderRegionRadixSource.radixFields region).length
  let prepared := BuilderRegionRadixSource.preparedPolynomial splits (BuilderRegionRadixSource.sourceBound verifier)
  .add prepared (.mul (.constant splits) (.add (.mul (.constant 3) prepared) (.constant 6)))

theorem entrySpanPolynomial_eval {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (inputLength : Nat) :
    (entrySpanPolynomial verifier region).eval inputLength =
      BuilderRegionRadixSource.preparedBound (BuilderRegionRadixSource.radixFields region).length
        ((BuilderRegionRadixSource.sourceBound verifier).eval inputLength) +
      (BuilderRegionRadixSource.radixFields region).length *
        (3 * BuilderRegionRadixSource.preparedBound (BuilderRegionRadixSource.radixFields region).length
          ((BuilderRegionRadixSource.sourceBound verifier).eval inputLength) + 6) := by
  simp only [entrySpanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant,
    BuilderRegionRadixSource.preparedPolynomial_eval]

def finalRegisterSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (entrySpanPolynomial verifier .shape)
    (.add (entrySpanPolynomial verifier .initial)
      (.add (entrySpanPolynomial verifier .control)
        (.add (entrySpanPolynomial verifier .preservation) (entrySpanPolynomial verifier .accepting))))

theorem entrySpanPolynomial_le {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (inputLength : Nat) :
    (entrySpanPolynomial verifier region).eval inputLength ≤ (finalRegisterSpanBound verifier).eval inputLength := by
  cases region <;> simp only [finalRegisterSpanBound, NatPolynomial.eval_add] <;> omega

theorem final_register_span_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining)).length ≤
      (finalRegisterSpanBound problem.verifier).eval problem.input.length := by
  have hRegion := selectedRegion_correct problem index hBody
  have hSpan := BuilderRegionRadixSource.selected_span_le problem index remaining
    (selectedRegion problem index) hBody hBalance hRegion
  have h := BuilderRegionRadixSource.final_span_le problem index remaining (selectedRegion problem index) _ hSpan
  have hLocal : (registerWord (finalValues problem index remaining)).length ≤
      (entrySpanPolynomial problem.verifier (selectedRegion problem index)).eval problem.input.length := by
    simpa only [finalValues, entrySpanPolynomial_eval] using h
  exact Nat.le_trans hLocal (entrySpanPolynomial_le problem.verifier (selectedRegion problem index) problem.input.length)

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _ (BuilderConstraintRegionSource.rules_pairwise_query_distinct verifier)
    (dispatch_rules_pairwise verifier) (BuilderConstraintRegionSource.noRuleAtAccept verifier)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineChain.noRuleAtAccept _ _ (dispatch_noRuleAtAccept verifier)

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  WorkMachineChain.noRuleAtAccept (BuilderConstraintRegionSource.machine verifier)
    { dispatchMachine verifier with acceptState := (dispatchMachine verifier).rejectState }
    (dispatch_noRuleAtReject verifier)

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ (dispatch_accept_ne_reject verifier)

end PNP.Concrete.CookLevin.BuilderRegionRadixDispatch
