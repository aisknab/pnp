import PNP

namespace PNP.Concrete.CookLevinBuilderArbitrarySlotHeaderRouterRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderArbitrarySlotHeaderRouter

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

def inputOnlyVerifier : PolynomialTimeVerifier (fun _ => True) :=
  verifierFromDecider
    (PolynomialTimeDecider.ofMachine acceptAllPolynomialTime)

def pairedVerifier : PolynomialTimeVerifier (fun _ => True) :=
  { program :=
      { inputMode := .paired
        decision := .machine immediateAcceptMachine (.constant 0) }
    certificateBound := .linear 1 1
    runtimeBound := .constant 0
    haltsWithin := by
      intro input certificate hCertificate
      exact Verdict.noConfusion
    runtime_le := by
      intro input certificate hCertificate
      exact Nat.le_refl 0
    accepts_iff := by
      intro input
      constructor
      · intro member
        exact ⟨[], Nat.zero_le _, rfl⟩
      · intro witness
        exact True.intro }

def inputOnlyProblem (input : BitString) :
    VerifierTableauProblem (fun _ => True) :=
  { verifier := inputOnlyVerifier, input := input }

def pairedProblem (input : BitString) :
    VerifierTableauProblem (fun _ => True) :=
  { verifier := pairedVerifier, input := input }

example (input : BitString) (coordinate : Nat) :
    (inputOnlyProblem input).formulaTokenSlotDirect coordinate =
      match outerRoute (inputOnlyProblem input) coordinate with
      | .header headerCoordinate =>
          (inputOnlyProblem input).formulaHeaderTokenSlotDirect
            headerCoordinate
      | .postHeader remainder =>
          postHeaderSlotDirect (inputOnlyProblem input) remainder :=
  formulaTokenSlotDirect_route (inputOnlyProblem input) coordinate

example (input : BitString) (coordinate : Nat) :
    outerRoute (pairedProblem input) coordinate = .header coordinate ↔
      coordinate <
        BuilderFullScheduleCursorController.firstBodySlot
          (pairedProblem input) := by
  simpa using
    (outerRoute_eq_header_iff (pairedProblem input) coordinate coordinate)

example : RawRouter.rules.length = 54 := RawRouter.rules_length

example :
    RawRouter.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) :=
  RawRouter.rules_pairwise_query_distinct

example (coordinate boundary : Nat) :
    workRunExact? RawRouter.machine
        (RawRouter.workSteps coordinate boundary)
        (workStartConfiguration RawRouter.machine
          (RawRouter.inputTape coordinate boundary)) =
      some (RawRouter.finalConfiguration coordinate boundary) :=
  RawRouter.workRunExact coordinate boundary

example (coordinate boundary : Nat) :
    workBoundedDecide RawRouter.machine
        (RawRouter.workSteps coordinate boundary)
        (RawRouter.inputTape coordinate boundary) =
      if coordinate < boundary then .accept else .reject :=
  RawRouter.workBoundedDecide_eq coordinate boundary

example :
    workBoundedDecide RawRouter.machine (RawRouter.workSteps 0 3)
        (RawRouter.inputTape 0 3) = .accept := by
  simpa using RawRouter.workBoundedDecide_eq 0 3

example :
    workBoundedDecide RawRouter.machine (RawRouter.workSteps 3 3)
        (RawRouter.inputTape 3 3) = .reject := by
  simpa using RawRouter.workBoundedDecide_eq 3 3

example :
    workBoundedDecide RawRouter.machine (RawRouter.workSteps 4 2)
        (RawRouter.inputTape 4 2) = .reject := by
  simpa using RawRouter.workBoundedDecide_eq 4 2

example (coordinate boundary : Nat) :
    RawRouter.workSteps coordinate boundary ≤
      6 * (coordinate + 1) * (coordinate + 1) :=
  RawRouter.workSteps_le coordinate boundary

example (input : BitString)
    (coordinate : Fin
      (BuilderFullScheduleCursorController.terminalSlot
        (inputOnlyProblem input))) :
    6 * RawRouter.workSteps coordinate.val
        (BuilderFullScheduleCursorController.firstBodySlot
          (inputOnlyProblem input)) ≤
      (RawRouter.rawTimeBound inputOnlyVerifier).eval input.length :=
  RawRouter.rawTimeBound_le (inputOnlyProblem input) coordinate.val
    coordinate.isLt

example (input : BitString)
    (coordinate : Fin
      (BuilderFullScheduleCursorController.terminalSlot
        (pairedProblem input))) :
    run (compileWorkMachine RawRouter.machine)
        ((RawRouter.rawTimeBound pairedVerifier).eval input.length)
        (encodeWorkConfiguration
          (workStartConfiguration RawRouter.machine
            (RawRouter.inputTape coordinate.val
              (BuilderFullScheduleCursorController.firstBodySlot
                (pairedProblem input))))) =
      encodeWorkConfiguration
        (RawRouter.finalConfiguration coordinate.val
          (BuilderFullScheduleCursorController.firstBodySlot
            (pairedProblem input))) :=
  RawRouter.run_compile_rawTimeBound (pairedProblem input) coordinate.val
    coordinate.isLt

example (coordinate boundary : Nat) :
    workBoundedDecide RawRouter.machine
        (RawRouter.workSteps coordinate boundary - 1)
        (RawRouter.inputTape coordinate boundary) = .timeout :=
  RawRouter.work_one_step_short_timeout coordinate boundary

example (fuel : Nat) (left right : List WorkSymbol) :
    workBoundedDecide RawRouter.machine fuel
        (RawRouter.malformedConfiguration left right).tape = .timeout :=
  RawRouter.malformed_timeout fuel left right

example (input : BitString) (coordinate : Nat) :
    (RawRouter.finalConfiguration coordinate
      (BuilderFullScheduleCursorController.firstBodySlot
        (inputOnlyProblem input))).state = RawRouter.machine.acceptState ↔
      ∃ headerCoordinate,
        outerRoute (inputOnlyProblem input) coordinate =
          .header headerCoordinate :=
  rawRouter_accept_iff_header (inputOnlyProblem input) coordinate

example (input : BitString)
    (coordinate : Fin
      (BuilderFullScheduleCursorController.terminalSlot
        (pairedProblem input))) :
    (pairedProblem input).formulaTokenSlotDirect coordinate.val =
      match outerRoute (pairedProblem input) coordinate.val with
      | .header headerCoordinate =>
          (pairedProblem input).formulaHeaderTokenSlotDirect headerCoordinate
      | .postHeader remainder =>
          postHeaderSlotDirect (pairedProblem input) remainder := by
  exact
    (cook_levin_arbitrary_slot_header_router_checked_complete
      (pairedProblem input) coordinate).1

example (input : BitString)
    (coordinate : Fin
      (BuilderFullScheduleCursorController.terminalSlot
        (inputOnlyProblem input))) :
    RawRouter.rules.length = 54 := by
  exact
    (cook_levin_arbitrary_slot_header_router_checked_complete
      (inputOnlyProblem input) coordinate).2.2.2.2.2.2

end PNP.Concrete.CookLevinBuilderArbitrarySlotHeaderRouterRegression
