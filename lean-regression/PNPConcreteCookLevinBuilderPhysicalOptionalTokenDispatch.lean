import PNP

namespace PNP.Concrete.CookLevinBuilderPhysicalOptionalTokenDispatchRegression

open CookLevin
open CookLevin.BuilderPhysicalOptionalTokenDispatch

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example :
    CookLevin.BuilderPhysicalOptionalTokenDispatch.rules.length = 64 :=
  CookLevin.BuilderPhysicalOptionalTokenDispatch.rules_length

example : Function.Injective
    CookLevin.BuilderPhysicalOptionalTokenDispatch.requestSymbol :=
  CookLevin.BuilderPhysicalOptionalTokenDispatch.requestSymbol_injective

example (input : BitString) (outsideLeft : List WorkSymbol)
    (output : List CNFToken) (request : Option CNFToken) :
    ((CookLevin.BuilderPhysicalOptionalTokenDispatch.requestTape input
      outsideLeft output request).write PipelineTape.leftMarker).move .right =
        CookLevin.BuilderTokenAppender.workspaceTape input outsideLeft output :=
  CookLevin.BuilderPhysicalOptionalTokenDispatch.requestTape_dispatch_restores_workspace
    input outsideLeft output request

example (input : BitString) (outsideLeft : List WorkSymbol)
    (output : List CNFToken) (request : Option CNFToken) :
    workRunExact?
        CookLevin.BuilderPhysicalOptionalTokenDispatch.machine
        (CookLevin.BuilderPhysicalOptionalTokenDispatch.workSteps input output
          request)
        (CookLevin.BuilderPhysicalOptionalTokenDispatch.entryConfiguration
          input outsideLeft output request) =
      some
        (CookLevin.BuilderPhysicalOptionalTokenDispatch.finalConfiguration
          input outsideLeft output request) :=
  CookLevin.BuilderPhysicalOptionalTokenDispatch.workRunExact input outsideLeft
    output request

example (input : BitString) (outsideLeft : List WorkSymbol)
    (output : List CNFToken) (request : Option CNFToken) :
    run
        (compileWorkMachine
          CookLevin.BuilderPhysicalOptionalTokenDispatch.machine)
        (6 * CookLevin.BuilderPhysicalOptionalTokenDispatch.workSteps input
          output request)
        (encodeWorkConfiguration
          (CookLevin.BuilderPhysicalOptionalTokenDispatch.entryConfiguration
            input outsideLeft output request)) =
      encodeWorkConfiguration
        (CookLevin.BuilderPhysicalOptionalTokenDispatch.finalConfiguration
          input outsideLeft output request) :=
  CookLevin.BuilderPhysicalOptionalTokenDispatch.run_compile_exact input
    outsideLeft output request

example (input : BitString) (outsideLeft : List WorkSymbol)
    (output : List CNFToken) (request : Option CNFToken) :
    CookLevin.BuilderPhysicalOptionalTokenDispatch.machine.isHalted
        (workRun CookLevin.BuilderPhysicalOptionalTokenDispatch.machine
          (CookLevin.BuilderPhysicalOptionalTokenDispatch.workSteps input output
            request - 1)
          (CookLevin.BuilderPhysicalOptionalTokenDispatch.entryConfiguration
            input outsideLeft output request)) = false :=
  CookLevin.BuilderPhysicalOptionalTokenDispatch.one_step_short_not_halted
    input outsideLeft output request

example (fuel : Nat) (input : BitString) (outsideLeft : List WorkSymbol)
    (output : List CNFToken) :
    workBoundedDecide CookLevin.BuilderPhysicalOptionalTokenDispatch.machine
        fuel
        (CookLevin.BuilderPhysicalOptionalTokenDispatch.malformedRequestTape
          input outsideLeft output) = .timeout :=
  CookLevin.BuilderPhysicalOptionalTokenDispatch.malformedRequest_timeout fuel
    input outsideLeft output

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin
      (CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) :
    CookLevin.BuilderPhysicalOptionalTokenDispatch.CanonicalDispatchHolds
      problem index outsideLeft :=
  CookLevin.BuilderPhysicalOptionalTokenDispatch.canonicalDispatchHolds problem
    index outsideLeft

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin
      (CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * CookLevin.BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps
          problem index <=
      (CookLevin.BuilderPhysicalOptionalTokenDispatch.rawTimeBound
        problem.verifier).eval problem.input.length :=
  CookLevin.BuilderPhysicalOptionalTokenDispatch.canonicalCompiledSteps_le_rawTimeBound
    problem index

example {language : Language} (problem : VerifierTableauProblem language) :=
  CookLevin.BuilderPhysicalOptionalTokenDispatch.cook_levin_builder_physical_optional_token_dispatch_checked_complete
    problem

end PNP.Concrete.CookLevinBuilderPhysicalOptionalTokenDispatchRegression
