import PNP

namespace PNP.Concrete.CookLevinBuilderPhysicalClassifierTerminalJoinRegression

open CookLevin
open CookLevin.BuilderPhysicalClassifierTerminalJoin
open PipelineStateNamespace

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example : redirectRules.length = 9 := redirectRules_length

example : rules.length = 720 := rules_length

example : rules.Pairwise (fun left right =>
    (left.sourceState, left.readSymbol) ≠
      (right.sourceState, right.readSymbol)) :=
  rules_pairwise_query_distinct

example : machine.acceptState ≠ machine.rejectState :=
  machine_acceptState_ne_rejectState

example : WorkMachineChain.NoRuleAtAccept machine :=
  noRuleAtAccept

example (tape : WorkTape) :
    workStep? machine
        (renameConfiguration sourceState
          { state := classifierMachine.rejectState, tape := tape }) =
      some (renameConfiguration sourceState
        { state := classifierMachine.acceptState, tape := tape }) :=
  redirect_workStep tape

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index workspace) =
      some (finalConfiguration problem index workspace) :=
  workRunExact problem index workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    (finalConfiguration problem index workspace).state = machine.acceptState :=
  rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index workspace)) =
      encodeWorkConfiguration (finalConfiguration problem index workspace) :=
  run_compile_exact problem index workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    machine.isHalted
      (workRun machine (workSteps problem index - 1)
        (entryConfiguration problem index workspace)) = false :=
  one_step_short_not_halted problem index workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * workSteps problem index ≤
      (BuilderPhysicalClassifierTerminalJoin.rawTimeBound
        problem.verifier).eval problem.input.length :=
  compiledSteps_le_rawTimeBound problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    TerminalJoinHolds problem index workspace :=
  terminalJoinHolds problem index workspace

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_physical_classifier_terminal_join_checked_complete problem

end PNP.Concrete.CookLevinBuilderPhysicalClassifierTerminalJoinRegression
