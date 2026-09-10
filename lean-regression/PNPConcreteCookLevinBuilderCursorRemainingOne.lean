/- Actual cursor one-remaining guard: exact interfaces and general boundary cases. -/
import PNP.Concrete.CookLevinBuilderCursorRemainingOne

namespace PNP.Concrete.CookLevin.BuilderCursorRemainingOne

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept machine :=
  noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  noRuleAtReject

example : machine.acceptState ≠ machine.rejectState :=
  acceptState_ne_rejectState

example (remaining : Nat) : (result remaining).val < 2 :=
  result_lt_two remaining

example (remaining : Nat) : (result remaining).val = machine.acceptState ↔ remaining = 1 :=
  result_accept_iff remaining

example (remaining : Nat) : (result remaining).val = machine.rejectState ↔ remaining ≠ 1 :=
  result_reject_iff remaining

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? machine (workSteps problem index remaining) (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) :=
  source_workRunExact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine machine) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  source_run_compile_exact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  rawTimeBound_le problem index remaining hBalance

-- The zero case is not mistaken for the final-token opportunity.
example : (result 0).val = machine.rejectState := rfl

example : (result 1).val = machine.acceptState := rfl

-- Every larger counter takes the non-final branch.
example (n : Nat) : (result (n + 2)).val = machine.rejectState := by
  apply (result_reject_iff _).2
  omega

-- The final cursor tape is exactly the original one, not merely its register count.
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      BuilderCursorSource.cursorTape problem index remaining output := rfl

-- Neither the actual input nor the remaining value parameterizes the finite machine.
example : machine = WorkMachineTerminalHandoff.machine
    (WorkMachineChain.machine BuilderRegisterAccess.seekMachine (BuilderUnaryTagMatch.machine 1))
    BuilderCursorRecovery.returnMachine classify := rfl

-- The fixed local comparison bound does not omit either full workspace traversal.
example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    workSteps problem index remaining =
      2 * (word problem index remaining).length + BuilderUnaryTagMatch.workSteps 1 remaining + 8 := by
  simp only [workSteps, probeSteps]
  omega

end PNP.Concrete.CookLevin.BuilderCursorRemainingOne
