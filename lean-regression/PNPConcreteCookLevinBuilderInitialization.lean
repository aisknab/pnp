import PNP.Concrete.CookLevinBuilderInitialization

namespace PNP.Concrete.CookLevinBuilderInitializationRegression

open PipelineTape CookLevin CookLevin.BuilderInitialization

-- The machine table is fixed even when the input changes.
example {language : Language} (verifier : PolynomialTimeVerifier language)
    (input : BitString) :
    headerMachine verifier =
      BuilderCompleteHeader.machine (VerifierTableauProblem.mk verifier input) :=
  headerMachine_eq (VerifierTableauProblem.mk verifier input)

example {language : Language} (problem : VerifierTableauProblem language) :
    (initialConfiguration problem).tape = rawInputWorkTape problem.input := rfl

example {language : Language} (problem : VerifierTableauProblem language) :
    (BuilderCompleteHeader.finalConfiguration problem).tape =
      (dimensionInitial problem).tape := stage_handoff problem

example {language : Language} (problem : VerifierTableauProblem language) :
    workSteps problem = BuilderCompleteHeader.workSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (BuilderDimensionRegisters.polynomial problem.verifier) problem.input := rfl

-- The transition between phases costs six compiled steps, not zero.
example {language : Language} (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderCompleteHeader.rawTimeBound problem.verifier).eval problem.input.length +
        6 + 6 * BuilderUnaryPolynomial.workSteps
          (BuilderDimensionRegisters.polynomial problem.verifier) problem.input :=
  rawTimeBound_eval problem

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier

example {language : Language} (problem : VerifierTableauProblem language) :
    ∃ wordPrefix,
      workRunExact? (machine problem.verifier) (workSteps problem)
          (workStartConfiguration (machine problem.verifier)
            (rawInputWorkTape problem.input)) = some (finalConfiguration problem) ∧
      run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem)
          (encodeWorkConfiguration (initialConfiguration problem)) =
        encodeWorkConfiguration (finalConfiguration problem) ∧
      (finalConfiguration problem).tape =
        BuilderTokenAppender.workspaceTape problem.input
          ((wordPrefix ++ BuilderDimensionRegisters.dimensionWord
            problem.formulaClauseSlotsPerConstraint
            (BuilderFullScheduleCursorController.bodySlotCount problem)) ++
            BuilderUnaryPolynomial.scratchEndSymbol ::
              (BuilderCompleteHeader.finalOutside problem).drop
                ((BuilderUnaryPolynomial.scratchWord
                  (BuilderDimensionRegisters.polynomial problem.verifier)
                  problem.input.length).length + 1))
          (encodeUnaryTokens problem.FormulaWidth) ∧
      6 * workSteps problem ≤
        (rawTimeBound problem.verifier).eval problem.input.length :=
  initialize_from_raw problem

end PNP.Concrete.CookLevinBuilderInitializationRegression
