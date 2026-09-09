import PNP.Concrete.CookLevinBuilderRequestRegisterMatch

namespace PNP.Concrete.CookLevin.BuilderRequestRegisterMatchRegression

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open WorkMachineProgramGraph (endpointConfiguration endpointState)
open BuilderRequestRegisterMatch

example (offset expected : Nat) : (graph offset expected).WellFormed :=
  PNP.Concrete.CookLevin.BuilderRequestRegisterMatch.graph_wellFormed offset expected

example (offset expected : Nat) :
    (machine offset expected).rules.Pairwise WorkMachineChain.QueryDistinct :=
  PNP.Concrete.CookLevin.BuilderRequestRegisterMatch.rules_pairwise_query_distinct offset expected

example (offset expected : Nat) : WorkMachineChain.NoRuleAtAccept (machine offset expected) :=
  PNP.Concrete.CookLevin.BuilderRequestRegisterMatch.noRuleAtAccept offset expected

example (offset expected : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine offset expected) (machine offset expected).rejectState :=
  PNP.Concrete.CookLevin.BuilderRequestRegisterMatch.noRuleAtReject offset expected

example (offset expected : Nat) :
    (machine offset expected).acceptState ≠ (machine offset expected).rejectState :=
  PNP.Concrete.CookLevin.BuilderRequestRegisterMatch.acceptState_ne_rejectState offset expected

example (offset expected actual : Nat) (older newer : List Nat)
    (inside outside : List WorkSymbol) (hLength : newer.length = offset) :
    workRunExact? (machine offset expected) (workSteps expected actual newer)
      (initialConfiguration offset expected actual older newer inside outside) =
      some (finalConfiguration expected actual older newer inside outside) :=
  PNP.Concrete.CookLevin.BuilderRequestRegisterMatch.workRunExact offset expected actual older newer inside outside hLength

example (expected actual : Nat) (older newer : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration expected actual older newer inside outside).state =
      if actual = expected then 0 else 1 :=
  PNP.Concrete.CookLevin.BuilderRequestRegisterMatch.final_state expected actual older newer inside outside

example (expected actual : Nat) (older newer : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration expected actual older newer inside outside).tape =
      endTape (older ++ [actual] ++ newer) inside (restoredOutside actual outside) :=
  PNP.Concrete.CookLevin.BuilderRequestRegisterMatch.final_registers expected actual older newer inside outside

example (expected actual : Nat) (older newer : List Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (inputValues older actual newer)).length + outside.length ≤ bound.eval input) :
    (registerWord (inputValues older actual newer)).length + (restoredOutside actual outside).length ≤
        (spanPolynomial bound).eval input ∧
      6 * workSteps expected actual newer ≤ (rawTimePolynomial expected bound).eval input :=
  PNP.Concrete.CookLevin.BuilderRequestRegisterMatch.source_polynomial_bounds expected actual older newer outside bound input hSpan

example (expected actual : Nat) (older newer : List Nat) (inside : List WorkSymbol) :
    WorkTape.BlankEquivalent (finalConfiguration expected actual older newer inside []).tape
      (endTape (inputValues older actual newer) inside []) :=
  PNP.Concrete.CookLevin.BuilderRequestRegisterMatch.canonical_final_blankEquivalent expected actual older newer inside

example (offset expected actual : Nat) (older newer : List Nat)
    (inside : List WorkSymbol) (tape : WorkTape) (bound : NatPolynomial) (input : Nat)
    (hLength : newer.length = offset)
    (hSpan : (registerWord (inputValues older actual newer)).length ≤ bound.eval input)
    (hTape : WorkTape.BlankEquivalent tape (endTape (inputValues older actual newer) inside [])) :
    ∃ final : WorkConfiguration,
      workRunExact? (machine offset expected) (workSteps expected actual newer)
        (workStartConfiguration (machine offset expected) tape) = some final ∧
      final.state = endpointState (endpoint expected actual) ∧
      WorkTape.BlankEquivalent final.tape (endTape (inputValues older actual newer) inside []) ∧
      6 * workSteps expected actual newer ≤ (rawTimePolynomial expected bound).eval input :=
  PNP.Concrete.CookLevin.BuilderRequestRegisterMatch.workRun_preserving_match offset expected actual older newer inside tape bound input hLength hSpan hTape

example (offset expected actual : Nat) (older newer : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hLength : newer.length = offset)
    (hSpan : (registerWord (inputValues older actual newer)).length + outside.length ≤ bound.eval input) :
    6 * workSteps expected actual newer ≤ (rawTimePolynomial expected bound).eval input ∧
      run (compileWorkMachine (machine offset expected)) (6 * workSteps expected actual newer)
        (encodeWorkConfiguration (initialConfiguration offset expected actual older newer inside outside)) =
        encodeWorkConfiguration (finalConfiguration expected actual older newer inside outside) ∧
      (registerWord (inputValues older actual newer)).length + (restoredOutside actual outside).length ≤
        (spanPolynomial bound).eval input :=
  PNP.Concrete.CookLevin.BuilderRequestRegisterMatch.uniform_polynomial_match offset expected actual older newer inside outside bound input hLength hSpan

-- Independent contracts: both runtime branches preserve the original frame.
example (value : Nat) : endpoint value value = .accept := by simp only [endpoint, ite_true]

example (expected actual : Nat) (h : actual ≠ expected) :
    endpoint expected actual = .reject := by simp only [endpoint, if_neg h]

example (offset expected : Nat) : (machine offset expected).acceptState = 0 := rfl

example (offset expected : Nat) : (machine offset expected).rejectState = 1 := rfl

example (expected actual : Nat) (older newer : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration expected actual older newer inside outside).tape =
      endTape (older ++ [actual] ++ newer) inside
        (List.replicate (actual + 1) WorkSymbol.blank ++ outside.drop (actual + 1)) := rfl

example (expected actual : Nat) (newer : List Nat) :
    workSteps expected actual newer =
      RegisterCopy.steps newer actual + BuilderUnaryTagMatch.workSteps expected actual + actual + 5 := by
  unfold BuilderRequestRegisterMatch.workSteps
  omega

example (expected bound input : Nat) :
    (rawTimePolynomial expected (.constant bound)).eval input =
      6 * (4 * (bound + 1) * (bound + 1) + 9 * (bound + 1) + 5 + bound + (2 * expected + 8)) := rfl

example (bound input : Nat) :
    (spanPolynomial (.constant bound)).eval input = 2 * bound + 1 := rfl

end PNP.Concrete.CookLevin.BuilderRequestRegisterMatchRegression
