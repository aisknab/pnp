import PNP.Concrete.CookLevinBuilderRequestTokenLookup

namespace PNP.Concrete.CookLevin.BuilderRequestTokenLookupRegression

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (Slot)
open BuilderPayloadSearchSource (Family Request family body)
open BuilderRequestDispatch (graph machine bodyNode exclusionNode absentNode requestValues initialConfiguration)
open WorkMachineProgramGraph (Node Endpoint endpointConfiguration endpointState)
open PipelineStateNamespace (renameConfiguration)
open BuilderRequestTokenLookup

/- Exact execution and stable-state boundary contracts. -/

example (tape : WorkTape) : observe {state := 0, tape := tape} = some (some .t) :=
  BuilderRequestTokenLookup.observe_true tape

example (tape : WorkTape) : observe {state := 1, tape := tape} = some (some .f) :=
  BuilderRequestTokenLookup.observe_false tape

example (tape : WorkTape) : observe {state := missingState, tape := tape} = none :=
  BuilderRequestTokenLookup.observe_missing tape

example (tape : WorkTape) : observe {state := 2, tape := tape} = some none :=
  BuilderRequestTokenLookup.observe_padding tape

example (kind : Family) (configuration : WorkConfiguration) :
    observe (finishConfiguration (bodyNode kind) configuration) = some (BuilderPayloadBodyTokenLookup.observe configuration) :=
  BuilderRequestTokenLookup.observe_body_finished kind configuration

example (configuration : WorkConfiguration) :
    observe (finishConfiguration exclusionNode configuration) = some (BuilderRequestedExclusionTokenLookup.observe configuration) :=
  BuilderRequestTokenLookup.observe_exclusion_finished configuration

example {actual canonical : WorkConfiguration}
    (hEquivalent : WorkConfiguration.BlankEquivalent actual canonical) :
    observe actual = observe canonical :=
  BuilderRequestTokenLookup.observe_blankEquivalent hEquivalent

example : WorkMachineProgramGraph.NoRuleAt machine missingState :=
  BuilderRequestTokenLookup.missing_no_rule

example (node : Node) (configuration : WorkConfiguration) : finishSteps node configuration ≤ 1 :=
  BuilderRequestTokenLookup.finish_steps_le_one node configuration

example (node : Node) (configuration : WorkConfiguration) (hMem : node ∈ graph.nodes) :
    workRunExact? machine (finishSteps node configuration) (renameConfiguration node.encode configuration) =
      some (finishConfiguration node configuration) :=
  BuilderRequestTokenLookup.workRun_finish node configuration hMem

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (hZero : request.clauseIndex = 0) :
    canonicalResult (some (some constraint)) request =
      some ((encodeClauseTokens (BoundedClause.emit (body constraint)))[request.originalPosition]?) :=
  BuilderRequestTokenLookup.canonical_body constraint request hZero

example {width : Nat} (variables : List (Fin width)) (request : Request) :
    canonicalResult (some (some (.exactlyOne variables))) request =
      some (BuilderRequestedExclusionTokenLookup.canonicalToken variables request) :=
  BuilderRequestTokenLookup.canonical_exclusion variables request

example {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside : List WorkSymbol) (tape : WorkTape) (bound : NatPolynomial) (input : Nat)
    (hTape : WorkTape.BlankEquivalent tape (endTape (requestValues slot request older) inside []))
    (hSpan : (registerWord (requestValues slot request older)).length ≤ bound.eval input) :
    ∃ steps final,
      workRunExact? machine steps
        (endpointConfiguration (BuilderRequestDispatch.entry (BuilderRequestDispatch.route slot request.clauseIndex)) tape) = some final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = canonicalResult slot request ∧
      6 * steps ≤ (selectedRawTimePolynomial bound).eval input :=
  BuilderRequestTokenLookup.workRun_from_dispatch slot request older inside tape bound input hTape hSpan

example {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (requestValues slot request older)).length + outside.length ≤ bound.eval input) :
    ∃ steps final,
      workRunExact? machine steps (initialConfiguration slot request older inside outside) = some final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = canonicalResult slot request ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input :=
  BuilderRequestTokenLookup.workRun_polynomial_lookup slot request older inside outside bound input hBlank hSpan

example {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (requestValues slot request older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps final,
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps (encodeWorkConfiguration (initialConfiguration slot request older inside outside)) =
        encodeWorkConfiguration final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = canonicalResult slot request ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input :=
  BuilderRequestTokenLookup.uniform_polynomial_lookup slot request older inside outside bound input hBlank hSpan

/- Independent semantic and physical boundary contracts. -/
example {width : Nat} (request : Request) : canonicalResult (none : Slot width) request = none := rfl
example {width : Nat} (request : Request) : canonicalResult (some none : Slot width) request = some none := rfl
example {width : Nat} (constraint : LocalConstraint width) (request : Request) :
    canonicalResult (some (some constraint)) request =
      some ((constraint.emit[request.clauseIndex]?).bind
        (fun clause => (encodeClauseTokens (BoundedClause.emit clause))[request.originalPosition]?)) := rfl
example (tape : WorkTape) : observe {state := 0,tape := tape} ≠ observe {state := 1,tape := tape} := by
  rw [observe_true,observe_false]; decide
example (tape : WorkTape) : observe {state := 1,tape := tape} ≠ observe {state := 2,tape := tape} := by
  rw [observe_false,observe_padding]; decide
example (tape : WorkTape) : observe {state := missingState,tape := tape} ≠ observe {state := 2,tape := tape} := by
  rw [observe_missing,observe_padding]; decide
example (tape : WorkTape) : observe {state := missingState,tape := tape} ≠ observe {state := 1,tape := tape} := by
  rw [observe_missing,observe_false]; decide
example (kind : Family) : (bodyNode kind).program = BuilderPayloadBodyTokenLookup.machine kind := rfl
example : exclusionNode.program = BuilderRequestedExclusionTokenLookup.machine := rfl
example (kind : Family) : (bodyNode kind).onAccept = .accept ∧ (bodyNode kind).onReject = .reject := ⟨rfl,rfl⟩
example : exclusionNode.onAccept = .accept ∧ exclusionNode.onReject = .reject := ⟨rfl,rfl⟩
example (node : Node) (configuration : WorkConfiguration)
    (hAccept : configuration.state = node.program.acceptState) :
    finishSteps node configuration = 1 := by
  simp only [finishSteps,if_pos hAccept]
example (node : Node) (configuration : WorkConfiguration)
    (hAccept : configuration.state ≠ node.program.acceptState)
    (hReject : configuration.state = node.program.rejectState) :
    finishSteps node configuration = 1 := by
  simp only [finishSteps,if_neg hAccept,if_pos hReject]
example (node : Node) (configuration : WorkConfiguration)
    (hAccept : configuration.state ≠ node.program.acceptState)
    (hReject : configuration.state ≠ node.program.rejectState) :
    finishSteps node configuration = 0 ∧
      finishConfiguration node configuration = renameConfiguration node.encode configuration := by
  simp only [finishSteps,finishConfiguration,if_neg hAccept,if_neg hReject,and_self]
example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input =
      (BuilderRequestDispatch.rawTimePolynomial bound).eval input +
      (BuilderPayloadBodyTokenLookup.rawTimePolynomial bound).eval input +
      (BuilderRequestedExclusionTokenLookup.rawTimePolynomial bound).eval input + 6 := by
  simp only [rawTimePolynomial,selectedRawTimePolynomial,NatPolynomial.eval_add,NatPolynomial.eval_constant]
  omega
example (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial bound).eval input = bound.eval input + (rawTimePolynomial bound).eval input := by
  rw [spanPolynomial,NatPolynomial.eval_add]
example {width : Nat} (slot : Slot width) (request : Request) (older : List Nat) (inside outside : List WorkSymbol) :
    initialConfiguration slot request older inside outside =
      workStartConfiguration BuilderRequestDispatch.machine (endTape (requestValues slot request older) inside outside) := rfl
example (node : Node) (configuration : WorkConfiguration) :
    (finishConfiguration node configuration).tape = configuration.tape := by
  unfold finishConfiguration
  split <;> (try split) <;> rfl

end PNP.Concrete.CookLevin.BuilderRequestTokenLookupRegression
