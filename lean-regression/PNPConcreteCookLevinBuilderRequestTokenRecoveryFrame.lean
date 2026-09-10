/-
Copyright (c) 2026 PNP Labs.
Exact recoverable-frame contracts for all-request dispatch and token execution.
The existing token regression retains its independent public observations.
-/
import PNP.Concrete.CookLevinBuilderRequestTokenLookup

namespace PNP.Concrete.CookLevin.BuilderRequestTokenRecoveryFrameRegression

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (Slot)
open BuilderPayloadSearchSource (Request)
open BuilderPayloadSourceSearchBlank (BlankOutside)
open BuilderRequestDispatch (machine requestValues initialConfiguration)
open WorkMachineProgramGraph (Node endpointConfiguration)
open BuilderRequestTokenLookup

example (node : Node) (configuration : WorkConfiguration) :
    (finishConfiguration node configuration).tape = configuration.tape :=
  BuilderRequestTokenLookup.finish_tape node configuration

example {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside : List WorkSymbol) (tape : WorkTape) (bound : NatPolynomial) (input : Nat)
    (hTape : WorkTape.BlankEquivalent tape (endTape (requestValues slot request older) inside []))
    (hSpan : (registerWord (requestValues slot request older)).length ≤ bound.eval input) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol) (final : WorkConfiguration),
      workRunExact? machine steps
        (endpointConfiguration (BuilderRequestDispatch.entry (BuilderRequestDispatch.route slot request.clauseIndex)) tape) = some final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = canonicalResult slot request ∧
      (∃ scratch, values = requestValues slot request older ++ scratch) ∧
      WorkTape.BlankEquivalent final.tape (endTape values inside resultOutside) ∧
      BlankOutside resultOutside ∧
      (registerWord values).length + resultOutside.length ≤ (canonicalSpanPolynomial bound).eval input ∧
      6 * steps ≤ (selectedRawTimePolynomial bound).eval input :=
  BuilderRequestTokenLookup.workRun_from_dispatch_with_frame slot request older inside tape bound input hTape hSpan

example {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (requestValues slot request older)).length + outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol) (final : WorkConfiguration),
      workRunExact? machine steps (initialConfiguration slot request older inside outside) = some final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = canonicalResult slot request ∧
      (∃ scratch, values = requestValues slot request older ++ scratch) ∧
      WorkTape.BlankEquivalent final.tape (endTape values inside resultOutside) ∧
      BlankOutside resultOutside ∧
      (registerWord values).length + resultOutside.length ≤ (canonicalSpanPolynomial bound).eval input ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input :=
  BuilderRequestTokenLookup.workRun_polynomial_lookup_with_frame slot request older inside outside bound input hBlank hSpan

example {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (requestValues slot request older)).length + outside.length ≤ bound.eval input) :
    ∃ (rawSteps : Nat) (values : List Nat) (resultOutside : List WorkSymbol) (final : WorkConfiguration),
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps (encodeWorkConfiguration (initialConfiguration slot request older inside outside)) =
        encodeWorkConfiguration final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = canonicalResult slot request ∧
      (∃ scratch, values = requestValues slot request older ++ scratch) ∧
      WorkTape.BlankEquivalent final.tape (endTape values inside resultOutside) ∧
      BlankOutside resultOutside ∧
      (registerWord values).length + resultOutside.length ≤ (canonicalSpanPolynomial bound).eval input ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input :=
  BuilderRequestTokenLookup.uniform_polynomial_lookup_with_frame slot request older inside outside bound input hBlank hSpan

example (node : Node) (tape : WorkTape) :
    (finishConfiguration node {state := node.program.acceptState, tape := tape}).tape = tape :=
  finish_tape node _

example (node : Node) (tape : WorkTape) :
    (finishConfiguration node {state := node.program.rejectState, tape := tape}).tape = tape :=
  finish_tape node _

example (bound : NatPolynomial) (input : Nat) :
    (canonicalSpanPolynomial bound).eval input =
      bound.eval input + ((BuilderPayloadBodyTokenLookup.spanPolynomial bound).eval input +
        (BuilderExclusionTokenRecoveryFrame.canonicalSpanPolynomial bound).eval input) := rfl

end PNP.Concrete.CookLevin.BuilderRequestTokenRecoveryFrameRegression
