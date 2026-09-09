/-
Copyright (c) 2026 PNP Labs.

Complete arbitrary-source execution, canonical token and retained/exhausted frame
contracts carry their own encoded-input polynomial time and space bounds.
The public execution contracts have no supplied trace or correctness premise.
-/
import PNP.Concrete.CookLevinBuilderPayloadSourceSearchBounds

namespace PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBoundsRegression

open PipelineTape
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource
open BuilderPayloadSourceSearch (CostVisit costVisit CostTrace)
open BuilderPayloadSourceSearchControl (graph guardNode graph_wellFormed guardedOutside guardSteps)
open BuilderPayloadSourceSearchEnvelope
open BuilderLiteralSearchFrame (residual)
open BuilderLocalConstraintPayload (front)
open WorkMachineProgramGraph (endpointConfiguration)

example {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat)
    (ordinal remaining : Nat) (prior : List Nat)
    (hIndex : ordinal < (body constraint).length) (hPrior : prior.length = 17 * ordinal)
    (position : Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hLength : (body constraint).length ≤ bound.eval input)
    (hPayload : (front (some (some constraint))).sum ≤ bound.eval input)
    (hBalance : ordinal + (remaining + 1) = (body constraint).length)
    (hPosition : position ≤ bound.eval input)
    (hSpan : (registerWord (initialValues constraint request older prior ordinal (remaining + 1) position)).length +
      outside.length ≤ entryBudget (bound.eval input) ordinal) :
    let visit := costVisit constraint request older ordinal remaining prior hIndex hPrior position outside
    (registerWord visit.hitValues).length + visit.hitOutside.length ≤ (spanPolynomial bound).eval input ∧
    6 * visit.hitSteps ≤ (passRawPolynomial bound).eval input ∧
    6 * visit.missSteps ≤ (passRawPolynomial bound).eval input ∧
    visit.nextPosition ≤ position ∧
    (registerWord (initialValues constraint request older visit.nextPrior (ordinal + 1) remaining visit.nextPosition)).length +
      visit.nextOutside.length ≤ entryBudget (bound.eval input) (ordinal + 1) :=
  BuilderPayloadSourceSearchBounds.visit_bounds constraint request older ordinal remaining prior hIndex hPrior position outside bound input hLength hPayload hBalance hPosition hSpan

example {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat)
    (bound : NatPolynomial) (input : Nat)
    (ordinal count : Nat) (prior : List Nat) (position : Nat) (outside : List WorkSymbol)
    (steps : Nat) (resultValues : List Nat) (resultOutside : List WorkSymbol)
    (hTrace : CostTrace constraint request older ordinal count prior position outside steps resultValues resultOutside)
    (hLength : (body constraint).length ≤ bound.eval input)
    (hPayload : (front (some (some constraint))).sum ≤ bound.eval input)
    (hBalance : ordinal + count = (body constraint).length)
    (hPosition : position ≤ bound.eval input)
    (hSpan : (registerWord (initialValues constraint request older prior ordinal count position)).length + outside.length ≤
      entryBudget (bound.eval input) ordinal) :
    (registerWord resultValues).length + resultOutside.length ≤ (spanPolynomial bound).eval input ∧
      6 * steps ≤ (count + 1) * (passRawPolynomial bound).eval input :=
  BuilderPayloadSourceSearchBounds.trace_bounds constraint request older bound input ordinal count prior position outside steps resultValues resultOutside hTrace hLength hPayload hBalance hPosition hSpan

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues constraint request older [] 0 (body constraint).length position)).length +
      outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (resultValues : List Nat) (resultOutside : List WorkSymbol),
      workRunExact? (BuilderPayloadSourceSearchControl.machine (family constraint)) steps
        (workStartConfiguration (BuilderPayloadSourceSearchControl.machine (family constraint))
          (endTape (initialValues constraint request older [] 0 (body constraint).length position) inside outside)) =
        some (endpointConfiguration (BuilderLiteralListSearch.endpoint (body constraint) position)
          (endTape resultValues inside resultOutside)) ∧
      BuilderLiteralTokenSelector.observe
        (endpointConfiguration (BuilderLiteralListSearch.endpoint (body constraint) position)
          (endTape resultValues inside resultOutside)) =
        DirectToken.boundedLiteralListSlot (body constraint) position ∧
      (∃ scratch, resultValues = requestValues constraint request older ++ scratch) ∧
      (BuilderLiteralListSearch.endpoint (body constraint) position = .dead →
        ∃ finalPrior, finalPrior.length = 17 * (body constraint).length ∧
          resultValues = initialValues constraint request older finalPrior (body constraint).length 0
            (position - DirectToken.boundedLiteralListWidth (body constraint))) ∧
      (registerWord resultValues).length + resultOutside.length ≤ (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input :=
  BuilderPayloadSourceSearchBounds.source_polynomial_bounds constraint request position older inside outside bound input hSpan

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues constraint request older [] 0 (body constraint).length position)).length +
      outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (resultValues : List Nat) (resultOutside : List WorkSymbol),
      run (compileWorkMachine (BuilderPayloadSourceSearchControl.machine (family constraint))) (6 * steps)
        (encodeWorkConfiguration
          (workStartConfiguration (BuilderPayloadSourceSearchControl.machine (family constraint))
            (endTape (initialValues constraint request older [] 0 (body constraint).length position) inside outside))) =
        encodeWorkConfiguration
          (endpointConfiguration (BuilderLiteralListSearch.endpoint (body constraint) position)
            (endTape resultValues inside resultOutside)) ∧
      BuilderLiteralTokenSelector.observe
        (endpointConfiguration (BuilderLiteralListSearch.endpoint (body constraint) position)
          (endTape resultValues inside resultOutside)) =
        DirectToken.boundedLiteralListSlot (body constraint) position ∧
      (∃ scratch, resultValues = requestValues constraint request older ++ scratch) ∧
      (BuilderLiteralListSearch.endpoint (body constraint) position = .dead →
        ∃ finalPrior, finalPrior.length = 17 * (body constraint).length ∧
          resultValues = initialValues constraint request older finalPrior (body constraint).length 0
            (position - DirectToken.boundedLiteralListWidth (body constraint))) ∧
      (registerWord resultValues).length + resultOutside.length ≤ (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input :=
  BuilderPayloadSourceSearchBounds.run_compile_polynomial_bound constraint request position older inside outside bound input hSpan

-- Each full loop is charged at most the original count plus one visits.
example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input =
      (bound.eval input + 1) * (passRawPolynomial bound).eval input := rfl
-- Final space includes a single selected-branch envelope, not an iterated one.
example (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial bound).eval input = (envelope bound).eval input +
      (kindSum (fun kind => BuilderPayloadSearchHit.spanPolynomial kind (envelope bound))).eval input := rfl

end PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBoundsRegression
