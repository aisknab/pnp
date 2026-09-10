/-
Copyright (c) 2026 PNP Labs.

Universal source-body execution, retained request and exact exhaustion contracts.
Fixed body-shape regressions do not stand in for the all-input execution theorem.
-/
import PNP.Concrete.CookLevinBuilderPayloadSourceSearch

namespace PNP.Concrete.CookLevin.BuilderPayloadSourceSearchRegression

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource BuilderPayloadSourceSearchControl
open WorkMachineProgramGraph (Endpoint endpointConfiguration)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)
open BuilderPayloadSourceSearch (CostTrace)

example {width : Nat} (remaining : List (BoundedLiteral width))
    (constraint : LocalConstraint width) (completed : List (BoundedLiteral width))
    (hList : body constraint = completed ++ remaining)
    (request : Request) (prior : List Nat) (hPrior : prior.length = 17 * completed.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    ∃ (steps : Nat) (resultValues : List Nat) (resultOutside : List WorkSymbol),
      AcceptPath (graph (family constraint)) (.node (guardNode (family constraint)).reference)
        (BuilderLiteralListSearch.endpoint remaining position) steps
        (endTape (initialValues constraint request older prior completed.length remaining.length position) inside outside)
        (endTape resultValues inside resultOutside) ∧
      (∃ scratch, resultValues = requestValues constraint request older ++ scratch) ∧
      (BuilderLiteralListSearch.endpoint remaining position = .dead →
        ∃ finalPrior, finalPrior.length = 17 * (body constraint).length ∧
          resultValues = initialValues constraint request older finalPrior (body constraint).length 0
            (position - DirectToken.boundedLiteralListWidth remaining)) :=
  BuilderPayloadSourceSearch.loop_path remaining constraint completed hList request prior hPrior position older inside outside

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
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
            (position - DirectToken.boundedLiteralListWidth (body constraint))) :=
  BuilderPayloadSourceSearch.workRun_observes_body constraint request position older inside outside

example {width : Nat} (literal : BoundedLiteral width) :
    body (.require literal) = [literal] := rfl
example {width : Nat} (premises : List (BoundedLiteral width)) (resultLiteral : BoundedLiteral width) :
    body (.implication premises resultLiteral) = BoundedClause.negated premises ++ [resultLiteral] := rfl
example {width : Nat} (variables : List (Fin width)) :
    body (.exactlyOne variables) = variables.map (fun index => ⟨true,index⟩) := rfl
example {width : Nat} (position : Nat) :
    BuilderLiteralListSearch.endpoint (body (.exactlyOne ([] : List (Fin width)))) position = .dead := rfl

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
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
            (position - DirectToken.boundedLiteralListWidth (body constraint))) :=
  BuilderPayloadSourceSearch.run_compile_observes_body constraint request position older inside outside

example {width : Nat} (remaining : List (BoundedLiteral width))
    (constraint : LocalConstraint width) (completed : List (BoundedLiteral width))
    (hList : body constraint = completed ++ remaining)
    (request : Request) (prior : List Nat) (hPrior : prior.length = 17 * completed.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    ∃ (steps : Nat) (resultValues : List Nat) (resultOutside : List WorkSymbol),
      CostTrace constraint request older completed.length remaining.length prior position outside steps resultValues resultOutside ∧
      AcceptPath (graph (family constraint)) (.node (guardNode (family constraint)).reference)
        (BuilderLiteralListSearch.endpoint remaining position) steps
        (endTape (initialValues constraint request older prior completed.length remaining.length position) inside outside)
        (endTape resultValues inside resultOutside) ∧
      (∃ scratch, resultValues = requestValues constraint request older ++ scratch) ∧
      (BuilderLiteralListSearch.endpoint remaining position = .dead →
        ∃ finalPrior, finalPrior.length = 17 * (body constraint).length ∧
          resultValues = initialValues constraint request older finalPrior (body constraint).length 0
            (position - DirectToken.boundedLiteralListWidth remaining)) :=
  BuilderPayloadSourceSearch.loop_path_traced remaining constraint completed hList request prior hPrior position older inside outside

end PNP.Concrete.CookLevin.BuilderPayloadSourceSearchRegression
