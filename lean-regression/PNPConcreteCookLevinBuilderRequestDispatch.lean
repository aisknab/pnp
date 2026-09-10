import PNP.Concrete.CookLevinBuilderRequestDispatch

namespace PNP.Concrete.CookLevin.BuilderRequestDispatchRegression

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (Slot values)
open BuilderPayloadClauseOccupancy (tag beforeTag)
open BuilderPayloadSearchSource (Family Request family)
open WorkMachineProgramGraph (Node NodeRef Graph Endpoint endpointConfiguration endpointState)
open BuilderRequestDispatch

example {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat) :
    requestValues (some (some constraint)) request older =
      BuilderPayloadSearchSource.requestValues constraint request older :=
  PNP.Concrete.CookLevin.BuilderRequestDispatch.request_values_present constraint request older

example {width : Nat} (slot : Slot width) (request : Request) (older : List Nat) :
    requestValues slot request older =
      BuilderRequestRegisterMatch.inputValues (tagPrefix slot older) (tag slot) (tagSuffix request) :=
  PNP.Concrete.CookLevin.BuilderRequestDispatch.tag_operand_layout slot request older

example (request : Request) : (tagSuffix request).length = 11 :=
  PNP.Concrete.CookLevin.BuilderRequestDispatch.tag_offset request

example {width : Nat} (slot : Slot width) (request : Request) (older : List Nat) :
    requestValues slot request older =
      BuilderRequestRegisterMatch.inputValues (indexPrefix slot request older) request.clauseIndex [request.originalPosition] :=
  PNP.Concrete.CookLevin.BuilderRequestDispatch.index_operand_layout slot request older

example {width : Nat} (slot : Slot width) (index : Nat)
    (hRoute : route slot index = .exclusion) :
    ∃ variables : List (Fin width), slot = some (some (.exactlyOne variables)) ∧ 0 < index :=
  PNP.Concrete.CookLevin.BuilderRequestDispatch.exclusion_invariant slot index hRoute

example :
    endpointState (entry .missing) ≠ endpointState (entry .padding) :=
  PNP.Concrete.CookLevin.BuilderRequestDispatch.missing_padding_states_distinct

example : graph.WellFormed :=
  PNP.Concrete.CookLevin.BuilderRequestDispatch.graph_wellFormed

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  PNP.Concrete.CookLevin.BuilderRequestDispatch.rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept machine :=
  PNP.Concrete.CookLevin.BuilderRequestDispatch.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  PNP.Concrete.CookLevin.BuilderRequestDispatch.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState :=
  PNP.Concrete.CookLevin.BuilderRequestDispatch.acceptState_ne_rejectState

example {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (requestValues slot request older)).length + outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (final : WorkTape),
      workRunExact? machine steps (initialConfiguration slot request older inside outside) =
        some (endpointConfiguration (entry (route slot request.clauseIndex)) final) ∧
      WorkTape.BlankEquivalent final (endTape (requestValues slot request older) inside []) ∧
      BuilderRequestedPairLookup.storedCells final ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input :=
  PNP.Concrete.CookLevin.BuilderRequestDispatch.workRun_request_dispatch slot request older inside outside bound input hBlank hSpan

example {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (requestValues slot request older)).length + outside.length ≤ bound.eval input) :
    ∃ (rawSteps : Nat) (final : WorkTape),
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps (encodeWorkConfiguration (initialConfiguration slot request older inside outside)) =
        encodeWorkConfiguration (endpointConfiguration (entry (route slot request.clauseIndex)) final) ∧
      WorkTape.BlankEquivalent final (endTape (requestValues slot request older) inside []) ∧
      BuilderRequestedPairLookup.storedCells final ≤ inside.length + (spanPolynomial bound).eval input :=
  PNP.Concrete.CookLevin.BuilderRequestDispatch.uniform_polynomial_dispatch slot request older inside outside bound input hBlank hSpan

-- Independent semantic route contracts, not fixed source instances.
example (width index : Nat) : route (none : Slot width) index = .missing := rfl

example (width index : Nat) : route (some none : Slot width) index = .padding := rfl

example {width : Nat} (literal : BoundedLiteral width) :
    route (some (some (.require literal))) 0 = .required := rfl

example {width : Nat} (literal : BoundedLiteral width) (index : Nat) (hPositive : 0 < index) :
    route (some (some (.require literal))) index = .padding := by
  exact if_neg (by omega)

example {width : Nat} (premises : List (BoundedLiteral width)) (conclusion : BoundedLiteral width) :
    route (some (some (.implication premises conclusion))) 0 = .implication := rfl

example {width : Nat} (premises : List (BoundedLiteral width)) (conclusion : BoundedLiteral width)
    (index : Nat) (hPositive : 0 < index) :
    route (some (some (.implication premises conclusion))) index = .padding := by
  exact if_neg (by omega)

example {width : Nat} (variables : List (Fin width)) :
    route (some (some (.exactlyOne variables))) 0 = .positive := rfl

example {width : Nat} (variables : List (Fin width)) (index : Nat) (hPositive : 0 < index) :
    route (some (some (.exactlyOne variables))) index = .exclusion := by
  exact if_neg (by omega)

example : graph.entry = tagRef 0 := rfl

example (kind : Family) :
    (bodyNode kind).program = BuilderPayloadBodyTokenLookup.machine kind := rfl

example : exclusionNode.program = BuilderRequestedExclusionTokenLookup.machine := rfl

example : absentNode.program.rules = [] := rfl

example : (tagNode 0).onAccept = .node absentNode.reference := rfl

example : (tagNode 1).onAccept = .dead := rfl

example : (tagNode 2).onAccept = .node (indexNode .required).reference := rfl

example : (tagNode 3).onAccept = .node (indexNode .implication).reference := rfl

example : (tagNode 4).onAccept = .node (indexNode .positive).reference := rfl

example : (indexNode .required).onReject = .dead := rfl

example : (indexNode .implication).onReject = .dead := rfl

example : (indexNode .positive).onReject = .node exclusionNode.reference := rfl

example (kind : Family) : (indexNode kind).program = BuilderRequestRegisterMatch.machine 1 0 := rfl

example (code : Nat) : (tagNode code).program = BuilderRequestRegisterMatch.machine 11 code := rfl

example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input =
      5 * (tagRawPolynomial bound).eval input + (indexRawPolynomial bound).eval input := rfl

example : endpointState (entry .missing) ≠ machine.rejectState := by
  have h := WorkMachineProgramGraph.nodeState_ge_three absentNode.name absentNode.program.startState
  change WorkMachineProgramGraph.nodeState absentNode.name absentNode.program.startState ≠ 1
  omega

end PNP.Concrete.CookLevin.BuilderRequestDispatchRegression
