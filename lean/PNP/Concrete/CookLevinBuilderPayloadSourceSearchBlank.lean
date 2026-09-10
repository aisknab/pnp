/-
Copyright (c) 2026 PNP Labs.

Blank-exterior preservation for the complete actual-source literal search.
Induction follows the trace produced by the execution proof, including every
hit, miss and exhausted branch. No trace or blank-result certificate is added
to the caller interface. Existing canonical tokens, retained requests and
original-input polynomial bounds are preserved.
-/
import PNP.Concrete.CookLevinBuilderPayloadSourceSearchBounds
import PNP.Concrete.WorkMachineBlankEquivalence

namespace PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank

open PipelineTape
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource
open BuilderPayloadLiteralTokenSelector (Source Context)
open BuilderPayloadSourceSearch (CostTrace costVisit)
open BuilderPayloadSourceSearchControl (graph graph_wellFormed)
open BuilderPayloadSourceSearchEnvelope
open WorkMachineProgramGraph (endpointConfiguration)

/-- The finite exterior denotes only implicit blank cells. -/
def BlankOutside (outside : List WorkSymbol) : Prop :=
  ∀ index, WorkTape.blankCellAt outside index = WorkSymbol.blank

theorem blank_nil : BlankOutside ([] : List WorkSymbol) := fun _ => rfl

theorem blank_cons (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (WorkSymbol.blank :: outside) := by
  intro index
  cases index with
  | zero => rfl
  | succ index => exact hBlank index

theorem blank_drop (outside : List WorkSymbol) (amount : Nat) (hBlank : BlankOutside outside) :
    BlankOutside (outside.drop amount) := by
  induction amount generalizing outside with
  | zero => exact hBlank
  | succ amount ih =>
      cases outside with
      | nil => exact blank_nil
      | cons symbol rest => exact ih rest (fun index => hBlank (index + 1))

theorem blank_replicate_append (amount : Nat) (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (List.replicate amount WorkSymbol.blank ++ outside) := by
  induction amount with
  | zero => exact hBlank
  | succ amount ih => exact blank_cons _ ih

theorem guard_blank (count : Nat) (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderLiteralSearchGuard.finalOutside count outside) :=
  blank_replicate_append _ _ (blank_drop outside _ hBlank)

private theorem guarded_blank (count : Nat) (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderPayloadSourceSearchControl.guardedOutside count outside) :=
  guard_blank count _ (guard_blank count outside hBlank)

theorem literal_blank (positive : Bool) (value position : Nat) (outside : List WorkSymbol)
    (hBlank : BlankOutside outside) :
    BlankOutside (BuilderLiteralTokenSelector.finalOutside positive value position outside) := by
  unfold BuilderLiteralTokenSelector.finalOutside
  split
  · exact blank_replicate_append _ _ (blank_drop outside _ hBlank)
  · exact blank_drop _ _ (blank_drop _ _ (blank_cons _ (blank_drop outside _ hBlank)))

theorem payload_prepare_blank {width : Nat} (source : Source width) (context : Context source.ordinal)
    (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderPayloadLiteralTokenSelector.prepareOutside source context outside) := by
  have hValue : BlankOutside (BuilderPayloadLiteralTokenSelector.valueOutside source outside) :=
    blank_drop outside _ hBlank
  have hSignRead : BlankOutside (BuilderPayloadLiteralTokenSelector.signReadOutside source outside) := by
    unfold BuilderPayloadLiteralTokenSelector.signReadOutside
    split <;> exact blank_drop _ _ hValue
  have hSign : BlankOutside (BuilderPayloadLiteralTokenSelector.signOutside source outside) := by
    unfold BuilderPayloadLiteralTokenSelector.signOutside
    split
    · unfold BuilderPayloadLiteralTokenSelector.flipOutside
      split
      · exact blank_cons _ hSignRead
      · exact blank_drop _ _ hSignRead
    · exact hSignRead
  exact blank_drop _ _ hSign

theorem comparison_blank {width : Nat} (source : Source width) (context : Context source.ordinal)
    (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderPayloadSearchComparison.finalOutside source context outside) :=
  blank_drop _ _ (blank_drop _ _ (blank_drop _ _ (blank_drop outside _ hBlank)))

theorem hit_blank {width : Nat} (source : Source width) (context : Context source.ordinal)
    (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderPayloadSearchHit.finalOutside source context outside) :=
  literal_blank _ _ _ _
    (payload_prepare_blank source context _ (blank_replicate_append _ outside hBlank))

theorem advance_blank (ordinal remaining residual : Nat) (outside : List WorkSymbol)
    (hBlank : BlankOutside outside) :
    BlankOutside (BuilderPayloadSearchAdvance.finalOutside ordinal remaining residual outside) :=
  blank_drop _ _ (blank_cons _ (blank_drop _ _ (blank_drop _ _ (blank_drop outside _ hBlank))))

theorem visit_blank {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat)
    (ordinal remaining : Nat) (prior : List Nat)
    (hIndex : ordinal < (body constraint).length) (hPrior : prior.length = 17 * ordinal)
    (position : Nat) (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (costVisit constraint request older ordinal remaining prior hIndex hPrior position outside).hitOutside ∧
      BlankOutside (costVisit constraint request older ordinal remaining prior hIndex hPrior position outside).nextOutside := by
  let index : Fin (body constraint).length := ⟨ordinal,hIndex⟩
  let source := atSource constraint index
  let ctx := context constraint index request prior hPrior (remaining + 1) position
  have hCompared := comparison_blank source ctx _ (guarded_blank (remaining + 1) outside hBlank)
  exact ⟨hit_blank source ctx _ hCompared, advance_blank ordinal remaining _ _ hCompared⟩

/-- Every trace is constructed by the actual source-search proof. -/
theorem trace_blank {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat)
    (ordinal count : Nat) (prior : List Nat) (position : Nat) (outside : List WorkSymbol)
    (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol)
    (hTrace : CostTrace constraint request older ordinal count prior position outside steps values resultOutside) :
    BlankOutside outside → BlankOutside resultOutside := by
  induction hTrace with
  | empty ordinal prior position outside => exact guard_blank 0 outside
  | hit ordinal remaining prior hIndex hPrior position outside =>
      intro hBlank
      exact (visit_blank constraint request older ordinal remaining prior hIndex hPrior position outside hBlank).1
  | miss ordinal remaining prior hIndex hPrior position outside tailSteps resultValues resultOutside hTail ih =>
      intro hBlank
      exact ih (visit_blank constraint request older ordinal remaining prior hIndex hPrior position outside hBlank).2

/-- Strengthen the existing exact search contract with a proved exterior invariant.
The implication is a conclusion, not an extra execution premise. -/
theorem source_polynomial_bounds {width : Nat} (constraint : LocalConstraint width) (request : Request)
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
      6 * steps ≤ (rawTimePolynomial bound).eval input ∧
      (BlankOutside outside → BlankOutside resultOutside) := by
  obtain ⟨steps, resultValues, resultOutside, hTrace, hPath, hRetained, hExhausted⟩ :=
    BuilderPayloadSourceSearch.loop_path_traced (body constraint) constraint [] rfl request [] rfl position older inside outside
  have hScalars := initial_scalar_bounds constraint request position older outside (bound.eval input) hSpan
  have hInitialBudget :
      (registerWord (initialValues constraint request older [] 0 (body constraint).length position)).length +
        outside.length ≤ entryBudget (bound.eval input) 0 := by
    simpa only [entryBudget, Nat.zero_mul, Nat.add_zero] using hSpan
  have hBounds := BuilderPayloadSourceSearchBounds.trace_bounds constraint request older bound input 0 (body constraint).length [] position outside
    steps resultValues resultOutside hTrace hScalars.1 hScalars.2.1 (by omega) hScalars.2.2 hInitialBudget
  have hRun := WorkMachineProgramPath.runExact (graph (family constraint)) _ _ _ _ _
    (graph_wellFormed (family constraint)) hPath
  refine ⟨steps, resultValues, resultOutside, ?_, ?_, hRetained, hExhausted, hBounds.1, ?_, ?_⟩
  · exact hRun
  · exact BuilderLiteralListSearch.endpoint_observes_list (body constraint) position _
  · have hCount := Nat.add_le_add_right hScalars.1 1
    have h := Nat.le_trans hBounds.2 (Nat.mul_le_mul_right ((passRawPolynomial bound).eval input) hCount)
    simpa only [rawTimePolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_add, NatPolynomial.eval_constant] using h
  · exact trace_blank constraint request older 0 (body constraint).length [] position outside
      steps resultValues resultOutside hTrace

end PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank
