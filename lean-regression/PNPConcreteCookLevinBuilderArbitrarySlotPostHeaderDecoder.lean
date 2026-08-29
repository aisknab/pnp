import PNP

namespace PNP.Concrete.CookLevinBuilderArbitrarySlotPostHeaderDecoderRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderArbitrarySlotHeaderRouter
open CookLevin.BuilderArbitrarySlotPostHeaderDecoder

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

def inputOnlyVerifier : PolynomialTimeVerifier (fun _ => True) :=
  verifierFromDecider
    (PolynomialTimeDecider.ofMachine acceptAllPolynomialTime)

def pairedVerifier : PolynomialTimeVerifier (fun _ => True) :=
  { program :=
      { inputMode := .paired
        decision := .machine immediateAcceptMachine (.constant 0) }
    certificateBound := .linear 1 1
    runtimeBound := .constant 0
    haltsWithin := by
      intro input certificate hCertificate
      exact Verdict.noConfusion
    runtime_le := by
      intro input certificate hCertificate
      exact Nat.le_refl 0
    accepts_iff := by
      intro input
      constructor
      · intro member
        exact ⟨[], Nat.zero_le _, rfl⟩
      · intro witness
        exact True.intro }

def inputOnlyProblem (input : BitString) :
    VerifierTableauProblem (fun _ => True) :=
  { verifier := inputOnlyVerifier, input := input }

def pairedProblem (input : BitString) :
    VerifierTableauProblem (fun _ => True) :=
  { verifier := pairedVerifier, input := input }

example : rectangleCoordinate? 3 4 5 =
    some (⟨1, by decide⟩, ⟨1, by decide⟩) := by
  decide

example : rectangleCoordinate? 3 4 11 =
    some (⟨2, by decide⟩, ⟨3, by decide⟩) := by
  decide

example : rectangleCoordinate? 3 4 12 = none := by
  decide

example : rectangleCoordinate? 0 4 0 = none := by
  decide

example : rectangleCoordinate? 3 0 0 = none := by
  decide

example : rectangleCoordinate? 3 4 0 =
    some (⟨0, by decide⟩, ⟨0, by decide⟩) := by
  decide

example (count width index : Nat) :
    rectangleCoordinate? count width index = none ↔
      count * width ≤ index :=
  rectangleCoordinate?_eq_none_iff count width index

example {count width index : Nat}
    {coordinate : Fin count × Fin width}
    (hCoordinate : rectangleCoordinate? count width index = some coordinate) :
    coordinate.1.val * width + coordinate.2.val = index :=
  rectangleCoordinate?_reconstruct hCoordinate

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause)
    (hRoute : postHeaderRoute problem index =
      .body clauseCoordinate tokenCoordinate) :
    clauseCoordinate.val * problem.formulaTokensPerClause +
        tokenCoordinate.val = index :=
  postHeaderRoute_body_reconstruct problem index clauseCoordinate
    tokenCoordinate hRoute

example {language : Language} (problem : VerifierTableauProblem language) :
    postHeaderRoute problem
        (problem.formulaClauseSlotCount * problem.formulaTokensPerClause) =
      .finish :=
  (postHeaderRoute_eq_finish_iff problem _).2 rfl

example {language : Language} (problem : VerifierTableauProblem language) :
    postHeaderRoute problem
        (problem.formulaClauseSlotCount * problem.formulaTokensPerClause + 1) =
      .outOfRange :=
  (postHeaderRoute_eq_outOfRange_iff problem _).2 (by omega)

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) :
    postHeaderSlotDirect problem index =
      (postHeaderRoute problem index).token? :=
  postHeaderSlotDirect_route problem index

example (input : BitString) (coordinate : Nat) :
    (inputOnlyProblem input).formulaTokenSlotDirect coordinate =
      decodedTokenSlotDirect (inputOnlyProblem input) coordinate :=
  formulaTokenSlotDirect_decoded (inputOnlyProblem input) coordinate

example :
    RawRemainder.configurationPostHeaderRemainder?
        (RawRouter.resultConfiguration (.equal 7)) = some 0 := by
  simpa [RawRemainder.comparisonResultPostHeaderRemainder?] using
    RawRemainder.configurationPostHeaderRemainder?_resultConfiguration
      (.equal 7)

example :
    RawRemainder.configurationPostHeaderRemainder?
        (RawRouter.resultConfiguration (.greater 3 8)) = some 9 := by
  simpa [RawRemainder.comparisonResultPostHeaderRemainder?] using
    RawRemainder.configurationPostHeaderRemainder?_resultConfiguration
      (.greater 3 8)

example (coordinate boundary : Nat) :
    RawRemainder.configurationPostHeaderRemainder?
        (RawRouter.finalConfiguration coordinate boundary) =
      if coordinate < boundary then none else some (coordinate - boundary) :=
  RawRemainder.finalConfiguration_postHeaderRemainder? coordinate boundary

example (input : BitString)
    (coordinate : Fin
      (BuilderFullScheduleCursorController.terminalSlot
        (pairedProblem input))) :
    (pairedProblem input).formulaTokenSlotDirect coordinate.val =
      decodedTokenSlotDirect (pairedProblem input) coordinate.val :=
  (cook_levin_arbitrary_slot_post_header_decoder_checked_complete
    (pairedProblem input) coordinate).1

example (input : BitString)
    (coordinate : Fin
      (BuilderFullScheduleCursorController.terminalSlot
        (inputOnlyProblem input))) (remainder : Nat)
    (hOuter : outerRoute (inputOnlyProblem input) coordinate.val =
      .postHeader remainder) :
    postHeaderRoute (inputOnlyProblem input) remainder ≠ .outOfRange :=
  (cook_levin_arbitrary_slot_post_header_decoder_checked_complete
    (inputOnlyProblem input) coordinate).2.1 remainder hOuter

end PNP.Concrete.CookLevinBuilderArbitrarySlotPostHeaderDecoderRegression
