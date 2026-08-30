import PNP

namespace PNP.Concrete.CookLevinBuilderPostHeaderRawLaunchRegression

open CookLevin
open CookLevin.BuilderArbitrarySlotHeaderRouter
open CookLevin.BuilderArbitrarySlotPostHeaderDecoder
open CookLevin.BuilderPostHeaderRawLaunch

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) :
    recoveredRemainder? problem coordinate =
      if coordinate <
          BuilderFullScheduleCursorController.firstBodySlot problem then
        none
      else
        some (coordinate -
          BuilderFullScheduleCursorController.firstBodySlot problem) :=
  recoveredRemainder?_eq problem coordinate

example {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) :
    launch? problem coordinate = none ↔
      outerRoute problem coordinate = .header coordinate :=
  launch?_eq_none_iff_header problem coordinate

example {language : Language} (problem : VerifierTableauProblem language)
    (coordinate remainder : Nat)
    (hRoute : outerRoute problem coordinate = .postHeader remainder) :
    launch? problem coordinate =
      some (BuilderPostHeaderRawDivider.finalConfiguration remainder
        problem.formulaTokensPerClause) :=
  launch?_postHeader problem coordinate remainder hRoute

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) :
    decodedPair problem index =
      (index / problem.formulaTokensPerClause,
        index % problem.formulaTokensPerClause) :=
  decodedPair_eq_div_mod problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) : RouteDecodeHolds problem index :=
  routeDecodeHolds problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (coordinate :
      Fin (BuilderFullScheduleCursorController.terminalSlot problem)) :
    match outerRoute problem coordinate.val with
    | .header _ => launch? problem coordinate.val = none
    | .postHeader remainder =>
        launch? problem coordinate.val =
            some (BuilderPostHeaderRawDivider.finalConfiguration remainder
              problem.formulaTokensPerClause) ∧
          RouteDecodeHolds problem remainder ∧
          postHeaderRoute problem remainder ≠ .outOfRange :=
  inRange_launch problem coordinate

example {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat)
    (hCoordinate :
      coordinate < BuilderFullScheduleCursorController.terminalSlot problem) :
    stagedCompiledSteps problem coordinate ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  stagedCompiledSteps_le_rawTimeBound problem coordinate hCoordinate

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_post_header_raw_launch_checked_complete problem

end PNP.Concrete.CookLevinBuilderPostHeaderRawLaunchRegression
