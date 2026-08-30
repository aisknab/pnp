import PNP

namespace PNP.Concrete.CookLevinBuilderPostHeaderRawDividerRegression

open CookLevin
open CookLevin.BuilderArbitrarySlotPostHeaderDecoder
open CookLevin.BuilderPostHeaderRawDivider

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example : rules.length = 99 := rules_length

example : divide? 7 0 = none := divide?_zero 7

example :
    workRunExact? machine (workSteps 0 7)
        (workStartConfiguration machine (inputTape 0 7)) =
      some (finalConfiguration 0 7) :=
  workRunExact 0 7 (by decide)

example :
    workRunExact? machine (workSteps 3 5)
        (workStartConfiguration machine (inputTape 3 5)) =
      some (finalConfiguration 3 5) :=
  workRunExact 3 5 (by decide)

example :
    workRunExact? machine (workSteps 12 3)
        (workStartConfiguration machine (inputTape 12 3)) =
      some (finalConfiguration 12 3) :=
  workRunExact 12 3 (by decide)

example :
    workRunExact? machine (workSteps 9 1)
        (workStartConfiguration machine (inputTape 9 1)) =
      some (finalConfiguration 9 1) :=
  workRunExact 9 1 (by decide)

example :
    workRunExact? machine (workSteps 17 4)
        (workStartConfiguration machine (inputTape 17 4)) =
      some (finalConfiguration 17 4) :=
  workRunExact 17 4 (by decide)

example :
    terminalQuotientRemainder (finalConfiguration 17 4) = (4, 1) := by
  simpa using final_quotient_remainder 17 4

example (dividend width : Nat) :
    (dividend / width) * width + dividend % width = dividend :=
  quotient_remainder_reconstruct dividend width

example (dividend width : Nat) (hWidth : 0 < width) :
    dividend % width < width :=
  remainder_lt_width dividend width hWidth

example (dividend width : Nat) (hWidth : 0 < width) :
    workSteps dividend width ≤
      20 * (dividend + width + 1) * (dividend + width + 1) :=
  workSteps_le_quadratic dividend width hWidth

example (dividend width : Nat) (hWidth : 0 < width) :
    run (compileWorkMachine machine) (6 * workSteps dividend width)
        (encodeWorkConfiguration
          (workStartConfiguration machine (inputTape dividend width))) =
      encodeWorkConfiguration (finalConfiguration dividend width) :=
  run_compile_exact dividend width hWidth

example (dividend width : Nat) (hWidth : 0 < width) :
    workBoundedDecide machine (workSteps dividend width - 1)
        (inputTape dividend width) = .timeout :=
  work_one_step_short_timeout dividend width hWidth

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause)
    (hRoute : postHeaderRoute problem index =
      .body clauseCoordinate tokenCoordinate) :
    terminalQuotientRemainder
        (finalConfiguration index problem.formulaTokensPerClause) =
      (clauseCoordinate.val, tokenCoordinate.val) :=
  final_quotient_remainder_eq_body_coordinates problem index
    clauseCoordinate tokenCoordinate hRoute

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause)
    (hRoute : postHeaderRoute problem index =
      .body clauseCoordinate tokenCoordinate) :
    workRunExact? machine
          (workSteps index problem.formulaTokensPerClause)
          (workStartConfiguration machine
            (inputTape index problem.formulaTokensPerClause)) =
        some (finalConfiguration index problem.formulaTokensPerClause) ∧
      terminalQuotientRemainder
          (finalConfiguration index problem.formulaTokensPerClause) =
        (clauseCoordinate.val, tokenCoordinate.val) :=
  workRunExact_body_coordinates problem index clauseCoordinate
    tokenCoordinate hRoute

example := cook_levin_builder_post_header_raw_divider_checked_complete

end PNP.Concrete.CookLevinBuilderPostHeaderRawDividerRegression
