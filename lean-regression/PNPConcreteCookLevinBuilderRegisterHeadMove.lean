import PNP.Concrete.CookLevinBuilderRegisterHeadMove

open PNP.Concrete
open PNP.Concrete.CookLevin
open BuilderRegisterHeadMove
open BuilderDividerOperands (endTape)
open BuilderUnaryPolynomial (registerWord)

example : graph.WellFormed := graph_wellFormed
example : moveCode .stay = 0 := rfl
example : moveCode .left = 1 := rfl
example : moveCode .right = 2 := rfl
example (move : HeadMove) : moveCode move ≤ 2 := moveCode_le move

example {width : Nat} (position : Fin width) (move : HeadMove) :
    moved width position.val move = (VerifierTableauProblem.movePosition position move).val :=
  moved_eq_canonical position move

example {width : Nat} (position : Fin width) (move : HeadMove) :
    moved width position.val move < width := moved_lt position move

example (width position : Nat) : moved width position .stay = position := rfl
example (width : Nat) : moved width 0 .left = 0 := rfl
example (width position : Nat) : moved width (position + 1) .left = position := by
  simp only [moved, Nat.add_sub_cancel]
example (width position : Nat) (hNext : position + 1 < width) :
    moved width position .right = position + 1 := by
  simp only [moved, if_pos hNext]
example (position : Nat) : moved (position + 1) position .right = position := by
  simp only [moved, Nat.lt_irrefl, ite_false]
example : moved 1 0 .right = 0 := rfl
example : moved 3 2 .right ≠ 3 := by decide
example : moved 3 1 .right ≠ 1 := by decide
example (width position : Nat) (move : HeadMove) :
    moved width position move ≤ position + 1 := moved_le width position move

example (width position : Nat) (move : HeadMove) :
    (finalValues width position move).length = 4 := finalValues_length width position move

example (width position : Nat) (move : HeadMove) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps width position move)
      (initialConfiguration width position move older inside outside) =
      some (finalConfiguration width position move older inside outside) :=
  workRunExact width position move older inside outside

example (width position : Nat) (move : HeadMove) (older : List Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps width position move)
      (encodeWorkConfiguration (initialConfiguration width position move older inside outside)) =
      encodeWorkConfiguration (finalConfiguration width position move older inside outside) :=
  run_compile_exact width position move older inside outside

example : workRunExact? machine (workSteps 4 1 .stay)
    (initialConfiguration 4 1 .stay [7] [.oneZero] [.oneOne, .oneZero, .zeroOne]) =
    some {
      state := machine.acceptState
      tape := endTape [7, 4, 1, 0, 1] [.oneZero] [.zeroOne]} :=
  workRunExact 4 1 .stay [7] [.oneZero] [.oneOne, .oneZero, .zeroOne]

example : workRunExact? machine (workSteps 1 0 .left)
    (initialConfiguration 1 0 .left [7] [.oneZero] [.oneOne, .zeroOne]) =
    some {
      state := machine.acceptState
      tape := endTape [7, 1, 0, 1, 0] [.oneZero] [.zeroOne]} :=
  workRunExact 1 0 .left [7] [.oneZero] [.oneOne, .zeroOne]

example : workRunExact? machine (workSteps 3 2 .left)
    (initialConfiguration 3 2 .left [7] [.oneZero] []) =
    some {
      state := machine.acceptState
      tape := endTape [7, 3, 2, 1, 1] [.oneZero] [.blank]} :=
  workRunExact 3 2 .left [7] [.oneZero] []

example : workRunExact? machine (workSteps 3 1 .right)
    (initialConfiguration 3 1 .right [7] [.oneZero] []) =
    some {
      state := machine.acceptState
      tape := endTape [7, 3, 1, 2, 2] [.oneZero] (List.replicate 8 .blank)} :=
  workRunExact 3 1 .right [7] [.oneZero] []

example : workRunExact? machine (workSteps 3 2 .right)
    (initialConfiguration 3 2 .right [7] [.oneZero] []) =
    some {
      state := machine.acceptState
      tape := endTape [7, 3, 2, 2, 2] [.oneZero] (List.replicate 10 .blank)} :=
  workRunExact 3 2 .right [7] [.oneZero] []

example (width position code : Nat) (older : List Nat) (inside outside : List WorkSymbol)
    (hInvalid : code ≠ 0 ∧ code ≠ 1 ∧ code ≠ 2) :
    workRunExact? machine (invalidSteps code)
      (workStartConfiguration machine (endTape (older ++ [width, position, code]) inside outside)) =
      some {
        state := machine.rejectState
        tape := endTape (older ++ [width, position, code]) inside outside} :=
  invalid_workRunExact width position code older inside outside hInvalid

example : workRunExact? machine (invalidSteps 3)
    (workStartConfiguration machine (endTape [7, 3, 1, 3] [.oneZero] [.zeroOne])) =
    some {
      state := machine.rejectState
      tape := endTape [7, 3, 1, 3] [.oneZero] [.zeroOne]} :=
  invalid_workRunExact 3 1 3 [7] [.oneZero] [.zeroOne] (by decide)

example (width position : Nat) (outside : List WorkSymbol) :
    comparedOutside width position outside =
      List.replicate (position + width + 4) WorkSymbol.blank ++
        outside.drop (2 * position + width + 6) :=
  comparedOutside_eq width position outside

example (width position : Nat) (move : HeadMove) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration width position move older inside outside).tape.right =
      (registerWord (finalValues width position move)).reverse ++ ((registerWord older).reverse ++ inside) :=
  final_inside_preserved width position move older inside outside

example (width position : Nat) (move : HeadMove) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration width position move older inside outside).tape.left =
      finalOutside width position move outside :=
  final_exterior_accounted width position move older inside outside

example : finalOutside 3 2 .right [] ≠ [] := by decide
example (width position : Nat) (move : HeadMove) (outside : List WorkSymbol) :
    (finalOutside width position move outside).length ≤ outside.length + position + width + 5 :=
  finalOutside_length_le width position move outside

example (width position bound : Nat) (move : HeadMove) (hw : width ≤ bound) (hp : position ≤ bound) :
    workSteps width position move ≤ workBound bound := workSteps_le width position bound move hw hp
example (bound : NatPolynomial) (input : Nat) :
    (copyPolynomial bound).eval input = copyBound (bound.eval input) := copyPolynomial_eval bound input
example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) :=
  rawTimePolynomial_eval bound input
example (width position : Nat) (move : HeadMove) (bound : NatPolynomial) (input : Nat)
    (hw : width ≤ bound.eval input) (hp : position ≤ bound.eval input) :
    6 * workSteps width position move ≤ (rawTimePolynomial bound).eval input :=
  raw_time_polynomial width position move bound input hw hp
example (width position : Nat) (move : HeadMove) (older : List Nat) :
    (registerWord (older ++ finalValues width position move)).length =
      (registerWord (older ++ inputValues width position move)).length + moved width position move + 1 :=
  output_span width position move older
example (width position : Nat) (move : HeadMove) (older : List Nat)
    (bound : NatPolynomial) (input : Nat)
    (hInput : (registerWord (older ++ inputValues width position move)).length ≤ bound.eval input) :
    (registerWord (older ++ finalValues width position move)).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps width position move ≤ (rawTimePolynomial bound).eval input :=
  source_polynomial_bounds width position move older bound input hInput

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState
