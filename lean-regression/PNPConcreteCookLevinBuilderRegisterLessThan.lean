import PNP.Concrete.CookLevinBuilderRegisterLessThan

open PNP.Concrete
open PNP.Concrete.CookLevin
open BuilderRegisterLessThan
open BuilderDividerOperands (endTape)
open BuilderUnaryPolynomial (registerWord)

example (v : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? BuilderRegisterCountdownControl.decrement 2
      (workStartConfiguration BuilderRegisterCountdownControl.decrement
        (endTape (older ++ [v + 1]) inside outside)) =
      some {
        state := BuilderRegisterCountdownControl.decrement.acceptState
        tape := endTape (older ++ [v]) inside (WorkSymbol.blank :: outside)} :=
  decrement_workRunExact v older inside outside

example (v : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? reserveMachine 5
      (workStartConfiguration reserveMachine (endTape (older ++ [v]) inside outside)) =
      some {
        state := reserveMachine.acceptState
        tape := endTape (older ++ [v]) inside (WorkSymbol.blank :: outside.drop 1)} :=
  reserve_workRunExact v older inside outside

example : workRunExact? reserveMachine 5
    (workStartConfiguration reserveMachine (endTape [4, 0] [.oneZero] [.oneOne, .zeroOne])) =
    some {
      state := reserveMachine.acceptState
      tape := endTape [4, 0] [.oneZero] [.blank, .zeroOne]} :=
  reserve_workRunExact 0 [4] [.oneZero] [.oneOne, .zeroOne]

example : workRunExact? reserveMachine 5
    (workStartConfiguration reserveMachine (endTape [0] [] [])) =
    some {state := reserveMachine.acceptState, tape := endTape [0] [] [.blank]} :=
  reserve_workRunExact 0 [] [] []

example : graph.WellFormed := graph_wellFormed
example (r : BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult) :
    (resultValues r).length = 3 := resultValues_length r
example (c b : Nat) :
    clearedSpan (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 c b) = c + b + 3 :=
  clearedSpan_eq c b

example (c b : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps c b) (initialConfiguration c b older inside outside) =
      some (finalConfiguration c b older inside outside) := workRunExact c b older inside outside

example (c b : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps c b)
      (encodeWorkConfiguration (initialConfiguration c b older inside outside)) =
      encodeWorkConfiguration (finalConfiguration c b older inside outside) :=
  run_compile_exact c b older inside outside

example (c b : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration c b older inside outside).state = machine.acceptState ↔ c < b :=
  final_accept_iff c b older inside outside

example (c b : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration c b older inside outside).state = machine.rejectState ↔ b ≤ c :=
  final_reject_iff c b older inside outside

example (n : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration n n older inside outside).state = machine.rejectState :=
  (final_reject_iff n n older inside outside).2 (Nat.le_refl n)

example (n : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration n (n + 1) older inside outside).state = machine.acceptState :=
  (final_accept_iff n (n + 1) older inside outside).2 (by omega)

example (n : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration (n + 1) n older inside outside).state = machine.rejectState :=
  (final_reject_iff (n + 1) n older inside outside).2 (by omega)

example (n : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration 0 (n + 1) older inside outside).state = machine.acceptState :=
  (final_accept_iff 0 (n + 1) older inside outside).2 (by omega)

example (n : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration n 0 older inside outside).state = machine.rejectState :=
  (final_reject_iff n 0 older inside outside).2 (Nat.zero_le n)

example (c b : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration c b older inside outside).tape.right =
      (registerWord older).reverse ++ inside := final_inside_preserved c b older inside outside

example (c b : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration c b older inside outside).tape.left =
      List.replicate (c + b + 3) WorkSymbol.blank ++ outside.drop 1 :=
  final_outside_accounted c b older inside outside

example (c b : Nat) (older : List Nat) (inside tail : List WorkSymbol) (first : WorkSymbol) :
    (finalConfiguration c b older inside (first :: tail)).tape.left =
      List.replicate (c + b + 3) WorkSymbol.blank ++ tail := rfl

example (c b : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration c b older inside []).tape.left =
      List.replicate (c + b + 3) WorkSymbol.blank := by
  simp only [final_outside_accounted, List.drop_nil, List.append_nil]

example : (finalConfiguration 0 0 [] [] []).tape.left ≠ [] := by decide

example (p width : Nat) (hp : p + 1 < width) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration (p + 1) width older inside outside).state = machine.acceptState :=
  (final_accept_iff (p + 1) width older inside outside).2 hp

example (p : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration (p + 1) (p + 1) older inside outside).state = machine.rejectState :=
  (final_reject_iff (p + 1) (p + 1) older inside outside).2 (Nat.le_refl _)

example (c b bound : Nat) (hc : c ≤ bound) (hb : b ≤ bound) :
    workSteps c b ≤ workBound bound := workSteps_le c b bound hc hb

example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) :=
  rawTimePolynomial_eval bound input

example (c b : Nat) (bound : NatPolynomial) (input : Nat)
    (hc : c ≤ bound.eval input) (hb : b ≤ bound.eval input) :
    6 * workSteps c b ≤ (rawTimePolynomial bound).eval input := raw_time_polynomial c b bound input hc hb

example : (rawTimePolynomial (.constant 0)).eval 42 = 516 := rfl

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState
