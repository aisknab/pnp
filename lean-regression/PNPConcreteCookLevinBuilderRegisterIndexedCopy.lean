import PNP.Concrete.CookLevinBuilderRegisterIndexedCopy

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderRegisterIndexedCopy
open BuilderUnaryPolynomial (registerWord unitSymbol separatorSymbol scratchEndSymbol)
open BuilderDividerOperands (endTape)

-- Encodings and clocks are independent fixtures, not an input-specific program.
example : readerWord [] = [] := rfl
example : readerWord [0, 2] = [separatorSymbol, unitSymbol, unitSymbol, separatorSymbol] := rfl
example (values : List Nat) : readerWord values = (registerWord values.reverse).reverse := readerWord_eq_reverse values
example (left right : List Nat) : readerWord (left ++ right) = readerWord left ++ readerWord right := readerWord_append left right
example : initializeSteps 0 0 = 5 := rfl
example : initializeSteps 2 3 = 15 := rfl
example : advanceSteps 2 [0, 2] 1 3 = 27 := rfl
example : finalizeSteps 2 [0, 2] 3 = 23 := rfl
example : workSteps [] 0 = 32 := rfl
example : workSteps [] 1 = 55 := rfl
example : graph.nodes.length = 5 := graph_nodes_length

example (count value : Nat) (inside outside : List WorkSymbol) :
    workRunExact? initializeMachine (initializeSteps count value)
      (workStartConfiguration initializeMachine (endTape [value, count] inside outside)) =
      some {state := initializeMachine.acceptState, tape := candidateTape 0 count [] value inside outside} :=
  initialize_workRunExact count value inside outside
example (spent remaining : Nat) (before : List Nat) (value next : Nat) (inside outside : List WorkSymbol) :
    workRunExact? advance (advanceSteps (spent + remaining) before value next)
      (workStartConfiguration advance
        (candidateTape spent remaining before value (List.replicate next unitSymbol ++ separatorSymbol :: inside) outside)) =
      some {state := advance.acceptState, tape := candidateTape spent remaining (before ++ [value]) next inside outside} :=
  advance_workRunExact spent remaining before value next inside outside
example (count : Nat) (before : List Nat) (value : Nat) (inside outside : List WorkSymbol) :
    workRunExact? finalize (finalizeSteps count before value)
      (workStartConfiguration finalize (candidateTape 0 count before value inside outside)) =
      some {state := finalize.acceptState,
            tape := BuilderRegisterCountdownControl.markedTape 0 value (before.reverse ++ [count]) inside outside} :=
  finalize_workRunExact count before value inside outside

-- Arbitrary list splits, zero values and unbounded histories.
example (before : List Nat) (value : Nat) (after older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps before value) (initialConfiguration before value after older inside outside) =
      some (finalConfiguration before value after older inside outside) :=
  workRunExact before value after older inside outside
example (value : Nat) (after older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps [] value) (initialConfiguration [] value after older inside outside) =
      some (finalConfiguration [] value after older inside outside) := workRunExact [] value after older inside outside
example (before : List Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps before 0) (initialConfiguration before 0 [] older inside outside) =
      some (finalConfiguration before 0 [] older inside outside) := workRunExact before 0 [] older inside outside
example (count repeated value : Nat) (after older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps (List.replicate count repeated) value)
      (initialConfiguration (List.replicate count repeated) value after older inside outside) =
      some (finalConfiguration (List.replicate count repeated) value after older inside outside) :=
  workRunExact (List.replicate count repeated) value after older inside outside
example (before : List Nat) (value : Nat) (after older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps before value)
      (encodeWorkConfiguration (initialConfiguration before value after older inside outside)) =
      encodeWorkConfiguration (finalConfiguration before value after older inside outside) :=
  run_compile_exact before value after older inside outside

-- Ordinary list access: the written ordinal, not a supplied result, selects the entry.
example (values older : List Nat) (index : Fin values.length) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps (values.take index.val) values[index.val])
      (workStartConfiguration machine (endTape (older ++ values.reverse ++ [index.val]) inside outside)) =
      some {state := machine.acceptState,
            tape := endTape (older ++ values.reverse ++ [index.val, values[index.val]])
              inside (outside.drop (values[index.val] + 1))} :=
  workRun_select_getElem values older index inside outside
example (values older : List Nat) (index : Fin values.length) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps (values.take index.val) values[index.val])
      (encodeWorkConfiguration (workStartConfiguration machine (endTape (older ++ values.reverse ++ [index.val]) inside outside))) =
      encodeWorkConfiguration
        {state := machine.acceptState,
         tape := endTape (older ++ values.reverse ++ [index.val, values[index.val]])
          inside (outside.drop (values[index.val] + 1))} :=
  run_compile_select_getElem values older index inside outside
example (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps [0, 3] 2)
      (workStartConfiguration machine (endTape [2, 3, 0, 2] inside outside)) =
      some {state := machine.acceptState, tape := endTape [2, 3, 0, 2, 2] inside (outside.drop 3)} :=
  workRun_select_getElem [0, 3, 2] [] ⟨2, by decide⟩ inside outside

example (before : List Nat) (value : Nat) (after older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration before value after older inside outside).tape =
      endTape (inputValues before value after older ++ [value]) inside (outside.drop (value + 1)) :=
  final_tape before value after older inside outside
example (before : List Nat) (value : Nat) (after older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration before value after older inside []).tape.left = [] := rfl
example (before : List Nat) (value : Nat) (after older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration before value after older inside outside).state = machine.acceptState := rfl

example : workStep? initializeMachine {state := 0, tape := {left := [], head := unitSymbol, right := []}} = none := rfl
example : workStep? advance {state := 1, tape := {left := [], head := scratchEndSymbol, right := []}} = none := rfl
example : workStep? finalize {state := 1, tape := {left := [], head := separatorSymbol, right := []}} = none := rfl
example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState
example : graph.WellFormed := graph_wellFormed

example (before : List Nat) (value : Nat) (after older : List Nat) (bound : Nat)
    (hSpan : (registerWord (inputValues before value after older)).length ≤ bound) :
    workSteps before value ≤ workBound bound := workSteps_le before value after older bound hSpan
example (before : List Nat) (value : Nat) (after older : List Nat) (outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (inputValues before value after older)).length + outside.length ≤ bound.eval input) :
    (registerWord (inputValues before value after older ++ [value])).length +
        (outside.drop (value + 1)).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps before value ≤ (rawTimePolynomial bound).eval input :=
  source_polynomial_bounds before value after older outside bound input hSpan
example (values older : List Nat) (index : Fin values.length) (outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (older ++ values.reverse ++ [index.val])).length + outside.length ≤ bound.eval input) :
    (registerWord (older ++ values.reverse ++ [index.val, values[index.val]])).length +
        (outside.drop (values[index.val] + 1)).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps (values.take index.val) values[index.val] ≤ (rawTimePolynomial bound).eval input :=
  selected_source_polynomial_bounds values older index outside bound input hSpan
