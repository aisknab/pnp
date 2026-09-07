import PNP.Concrete.CookLevinBuilderRegisterTable

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderRegisterTable

example (row : List Nat) : BuilderRegisterPack.values (fields row) emptyEnvironment = row := fields_values row
example (row older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (rowMachine row) (rowSteps row)
      (workStartConfiguration (rowMachine row) (endTape older inside outside)) =
      some {
        state := (rowMachine row).acceptState
        tape := endTape (older ++ row) inside (outside.drop (rowSpan row)) } :=
  row_workRunExact row older inside outside

example : lookup [] 0 0 = none := rfl
example : lookup [[]] 0 0 = some [] := rfl
example : lookup [[7, 0, 1], [3, 2, 0]] 0 0 = some [7, 0, 1] := rfl
example : lookup [[7, 0, 1], [3, 2, 0]] 0 1 = some [3, 2, 0] := rfl
example : lookup [[7, 0, 1], [3, 2, 0]] 0 2 = none := rfl
example : lookup [[7, 0, 1], [3, 2, 0]] 4 3 = none := rfl
example : lookup [[7, 0, 1], [3, 2, 0]] 4 4 = some [7, 0, 1] := rfl
example : lookup [[7, 0, 1], [3, 2, 0]] 4 5 = some [3, 2, 0] := rfl
example : lookup [[7, 0, 1], [3, 2, 0]] 4 6 = none := rfl
example : lookup [[7, 0, 1], [3, 2, 0]] 4 100 = none := rfl

example (rows : List (List Nat)) (first index : Nat) (h : index < rows.length) :
    lookup rows first (first + index) = some rows[index] := lookup_at rows first index h
example (rows : List (List Nat)) (first actual : Nat) (h : actual < first) :
    lookup rows first actual = none := lookup_outside rows first actual (Or.inl h)
example (rows : List (List Nat)) (first actual : Nat) (h : first + rows.length ≤ actual) :
    lookup rows first actual = none := lookup_outside rows first actual (Or.inr h)
example (rows : List (List Nat)) (first actual : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine rows first) (workSteps rows first actual)
      (initialConfiguration rows first actual older inside outside) =
      some (finalConfiguration rows first actual older inside outside) :=
  workRunExact rows first actual older inside outside
example (rows : List (List Nat)) (first actual : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine rows first)) (6 * workSteps rows first actual)
      (encodeWorkConfiguration (initialConfiguration rows first actual older inside outside)) =
      encodeWorkConfiguration (finalConfiguration rows first actual older inside outside) :=
  run_compile_exact rows first actual older inside outside

example (rows : List (List Nat)) (first index : Nat) (h : index < rows.length)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine rows first) (workSteps rows first (first + index))
      (initialConfiguration rows first (first + index) older inside outside) =
      some {
        state := (machine rows first).acceptState
        tape := endTape (older ++ [first + index] ++ rows[index]) inside
          (outside.drop (rowSpan rows[index])) } :=
  selected_workRunExact rows first index h older inside outside
example (rows : List (List Nat)) (first actual : Nat) (h : actual < first ∨ first + rows.length ≤ actual)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine rows first) (workSteps rows first actual)
      (initialConfiguration rows first actual older inside outside) =
      some {
        state := (machine rows first).rejectState
        tape := endTape (older ++ [actual]) inside outside } :=
  rejected_workRunExact rows first actual h older inside outside

example (rows : List (List Nat)) (first actual : Nat) :
    workSteps rows first actual ≤ workBound rows first := workSteps_le rows first actual
example (rows : List (List Nat)) (first actual : Nat) :
    rowSpan ((lookup rows first actual).getD []) ≤ tableSpan rows := selected_span_le rows first actual
example (rows : List (List Nat)) (first actual : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration rows first actual older inside outside).tape.left.length ≤ outside.length :=
  final_exterior_length_le rows first actual older inside outside
example (rows : List (List Nat)) (first actual : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (h : (registerWord (older ++ [actual])).length ≤ bound.eval inputLength) :
    (registerWord (older ++ [actual] ++ (lookup rows first actual).getD [])).length ≤
        (spanPolynomial rows bound).eval inputLength ∧
      6 * workSteps rows first actual ≤ (rawTimePolynomial rows first).eval inputLength :=
  source_polynomial_bounds rows first actual older bound inputLength h

example (rows : List (List Nat)) (first : Nat) :
    (machine rows first).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  rules_pairwise_query_distinct rows first
example (rows : List (List Nat)) (first : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine rows first) (machine rows first).acceptState :=
  noRuleAtAccept rows first
example (rows : List (List Nat)) (first : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine rows first) (machine rows first).rejectState :=
  noRuleAtReject rows first
example (rows : List (List Nat)) (first : Nat) :
    (machine rows first).acceptState ≠ (machine rows first).rejectState :=
  acceptState_ne_rejectState rows first

example (row : List Nat) (first : Nat) :
    (finalConfiguration [row] first first [] [] []).tape =
      endTape ([first] ++ row) [] [] := by
  simp only [finalConfiguration, lookup, if_pos rfl, ite_true, resultTape, List.nil_append, List.drop_nil]
example (first actual : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration [] first actual older inside outside).tape =
      endTape (older ++ [actual]) inside outside := rfl
example (first : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration [[]] first first older inside outside).tape =
      endTape (older ++ [first]) inside outside := by
  simp only [finalConfiguration, lookup, if_pos rfl, ite_true, resultTape, rowSpan, registerWord,
    List.length_nil, List.append_nil, List.drop_zero]
example (rows : List (List Nat)) (first actual : Nat) (older : List Nat) (inside outside : List WorkSymbol)
    (h : first + rows.length ≤ actual) :
    (finalConfiguration rows first actual older inside outside).tape = endTape (older ++ [actual]) inside outside := by
  simp only [finalConfiguration, lookup_outside rows first actual (Or.inr h), resultTape]
