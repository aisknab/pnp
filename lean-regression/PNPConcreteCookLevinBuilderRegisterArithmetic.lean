/-
Copyright (c) 2026 PNP Labs.
The reusable arithmetic must execute on existing cells, preserve all operands
and inside data, and charge the appended unary register and complete work.
-/
import PNP.Concrete.CookLevinBuilderUnaryPolynomial

namespace PNP.Concrete.CookLevin.BuilderUnaryPolynomial.RegisterArithmeticRegression

example (value : Nat) : (RegisterConstant.machine value).rules.length =
    9 * RegisterConstant.stateCount value := RegisterConstant.rules_length value
example (value : Nat) : (RegisterConstant.machine value).rules.Pairwise (fun left right => (left.sourceState, left.readSymbol) ≠ (right.sourceState, right.readSymbol)) :=
  RegisterConstant.rules_pairwise_query_distinct value
example (value : Nat) (rule : WorkRule) (h : rule ∈ (RegisterConstant.machine value).rules) :
    rule.sourceState < (RegisterConstant.machine value).acceptState :=
  RegisterConstant.rule_source_lt_acceptState value rule h
example (value : Nat) : (RegisterConstant.machine value).acceptState ≠
    (RegisterConstant.machine value).rejectState := RegisterConstant.machine_acceptState_ne_rejectState value
example (value : Nat) (existing : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (RegisterConstant.machine value) (RegisterConstant.steps value)
      (RegisterConstant.initialConfiguration value existing inside outside) =
      some (RegisterConstant.finalConfiguration value existing inside outside) :=
  RegisterConstant.workRunExact value existing inside outside
example (value : Nat) (existing : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (RegisterConstant.machine value)) (6 * RegisterConstant.steps value)
      (encodeWorkConfiguration (RegisterConstant.initialConfiguration value existing inside outside)) =
      encodeWorkConfiguration (RegisterConstant.finalConfiguration value existing inside outside) :=
  RegisterConstant.run_compile_exact value existing inside outside

example : RegisterConstant.steps 0 = 2 := rfl
example : RegisterConstant.steps 3 = 8 := rfl
example : workRunExact? (RegisterConstant.machine 0) 2
    (RegisterConstant.initialConfiguration 0 [] [] []) =
      some (RegisterConstant.finalConfiguration 0 [] [] []) := by rfl
example : workRunExact? (RegisterConstant.machine 3) 8
    (RegisterConstant.initialConfiguration 3 [1, 0] [.blankZero, .oneBlank] [.zeroZero, .oneOne]) =
      some (RegisterConstant.finalConfiguration 3 [1, 0] [.blankZero, .oneBlank] [.zeroZero, .oneOne]) := by rfl

example (operator : RegisterBinary.Operator) (betweenCount : Nat) :
    (RegisterBinary.machine operator betweenCount).rules.length =
      9 * RegisterBinary.stateCount operator betweenCount := RegisterBinary.rules_length operator betweenCount
example (operator : RegisterBinary.Operator) (betweenCount : Nat) :
    (RegisterBinary.machine operator betweenCount).rules.Pairwise (fun left right => (left.sourceState, left.readSymbol) ≠ (right.sourceState, right.readSymbol)) :=
  RegisterBinary.rules_pairwise_query_distinct operator betweenCount
example (operator : RegisterBinary.Operator) (betweenCount : Nat) (rule : WorkRule)
    (h : rule ∈ (RegisterBinary.machine operator betweenCount).rules) :
    rule.sourceState < (RegisterBinary.machine operator betweenCount).acceptState :=
  RegisterBinary.rule_source_lt_acceptState operator betweenCount rule h
example (operator : RegisterBinary.Operator) (betweenCount : Nat) :
    (RegisterBinary.machine operator betweenCount).acceptState ≠
      (RegisterBinary.machine operator betweenCount).rejectState :=
  RegisterBinary.machine_acceptState_ne_rejectState operator betweenCount
example (operator : RegisterBinary.Operator) (older between : List Nat) (left right : Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? (RegisterBinary.machine operator between.length)
      (RegisterBinary.steps operator between left right)
      (RegisterBinary.initialConfiguration older between left right inside outside) =
      some (RegisterBinary.finalConfiguration operator older between left right inside outside) :=
  RegisterBinary.workRunExact operator older between left right inside outside
example (operator : RegisterBinary.Operator) (older between : List Nat) (left right : Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine (RegisterBinary.machine operator between.length))
      (6 * RegisterBinary.steps operator between left right)
      (encodeWorkConfiguration (RegisterBinary.initialConfiguration older between left right inside outside)) =
      encodeWorkConfiguration (RegisterBinary.finalConfiguration operator older between left right inside outside) :=
  RegisterBinary.run_compile_exact operator older between left right inside outside

example : RegisterBinary.value .add 2 3 = 5 := rfl
example : RegisterBinary.value .mul 2 3 = 6 := rfl
example : RegisterBinary.value .mul 0 3 = 0 := rfl
example : RegisterBinary.value .mul 3 0 = 0 := rfl
example : RegisterBinary.value .add 2 3 ≠ RegisterBinary.value .mul 2 3 := by decide
example : RegisterBinary.value .mul 1 7 = 7 := rfl
example : RegisterBinary.value .add 0 7 = 7 := rfl

example : workRunExact? (RegisterBinary.machine .add 0) (RegisterBinary.steps .add [] 0 0)
    (RegisterBinary.initialConfiguration [] [] 0 0 [] []) =
      some (RegisterBinary.finalConfiguration .add [] [] 0 0 [] []) := by rfl
example : workRunExact? (RegisterBinary.machine .add 0) (RegisterBinary.steps .add [] 2 3)
    (RegisterBinary.initialConfiguration [] [] 2 3 [] []) =
      some (RegisterBinary.finalConfiguration .add [] [] 2 3 [] []) := by rfl
example : workRunExact? (RegisterBinary.machine .mul 0) (RegisterBinary.steps .mul [] 0 3)
    (RegisterBinary.initialConfiguration [] [] 0 3 [] []) =
      some (RegisterBinary.finalConfiguration .mul [] [] 0 3 [] []) := by rfl
example : workRunExact? (RegisterBinary.machine .mul 0) (RegisterBinary.steps .mul [] 3 0)
    (RegisterBinary.initialConfiguration [] [] 3 0 [] []) =
      some (RegisterBinary.finalConfiguration .mul [] [] 3 0 [] []) := by rfl
set_option maxRecDepth 4096 in
example : workRunExact? (RegisterBinary.machine .mul 0) (RegisterBinary.steps .mul [] 2 3)
    (RegisterBinary.initialConfiguration [] [] 2 3 [] []) =
      some (RegisterBinary.finalConfiguration .mul [] [] 2 3 [] []) := by rfl
set_option maxRecDepth 4096 in
example : workRunExact? (RegisterBinary.machine .add 2) (RegisterBinary.steps .add [1, 0] 1 2)
    (RegisterBinary.initialConfiguration [4] [1, 0] 1 2 [.blankZero, .oneZero, .blankOne] [.oneOne, .zeroBlank]) =
      some (RegisterBinary.finalConfiguration .add [4] [1, 0] 1 2 [.blankZero, .oneZero, .blankOne] [.oneOne, .zeroBlank]) := by rfl
set_option maxRecDepth 4096 in
example : workRunExact? (RegisterBinary.machine .mul 2) (RegisterBinary.steps .mul [1, 0] 1 2)
    (RegisterBinary.initialConfiguration [4] [1, 0] 1 2 [.blankZero, .oneZero, .blankOne] [.oneOne, .zeroBlank]) =
      some (RegisterBinary.finalConfiguration .mul [4] [1, 0] 1 2 [.blankZero, .oneZero, .blankOne] [.oneOne, .zeroBlank]) := by rfl

example (operator : RegisterBinary.Operator) (between : List Nat) (left right bound : Nat)
    (hSpan : (registerWord ([left] ++ between ++ [right])).length ≤ bound) :
    RegisterBinary.steps operator between left right ≤ RegisterBinary.workBound operator bound :=
  RegisterBinary.steps_le operator between left right bound hSpan
example (operator : RegisterBinary.Operator) (left right bound : Nat)
    (hLeft : left ≤ bound) (hRight : right ≤ bound) :
    RegisterBinary.value operator left right ≤ RegisterBinary.resultBound operator bound :=
  RegisterBinary.value_le operator left right bound hLeft hRight
example (operator : RegisterBinary.Operator) (older between : List Nat) (left right : Nat) :
    (registerWord (older ++ [left] ++ between ++ [right, RegisterBinary.value operator left right])).length =
      (registerWord (older ++ [left] ++ between ++ [right])).length +
        RegisterBinary.value operator left right + 1 :=
  RegisterBinary.register_span_added operator older between left right

example : workRunExact? (RegisterConstant.machine 3) 1
    { state := 0
      tape := { left := [], head := .blank, right := [] } } =
      some
        { state := (RegisterConstant.machine 3).rejectState
          tape := { left := [], head := .blank, right := [] } } := by rfl
example : workRunExact? (RegisterBinary.machine .add 0) 1
    { state := 0
      tape := { left := [], head := .blank, right := [] } } =
      some
        { state := (RegisterBinary.machine .add 0).rejectState
          tape := { left := [], head := .blank, right := [] } } := by rfl
example : workRunExact? (RegisterBinary.machine .mul 0) 1
    { state := 0
      tape := { left := [], head := .blank, right := [] } } =
      some
        { state := (RegisterBinary.machine .mul 0).rejectState
          tape := { left := [], head := .blank, right := [] } } := by rfl

end PNP.Concrete.CookLevin.BuilderUnaryPolynomial.RegisterArithmeticRegression
