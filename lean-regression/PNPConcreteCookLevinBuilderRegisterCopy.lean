import PNP.Concrete.CookLevinBuilderUnaryPolynomial

namespace PNP.Concrete.CookLevinBuilderRegisterCopyRegression

open CookLevin.BuilderUnaryPolynomial
open CookLevin.BuilderUnaryPolynomial.RegisterCopy

example (newerCount : Nat) :
    (RegisterCopy.machine newerCount).rules.length =
      9 * RegisterCopy.stateCount newerCount := RegisterCopy.rules_length newerCount

example : (RegisterCopy.machine 0).rules.length = 90 := by decide

example (newerCount : Nat) :
    (RegisterCopy.machine newerCount).rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) :=
  RegisterCopy.rules_pairwise_query_distinct newerCount

example (newerCount : Nat) (rule : WorkRule)
    (hMem : rule ∈ (RegisterCopy.machine newerCount).rules) :
    rule.sourceState < (RegisterCopy.machine newerCount).acceptState :=
  RegisterCopy.rule_source_lt_acceptState newerCount rule hMem

example (newerCount : Nat) :
    (RegisterCopy.machine newerCount).startState = 0 :=
  RegisterCopy.machine_startState newerCount

example (newerCount : Nat) :
    (RegisterCopy.machine newerCount).acceptState ≠
      (RegisterCopy.machine newerCount).rejectState :=
  RegisterCopy.machine_acceptState_ne_rejectState newerCount

example : RegisterCopy.steps [] 0 = 7 := by decide

example : RegisterCopy.steps [0, 2] 3 = 84 := by decide

example :
    workRunExact? (RegisterCopy.machine 0) 7
        (RegisterCopy.initialConfiguration [] [] [] 0 []) =
      some (RegisterCopy.finalConfiguration [] [] [] 0 []) := by decide

example :
    workRunExact? (RegisterCopy.machine 0) 33
        (RegisterCopy.initialConfiguration
          [scratchEndSymbol] [registerMarkSymbol, scratchEndSymbol]
          [unitSymbol, separatorSymbol, scratchEndSymbol, registerMarkSymbol] 2 []) =
      some (RegisterCopy.finalConfiguration
        [scratchEndSymbol] [registerMarkSymbol, scratchEndSymbol]
        [unitSymbol, separatorSymbol, scratchEndSymbol, registerMarkSymbol] 2 []) := by decide

example :
    workRunExact? (RegisterCopy.machine 2) 84
        (RegisterCopy.initialConfiguration [registerMarkSymbol] [scratchEndSymbol] [] 3 [0, 2]) =
      some (RegisterCopy.finalConfiguration
        [registerMarkSymbol] [scratchEndSymbol] [] 3 [0, 2]) := by decide

example :
    (RegisterCopy.finalConfiguration [] [] [] 3 [0, 2]).tape.right =
      (registerWord [3, 0, 2, 3]).reverse := rfl

example :
    (RegisterCopy.finalConfiguration [] [] [unitSymbol, separatorSymbol,
      scratchEndSymbol, registerMarkSymbol, WorkSymbol.blank] 2 []).tape.left =
      [registerMarkSymbol, WorkSymbol.blank] := rfl

example :
    workStep? (RegisterCopy.machine 0)
        { state := 0, tape := { left := [], head := WorkSymbol.blank, right := [] } } =
      some { state := 11, tape := { left := [], head := WorkSymbol.blank, right := [] } } := by decide

example (older inside outsideTail : List WorkSymbol) (sourceValue : Nat) (newer : List Nat) :
    workRunExact? (RegisterCopy.machine newer.length) (RegisterCopy.steps newer sourceValue)
        (RegisterCopy.initialConfiguration older inside outsideTail sourceValue newer) =
      some (RegisterCopy.finalConfiguration older inside outsideTail sourceValue newer) :=
  RegisterCopy.workRunExact older inside outsideTail sourceValue newer

example (newer : List Nat) (sourceValue : Nat) :
    let span := newer.length + 1 + newer.sum
    RegisterCopy.steps newer sourceValue =
      2 * span * sourceValue + 2 * sourceValue * sourceValue +
        7 * sourceValue + 2 * span + 5 := RegisterCopy.steps_closed newer sourceValue

example (newer : List NatPolynomial) (sourceValue : NatPolynomial) (input : Nat) :
    (RegisterCopy.timePolynomial newer sourceValue).eval input =
      RegisterCopy.steps (newer.map (fun value => value.eval input)) (sourceValue.eval input) :=
  RegisterCopy.timePolynomial_eval newer sourceValue input

example (newer : List Nat) (sourceValue bound : Nat)
    (hSource : sourceValue ≤ bound) (hNewer : newer.length + newer.sum ≤ bound) :
    RegisterCopy.steps newer sourceValue ≤
      4 * (bound + 1) * (bound + 1) + 9 * (bound + 1) + 5 :=
  RegisterCopy.steps_le newer sourceValue bound hSource hNewer

end PNP.Concrete.CookLevinBuilderRegisterCopyRegression
