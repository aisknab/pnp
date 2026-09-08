import PNP.Concrete.CookLevinBuilderExactlyOneClauseOccupancy

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderExactlyOneClauseOccupancy
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)

-- The empty exactly-one list emits one empty clause; it is not padding.
example : LocalConstraint.pairCount 0 = 0 := rfl
example : LocalConstraint.pairCount 1 = 0 := rfl
example : LocalConstraint.pairCount 2 = 1 := rfl
example : LocalConstraint.pairCount 4 = 6 := rfl
example : LocalConstraint.pairCount 10 = 45 := rfl
example (count : Nat) : 2 * LocalConstraint.pairCount count + count = count * count :=
  pairCount_twice count
example (index count : Nat) :
    index < 1 + LocalConstraint.pairCount count ↔ leftValue index count < rightValue count :=
  occupancy_iff index count
example : ClauseOccupancy.localSlot (.exactlyOne ([] : List (Fin 0))) 0 = true := rfl
example : ClauseOccupancy.localSlot (.exactlyOne ([] : List (Fin 0))) 1 = false := rfl
example : ClauseOccupancy.localSlot (.exactlyOne [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩] : LocalConstraint 1) 3 = true := rfl
example : ClauseOccupancy.localSlot (.exactlyOne [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩] : LocalConstraint 1) 4 = false := rfl
example : leftValue 0 0 < rightValue 0 := by decide
example : ¬ leftValue 1 0 < rightValue 0 := by decide
example : leftValue 6 4 < rightValue 4 := by decide
example : ¬ leftValue 7 4 < rightValue 4 := by decide
example : scratchValues 1 2 = [2, 1, 2, 2, 4, 2, 2, 4, 2, 6, 4, 6] := rfl
example (index count : Nat) : (history index count).length = 12 := rfl
example (index count : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps index count) (initialConfiguration index count older inside outside) =
      some (finalConfiguration index count older inside outside) :=
  workRunExact index count older inside outside
example (index count : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps index count)
      (encodeWorkConfiguration (initialConfiguration index count older inside outside)) =
      encodeWorkConfiguration (finalConfiguration index count older inside outside) :=
  run_compile_exact index count older inside outside
example (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration 0 0 older inside outside).state = machine.acceptState :=
  (final_accept_iff 0 0 older inside outside).mpr (by decide)
example (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration 1 0 older inside outside).state = machine.rejectState :=
  (final_reject_iff 1 0 older inside outside).mpr (by decide)
example (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration 6 4 older inside outside).state = machine.acceptState :=
  (final_accept_iff 6 4 older inside outside).mpr (by decide)
example (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration 7 4 older inside outside).state = machine.rejectState :=
  (final_reject_iff 7 4 older inside outside).mpr (by decide)
example {width : Nat} (variables : List (Fin width)) (index : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration index variables.length older inside outside).state = machine.acceptState ↔
      ClauseOccupancy.localSlot (.exactlyOne variables) index = true :=
  canonical_occupancy variables index older inside outside
example (index count : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration index count older inside outside).tape =
      endTape (older ++ history index count) inside (finalOutside index count outside) :=
  final_tape index count older inside outside
example (index count : Nat) (outside : List WorkSymbol) :
    (finalOutside index count outside).length ≤ leftValue index count + rightValue count + 3 + outside.length :=
  final_outside_length_le index count outside
example (index count : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps index count)
      (initialConfiguration index count older inside [BuilderUnaryPolynomial.scratchEndSymbol, .oneOne, .blank]) =
      some (finalConfiguration index count older inside [BuilderUnaryPolynomial.scratchEndSymbol, .oneOne, .blank]) :=
  workRunExact index count older inside _
example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState
example (index count : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial)
    (inputLength : Nat)
    (hSpan : (registerWord (older ++ [index, count])).length + outside.length ≤ bound.eval inputLength) :
    (registerWord (older ++ history index count)).length + (finalOutside index count outside).length ≤
        (spanPolynomial bound).eval inputLength ∧ 6 * workSteps index count ≤ (rawTimePolynomial bound).eval inputLength :=
  source_polynomial_bounds index count older outside bound inputLength hSpan
