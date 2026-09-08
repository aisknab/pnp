/-
Copyright (c) 2026 PNP Labs.
Canonical payload-driven occupancy, distinct absent/padding outcomes, exact
restoration, empty and repeated variables, fixed control and polynomial bounds.
-/
import PNP.Concrete.CookLevinBuilderPayloadClauseOccupancy

namespace PNP.Concrete.CookLevin.BuilderPayloadClauseOccupancy.Regression
open BuilderPayloadClauseOccupancy
open BuilderLocalConstraintPayload (Slot values)
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)

def literal : BoundedLiteral 1 := ⟨false, ⟨0, by decide⟩⟩
def atom : Fin 1 := ⟨0, by decide⟩
example : tag (none : Slot 0) = 0 := rfl
example : tag (some none : Slot 0) = 1 := rfl
example : tag (some (some (.require literal))) = 2 := rfl
example : tag (some (some (.implication [] literal))) = 3 := rfl
example : tag (some (some (.exactlyOne ([] : List (Fin 0))))) = 4 := rfl
example : [testSteps 0, testSteps 1, testSteps 2, testSteps 3, testSteps 4] = [4,10,18,28,40] := rfl
example : graph.nodes.length = 13 := graph_nodes_length
example : graph.WellFormed := graph_wellFormed
example : countNode.program = BuilderUnaryPolynomial.RegisterCopy.machine 2 := rfl
example : copyTagNode.program = BuilderUnaryPolynomial.RegisterCopy.machine 1 := rfl
example : (eraseNode 0).onAccept = .dead := rfl
example : (eraseNode 1).onAccept = .reject := rfl
example : (eraseNode 2).onAccept = .node singleNode.reference := rfl
example : (eraseNode 3).onAccept = .node singleNode.reference := rfl
example : (eraseNode 4).onAccept = .node countNode.reference := rfl
example : (testNode 4).onReject = .dead := rfl
example : endpoint (none : Slot 0) 0 = .dead := rfl
example : endpoint (some none : Slot 0) 0 = .reject := rfl
example : endpoint (some (some (.require literal))) 0 = .accept := rfl
example : endpoint (some (some (.require literal))) 1 = .reject := rfl
example : endpoint (some (some (.implication [] literal))) 0 = .accept := rfl
example : endpoint (some (some (.implication [literal, literal] literal))) 1 = .reject := rfl
example : endpoint (some (some (.exactlyOne ([] : List (Fin 0))))) 0 = .accept := rfl
example : endpoint (some (some (.exactlyOne ([] : List (Fin 0))))) 1 = .reject := rfl
example : endpoint (some (some (.exactlyOne [atom]))) 1 = .reject := rfl
example : endpoint (some (some (.exactlyOne [atom, atom]))) 1 = .accept := rfl
example : endpoint (some (some (.exactlyOne [atom, atom]))) 2 = .reject := rfl
example : endpoint (some (some (.exactlyOne [atom, atom, atom]))) 3 = .accept := rfl
example : endpoint (some (some (.exactlyOne [atom, atom, atom]))) 4 = .reject := rfl

section Uniform
variable {width : Nat} (slot : Slot width) (index : Nat) (older : List Nat) (inside outside : List WorkSymbol)
example : values slot = beforeTag slot ++ [tag slot] := values_suffix slot
example : tag slot ≤ 4 := tag_le slot
example (variables : List (Fin width)) : values (some (some (.exactlyOne variables))) =
    (BuilderLocalConstraintPayload.variableValues variables).reverse ++ [variables.length,4] := exactly_one_values variables
example : workRunExact? machine (workSteps slot index) (initialConfiguration slot index older inside outside) =
    some (finalConfiguration slot index older inside outside) := workRunExact slot index older inside outside
example : run (compileWorkMachine machine) (6 * workSteps slot index)
    (encodeWorkConfiguration (initialConfiguration slot index older inside outside)) =
    encodeWorkConfiguration (finalConfiguration slot index older inside outside) := run_compile_exact slot index older inside outside
example : (initialConfiguration slot index older inside outside).tape =
    endTape (older ++ values slot ++ [index]) inside outside := rfl
example : (finalConfiguration slot index older inside outside).tape =
    endTape (finalValues slot index older) inside (finalOutside slot index outside) := final_tape slot index older inside outside
example : observe (finalConfiguration slot index older inside outside) = result slot index :=
  canonical_result slot index older inside outside
example : observe (finalConfiguration (none : Slot width) index older inside outside) = none ∧
    observe (finalConfiguration (some none : Slot width) index older inside outside) = some false :=
  absent_not_padding index older inside outside
example : (finalConfiguration slot index older inside outside).tape.right =
    (registerWord (finalValues slot index older)).reverse ++ inside := rfl
example : finalValues (some (some (.require literal))) index older =
    older ++ values (some (some (.require literal))) ++ [index] := rfl
example (variables : List (Fin width)) :
    finalValues (some (some (.exactlyOne variables))) index older =
      older ++ values (some (some (.exactlyOne variables))) ++ BuilderExactlyOneClauseOccupancy.history index variables.length := rfl
example : finalOutside (none : Slot width) index outside = List.replicate 1 WorkSymbol.blank ++ outside.drop 1 := rfl
example : finalOutside (some none : Slot width) index outside = List.replicate 2 WorkSymbol.blank ++ outside.drop 2 := rfl
example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState
example (code : Nat) : testSteps code ≤ 40 := testSteps_le code
example (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (older ++ values slot ++ [index])).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues slot index older)).length + (finalOutside slot index outside).length ≤
        (spanPolynomial bound).eval input ∧
      6 * workSteps slot index ≤ (rawTimePolynomial bound).eval input :=
  source_polynomial_bounds slot index older outside bound input hSpan
end Uniform
end PNP.Concrete.CookLevin.BuilderPayloadClauseOccupancy.Regression
