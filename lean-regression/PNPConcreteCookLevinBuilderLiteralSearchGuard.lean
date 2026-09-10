import PNP.Concrete.CookLevinBuilderLiteralSearchGuard

open PNP.Concrete PNP.Concrete.CookLevin
open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLiteralSearchGuard

-- Independent boundary and scratch-restoration contracts.
example : graph.nodes.length = 4 := rfl
example : endpoint 0 = .accept := rfl
example : endpoint 1 = .reject := rfl
example : endpoint 23 = .reject := rfl
example : finalOutside 0 [] = [.blank] := rfl
example : finalOutside 2 [] = [.blank,.blank,.blank] := rfl
example : (finalOutside 2 (List.replicate 7 .blank)).length = 7 := rfl
example : spanBound 0 = 1 := rfl
example : workBound 0 = 26 := rfl
example (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps 0 7) (initialConfiguration older 5 0 7 inside outside) =
      some (finalConfiguration older 5 0 7 inside outside) := workRunExact _ _ _ _ _ _
example (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps 3 0) (initialConfiguration older 0 3 0 inside outside) =
      some (finalConfiguration older 0 3 0 inside outside) := workRunExact _ _ _ _ _ _
example (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration older 5 0 7 inside outside).tape =
      endTape (older ++ [5,0,7]) inside ([.blank] ++ outside.drop 1) := rfl

example : graph.nodes.length = 4 :=
  BuilderLiteralSearchGuard.graph_nodes_length

example : graph.WellFormed :=
  BuilderLiteralSearchGuard.graph_wellFormed

example (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps count position)
      (initialConfiguration older ordinal count position inside outside) =
      some (finalConfiguration older ordinal count position inside outside) :=
  BuilderLiteralSearchGuard.workRunExact older ordinal count position inside outside

example (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps count position)
      (encodeWorkConfiguration (initialConfiguration older ordinal count position inside outside)) =
      encodeWorkConfiguration (finalConfiguration older ordinal count position inside outside) :=
  BuilderLiteralSearchGuard.run_compile_exact older ordinal count position inside outside

example (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration older ordinal count position inside outside).state = machine.acceptState ↔ count = 0 :=
  BuilderLiteralSearchGuard.final_accept_iff older ordinal count position inside outside

example (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration older ordinal count position inside outside).state = machine.rejectState ↔ 0 < count :=
  BuilderLiteralSearchGuard.final_reject_iff older ordinal count position inside outside

example (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration older ordinal count position inside outside).tape =
      endTape (older ++ frame ordinal count position) inside (finalOutside count outside) :=
  BuilderLiteralSearchGuard.final_tape older ordinal count position inside outside

example (count : Nat) (outside : List WorkSymbol) :
    (finalOutside count outside).length ≤ outside.length + count + 1 :=
  BuilderLiteralSearchGuard.finalOutside_length_le count outside

example (older : List Nat) (ordinal count position : Nat) (outside : List WorkSymbol) :
    (registerWord (older ++ frame ordinal count position)).length + (finalOutside count outside).length ≤
      (registerWord (older ++ frame ordinal count position)).length + outside.length + count + 1 :=
  BuilderLiteralSearchGuard.final_span_le older ordinal count position outside

example (count position : Nat) :
    workSteps count position = RegisterCopy.steps [position] count + count + 8 :=
  BuilderLiteralSearchGuard.workSteps_eq count position

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  BuilderLiteralSearchGuard.rules_pairwise_query_distinct

example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  BuilderLiteralSearchGuard.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  BuilderLiteralSearchGuard.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState :=
  BuilderLiteralSearchGuard.acceptState_ne_rejectState

example (older : List Nat) (ordinal count position bound : Nat) (outside : List WorkSymbol)
    (hSpan : (registerWord (older ++ frame ordinal count position)).length + outside.length ≤ bound) :
    (registerWord (older ++ frame ordinal count position)).length + (finalOutside count outside).length ≤ spanBound bound ∧
    workSteps count position ≤ workBound bound :=
  BuilderLiteralSearchGuard.space_time_bounds older ordinal count position bound outside hSpan

example (older : List Nat) (ordinal count position : Nat) (outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (older ++ frame ordinal count position)).length + outside.length ≤ bound.eval input) :
    (registerWord (older ++ frame ordinal count position)).length + (finalOutside count outside).length ≤ (spanPolynomial bound).eval input ∧
    6 * workSteps count position ≤ (rawTimePolynomial bound).eval input :=
  BuilderLiteralSearchGuard.source_polynomial_bounds older ordinal count position outside bound input hSpan
