/-
Copyright (c) 2026 PNP Labs.

The conclusion selector checks the physical count, restores the frame, and
derives the premise/conclusion ordinal boundary without a supplied branch bit.
-/
import PNP.Concrete.CookLevinBuilderPayloadConclusionGuard

namespace PNP.Concrete.CookLevin.BuilderPayloadConclusionGuardRegression

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open WorkMachineProgramGraph (Node Graph Endpoint endpointConfiguration)
open BuilderPayloadConclusionGuard

example : graph.nodes.length = 4 :=
  BuilderPayloadConclusionGuard.graph_nodes_length

example : graph.WellFormed :=
  BuilderPayloadConclusionGuard.graph_wellFormed

example (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? BuilderPayloadConclusionGuard.machine (workSteps count position)
      (initialConfiguration older ordinal count position inside outside) =
      some (finalConfiguration older ordinal count position inside outside) :=
  BuilderPayloadConclusionGuard.workRunExact older ordinal count position inside outside

example (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine BuilderPayloadConclusionGuard.machine) (6 * workSteps count position)
      (encodeWorkConfiguration (initialConfiguration older ordinal count position inside outside)) =
      encodeWorkConfiguration (finalConfiguration older ordinal count position inside outside) :=
  BuilderPayloadConclusionGuard.run_compile_exact older ordinal count position inside outside

example (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration older ordinal count position inside outside).state = BuilderPayloadConclusionGuard.machine.acceptState ↔ count = 1 :=
  BuilderPayloadConclusionGuard.final_accept_iff older ordinal count position inside outside

example (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration older ordinal count position inside outside).state = BuilderPayloadConclusionGuard.machine.rejectState ↔ count ≠ 1 :=
  BuilderPayloadConclusionGuard.final_reject_iff older ordinal count position inside outside

example (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration older ordinal count position inside outside).tape =
      endTape (older ++ frame ordinal count position) inside (finalOutside count outside) :=
  BuilderPayloadConclusionGuard.final_tape older ordinal count position inside outside

example (count : Nat) (outside : List WorkSymbol) :
    (finalOutside count outside).length ≤ outside.length + count + 1 :=
  BuilderPayloadConclusionGuard.finalOutside_length_le count outside

example (older : List Nat) (ordinal count position : Nat) (outside : List WorkSymbol) :
    (registerWord (older ++ frame ordinal count position)).length + (finalOutside count outside).length ≤
      (registerWord (older ++ frame ordinal count position)).length + outside.length + count + 1 :=
  BuilderPayloadConclusionGuard.final_span_le older ordinal count position outside

example (count position : Nat) :
    workSteps count position = RegisterCopy.steps [position] count + count + 8 + 2 * min 1 count :=
  BuilderPayloadConclusionGuard.workSteps_eq count position

example : BuilderPayloadConclusionGuard.machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  BuilderPayloadConclusionGuard.rules_pairwise_query_distinct

example : WorkMachineProgramGraph.NoRuleAt BuilderPayloadConclusionGuard.machine BuilderPayloadConclusionGuard.machine.acceptState :=
  BuilderPayloadConclusionGuard.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt BuilderPayloadConclusionGuard.machine BuilderPayloadConclusionGuard.machine.rejectState :=
  BuilderPayloadConclusionGuard.noRuleAtReject

example : BuilderPayloadConclusionGuard.machine.acceptState ≠ BuilderPayloadConclusionGuard.machine.rejectState :=
  BuilderPayloadConclusionGuard.acceptState_ne_rejectState

example (older : List Nat) (ordinal count position bound : Nat) (outside : List WorkSymbol)
    (hSpan : (registerWord (older ++ frame ordinal count position)).length + outside.length ≤ bound) :
    (registerWord (older ++ frame ordinal count position)).length + (finalOutside count outside).length ≤ spanBound bound ∧
    workSteps count position ≤ workBound bound :=
  BuilderPayloadConclusionGuard.space_time_bounds older ordinal count position bound outside hSpan

example (older : List Nat) (ordinal count position : Nat) (outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (older ++ frame ordinal count position)).length + outside.length ≤ bound.eval input) :
    (registerWord (older ++ frame ordinal count position)).length + (finalOutside count outside).length ≤ (spanPolynomial bound).eval input ∧
    6 * workSteps count position ≤ (rawTimePolynomial bound).eval input :=
  BuilderPayloadConclusionGuard.source_polynomial_bounds older ordinal count position outside bound input hSpan

example : endpoint 0 = .reject := rfl
example : endpoint 1 = .accept := rfl
example : endpoint 2 = .reject := rfl

example (older : List Nat) (ordinal count position : Nat) (inside outside : List WorkSymbol)
    (hCount : 2 ≤ count) :
    (finalConfiguration older ordinal count position inside outside).state =
      BuilderPayloadConclusionGuard.machine.rejectState :=
  (BuilderPayloadConclusionGuard.final_reject_iff older ordinal count position inside outside).2 (by omega)

-- Count accounting and the actual accepting state force the conclusion ordinal.
example {width : Nat} (premises : List (BoundedLiteral width)) (older : List Nat)
    (ordinal count position : Nat) (inside outside : List WorkSymbol)
    (hSize : ordinal + count = premises.length + 1)
    (hAccepted : (finalConfiguration older ordinal count position inside outside).state =
      BuilderPayloadConclusionGuard.machine.acceptState) :
    ordinal = premises.length := by
  have hCount := (BuilderPayloadConclusionGuard.final_accept_iff older ordinal count position inside outside).1 hAccepted
  omega

-- Positive, nonfinal counts force a valid premise index; no index is supplied.
example {width : Nat} (premises : List (BoundedLiteral width)) (older : List Nat)
    (ordinal count position : Nat) (inside outside : List WorkSymbol)
    (hSize : ordinal + count = premises.length + 1)
    (hNotEmpty : (BuilderLiteralSearchGuard.finalConfiguration older ordinal count position inside outside).state =
      BuilderLiteralSearchGuard.machine.rejectState)
    (hNotLast : (finalConfiguration older ordinal count position inside outside).state =
      BuilderPayloadConclusionGuard.machine.rejectState) :
    ordinal < premises.length := by
  have hPositive := (BuilderLiteralSearchGuard.final_reject_iff older ordinal count position inside outside).1 hNotEmpty
  have hOther := (BuilderPayloadConclusionGuard.final_reject_iff older ordinal count position inside outside).1 hNotLast
  omega

example (position : Nat) :
    workSteps 0 position = RegisterCopy.steps [position] 0 + 8 := by
  rw [BuilderPayloadConclusionGuard.workSteps_eq]
  simp only [Nat.min_zero, Nat.mul_zero, Nat.add_zero]

example (count position : Nat) (hPositive : 0 < count) :
    workSteps count position = RegisterCopy.steps [position] count + count + 10 := by
  have hMin : min 1 count = 1 := Nat.min_eq_left (by omega)
  rw [BuilderPayloadConclusionGuard.workSteps_eq, hMin]

end PNP.Concrete.CookLevin.BuilderPayloadConclusionGuardRegression
