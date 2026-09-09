import PNP.Concrete.CookLevinBuilderLiteralListSearch

open PNP.Concrete PNP.Concrete.CookLevin
open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLiteralListSearch
open WorkMachineProgramGraph (endpointConfiguration)

-- Independent mixed-width, sign, unary terminator and exhaustion contracts.
example : graph.nodes.length = 4 := rfl
example (position : Nat) : endpoint ([] : List (BoundedLiteral 0)) position = .dead := rfl
example : endpoint ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 0 = .accept := rfl
example : endpoint ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 1 = .accept := rfl
example : endpoint ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 2 = .accept := rfl
example : endpoint ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 3 = .reject := rfl
example : endpoint ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 4 = .reject := rfl
example : endpoint ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 5 = .reject := rfl
example : endpoint ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 6 = .accept := rfl
example : endpoint ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 7 = .accept := rfl
example : endpoint ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 8 = .reject := rfl
example : endpoint ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 9 = .dead := rfl
example : endpoint ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 25 = .dead := rfl
example (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps ([] : List (BoundedLiteral 0)) position)
      (initialConfiguration ([] : List (BoundedLiteral 0)) position older inside outside)) = none :=
  workRun_observes_list ([] : List (BoundedLiteral 0)) position older inside outside
example (older : List Nat) (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 4)
      (initialConfiguration ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 4 older inside outside)) = some .f :=
  workRun_observes_list _ _ _ _ _
example (older : List Nat) (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 9)
      (initialConfiguration ([{positive := true, index := ⟨2, by decide⟩}, {positive := false, index := ⟨0, by decide⟩}, {positive := true, index := ⟨1, by decide⟩}] : List (BoundedLiteral 3)) 9 older inside outside)) = none :=
  workRun_observes_list _ _ _ _ _

example : graph.nodes.length = 4 :=
  BuilderLiteralListSearch.graph_nodes_length

example : guardNode.reference = guardReference :=
  BuilderLiteralListSearch.guard_reference

example : graph.WellFormed :=
  BuilderLiteralListSearch.graph_wellFormed

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps literals position) (initialConfiguration literals position older inside outside) =
      some (finalConfiguration literals position older inside outside) :=
  BuilderLiteralListSearch.workRunExact literals position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps literals position)
      (encodeWorkConfiguration (initialConfiguration literals position older inside outside)) =
      encodeWorkConfiguration (finalConfiguration literals position older inside outside) :=
  BuilderLiteralListSearch.run_compile_exact literals position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (tape : WorkTape) :
    observe (endpointConfiguration (endpoint literals position) tape) = DirectToken.boundedLiteralListSlot literals position :=
  BuilderLiteralListSearch.endpoint_observes_list literals position tape

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    observe (finalConfiguration literals position older inside outside) = DirectToken.boundedLiteralListSlot literals position :=
  BuilderLiteralListSearch.canonical_result literals position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps literals position) (initialConfiguration literals position older inside outside)) =
      DirectToken.boundedLiteralListSlot literals position :=
  BuilderLiteralListSearch.workRun_observes_list literals position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps literals position) (initialConfiguration literals position older inside outside)) =
      (encodeLiteralListTokens (BoundedClause.emit literals))[position]? :=
  BuilderLiteralListSearch.workRun_observes_encoding literals position older inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration literals position older inside outside).tape =
      endTape (finalValues literals position older) inside (finalOutside literals position outside) :=
  BuilderLiteralListSearch.final_tape literals position older inside outside

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  BuilderLiteralListSearch.rules_pairwise_query_distinct

example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  BuilderLiteralListSearch.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  BuilderLiteralListSearch.noRuleAtReject

example : WorkMachineProgramGraph.NoRuleAt machine 2 :=
  BuilderLiteralListSearch.noRuleAtPadding

example : machine.acceptState ≠ machine.rejectState :=
  BuilderLiteralListSearch.acceptState_ne_rejectState
