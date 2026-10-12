/-
Copyright (c) 2026 PNP Labs.

Closed forward alternating-edge machine. One internally parsed input
determines both actual incidence and current matching membership. The
fixed finite program emits exactly their required Boolean combination;
every raw word terminates within the proved encoded-size polynomial bound.
This is a graph-query component, not a complete reachability algorithm.
-/

import PNP.Concrete.NormalizerForwardLoader

namespace PNP.Concrete.NormalizerBlocks.ForwardEdge

open BitRegister

def firstQuery : Block 14 := .seq (prepare true) (.seq query saveAnswer)
def firstAnswered (r : State) : State := marked (queried (ready true r))
def firstQueryFuel (r : State) : Nat := 15 + (GraphQuery.fuel (ready true r).core + 1)
theorem firstQuery_exec (r : State) :
    Exec firstQuery r.store (firstQueryFuel r) (firstAnswered r).store :=
  Exec.seq (prepare_exec true r) (Exec.seq (query_exec (ready true r)) (saveAnswer_exec (queried (ready true r))))

def secondQuery : Block 14 := .seq (prepare false) (.seq query finish)
def secondAnswered (r : State) : State := finished (queried (ready false r))
def secondQueryFuel (r : State) : Nat := 15 + (GraphQuery.fuel (ready false r).core + finishFuel (queried (ready false r)))
theorem secondQuery_exec (r : State) :
    Exec secondQuery r.store (secondQueryFuel r) (secondAnswered r).store :=
  Exec.seq (prepare_exec false r) (Exec.seq (query_exec (ready false r)) (finish_exec (queried (ready false r))))

def phase : Block 14 := .seq firstQuery secondQuery
def phaseResult (r : State) : State := secondAnswered (firstAnswered r)
def phaseFuel (r : State) : Nat := firstQueryFuel r + secondQueryFuel (firstAnswered r)

theorem phase_exec (r : State) : Exec phase r.store (phaseFuel r) (phaseResult r).store :=
  Exec.seq (firstQuery_exec r) (secondQuery_exec (firstAnswered r))

theorem phaseFuel_bound (r : State) :
    phaseFuel r + 1 ≤ 188 * r.formula.length + 188 * r.matching.length +
      40 * r.target.length + 40 * r.index.length + 602 := by
  have first := GraphQuery.prepared_fuel_bound r.target r.index r.formula
  have second := GraphQuery.prepared_fuel_bound r.target r.index r.matching
  have finish := finishFuel_bound (queried (ready false (firstAnswered r)))
  change (15 + (GraphQuery.fuel (GraphQuery.prepared r.target r.index r.formula) + 1)) +
    (15 + (GraphQuery.fuel (GraphQuery.prepared r.target r.index r.matching) +
      finishFuel (queried (ready false (firstAnswered r))))) + 1 ≤ _
  omega

theorem phase_output (r : State) :
    (phaseResult r).core.output =
      [present (GraphQuery.result (GraphQuery.prepared r.target r.index r.formula)).output &&
        !present (GraphQuery.result (GraphQuery.prepared r.target r.index r.matching)).output] := rfl

def block : Block 14 := .seq loader phase
def program : Program 14 := block.program 0 8
def result (input : BitString) : State := phaseResult (loaded input)
def sourceSteps (input : BitString) : Nat := loaderFuel input + phaseFuel (loaded input)
def sourceFuel : NatPolynomial := .linear 817 1164

theorem block_exec (input : BitString) : Exec block (initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (loader_exec input) (phase_exec (loaded input))

theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (initial input).store⟩ := rfl

theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have loader := loaderFuel_bound input
  have sizes := loaded_size input
  have phases := phaseFuel_bound (loaded input)
  change loaderFuel input + phaseFuel (loaded input) + 1 ≤ 817 * input.length + 1164
  omega

theorem padded_run (input : BitString) :
    BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  have bound := sourceSteps_bound input
  have split : sourceFuel.eval input.length =
      (sourceSteps input + 1) + (sourceFuel.eval input.length - (sourceSteps input + 1)) := by omega
  rw [split, BitRegister.run_add, closed_run, BitRegister.run_accepted]

theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).control = .accepted
  rw [padded_run]

def polynomial : PolynomialTimeFunction := CompilerIO.compilePolynomial program sourceFuel acceptsWithin

theorem polynomial_program :
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 14 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin

private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl

theorem polynomial_output (input : BitString) : polynomial.output input = (result input).core.output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 8 = _
  rw [padded_run]
  rfl

theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 14 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

def value (target index : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) : Bool :=
  ((clauses[index]?.getD []).find? (fun literal => literal.variableIndex == target)).isSome &&
    !(MatchingTable.read entries index == some target)

theorem polynomial_canonical (target index : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) :
    polynomial.output (encode target index clauses entries) = [value target index clauses entries] := by
  obtain ⟨targetRead, indexRead, formulaRead, matchingRead⟩ := loaded_canonical target index clauses entries
  rw [polynomial_output]
  change (phaseResult (loaded (encode target index clauses entries))).core.output = _
  rw [phase_output, targetRead, indexRead, formulaRead, matchingRead]
  change [present (GraphQuery.result (GraphQuery.prepared (List.replicate target true)
      (List.replicate index true) (GraphQuery.clauseData clauses))).output &&
    !present (GraphQuery.result (GraphQuery.prepared (List.replicate target true)
      (List.replicate index true) (GraphQuery.clauseData (MatchingTable.clauses entries)))).output] = _
  rw [GraphQuery.result_canonical, GraphQuery.result_canonical, present_answer, present_answer,
    MatchingTable.clauses_read, MatchingRelation.entry_matches]
  rfl

private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 14 sourceFuel).eval input.length) input := rfl

theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 14 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm

theorem machine_canonical (target index : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 14 sourceFuel).eval (encode target index clauses entries).length)
      (encode target index clauses entries) = [value target index clauses entries] := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.ForwardEdge
