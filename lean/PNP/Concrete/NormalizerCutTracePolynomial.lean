/-
Copyright (c) 2026 PNP Labs.

One encoded-input polynomial bounds internal matching, construction of the
final exploration packet, scratch reset and complete terminal trace generation.
The finite-tape program needs no supplied matching or trace.
-/
import PNP.Concrete.NormalizerCutTrace

namespace PNP.Concrete.NormalizerBlocks.CutTrace
open BitRegister

def packetPolynomial : NatPolynomial :=
  MatchingDriver.searchInputPolynomial.substitute MatchingDriver.limitPolynomial
def packPolynomial : NatPolynomial :=
  .add (.mul (.constant 3) (MatchingDriver.tablePolynomial.substitute MatchingDriver.limitPolynomial))
    (.add (.mul (.constant 14) MatchingDriver.limitPolynomial) (.constant 25))
def sourceFuel : NatPolynomial :=
  .add MatchingDriver.sourceFuel (.add packPolynomial
    (.add (Exploration.sourceFuel.substitute packetPolynomial) (.constant 32)))

theorem packetPolynomial_eval (size : Nat) :
    packetPolynomial.eval size = MatchingDriver.searchInputPolynomial.eval (6 * size + 6) := by
  rw [packetPolynomial, NatPolynomial.eval_substitute]
  rfl
theorem packPolynomial_eval (size : Nat) :
    packPolynomial.eval size =
      3 * MatchingDriver.tablePolynomial.eval (6 * size + 6) + (14 * (6 * size + 6) + 25) := by
  change 3 * (MatchingDriver.tablePolynomial.substitute MatchingDriver.limitPolynomial).eval size + _ = _
  rw [NatPolynomial.eval_substitute]
  rfl
theorem sourceFuel_eval (size : Nat) :
    sourceFuel.eval size = MatchingDriver.sourceFuel.eval size +
      (packPolynomial.eval size + (Exploration.sourceFuel.eval (packetPolynomial.eval size) + 32)) := by
  change _ + (_ + ((Exploration.sourceFuel.substitute packetPolynomial).eval size + 32)) = _
  rw [NatPolynomial.eval_substitute]

theorem packet_bound (input : BitString) : (packet input).length ≤ packetPolynomial.eval input.length := by
  rw [packetPolynomial_eval]
  exact MatchingDriver.search_input_bound _ (MatchingDriver.result input) (MatchingDriver.result_within input)
theorem packFuel_bound (input : BitString) :
    MatchingDriver.packSearchFuel (MatchingDriver.result input) ≤ packPolynomial.eval input.length := by
  have data := MatchingDriver.result_within input
  have table := data.table_bytes
  have width := data.width
  have formula := data.formula
  rw [packPolynomial_eval, MatchingDriver.tablePolynomial_eval]
  unfold MatchingDriver.packSearchFuel
  omega
theorem exploreFuel_packet (input : BitString) :
    exploreFuel (packed input) = 30 + Exploration.sourceSteps (packet input) := by
  change 29 + (1 + Exploration.sourceSteps (packed input).registers.input) = _
  rw [packed_input]
  omega
theorem sourceSteps_bound (input : BitString) :
    sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have matching := MatchingDriver.sourceSteps_bound input
  have packing := packFuel_bound input
  have exploration := Exploration.sourceSteps_bound (packet input)
  have monotone := NatPolynomial.eval_mono Exploration.sourceFuel (packet_bound input)
  rw [sourceFuel_eval]
  unfold sourceSteps
  rw [exploreFuel_packet]
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
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 33 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) :
    polynomial.output input = (result input).registers.output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 8 = _
  rw [padded_run, MatchingDriver.State.get_output]
theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 33 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input
theorem polynomial_canonical (variables : Nat) (clauses : List (List CNFLiteral)) :
    polynomial.output (MatchingDriver.encode variables clauses) =
      TraceData.encode (Search.traceValue variables clauses (MatchingLoop.fullTable variables clauses)) := by
  rw [polynomial_output, result_canonical]

private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 33 sourceFuel).eval input.length) input := rfl
theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 33 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm
theorem machine_canonical (variables : Nat) (clauses : List (List CNFLiteral)) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 33 sourceFuel).eval (MatchingDriver.encode variables clauses).length)
      (MatchingDriver.encode variables clauses) =
        TraceData.encode (Search.traceValue variables clauses (MatchingLoop.fullTable variables clauses)) := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.CutTrace
