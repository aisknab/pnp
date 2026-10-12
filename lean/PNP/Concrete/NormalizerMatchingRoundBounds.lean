/-
Copyright (c) 2026 PNP Labs.

Uniform per-round encoded runtime bounds. Search and update packets are
bounded from one fixed input-derived invariant; every closed submachine's
actual budget is evaluated at that same invariant, not at the prior round.
-/
import PNP.Concrete.NormalizerMatchingRawInvariant

namespace PNP.Concrete.NormalizerBlocks.MatchingDriver

def tablePolynomial : NatPolynomial := .add (.mul (.linear 2 8) .variable) (.constant 2)
def searchInputPolynomial : NatPolynomial := .add (.linear 3 3) (.mul (.constant 2) tablePolynomial)
def searchOutputPolynomial : NatPolynomial :=
  .add searchInputPolynomial (Search.sourceFuel.substitute searchInputPolynomial)
def searchWorkPolynomial : NatPolynomial :=
  .add (.add (.mul (.constant 3) tablePolynomial) (.linear 14 54))
    (Search.sourceFuel.substitute searchInputPolynomial)
def augmentationInputPolynomial : NatPolynomial :=
  .add (.mul (.constant 2) tablePolynomial) (.add searchOutputPolynomial (.constant 1))
def advanceWorkPolynomial : NatPolynomial :=
  .add (.add (.mul (.constant 4) searchOutputPolynomial) (.mul (.constant 11) tablePolynomial))
    (.add (.constant 45) (Augmentation.sourceFuel.substitute augmentationInputPolynomial))
def roundPolynomial : NatPolynomial := .add searchWorkPolynomial (.add advanceWorkPolynomial (.constant 2))

theorem tablePolynomial_eval (bound : Nat) :
    tablePolynomial.eval bound = MatchingLoop.tableBytes bound bound := rfl
theorem searchInputPolynomial_eval (bound : Nat) :
    searchInputPolynomial.eval bound = 3 * bound + 3 + 2 * tablePolynomial.eval bound := rfl
theorem searchOutputPolynomial_eval (bound : Nat) :
    searchOutputPolynomial.eval bound = searchInputPolynomial.eval bound +
      Search.sourceFuel.eval (searchInputPolynomial.eval bound) := by
  change _ + (Search.sourceFuel.substitute searchInputPolynomial).eval bound = _
  rw [NatPolynomial.eval_substitute]
theorem searchWorkPolynomial_eval (bound : Nat) :
    searchWorkPolynomial.eval bound = 3 * tablePolynomial.eval bound + (14 * bound + 54) +
      Search.sourceFuel.eval (searchInputPolynomial.eval bound) := by
  change _ + (Search.sourceFuel.substitute searchInputPolynomial).eval bound = _
  rw [NatPolynomial.eval_substitute]
  rfl
theorem augmentationInputPolynomial_eval (bound : Nat) :
    augmentationInputPolynomial.eval bound = 2 * tablePolynomial.eval bound + (searchOutputPolynomial.eval bound + 1) := rfl
theorem advanceWorkPolynomial_eval (bound : Nat) :
    advanceWorkPolynomial.eval bound = 4 * searchOutputPolynomial.eval bound + 11 * tablePolynomial.eval bound +
      (45 + Augmentation.sourceFuel.eval (augmentationInputPolynomial.eval bound)) := by
  change _ + (45 + (Augmentation.sourceFuel.substitute augmentationInputPolynomial).eval bound) = _
  rw [NatPolynomial.eval_substitute]
  rfl
theorem roundPolynomial_eval (bound : Nat) :
    roundPolynomial.eval bound = searchWorkPolynomial.eval bound + (advanceWorkPolynomial.eval bound + 2) := rfl

theorem searchPacket_length (width formula table : BitString) :
    (searchPacket width formula table).length = width.length + 2 * formula.length + 2 * table.length + 3 := by
  simp only [searchPacket, TableInit.encodeCount, List.length_append, List.length_cons, List.length_replicate]
  omega
theorem search_input_bound (bound : Nat) (r : State) (data : Within bound r) :
    (searchPacket r.width r.formula r.table).length ≤ searchInputPolynomial.eval bound := by
  have table : r.table.length ≤ tablePolynomial.eval bound := data.table_bytes
  have width := data.width
  have formula := data.formula
  rw [searchPacket_length, searchInputPolynomial_eval]
  omega

theorem searchSteps_bound (bound : Nat) (r : State) (data : Within bound r) :
    searchSteps r ≤ searchWorkPolynomial.eval bound := by
  have table : r.table.length ≤ tablePolynomial.eval bound := data.table_bytes
  have width := data.width
  have formula := data.formula
  have called := MatchingCall.searchFuel_bound (searchPacked r).core
  change searchFuel (searchPacked r) ≤ 29 + Search.sourceFuel.eval (searchPacked r).registers.input.length at called
  rw [searchPacked_input] at called
  have budget := NatPolynomial.eval_mono Search.sourceFuel (search_input_bound bound r data)
  rw [searchWorkPolynomial_eval]
  unfold searchSteps packSearchFuel
  omega

theorem search_output_bound (bound : Nat) (r : State) (data : Within bound r) :
    (searchResult r).registers.output.length ≤ searchOutputPolynomial.eval bound := by
  have input := search_input_bound bound r data
  have output := Search.polynomial_output_length (searchPacket r.width r.formula r.table)
  rw [Search.polynomial_output] at output
  rw [searchResult_output, searchOutputPolynomial_eval]
  exact Nat.le_trans output (Nat.add_le_add input (NatPolynomial.eval_mono Search.sourceFuel input))

theorem augmentationPacket_length (table path : BitString) :
    (augmentationPacket table path).length = 2 * table.length + path.length + 1 := by
  simp only [augmentationPacket, TableInit.encodeCount, List.length_append, List.length_cons, List.length_replicate]
  omega
theorem route_tail_bound (r : State) :
    (TableInit.readCount r.registers.output.tail).state.input.length ≤ r.registers.output.length := by
  have read := Occurrence.header_input_bound r.registers.output.tail (TableInit.seeded r.registers.output.tail)
  change (TableInit.readCount r.registers.output.tail).state.input.length ≤ r.registers.output.tail.length at read
  rw [List.length_tail] at read
  omega

theorem advanceFuel_bound (bound : Nat) (r : State)
    (table : r.table.length ≤ tablePolynomial.eval bound)
    (output : r.registers.output.length ≤ searchOutputPolynomial.eval bound) :
    advanceFuel r ≤ advanceWorkPolynomial.eval bound := by
  have header := TableInit.headerFuel_bound r.registers.output.tail
  rw [List.length_tail] at header
  have tail := route_tail_bound r
  have input : (augmentationPacked r).registers.input.length ≤ augmentationInputPolynomial.eval bound := by
    rw [augmentationPacked_input, augmentationPacket_length, augmentationInputPolynomial_eval]
    omega
  have called := MatchingCall.augmentationFuel_bound (augmentationPacked r).core
  change augmentationFuel (augmentationPacked r) ≤
    13 + Augmentation.sourceFuel.eval (augmentationPacked r).registers.input.length at called
  have budget := NatPolynomial.eval_mono Augmentation.sourceFuel input
  rw [advanceWorkPolynomial_eval]
  unfold advanceFuel packAugmentationFuel
  omega

theorem bodyFuel_bound (bound : Nat) (r : State) (data : Within bound r) :
    bodyFuel r ≤ roundPolynomial.eval bound := by
  have searched := searchSteps_bound bound r data
  have table : (searchResult r).table.length ≤ tablePolynomial.eval bound := by
    rw [(searchResult_frame r).2.2.1]
    exact data.table_bytes
  have advanced := advanceFuel_bound bound (searchResult r) table (search_output_bound bound r data)
  have decision : chooseFuel (searchResult r) ≤ advanceWorkPolynomial.eval bound + 2 := by
    unfold chooseFuel
    cases selected : ForwardEdge.present (searchResult r).registers.output <;>
      simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  rw [roundPolynomial_eval]
  unfold bodyFuel
  omega

end PNP.Concrete.NormalizerBlocks.MatchingDriver
