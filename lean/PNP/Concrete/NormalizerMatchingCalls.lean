/-
Copyright (c) 2026 PNP Labs.

Reentrant calls used by the outer matching loop. Every scratch register is
cleared before a closed search or augmentation call. The old working state
cannot become an undeclared premise or leak into a later matching round.
-/
import PNP.Concrete.NormalizerMatchingSize
import PNP.Concrete.NormalizerRegisterReset

namespace PNP.Concrete.NormalizerBlocks.MatchingCall
open BitRegister

def resetSearch : Block 29 := RegisterReset.keepFirst 28
theorem resetSearch_exec (r : Search.State) :
    Exec resetSearch r.store 29 (Search.initial r.registers.input).store :=
  RegisterReset.keepFirst_exec r.store

def search : Block 29 := .seq resetSearch Search.block
def searched (r : Search.State) : Search.State := Search.result r.registers.input
def searchFuel (r : Search.State) : Nat := 29 + Search.sourceSteps r.registers.input
theorem search_exec (r : Search.State) :
    Exec search r.store (searchFuel r) (searched r).store :=
  Exec.seq (resetSearch_exec r) (Search.block_exec r.registers.input)
theorem searchFuel_bound (r : Search.State) :
    searchFuel r ≤ 29 + Search.sourceFuel.eval r.registers.input.length := by
  have checked := Search.sourceSteps_bound r.registers.input
  unfold searchFuel
  omega
theorem searched_canonical (r : Search.State) (variables : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (input : r.registers.input = Exploration.encode variables clauses entries) :
    (searched r).registers.output = Search.answer (Search.value variables clauses entries) := by
  unfold searched
  rw [input]
  exact Search.result_canonical variables clauses entries

def resetAugmentation : Block 13 := RegisterReset.keepFirst 12
theorem resetAugmentation_exec (r : Augmentation.State) :
    Exec resetAugmentation r.store 13 (Augmentation.initial r.pairs.core.input).store :=
  RegisterReset.keepFirst_exec r.store

def augmentationPrefix : Block 13 := .seq resetAugmentation Augmentation.block
def augmentationPrefixFuel (r : Augmentation.State) : Nat := 13 + Augmentation.sourceSteps r.pairs.core.input
theorem augmentationPrefix_exec (r : Augmentation.State) :
    Exec augmentationPrefix r.store (augmentationPrefixFuel r)
      (Augmentation.result r.pairs.core.input).store :=
  Exec.seq (resetAugmentation_exec r) (Augmentation.block_exec r.pairs.core.input)

def augmentationView (r : Search.State) : Augmentation.State :=
  ⟨⟨r.registers, r.parent.graph.core.target, r.parent.graph.core.index, r.parent.graph.core.formula⟩,
    r.parent.graph.core.matching⟩
def withAugmentation (r : Search.State) (after : Augmentation.State) : Search.State :=
  r.withCandidate ⟨after.pairs.core, after.pairs.pending, after.pairs.firstIndex, after.pairs.buffer, after.table⟩
theorem augmentation_store (r : Search.State) :
    r.store = Frame.join (augmentationView r).store r.candidateFrame := by
  rw [Search.State.candidate_store]
  simp only [augmentationView, Search.State.candidate, Augmentation.State.store, Augmentation.State.frame,
    PathPairs.State.store, PathPairs.State.frame, Candidate.State.store, Candidate.State.frame,
    Occurrence.Registers.store, Frame.join]
theorem withAugmentation_store (r : Search.State) (after : Augmentation.State) :
    (withAugmentation r after).store = Frame.join after.store r.candidateFrame := by
  unfold withAugmentation
  rw [Search.State.withCandidate_store]
  simp only [Augmentation.State.store, Augmentation.State.frame, PathPairs.State.store,
    PathPairs.State.frame, Candidate.State.store, Candidate.State.frame, Occurrence.Registers.store, Frame.join]

def augmentation : Block 29 := Frame.block 16 augmentationPrefix
def augmented (r : Search.State) : Search.State := withAugmentation r (Augmentation.result r.registers.input)
def augmentationFuel (r : Search.State) : Nat := 13 + Augmentation.sourceSteps r.registers.input
theorem augmentation_exec (r : Search.State) :
    Exec augmentation r.store (augmentationFuel r) (augmented r).store := by
  rw [augmentation_store, show (augmented r).store =
    Frame.join (Augmentation.result r.registers.input).store r.candidateFrame from
      withAugmentation_store r (Augmentation.result r.registers.input)]
  exact Frame.execution (augmentationPrefix_exec (augmentationView r)) r.candidateFrame
theorem augmentationFuel_bound (r : Search.State) :
    augmentationFuel r ≤ 13 + Augmentation.sourceFuel.eval r.registers.input.length := by
  have checked := Augmentation.sourceSteps_bound r.registers.input
  unfold augmentationFuel
  omega
theorem augmented_canonical (r : Search.State) (entries : MatchingTable.Entries) (path : List CNFLiteral)
    (input : r.registers.input = Augmentation.encode entries path) :
    (augmented r).registers.output = MatchingTable.encode (MatchingTable.writeAll entries (PathPairs.value path)) := by
  change (Augmentation.result r.registers.input).pairs.core.output = _
  rw [input, ← Augmentation.polynomial_output, Augmentation.polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.MatchingCall
