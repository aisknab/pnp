/-
Copyright (c) 2026 PNP Labs.

Complete internal exploration initialization: derive counts, construct the
countdown and ordered unseen vertices, and start with an empty trace.
Every raw input satisfies the structural loop invariant and a uniform
encoded-input-size polynomial initialization bound.
-/

import PNP.Concrete.NormalizerExplorationVertices

namespace PNP.Concrete.NormalizerBlocks.Exploration
open BitRegister ExplorationData

def beforeVertices : Block 28 := .seq loader buildBudget
def beforeVerticesResult (input : BitString) : State := budgeted (loaded input)
def beforeVerticesFuel (input : BitString) : Nat := loaderFuel input + budgetFuel (loaded input)
theorem beforeVertices_exec (input : BitString) :
    Exec beforeVertices (initial input).store (beforeVerticesFuel input) (beforeVerticesResult input).store :=
  Exec.seq (loader_exec input) (buildBudget_exec (loaded input))

def initializeBlock : Block 28 := .seq beforeVertices buildVertices
def initialized (input : BitString) : State := verticesBuilt (beforeVerticesResult input)
def initializeFuel (input : BitString) : Nat := beforeVerticesFuel input + verticesFuel (beforeVerticesResult input)
theorem initialize_exec (input : BitString) :
    Exec initializeBlock (initial input).store (initializeFuel input) (initialized input).store :=
  Exec.seq (beforeVertices_exec input) (buildVertices_exec (beforeVerticesResult input))

def sourceVertices (input : BitString) : List CNFLiteral :=
  SearchVertices.vertices (sourceCount input) (sourceWidth input).length
def sourceLimit (input : BitString) : Nat := sourceCount input + (sourceWidth input).length

theorem initialized_fields (input : BitString) :
    (initialized input).core.parent.graph.core.formula = sourceFormula input ∧
      (initialized input).core.parent.graph.core.matching = sourceMatching input ∧
        (initialized input).core.trace = [] ∧
          (initialized input).core.pending = SearchVertices.encodeVertices (sourceVertices input) ∧
            (initialized input).remaining = List.replicate (sourceLimit input) true := by
  have data := loaded_fields input
  have budget := budgeted_fields (loaded input)
  have vertices := verticesBuilt_frame (beforeVerticesResult input)
  have pending := verticesBuilt_pending (beforeVerticesResult input)
  have width : (beforeVerticesResult input).core.parent.targetIndex = sourceWidth input := budget.2.1.trans data.1
  have clauses : (beforeVerticesResult input).core.parent.currentIndex = List.replicate (sourceCount input) true :=
    budget.2.2.1.trans data.2.1
  rw [width, clauses, List.length_replicate] at pending
  have remaining := vertices.2.2.2.trans budget.1
  rw [data.1, data.2.1, List.length_replicate] at remaining
  exact ⟨vertices.1.trans (budget.2.2.2.1.trans data.2.2.1),
    vertices.2.1.trans (budget.2.2.2.2.1.trans data.2.2.2.1),
    vertices.2.2.1.trans (budget.2.2.2.2.2.trans data.2.2.2.2.1), pending, remaining⟩

theorem sourceLimit_bound (input : BitString) : sourceLimit input ≤ 6 * input.length + 6 := by
  have sizes := source_sizes input
  unfold sourceLimit
  omega

theorem range_vertices_bound (clauses variables : Nat) :
    VerticesBound (clauses + variables) (SearchVertices.vertices clauses variables) := by
  intro vertex member
  rw [SearchVertices.vertices, List.mem_append] at member
  cases member with
  | inl left =>
      rw [SearchVertices.rangeData_finRange] at left
      obtain ⟨index, _, same⟩ := List.mem_map.mp left
      rw [← same]
      have size := index.isLt
      change 0 + index.val ≤ clauses + variables
      omega
  | inr right =>
      rw [SearchVertices.rangeData_finRange] at right
      obtain ⟨index, _, same⟩ := List.mem_map.mp right
      rw [← same]
      have size := index.isLt
      change 0 + index.val ≤ clauses + variables
      omega

theorem initialized_within (input : BitString) :
    Within (6 * input.length + 6) (sourceVertices input) [] (initialized input) := by
  have fields := initialized_fields input
  have limit := sourceLimit_bound input
  have indices := range_vertices_bound (sourceCount input) (sourceWidth input).length
  refine ⟨fields.2.2.2.1, fields.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro vertex member
    exact Nat.le_trans (indices vertex member) limit
  · intro entry member
    cases member
  · change (SearchVertices.vertices (sourceCount input) (sourceWidth input).length).length ≤ _
    rw [SearchVertices.vertices_length]
    exact limit
  · rw [fields.2.2.2.2, List.length_replicate]
    simpa only [List.length_nil, Nat.zero_add] using limit

theorem initial_bounded (input : BitString) : (initial input).store.Bounded input.length := by
  have checked := BitRegister.initial_bounded ((Block.skip : Block 28).program 0 8) input
  exact checked

theorem beforeVerticesFuel_bound (input : BitString) : beforeVerticesFuel input ≤ 118 * input.length + 224 := by
  have load := loaderFuel_bound input
  have sizes := source_sizes input
  have fields := loaded_fields input
  unfold beforeVerticesFuel
  rw [budgetFuel_eq, fields.1, fields.2.1, List.length_replicate]
  omega

def rangesPolynomial : NatPolynomial :=
  .add (.mul (.constant 2) (.mul (.linear 24 37) (.linear 6 6))) (.constant 7)
theorem rangesPolynomial_eval (size : Nat) :
    rangesPolynomial.eval size = 2 * ((4 * (6 * size + 6) + 13) * (6 * size + 6)) + 7 := by
  change 2 * ((24 * size + 37) * (6 * size + 6)) + 7 = _
  have same : 24 * size + 37 = 4 * (6 * size + 6) + 13 := by omega
  rw [same]

theorem initial_ranges_bound (input : BitString) :
    rangesBound (beforeVerticesResult input).core.parent.currentIndex.length
      (beforeVerticesResult input).core.parent.targetIndex.length ≤ rangesPolynomial.eval input.length := by
  have data := loaded_fields input
  have frame := budgeted_fields (loaded input)
  have sizes := source_sizes input
  have clauses : (beforeVerticesResult input).core.parent.currentIndex.length ≤ 6 * input.length + 6 := by
    rw [show (beforeVerticesResult input).core.parent.currentIndex = (loaded input).core.parent.currentIndex from frame.2.2.1,
      data.2.1, List.length_replicate]
    omega
  have variables : (beforeVerticesResult input).core.parent.targetIndex.length ≤ 6 * input.length + 6 := by
    rw [show (beforeVerticesResult input).core.parent.targetIndex = (loaded input).core.parent.targetIndex from frame.2.1, data.1]
    omega
  have left := Nat.mul_le_mul (show 4 * (beforeVerticesResult input).core.parent.currentIndex.length + 13 ≤
    4 * (6 * input.length + 6) + 13 by omega) clauses
  have right := Nat.mul_le_mul (show 4 * (beforeVerticesResult input).core.parent.targetIndex.length + 13 ≤
    4 * (6 * input.length + 6) + 13 by omega) variables
  unfold rangesBound
  rw [rangesPolynomial_eval]
  omega

def initializePolynomial : NatPolynomial :=
  .add (.linear 600 1200) (.mul (.constant 5) rangesPolynomial)
theorem initializePolynomial_eval (size : Nat) :
    initializePolynomial.eval size = 600 * size + 1200 + 5 * rangesPolynomial.eval size := rfl

theorem initializeFuel_bound (input : BitString) :
    initializeFuel input ≤ initializePolynomial.eval input.length := by
  have prior := beforeVerticesFuel_bound input
  have bounded := (beforeVertices_exec input).bounded input.length (initial_bounded input)
  have vertices := verticesFuel_bound (beforeVerticesResult input) (input.length + beforeVerticesFuel input) bounded
  have ranges := initial_ranges_bound input
  rw [initializePolynomial_eval]
  unfold initializeFuel
  omega

end PNP.Concrete.NormalizerBlocks.Exploration
