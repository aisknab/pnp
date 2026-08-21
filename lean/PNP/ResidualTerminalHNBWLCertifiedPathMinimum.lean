/-
Copyright (c) 2026 PNP Labs.

Exact finite minimization for proof-bearing hereditary paths at the residual
terminal HN/BWL boundary.  A path carries one of the four manuscript shape
tags, a nonempty block decomposition covering its support, a frontier-faithful
realization, and full direct-wire semantic equivalence.  Its objective is the
lexicographic tuple (cost, residual rank, frontier deviation, direct-wire
code), with cost derived from the carried implementation.

The path family and its completeness remain explicit inputs.  This module
does not derive paths from a candidate, prove shape-grammar completeness, LN
confluence, ParseOrExit, independent leaf tightness, the full BWL theorem, a
polynomial path generator or runtime, HResolve, the H0--H4 sidecar,
unconditional ZeroSlack, PCCMin, SAT in P, or P = NP.
-/

import PNP.NANDMinimum

namespace PNP
namespace DirectWire

/-! ## Certified hereditary paths and the exact BWL objective -/

/-- The four hereditary shape tags named by the terminal HN grammar. -/
inductive TerminalHNShape where
  | pair
  | tripod
  | spine
  | nonflat
  deriving Repr, DecidableEq

/-- The four-coordinate BWL objective in manuscript priority order. -/
structure TerminalHNBWLObjective where
  cost : Nat
  residualRank : Nat
  frontierDeviation : Nat
  directWireCode : Nat
  deriving Repr, DecidableEq

/-- Lexicographic comparison for equal-length natural-number coordinate
    vectors.  The empty vectors are equal; unequal lengths are rejected. -/
def terminalNatVectorLexLE : List Nat → List Nat → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | left :: leftTail, right :: rightTail =>
      left < right ∨
        left = right ∧ terminalNatVectorLexLE leftTail rightTail

/-- The executable reflection of natural-vector lexicographic comparison. -/
def checkTerminalNatVectorLexLE : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | left :: leftTail, right :: rightTail =>
      if left < right then true
      else if right < left then false
      else checkTerminalNatVectorLexLE leftTail rightTail

/-- The executable vector checker accepts exactly the mathematical
    lexicographic relation. -/
theorem checkTerminalNatVectorLexLE_eq_true_iff
    (left right : List Nat) :
    checkTerminalNatVectorLexLE left right = true ↔
      terminalNatVectorLexLE left right := by
  induction left generalizing right with
  | nil =>
      cases right <;>
        simp [checkTerminalNatVectorLexLE, terminalNatVectorLexLE]
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil =>
          simp [checkTerminalNatVectorLexLE, terminalNatVectorLexLE]
      | cons rightHead rightTail =>
          by_cases leftBefore : leftHead < rightHead
          · simp [checkTerminalNatVectorLexLE, terminalNatVectorLexLE,
              leftBefore]
          · by_cases rightBefore : rightHead < leftHead
            · have different : leftHead ≠ rightHead := by
                intro equal
                cases equal
                exact (Nat.lt_irrefl leftHead) rightBefore
              simp [checkTerminalNatVectorLexLE, terminalNatVectorLexLE,
                leftBefore, rightBefore, different]
            · have equal : leftHead = rightHead :=
                Nat.le_antisymm (Nat.le_of_not_gt rightBefore)
                  (Nat.le_of_not_gt leftBefore)
              cases equal
              simp [checkTerminalNatVectorLexLE, terminalNatVectorLexLE,
                leftBefore, inductionHypothesis]

/-- Equal-length natural vectors are comparable in lexicographic order. -/
theorem terminalNatVectorLexLE_total_of_length_eq
    (left right : List Nat) (sameLength : left.length = right.length) :
    terminalNatVectorLexLE left right ∨
      terminalNatVectorLexLE right left := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil =>
          exact Or.inl trivial
      | cons rightHead rightTail =>
          cases sameLength
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil =>
          cases sameLength
      | cons rightHead rightTail =>
          have tailLength : leftTail.length = rightTail.length :=
            Nat.succ.inj sameLength
          change
            (leftHead < rightHead ∨
              leftHead = rightHead ∧
                terminalNatVectorLexLE leftTail rightTail) ∨
            (rightHead < leftHead ∨
              rightHead = leftHead ∧
                terminalNatVectorLexLE rightTail leftTail)
          by_cases leftBefore : leftHead < rightHead
          · exact Or.inl (Or.inl leftBefore)
          · by_cases rightBefore : rightHead < leftHead
            · exact Or.inr (Or.inl rightBefore)
            · have equal : leftHead = rightHead :=
                Nat.le_antisymm (Nat.le_of_not_gt rightBefore)
                  (Nat.le_of_not_gt leftBefore)
              cases equal
              rcases inductionHypothesis rightTail tailLength with
                tailLE | tailGE
              · exact Or.inl (Or.inr ⟨rfl, tailLE⟩)
              · exact Or.inr (Or.inr ⟨rfl, tailGE⟩)

/-- Natural-vector lexicographic comparison is reflexive. -/
theorem terminalNatVectorLexLE_refl (coordinates : List Nat) :
    terminalNatVectorLexLE coordinates coordinates := by
  induction coordinates with
  | nil =>
      trivial
  | cons head tail inductionHypothesis =>
      exact Or.inr ⟨rfl, inductionHypothesis⟩

/-- Natural-vector lexicographic comparison is transitive. -/
theorem terminalNatVectorLexLE_trans
    {left middle right : List Nat}
    (leftMiddle : terminalNatVectorLexLE left middle)
    (middleRight : terminalNatVectorLexLE middle right) :
    terminalNatVectorLexLE left right := by
  induction left generalizing middle right with
  | nil =>
      cases middle with
      | nil =>
          cases right with
          | nil => trivial
          | cons rightHead rightTail =>
              exact False.elim middleRight
      | cons middleHead middleTail =>
          exact False.elim leftMiddle
  | cons leftHead leftTail inductionHypothesis =>
      cases middle with
      | nil =>
          exact False.elim leftMiddle
      | cons middleHead middleTail =>
          cases right with
          | nil =>
              exact False.elim middleRight
          | cons rightHead rightTail =>
              rcases leftMiddle with leftBefore | ⟨leftEqual, tailLeftMiddle⟩
              · rcases middleRight with
                  middleBefore | ⟨middleEqual, tailMiddleRight⟩
                · exact Or.inl (Nat.lt_trans leftBefore middleBefore)
                · cases middleEqual
                  exact Or.inl leftBefore
              · cases leftEqual
                rcases middleRight with
                  middleBefore | ⟨middleEqual, tailMiddleRight⟩
                · exact Or.inl middleBefore
                · cases middleEqual
                  exact Or.inr
                    ⟨rfl, inductionHypothesis tailLeftMiddle tailMiddleRight⟩

/-- Convert an objective to its manuscript-ordered coordinate vector. -/
def TerminalHNBWLObjective.coordinates
    (objective : TerminalHNBWLObjective) : List Nat :=
  [objective.cost, objective.residualRank, objective.frontierDeviation,
    objective.directWireCode]

/-- Exact lexicographic preorder on the four BWL coordinates. -/
def TerminalHNBWLObjective.LexLE
    (left right : TerminalHNBWLObjective) : Prop :=
  terminalNatVectorLexLE left.coordinates right.coordinates

/-- Executable reflection of the exact four-coordinate BWL preorder. -/
def TerminalHNBWLObjective.checkLexLE
    (left right : TerminalHNBWLObjective) : Bool :=
  checkTerminalNatVectorLexLE left.coordinates right.coordinates

/-- The executable BWL checker accepts exactly the exact lexicographic
    relation. -/
theorem TerminalHNBWLObjective.checkLexLE_eq_true_iff
    (left right : TerminalHNBWLObjective) :
    left.checkLexLE right = true ↔ left.LexLE right := by
  exact checkTerminalNatVectorLexLE_eq_true_iff
    left.coordinates right.coordinates

/-- Every BWL objective is at most itself. -/
theorem TerminalHNBWLObjective.lexLE_refl
    (objective : TerminalHNBWLObjective) : objective.LexLE objective :=
  terminalNatVectorLexLE_refl objective.coordinates

/-- Any two BWL objectives are lexicographically comparable. -/
theorem TerminalHNBWLObjective.lexLE_total
    (left right : TerminalHNBWLObjective) :
    left.LexLE right ∨ right.LexLE left := by
  apply terminalNatVectorLexLE_total_of_length_eq
  rfl

/-- The BWL objective preorder is transitive. -/
theorem TerminalHNBWLObjective.lexLE_trans
    {left middle right : TerminalHNBWLObjective}
    (leftMiddle : left.LexLE middle) (middleRight : middle.LexLE right) :
    left.LexLE right :=
  terminalNatVectorLexLE_trans leftMiddle middleRight

/-- A supplied hereditary path with proof-bearing structural, semantic, and
    frontier evidence.  The objective cost is deliberately not a field. -/
structure TerminalHNBWLCertifiedPath
    {inputs outputs : Nat} (current : Implementation inputs outputs)
    (Atom Frontier : Type) (expectedFrontier : List Frontier) where
  shape : TerminalHNShape
  support : List Atom
  blocks : List (List Atom)
  blocksNonempty : blocks ≠ []
  blocksCover : blocks.flatten = support
  frontier : List Frontier
  implementation : Implementation inputs outputs
  semanticFaithful : Equivalent
    implementation.candidate.program
    implementation.candidate.directWireWord
    current.candidate.program current.candidate.directWireWord
  frontierFaithful : frontier = expectedFrontier
  residualRank : Nat
  frontierDeviation : Nat
  directWireCode : Nat

/-- The exact BWL objective of a certified path.  Cost is mechanically bound
    to the realized implementation's gate count. -/
def TerminalHNBWLCertifiedPath.objective
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier : Type} {expectedFrontier : List Frontier}
    (path : TerminalHNBWLCertifiedPath current Atom Frontier
      expectedFrontier) : TerminalHNBWLObjective :=
  { cost := path.implementation.gateCount
    residualRank := path.residualRank
    frontierDeviation := path.frontierDeviation
    directWireCode := path.directWireCode }

/-! ## Deterministic finite minimum -/

/-- Choose the left path on an objective tie and otherwise choose the exact
    lexicographic minimum. -/
def terminalHNBWLChoose
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier : Type} {expectedFrontier : List Frontier}
    (left right : TerminalHNBWLCertifiedPath current Atom Frontier
      expectedFrontier) :
    TerminalHNBWLCertifiedPath current Atom Frontier expectedFrontier :=
  if left.objective.checkLexLE right.objective = true then left else right

/-- The pairwise chooser always returns one of its supplied paths. -/
theorem terminalHNBWLChoose_eq_left_or_right
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier : Type} {expectedFrontier : List Frontier}
    (left right : TerminalHNBWLCertifiedPath current Atom Frontier
      expectedFrontier) :
    terminalHNBWLChoose left right = left ∨
      terminalHNBWLChoose left right = right := by
  unfold terminalHNBWLChoose
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The chosen objective is no greater than the left objective. -/
theorem terminalHNBWLChoose_lexLE_left
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier : Type} {expectedFrontier : List Frontier}
    (left right : TerminalHNBWLCertifiedPath current Atom Frontier
      expectedFrontier) :
    (terminalHNBWLChoose left right).objective.LexLE left.objective := by
  unfold terminalHNBWLChoose
  split
  · exact left.objective.lexLE_refl
  · rename_i rejected
    have notLeft : ¬left.objective.LexLE right.objective := by
      intro leftLE
      exact rejected
        ((left.objective.checkLexLE_eq_true_iff right.objective).mpr leftLE)
    rcases left.objective.lexLE_total right.objective with leftLE | rightLE
    · exact False.elim (notLeft leftLE)
    · exact rightLE

/-- The chosen objective is no greater than the right objective. -/
theorem terminalHNBWLChoose_lexLE_right
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier : Type} {expectedFrontier : List Frontier}
    (left right : TerminalHNBWLCertifiedPath current Atom Frontier
      expectedFrontier) :
    (terminalHNBWLChoose left right).objective.LexLE right.objective := by
  unfold terminalHNBWLChoose
  split
  · rename_i accepted
    exact (left.objective.checkLexLE_eq_true_iff right.objective).mp accepted
  · exact right.objective.lexLE_refl

/-- Recursively compute the deterministic BWL minimum of a supplied list. -/
def terminalHNBWLMinimum?
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier : Type} {expectedFrontier : List Frontier} :
    List (TerminalHNBWLCertifiedPath current Atom Frontier expectedFrontier) →
      Option (TerminalHNBWLCertifiedPath current Atom Frontier
        expectedFrontier)
  | [] => none
  | head :: tail =>
      match terminalHNBWLMinimum? tail with
      | none => some head
      | some tailMinimum => some (terminalHNBWLChoose head tailMinimum)

/-- The minimum computation returns `none` exactly for the empty family. -/
theorem terminalHNBWLMinimum?_eq_none_iff
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier : Type} {expectedFrontier : List Frontier}
    (paths : List (TerminalHNBWLCertifiedPath current Atom Frontier
      expectedFrontier)) :
    terminalHNBWLMinimum? paths = none ↔ paths = [] := by
  induction paths with
  | nil =>
      simp [terminalHNBWLMinimum?]
  | cons head tail inductionHypothesis =>
      simp only [terminalHNBWLMinimum?]
      cases tailResult : terminalHNBWLMinimum? tail with
      | none =>
          simp
      | some tailMinimum =>
          simp

/-- A successful minimum computation returns a listed path and an objective
    no greater than every path in the supplied family. -/
theorem terminalHNBWLMinimum?_sound
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier : Type} {expectedFrontier : List Frontier}
    {paths : List (TerminalHNBWLCertifiedPath current Atom Frontier
      expectedFrontier)}
    {chosen : TerminalHNBWLCertifiedPath current Atom Frontier
      expectedFrontier}
    (chosenAt : terminalHNBWLMinimum? paths = some chosen) :
    chosen ∈ paths ∧
      ∀ alternative, alternative ∈ paths →
        chosen.objective.LexLE alternative.objective := by
  induction paths generalizing chosen with
  | nil =>
      cases chosenAt
  | cons head tail inductionHypothesis =>
      simp only [terminalHNBWLMinimum?] at chosenAt
      cases tailResult : terminalHNBWLMinimum? tail with
      | none =>
          rw [tailResult] at chosenAt
          cases chosenAt
          have tailEmpty : tail = [] :=
            (terminalHNBWLMinimum?_eq_none_iff tail).mp tailResult
          cases tailEmpty
          constructor
          · exact List.Mem.head []
          · intro alternative member
            rcases List.mem_cons.mp member with atHead | impossible
            · exact atHead ▸
                TerminalHNBWLObjective.lexLE_refl head.objective
            · exact False.elim (List.not_mem_nil impossible)
      | some tailMinimum =>
          rw [tailResult] at chosenAt
          cases chosenAt
          have tailSound := inductionHypothesis tailResult
          constructor
          · rcases terminalHNBWLChoose_eq_left_or_right head tailMinimum with
              selectedHead | selectedTail
            · rw [selectedHead]
              exact List.Mem.head tail
            · rw [selectedTail]
              exact List.Mem.tail head tailSound.1
          · intro alternative member
            cases member with
            | head =>
                exact terminalHNBWLChoose_lexLE_left head tailMinimum
            | tail _ tailMember =>
                exact TerminalHNBWLObjective.lexLE_trans
                  (terminalHNBWLChoose_lexLE_right head tailMinimum)
                  (tailSound.2 alternative tailMember)

/-- Every nonempty supplied family has a computed minimum. -/
theorem terminalHNBWLMinimum?_exists_of_ne_nil
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier : Type} {expectedFrontier : List Frontier}
    (paths : List (TerminalHNBWLCertifiedPath current Atom Frontier
      expectedFrontier))
    (nonempty : paths ≠ []) :
    ∃ chosen, terminalHNBWLMinimum? paths = some chosen := by
  cases minimumAt : terminalHNBWLMinimum? paths with
  | none =>
      exact False.elim
        (nonempty ((terminalHNBWLMinimum?_eq_none_iff paths).mp minimumAt))
  | some chosen =>
      exact ⟨chosen, rfl⟩

/-- Explicit completeness of a supplied finite path family relative to a
    caller-supplied governed predicate. -/
def TerminalHNBWLFamilyComplete
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier : Type} {expectedFrontier : List Frontier}
    (paths : List (TerminalHNBWLCertifiedPath current Atom Frontier
      expectedFrontier))
    (governed : TerminalHNBWLCertifiedPath current Atom Frontier
      expectedFrontier → Prop) : Prop :=
  ∀ path, governed path → path ∈ paths

/-- A nonempty complete supplied family yields a listed certified minimum,
    with a lower bound for every governed alternative and all carried
    structural, semantic, frontier, and shape evidence preserved. -/
theorem terminal_hn_bwl_certified_path_minimum_complete
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    {Atom Frontier : Type} {expectedFrontier : List Frontier}
    (paths : List (TerminalHNBWLCertifiedPath current Atom Frontier
      expectedFrontier))
    (governed : TerminalHNBWLCertifiedPath current Atom Frontier
      expectedFrontier → Prop)
    (nonempty : paths ≠ [])
    (complete : TerminalHNBWLFamilyComplete paths governed) :
    ∃ chosen,
      terminalHNBWLMinimum? paths = some chosen ∧
      chosen ∈ paths ∧
      (∀ alternative, governed alternative →
        chosen.objective.LexLE alternative.objective) ∧
      Equivalent chosen.implementation.candidate.program
        chosen.implementation.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      chosen.frontier = expectedFrontier ∧
      chosen.blocks ≠ [] ∧
      chosen.blocks.flatten = chosen.support ∧
      (chosen.shape = .pair ∨ chosen.shape = .tripod ∨
        chosen.shape = .spine ∨ chosen.shape = .nonflat) := by
  obtain ⟨chosen, chosenAt⟩ :=
    terminalHNBWLMinimum?_exists_of_ne_nil paths nonempty
  have sound := terminalHNBWLMinimum?_sound chosenAt
  refine ⟨chosen, chosenAt, sound.1, ?_, chosen.semanticFaithful,
    chosen.frontierFaithful, chosen.blocksNonempty, chosen.blocksCover, ?_⟩
  · intro alternative governedAlternative
    exact sound.2 alternative (complete alternative governedAlternative)
  · cases chosen.shape <;> simp

end DirectWire
end PNP
