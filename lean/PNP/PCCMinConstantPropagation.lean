/-
Copyright (c) 2026 PNP Labs.

Computed constant propagation through every gate of a finite direct-wire NAND
program. Source aliases can name retained gates, primary inputs or constants.
Only actual constant NAND identities eliminate gates; all other gates remain.

This is the physical constant-congruence subcase of the manuscript's R1 work,
not complete normalization, a full-profile ledger, semantic minimization or
a polynomial PCCMin theorem. No-elimination is not semantic minimality.
-/

import PNP.PCCMinNormalizeOracleComposition
import PNP.NANDComposition

namespace PNP
namespace DirectWire

private def propagationExtend {width : Nat} {alpha : Type}
    (earlier : Fin width → alpha) (last : alpha) (index : Fin (width + 1)) : alpha :=
  if within : index.val < width then earlier ⟨index.val, within⟩ else last

private theorem propagationExtend_castSucc {width : Nat} {alpha : Type}
    (earlier : Fin width → alpha) (last : alpha) (index : Fin width) :
    propagationExtend earlier last index.castSucc = earlier index := by
  unfold propagationExtend
  split
  · rfl
  · rename_i outside
    exact False.elim (outside index.isLt)

private theorem propagationExtend_last {width : Nat} {alpha : Type}
    (earlier : Fin width → alpha) (last : alpha) :
    propagationExtend earlier last (Fin.last width) = last := by
  unfold propagationExtend
  split
  · rename_i impossible
    exact False.elim (Nat.lt_irrefl width impossible)
  · rfl

private theorem propagationIndex_cases {width : Nat} (index : Fin (width + 1)) :
    (∃ earlier : Fin width, index = earlier.castSucc) ∨ index = Fin.last width := by
  if within : index.val < width then
    exact Or.inl ⟨⟨index.val, within⟩, Fin.ext rfl⟩
  else
    apply Or.inr
    apply Fin.ext
    have upper := index.isLt
    change index.val = width
    omega

/-- Replace a gate reference with its computed source alias. -/
def Source.propagationRename {inputs fromGates toGates : Nat}
    (alias : Fin fromGates → Source inputs toGates) :
    Source inputs fromGates → Source inputs toGates
  | .input index => .input index
  | .constant value => .constant value
  | .gate index => alias index

private def propagationRenameGate {inputs fromGates toGates : Nat}
    (alias : Fin fromGates → Source inputs toGates) (gate : Gate inputs fromGates) :
    Gate inputs toGates :=
  ⟨gate.left.propagationRename alias, gate.right.propagationRename alias⟩

private theorem propagationRename_eval {inputs fromGates toGates : Nat}
    (alias : Fin fromGates → Source inputs toGates)
    (source : Source inputs fromGates) (input : Valuation inputs)
    (original : Valuation fromGates) (retained : Valuation toGates)
    (correct : ∀ index, (alias index).eval input retained = original index) :
    (source.propagationRename alias).eval input retained = source.eval input original := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate index => exact correct index

private theorem propagationRenameGate_eval {inputs fromGates toGates : Nat}
    (alias : Fin fromGates → Source inputs toGates) (gate : Gate inputs fromGates)
    (input : Valuation inputs) (original : Valuation fromGates)
    (retained : Valuation toGates)
    (correct : ∀ index, (alias index).eval input retained = original index) :
    (propagationRenameGate alias gate).eval input retained =
      gate.eval input original := by
  unfold propagationRenameGate Gate.eval
  rw [propagationRename_eval alias gate.left input original retained correct,
    propagationRename_eval alias gate.right input original retained correct]

private theorem propagationWeaken_eval {inputs gates : Nat}
    (program : Program inputs gates) (gate : Gate inputs gates)
    (source : Source inputs gates) (input : Valuation inputs) :
    (source.weakenGates 1).eval input ((program.snoc gate).eval input) =
      source.eval input (program.eval input) := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate index => exact Program.eval_snoc_castSucc program gate input index

/-- The exact literal-constant NAND identities; no valuation search is used. -/
def constantGateValue {inputs gates : Nat} (gate : Gate inputs gates) : Option Bool :=
  if gate.left = .constant false ∨ gate.right = .constant false then some true
  else if gate.left = .constant true ∧ gate.right = .constant true then some false
  else none

/-- A recognized literal constant is the NAND value for every valuation. -/
theorem constantGateValue_sound {inputs gates : Nat}
    (gate : Gate inputs gates) (value : Bool)
    (checked : constantGateValue gate = some value)
    (input : Valuation inputs) (retained : Valuation gates) :
    value = gate.eval input retained := by
  unfold constantGateValue at checked
  split at checked
  · rename_i falseSource
    cases checked
    rcases falseSource with left | right
    · unfold Gate.eval
      rw [left]
      cases gate.right.eval input retained <;> rfl
    · unfold Gate.eval
      rw [right]
      cases gate.left.eval input retained <;> rfl
  · split at checked
    · rename_i trueSources
      cases checked
      unfold Gate.eval
      rw [trueSources.1, trueSources.2]
      rfl
    · cases checked

/-- The computed retained program and source aliases, with constructed proofs. -/
structure NANDConstantPropagationCompilation {inputs gates : Nat}
    (original : Program inputs gates) where
  gateCount : Nat
  program : Program inputs gateCount
  alias : Fin gates → Source inputs gateCount
  eliminationCount : Nat
  alias_correct : ∀ input index,
    (alias index).eval input (program.eval input) = original.eval input index
  gate_accounting : gateCount + eliminationCount = gates

private def propagationAppend {inputs gates : Nat} {original : Program inputs gates}
    (compiled : NANDConstantPropagationCompilation original) (gate : Gate inputs gates) :
    NANDConstantPropagationCompilation (original.snoc gate) where
  gateCount := compiled.gateCount + 1
  program := compiled.program.snoc (propagationRenameGate compiled.alias gate)
  alias := propagationExtend (fun index => (compiled.alias index).weakenGates 1)
    (.gate (Fin.last compiled.gateCount))
  eliminationCount := compiled.eliminationCount
  alias_correct := by
    intro input index
    rcases propagationIndex_cases index with ⟨earlier, rfl⟩ | rfl
    · rw [propagationExtend_castSucc, propagationWeaken_eval,
        Program.eval_snoc_castSucc]
      exact compiled.alias_correct input earlier
    · rw [propagationExtend_last]
      change (compiled.program.snoc (propagationRenameGate compiled.alias gate)).eval
        input (Fin.last compiled.gateCount) = (original.snoc gate).eval input (Fin.last gates)
      rw [Program.eval_snoc_last, Program.eval_snoc_last]
      exact propagationRenameGate_eval compiled.alias gate input
        (original.eval input) (compiled.program.eval input)
        (compiled.alias_correct input)
  gate_accounting := by
    have previous := compiled.gate_accounting
    omega

private def propagationEliminate {inputs gates : Nat} {original : Program inputs gates}
    (compiled : NANDConstantPropagationCompilation original) (gate : Gate inputs gates)
    (value : Bool)
    (checked : constantGateValue (propagationRenameGate compiled.alias gate) = some value) :
    NANDConstantPropagationCompilation (original.snoc gate) where
  gateCount := compiled.gateCount
  program := compiled.program
  alias := propagationExtend compiled.alias (.constant value)
  eliminationCount := compiled.eliminationCount + 1
  alias_correct := by
    intro input index
    rcases propagationIndex_cases index with ⟨earlier, rfl⟩ | rfl
    · rw [propagationExtend_castSucc, Program.eval_snoc_castSucc]
      exact compiled.alias_correct input earlier
    · rw [propagationExtend_last, Program.eval_snoc_last]
      exact (constantGateValue_sound (propagationRenameGate compiled.alias gate)
        value checked input (compiled.program.eval input)).trans
        (propagationRenameGate_eval compiled.alias gate input
          (original.eval input) (compiled.program.eval input)
          (compiled.alias_correct input))
  gate_accounting := by
    have previous := compiled.gate_accounting
    omega

/-- Compute literal constant propagation through the entire arbitrary program.
Every successful recognition removes one gate; all other gates are translated
and retained. Constant aliases can trigger eliminations arbitrarily later. -/
def compileNANDConstantPropagation {inputs gates : Nat} (program : Program inputs gates) :
    NANDConstantPropagationCompilation program :=
  match program with
  | .empty =>
      { gateCount := 0
        program := .empty
        alias := Fin.elim0
        eliminationCount := 0
        alias_correct := fun _ index => Fin.elim0 index
        gate_accounting := rfl }
  | .snoc initial gate =>
      let compiled := compileNANDConstantPropagation initial
      match checked : constantGateValue (propagationRenameGate compiled.alias gate) with
      | none => propagationAppend compiled gate
      | some value => propagationEliminate compiled gate value checked

/-- Every original gate has a computed source with the same value at every input. -/
theorem compileNANDConstantPropagation_alias_semantics {inputs gates : Nat}
    (program : Program inputs gates) (input : Valuation inputs) (index : Fin gates) :
    ((compileNANDConstantPropagation program).alias index).eval input
        ((compileNANDConstantPropagation program).program.eval input) =
      program.eval input index :=
  (compileNANDConstantPropagation program).alias_correct input index

/-- Actual constant-elimination branches account for exactly the removed gates. -/
theorem compileNANDConstantPropagation_exact_accounting {inputs gates : Nat}
    (program : Program inputs gates) :
    (compileNANDConstantPropagation program).gateCount +
        (compileNANDConstantPropagation program).eliminationCount = gates :=
  (compileNANDConstantPropagation program).gate_accounting

/-- Apply the computed pass and rewrite every original ordered output source. -/
def constantPropagationImplementation {inputs outputs : Nat}
    (current : Implementation inputs outputs) : Implementation inputs outputs :=
  let compiled := compileNANDConstantPropagation current.candidate.program
  { gateCount := compiled.gateCount
    candidate := Candidate.ofDirectWireWord compiled.program
      ⟨fun output =>
        (current.candidate.directWireWord.source output).propagationRename compiled.alias⟩ }

/-- Complete ordered multi-output semantics, including non-gate output sources. -/
theorem constantPropagationImplementation_equivalent {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    Equivalent (constantPropagationImplementation current).candidate.program
      (constantPropagationImplementation current).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord := by
  intro input output
  simp only [constantPropagationImplementation, semantics, DirectWireWord.eval,
    Candidate.ofDirectWireWord_program, Candidate.ofDirectWireWord_pointwise]
  exact propagationRename_eval (compileNANDConstantPropagation current.candidate.program).alias
    (current.candidate.directWireWord.source output) input
    (current.candidate.program.eval input)
    ((compileNANDConstantPropagation current.candidate.program).program.eval input)
    ((compileNANDConstantPropagation current.candidate.program).alias_correct input)

/-- The computed physical pass cannot increase gate count. -/
theorem constantPropagationImplementation_gateCount_le {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (constantPropagationImplementation current).gateCount ≤ current.gateCount := by
  have accounting := compileNANDConstantPropagation_exact_accounting current.candidate.program
  change (compileNANDConstantPropagation current.candidate.program).gateCount ≤ _
  omega

/-- The reference minimum is invariant, without running its exhaustive search. -/
theorem constantPropagationImplementation_referenceMinimum {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    referenceMinimum (constantPropagationImplementation current) = referenceMinimum current :=
  referenceMinimum_invariant (constantPropagationImplementation current) current
    (constantPropagationImplementation_equivalent current)

/-- Each actual constant elimination retires exactly one unit of residual slack. -/
theorem constantPropagationImplementation_residualSlack {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    residualSlack current = residualSlack (constantPropagationImplementation current) +
      (compileNANDConstantPropagation current.candidate.program).eliminationCount := by
  have accounting := compileNANDConstantPropagation_exact_accounting current.candidate.program
  have bounded := referenceMinimum_le_target (constantPropagationImplementation current)
  have sameMinimum := constantPropagationImplementation_referenceMinimum current
  change (constantPropagationImplementation current).gateCount +
    (compileNANDConstantPropagation current.candidate.program).eliminationCount =
    current.gateCount at accounting
  unfold residualSlack
  rw [sameMinimum] at bounded ⊢
  omega

/-- Strict gain is equivalent to a real elimination, not a supplied certificate. -/
theorem constantPropagationImplementation_strictGain_iff {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    StrictEquivalentGain current (constantPropagationImplementation current) ↔
      0 < (compileNANDConstantPropagation current.candidate.program).eliminationCount := by
  have accounting := compileNANDConstantPropagation_exact_accounting current.candidate.program
  change (constantPropagationImplementation current).gateCount +
    (compileNANDConstantPropagation current.candidate.program).eliminationCount =
    current.gateCount at accounting
  constructor
  · intro gain
    have smaller := gain.smaller
    omega
  · intro positive
    exact ⟨by omega, constantPropagationImplementation_equivalent current⟩

/-- Computed elimination strictly descends the existing loop's residual measure. -/
theorem constantPropagationImplementation_strictResidualDescent {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (positive : 0 <
      (compileNANDConstantPropagation current.candidate.program).eliminationCount) :
    residualSlack (constantPropagationImplementation current) < residualSlack current :=
  ((constantPropagationImplementation_strictGain_iff current).mpr positive).strictResidualDescent

/-- A concrete constant-propagation stage for the total normalizer interface.
The no-elimination branch makes no claim that other gains have been excluded. -/
def nandConstantPropagationNormalizer : PCCMinTotalNormalizer where
  normalize := fun current =>
    if positive : 0 <
        (compileNANDConstantPropagation current.candidate.program).eliminationCount then
      .gain (constantPropagationImplementation current)
        ((constantPropagationImplementation_strictGain_iff current).mpr positive)
    else
      .normal
        { result := constantPropagationImplementation current
          equivalent := constantPropagationImplementation_equivalent current
          gateCount_le := constantPropagationImplementation_gateCount_le current }

/-- Both branches return the computed implementation. Actual eliminations are
surfaced as strict gains; otherwise physical gate count is unchanged. -/
theorem nandConstantPropagationNormalizer_checked {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    match nandConstantPropagationNormalizer.normalize current with
    | .gain next _ =>
        next = constantPropagationImplementation current ∧
          0 < (compileNANDConstantPropagation current.candidate.program).eliminationCount
    | .normal normalized =>
        normalized.result = constantPropagationImplementation current ∧
          (compileNANDConstantPropagation current.candidate.program).eliminationCount = 0 ∧
          normalized.result.gateCount = current.gateCount := by
  by_cases positive : 0 <
    (compileNANDConstantPropagation current.candidate.program).eliminationCount
  · simp only [nandConstantPropagationNormalizer, dif_pos positive]
    exact ⟨True.intro, positive⟩
  · simp only [nandConstantPropagationNormalizer, dif_neg positive]
    have accounting := compileNANDConstantPropagation_exact_accounting current.candidate.program
    change (constantPropagationImplementation current).gateCount +
      (compileNANDConstantPropagation current.candidate.program).eliminationCount =
      current.gateCount at accounting
    exact ⟨True.intro, by omega, by omega⟩

end DirectWire
end PNP
