/-
Copyright (c) 2026 PNP Labs.

A computed structural-sharing pass for arbitrary finite direct-wire NAND
programs. Each gate is either appended with translated sources or reuses an
actual earlier gate with the same NAND inputs, allowing commuted inputs.
No semantic enumeration, supplied optimizer or correctness certificate is used.

This is the physical R1/R4 sharing subcase and a concrete input to the existing
normalization/oracle control flow. It is not complete manuscript normalization,
a full-profile rewrite ledger, a semantic minimum or a polynomial PCCMin claim.
-/

import PNP.PCCMinNormalizeOracleComposition
import PNP.ResidualTerminalPhysicalSupportCompletion

namespace PNP
namespace DirectWire

private def sharingExtend {width : Nat} {alpha : Type}
    (earlier : Fin width -> alpha) (last : alpha) (index : Fin (width + 1)) : alpha :=
  if within : index.val < width then earlier ⟨index.val, within⟩ else last

private theorem sharingExtend_castSucc {width : Nat} {alpha : Type}
    (earlier : Fin width -> alpha) (last : alpha) (index : Fin width) :
    sharingExtend earlier last index.castSucc = earlier index := by
  unfold sharingExtend
  split
  · rfl
  · rename_i outside
    exact False.elim (outside index.isLt)

private theorem sharingExtend_last {width : Nat} {alpha : Type}
    (earlier : Fin width -> alpha) (last : alpha) :
    sharingExtend earlier last (Fin.last width) = last := by
  unfold sharingExtend
  split
  · rename_i impossible
    exact False.elim (Nat.lt_irrefl width impossible)
  · rfl

private theorem sharingIndex_cases {width : Nat} (index : Fin (width + 1)) :
    (∃ earlier : Fin width, index = earlier.castSucc) ∨ index = Fin.last width := by
  if within : index.val < width then
    exact Or.inl ⟨⟨index.val, within⟩, Fin.ext rfl⟩
  else
    apply Or.inr
    apply Fin.ext
    have upper := index.isLt
    change index.val = width
    omega

/-- Translate gate references through computed aliases; inputs and constants
are unchanged. The alias need not be injective. -/
def Source.sharingRename {inputs fromGates toGates : Nat}
    (alias : Fin fromGates -> Fin toGates) :
    Source inputs fromGates -> Source inputs toGates
  | .input index => .input index
  | .constant value => .constant value
  | .gate index => .gate (alias index)

private def sharingRenameGate {inputs fromGates toGates : Nat}
    (alias : Fin fromGates -> Fin toGates) (gate : Gate inputs fromGates) :
    Gate inputs toGates :=
  ⟨gate.left.sharingRename alias, gate.right.sharingRename alias⟩

private theorem sharingRename_eval {inputs fromGates toGates : Nat}
    (alias : Fin fromGates -> Fin toGates)
    (source : Source inputs fromGates) (input : Valuation inputs)
    (original : Valuation fromGates) (retained : Valuation toGates)
    (correct : ∀ index, retained (alias index) = original index) :
    (source.sharingRename alias).eval input retained = source.eval input original := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate index => exact correct index

private theorem sharingRenameGate_eval {inputs fromGates toGates : Nat}
    (alias : Fin fromGates -> Fin toGates) (gate : Gate inputs fromGates)
    (input : Valuation inputs) (original : Valuation fromGates)
    (retained : Valuation toGates)
    (correct : ∀ index, retained (alias index) = original index) :
    (sharingRenameGate alias gate).eval input retained =
      gate.eval input original := by
  unfold sharingRenameGate Gate.eval
  rw [sharingRename_eval alias gate.left input original retained correct,
    sharingRename_eval alias gate.right input original retained correct]

private theorem sharingWeaken_eval {inputs gates : Nat}
    (program : Program inputs gates) (gate : Gate inputs gates)
    (source : Source inputs gates) (input : Valuation inputs) :
    (source.weakenGates 1).eval input ((program.snoc gate).eval input) =
      source.eval input (program.eval input) := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate index => exact Program.eval_snoc_castSucc program gate input index

private theorem sharingGateSources_eval {inputs gates : Nat}
    (program : Program inputs gates) (input : Valuation inputs) (index : Fin gates) :
    boolNand
        ((program.terminalGateSources index).1.eval input (program.eval input))
        ((program.terminalGateSources index).2.eval input (program.eval input)) =
      program.eval input index := by
  induction program with
  | empty => exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      rcases sharingIndex_cases index with ⟨earlier, rfl⟩ | rfl
      · have sources :
            (initial.snoc gate).terminalGateSources earlier.castSucc =
              ((initial.terminalGateSources earlier).1.weakenGates 1,
                (initial.terminalGateSources earlier).2.weakenGates 1) := by
          change (if within : earlier.castSucc.val < gates then
            let pair := initial.terminalGateSources ⟨earlier.castSucc.val, within⟩
            (pair.1.weakenGates 1, pair.2.weakenGates 1)
            else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
          split
          · rfl
          · rename_i outside
            exact False.elim (outside earlier.isLt)
        rw [sources, sharingWeaken_eval, sharingWeaken_eval, ih,
          Program.eval_snoc_castSucc]
      · have sources :
            (initial.snoc gate).terminalGateSources (Fin.last gates) =
              (gate.left.weakenGates 1, gate.right.weakenGates 1) := by
          change (if within : (Fin.last gates).val < gates then
            let pair := initial.terminalGateSources ⟨(Fin.last gates).val, within⟩
            (pair.1.weakenGates 1, pair.2.weakenGates 1)
            else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
          split
          · rename_i impossible
            exact False.elim (Nat.lt_irrefl gates impossible)
          · rfl
        rw [sources, sharingWeaken_eval, sharingWeaken_eval, Program.eval_snoc_last]
        rfl

private def sharingGateMatches {inputs gates : Nat}
    (program : Program inputs gates) (gate : Gate inputs gates) (index : Fin gates) : Bool :=
  let pair := program.terminalGateSources index
  decide ((pair.1 = gate.left ∧ pair.2 = gate.right) ∨
    (pair.1 = gate.right ∧ pair.2 = gate.left))

private def sharingFindGateIn {inputs gates : Nat}
    (program : Program inputs gates) (gate : Gate inputs gates) :
    List (Fin gates) -> Option (Fin gates)
  | [] => none
  | index :: remaining =>
      if sharingGateMatches program gate index then some index
      else sharingFindGateIn program gate remaining

/-- Search only actual retained gates, using structural equality of the two
translated sources, with NAND input commutation allowed. -/
def sharingFindGate {inputs gates : Nat}
    (program : Program inputs gates) (gate : Gate inputs gates) : Option (Fin gates) :=
  sharingFindGateIn program gate (allFin gates)

private theorem sharingFindGateIn_sound {inputs gates : Nat}
    (program : Program inputs gates) (gate : Gate inputs gates)
    (indices : List (Fin gates)) (found : Fin gates)
    (checked : sharingFindGateIn program gate indices = some found) :
    sharingGateMatches program gate found = true := by
  induction indices with
  | nil => cases checked
  | cons index remaining ih =>
      unfold sharingFindGateIn at checked
      split at checked
      · rename_i matched
        cases checked
        exact matched
      · exact ih checked

private theorem sharingFindGate_eval {inputs gates : Nat}
    (program : Program inputs gates) (gate : Gate inputs gates)
    (found : Fin gates) (checked : sharingFindGate program gate = some found)
    (input : Valuation inputs) :
    program.eval input found = gate.eval input (program.eval input) := by
  have matched := sharingFindGateIn_sound program gate (allFin gates) found checked
  have pairs := of_decide_eq_true matched
  rw [← sharingGateSources_eval program input found]
  rcases pairs with ⟨left, right⟩ | ⟨left, right⟩
  · rw [left, right]
    rfl
  · rw [left, right]
    unfold Gate.eval boolNand
    cases gate.left.eval input (program.eval input) <;>
      cases gate.right.eval input (program.eval input) <;> rfl

/-- The concrete pass result, including a computed alias for every original gate.
The proof fields are constructed by the pass, never supplied by its caller. -/
structure NANDSharingCompilation {inputs gates : Nat}
    (original : Program inputs gates) where
  gateCount : Nat
  program : Program inputs gateCount
  alias : Fin gates -> Fin gateCount
  foldCount : Nat
  alias_correct : ∀ input index,
    program.eval input (alias index) = original.eval input index
  gate_accounting : gateCount + foldCount = gates

private def sharingAppend {inputs gates : Nat} {original : Program inputs gates}
    (compiled : NANDSharingCompilation original) (gate : Gate inputs gates) :
    NANDSharingCompilation (original.snoc gate) where
  gateCount := compiled.gateCount + 1
  program := compiled.program.snoc (sharingRenameGate compiled.alias gate)
  alias := sharingExtend (fun index => (compiled.alias index).castSucc)
    (Fin.last compiled.gateCount)
  foldCount := compiled.foldCount
  alias_correct := by
    intro input index
    rcases sharingIndex_cases index with ⟨earlier, rfl⟩ | rfl
    · rw [sharingExtend_castSucc, Program.eval_snoc_castSucc,
        Program.eval_snoc_castSucc]
      exact compiled.alias_correct input earlier
    · rw [sharingExtend_last, Program.eval_snoc_last, Program.eval_snoc_last]
      exact sharingRenameGate_eval compiled.alias gate input
        (original.eval input) (compiled.program.eval input)
        (compiled.alias_correct input)
  gate_accounting := by
    have previous := compiled.gate_accounting
    omega

private def sharingReuse {inputs gates : Nat} {original : Program inputs gates}
    (compiled : NANDSharingCompilation original) (gate : Gate inputs gates)
    (found : Fin compiled.gateCount)
    (checked : sharingFindGate compiled.program
      (sharingRenameGate compiled.alias gate) = some found) :
    NANDSharingCompilation (original.snoc gate) where
  gateCount := compiled.gateCount
  program := compiled.program
  alias := sharingExtend compiled.alias found
  foldCount := compiled.foldCount + 1
  alias_correct := by
    intro input index
    rcases sharingIndex_cases index with ⟨earlier, rfl⟩ | rfl
    · rw [sharingExtend_castSucc, Program.eval_snoc_castSucc]
      exact compiled.alias_correct input earlier
    · rw [sharingExtend_last, Program.eval_snoc_last]
      exact (sharingFindGate_eval compiled.program
        (sharingRenameGate compiled.alias gate) found checked input).trans
        (sharingRenameGate_eval compiled.alias gate input
          (original.eval input) (compiled.program.eval input)
          (compiled.alias_correct input))
  gate_accounting := by
    have previous := compiled.gate_accounting
    omega

/-- Compute sharing for the complete arbitrary program. Every successful lookup
folds one gate; every unsuccessful lookup appends exactly one translated gate. -/
def compileNANDSharing {inputs gates : Nat} (program : Program inputs gates) :
    NANDSharingCompilation program :=
  match program with
  | .empty =>
      { gateCount := 0
        program := .empty
        alias := Fin.elim0
        foldCount := 0
        alias_correct := fun _ index => Fin.elim0 index
        gate_accounting := rfl }
  | .snoc initial gate =>
      let compiled := compileNANDSharing initial
      match checked : sharingFindGate compiled.program
          (sharingRenameGate compiled.alias gate) with
      | none => sharingAppend compiled gate
      | some found => sharingReuse compiled gate found checked

/-- Every computed alias preserves its original gate value for every input. -/
theorem compileNANDSharing_alias_semantics {inputs gates : Nat}
    (program : Program inputs gates) (input : Valuation inputs) (index : Fin gates) :
    (compileNANDSharing program).program.eval input
        ((compileNANDSharing program).alias index) =
      program.eval input index :=
  (compileNANDSharing program).alias_correct input index

/-- The retained gates and actual successful reuse branches exactly partition
the original gate count. -/
theorem compileNANDSharing_exact_accounting {inputs gates : Nat}
    (program : Program inputs gates) :
    (compileNANDSharing program).gateCount +
        (compileNANDSharing program).foldCount = gates :=
  (compileNANDSharing program).gate_accounting

/-- Apply the pass to every gate and translate every ordered output wire. -/
def sharingImplementation {inputs outputs : Nat}
    (current : Implementation inputs outputs) : Implementation inputs outputs :=
  let compiled := compileNANDSharing current.candidate.program
  { gateCount := compiled.gateCount
    candidate := Candidate.ofDirectWireWord compiled.program
      ⟨fun output =>
        (current.candidate.directWireWord.source output).sharingRename
          compiled.alias⟩ }

/-- Complete multi-output semantics is preserved, including constants, primary
inputs and duplicated output wires. -/
theorem sharingImplementation_equivalent {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    Equivalent (sharingImplementation current).candidate.program
      (sharingImplementation current).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord := by
  intro input output
  simp only [sharingImplementation, semantics, DirectWireWord.eval,
    Candidate.ofDirectWireWord_program, Candidate.ofDirectWireWord_pointwise]
  exact sharingRename_eval (compileNANDSharing current.candidate.program).alias
    (current.candidate.directWireWord.source output) input
    (current.candidate.program.eval input)
    ((compileNANDSharing current.candidate.program).program.eval input)
    ((compileNANDSharing current.candidate.program).alias_correct input)

/-- Structural sharing cannot increase the actual physical gate count. -/
theorem sharingImplementation_gateCount_le {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (sharingImplementation current).gateCount ≤ current.gateCount := by
  have accounting := compileNANDSharing_exact_accounting current.candidate.program
  change (compileNANDSharing current.candidate.program).gateCount ≤ _
  omega

/-- Sharing preserves the semantic reference minimum without executing the
exhaustive reference search. -/
theorem sharingImplementation_referenceMinimum {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    referenceMinimum (sharingImplementation current) = referenceMinimum current :=
  referenceMinimum_invariant (sharingImplementation current) current
    (sharingImplementation_equivalent current)

/-- Every successful structural reuse retires exactly one unit of physical
residual slack. The semantic minimum is unchanged. -/
theorem sharingImplementation_residualSlack {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    residualSlack current = residualSlack (sharingImplementation current) +
      (compileNANDSharing current.candidate.program).foldCount := by
  have accounting := compileNANDSharing_exact_accounting current.candidate.program
  have bounded := referenceMinimum_le_target (sharingImplementation current)
  have sameMinimum := sharingImplementation_referenceMinimum current
  change (sharingImplementation current).gateCount +
    (compileNANDSharing current.candidate.program).foldCount =
    current.gateCount at accounting
  unfold residualSlack
  rw [sameMinimum] at bounded ⊢
  omega

/-- The pass has a strict gain exactly when its actual execution reused a gate.
No supplied gain certificate is needed. -/
theorem sharingImplementation_strictGain_iff {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    StrictEquivalentGain current (sharingImplementation current) ↔
      0 < (compileNANDSharing current.candidate.program).foldCount := by
  have accounting := compileNANDSharing_exact_accounting current.candidate.program
  change (sharingImplementation current).gateCount +
    (compileNANDSharing current.candidate.program).foldCount =
    current.gateCount at accounting
  constructor
  · intro gain
    have smaller := gain.smaller
    omega
  · intro positive
    exact ⟨by omega, sharingImplementation_equivalent current⟩

/-- A computed fold strictly decreases residual slack at the existing loop's
well-founded measure. -/
theorem sharingImplementation_strictResidualDescent {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (positive : 0 < (compileNANDSharing current.candidate.program).foldCount) :
    residualSlack (sharingImplementation current) < residualSlack current :=
  ((sharingImplementation_strictGain_iff current).mpr positive).strictResidualDescent

/-- An actual all-input structural-sharing stage for the existing PCCMin
normalizer interface. A no-fold branch is not a claim of complete manuscript
normal form, absence of other gains or semantic minimality. -/
def nandSharingNormalizer : PCCMinTotalNormalizer where
  normalize := fun current =>
    if positive : 0 < (compileNANDSharing current.candidate.program).foldCount then
      .gain (sharingImplementation current)
        ((sharingImplementation_strictGain_iff current).mpr positive)
    else
      .normal
        { result := sharingImplementation current
          equivalent := sharingImplementation_equivalent current
          gateCount_le := sharingImplementation_gateCount_le current }

/-- The concrete interface returns its computed result in both branches, and
surfaces every computed fold as a checked strict gain. The no-fold branch
preserves gate count, without declaring the oracle or global obligations closed. -/
theorem nandSharingNormalizer_checked {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    match nandSharingNormalizer.normalize current with
    | .gain next _ =>
        next = sharingImplementation current ∧
          0 < (compileNANDSharing current.candidate.program).foldCount
    | .normal normalized =>
        normalized.result = sharingImplementation current ∧
          (compileNANDSharing current.candidate.program).foldCount = 0 ∧
          normalized.result.gateCount = current.gateCount := by
  by_cases positive : 0 < (compileNANDSharing current.candidate.program).foldCount
  · simp only [nandSharingNormalizer, dif_pos positive]
    exact ⟨True.intro, positive⟩
  · simp only [nandSharingNormalizer, dif_neg positive]
    have accounting := compileNANDSharing_exact_accounting current.candidate.program
    change (sharingImplementation current).gateCount +
      (compileNANDSharing current.candidate.program).foldCount =
      current.gateCount at accounting
    exact ⟨True.intro, by omega, by omega⟩

end DirectWire
end PNP
