import PNP.NANDFreshFieldCost

/-!
Explicit matching construction for fresh independent NAND outputs. The exact
minimum theorem concerns every finite old circuit and every extension width.
The reference minimum remains exhaustive; this is not a polynomial-time
minimization algorithm or a proof that arbitrary restoration charges are forced.
-/

namespace PNP.DirectWire.FreshNandCost

variable {inputs gates outputs : Nat}

/-- Emit a bounded prefix of primary-input NANDs, with one actual gate per index. -/
def inputNands {inputCount count : Nat} (left right : Fin count → Fin inputCount) :
    (length : Nat) → length ≤ count → Program inputCount length
  | 0, _ => .empty
  | length + 1, within =>
      .snoc (inputNands left right length (Nat.le_trans (Nat.le_succ length) within))
        ⟨.input (left ⟨length, Nat.lt_of_lt_of_le (Nat.lt_succ_self length) within⟩),
         .input (right ⟨length, Nat.lt_of_lt_of_le (Nat.lt_succ_self length) within⟩)⟩

theorem inputNands_eval {inputCount count : Nat} (left right : Fin count → Fin inputCount)
    (valuation : Valuation inputCount) :
    ∀ (length : Nat) (within : length ≤ count) (index : Fin length),
      (inputNands left right length within).eval valuation index =
        boolNand
          (valuation (left ⟨index.val, Nat.lt_of_lt_of_le index.isLt within⟩))
          (valuation (right ⟨index.val, Nat.lt_of_lt_of_le index.isLt within⟩)) := by
  intro length
  induction length with
  | zero => intro _ index; exact Fin.elim0 index
  | succ length ih =>
      intro within index
      refine Fin.lastCases ?_ (fun prior => ?_) index
      · rw [inputNands, Program.eval_snoc_last]
        rfl
      · rw [inputNands, Program.eval_snoc_castSucc]
        exact ih (Nat.le_trans (Nat.le_succ length) within) prior

def extendedProgram (candidate : Candidate inputs gates outputs) (width : Nat) :
    Program (inputs + (width + width)) (gates + width) :=
  (candidate.program.renameInputs (Fin.castAdd (width + width))).appendSubstituted
    (fun index => .input index)
    (inputNands leftInput rightInput width (Nat.le_refl width))

def extendedCandidate (candidate : Candidate inputs gates outputs) (width : Nat) :
    Candidate (inputs + (width + width)) (gates + width) (outputs + width) :=
  Candidate.ofDirectWireWord (extendedProgram candidate width)
    ⟨splitFin
      (fun output => ((candidate.directWireWord.source output).renameInputs
        (Fin.castAdd (width + width))).weakenGates width)
      (fun index => .gate (Fin.natAdd gates index))⟩

theorem extended_fresh (candidate : Candidate inputs gates outputs) (width : Nat)
    (valuation : Valuation (inputs + (width + width))) (index : Fin width) :
    (extendedCandidate candidate width).semantics valuation (Fin.natAdd outputs index) =
      freshValue valuation index := by
  unfold extendedCandidate
  rw [Candidate.ofDirectWireWord_semantics]
  unfold DirectWire.semantics DirectWireWord.eval
  dsimp only
  rw [splitFin_right]
  change (extendedProgram candidate width).eval valuation (Fin.natAdd gates index) = _
  unfold extendedProgram
  rw [Program.eval_appendSubstituted_suffix, inputNands_eval]
  rfl

theorem extended_old (candidate : Candidate inputs gates outputs) (width : Nat)
    (valuation : Valuation (inputs + (width + width))) (output : Fin outputs) :
    (extendedCandidate candidate width).semantics valuation (Fin.castAdd width output) =
      candidate.semantics (fun index => valuation (Fin.castAdd (width + width) index)) output := by
  unfold extendedCandidate
  rw [Candidate.ofDirectWireWord_semantics]
  unfold DirectWire.semantics DirectWireWord.eval
  dsimp only
  rw [splitFin_left, Source.eval_weakenGates, Source.eval_renameInputs]
  apply Source.eval_congr (candidate.directWireWord.source output) (fun _ => rfl)
  intro gate
  unfold extendedProgram
  rw [Program.eval_appendSubstituted_prefix, Program.eval_renameInputs]

def extend (target : Implementation inputs outputs) (width : Nat) :
    Implementation (inputs + (width + width)) (outputs + width) :=
  ⟨target.gateCount + width, extendedCandidate target.candidate width⟩

theorem extend_gateCount (target : Implementation inputs outputs) (width : Nat) :
    (extend target width).gateCount = target.gateCount + width := rfl

theorem extended_equivalent {leftGates rightGates : Nat}
    (left : Candidate inputs leftGates outputs) (right : Candidate inputs rightGates outputs)
    (equivalent : Equivalent left.program left.directWireWord right.program right.directWireWord)
    (width : Nat) :
    Equivalent (extendedCandidate left width).program (extendedCandidate left width).directWireWord
      (extendedCandidate right width).program (extendedCandidate right width).directWireWord := by
  intro valuation output
  change (extendedCandidate left width).semantics valuation output =
    (extendedCandidate right width).semantics valuation output
  rcases finSum_decompose output with ⟨index, equal⟩ | ⟨index, equal⟩
  · rw [equal, extended_old, extended_old]
    exact equivalent _ index
  · rw [equal, extended_fresh, extended_fresh]

/-- Exact semantic cost of any number of independent fresh NAND outputs. -/
theorem referenceMinimum_extend (target : Implementation inputs outputs) (width : Nat) :
    referenceMinimum (extend target width) = referenceMinimum target + width := by
  let enlarged := extend target width
  have enlargedWitness := equivalentBool_sound (referenceMinimumWitness_equivalent enlarged)
  have freshMatched : FreshMatches (referenceMinimumWitness enlarged) := by
    intro valuation index
    exact (enlargedWitness valuation (Fin.natAdd outputs index)).trans
      (extended_fresh target.candidate width valuation index)
  have oldMatched : OriginalMatches target (referenceMinimumWitness enlarged) := by
    intro valuation output
    exact (enlargedWitness valuation (Fin.castAdd width output)).trans
      (extended_old target.candidate width valuation output)
  have lower := gateCount_lower_bound target (referenceMinimumWitness enlarged)
    freshMatched oldMatched
  have oldWitness := equivalentBool_sound (referenceMinimumWitness_equivalent target)
  have upper := referenceMinimum_le_of_equivalent enlarged
    (extendedCandidate (referenceMinimumWitness target) width)
    (extended_equivalent (referenceMinimumWitness target) target.candidate oldWitness width)
  exact Nat.le_antisymm upper lower

end PNP.DirectWire.FreshNandCost
