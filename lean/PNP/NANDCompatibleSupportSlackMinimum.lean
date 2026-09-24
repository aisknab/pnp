/-
Copyright (c) 2026 PNP Labs.

A kernel-checked obstruction to the unrestricted compatible-support slack law.
The whole eleven-gate word is semantically minimum, while a proper computed
nine-gate cut has independent open minimum eight. Port completeness alone is
therefore insufficient for the manuscript's general replacement argument.

This does not refute the checked acyclic framed law or a properly restricted
admissible/full saturated-support law. It identifies a missing restriction;
it does not supply the remaining general routing or ZeroSlack proof.
-/

import PNP.NANDArbitrarySupportSplice
import PNP.DirectWireBaseline

set_option autoImplicit false
set_option Elab.async false

namespace PNP.DirectWire.CompatibleSupportSlackObstruction

def originalProgram : Program 4 11 :=
  let p0 := (Program.empty : Program 4 0).snoc ⟨.input 0, .input 1⟩
  let p1 := p0.snoc ⟨.gate 0, .gate 0⟩
  let p2 := p1.snoc ⟨.gate 1, .input 2⟩
  let p3 := p2.snoc ⟨.gate 2, .input 3⟩
  let p4 := p3.snoc ⟨.input 0, .gate 3⟩
  let p5 := p4.snoc ⟨.gate 4, .gate 4⟩
  let p6 := p5.snoc ⟨.gate 5, .input 1⟩
  let p7 := p6.snoc ⟨.gate 3, .gate 3⟩
  let p8 := p7.snoc ⟨.input 0, .gate 7⟩
  let p9 := p8.snoc ⟨.gate 8, .gate 8⟩
  p9.snoc ⟨.gate 9, .input 1⟩

def original : Candidate 4 11 10 :=
  Candidate.ofDirectWireWord originalProgram ⟨fun output => .gate output.succ⟩

def records : List (TerminalPrimitiveRecord 4 11 10 0) :=
  [.gate 0, .gate 1, .gate 4, .gate 5, .gate 6,
    .gate 7, .gate 8, .gate 9, .gate 10]

def support := extractTerminalSupport original records

def smallerProgram : Program 3 8 :=
  let p0 := (Program.empty : Program 3 0).snoc ⟨.input 0, .input 2⟩
  let p1 := p0.snoc ⟨.gate 0, .gate 0⟩
  let p2 := p1.snoc ⟨.gate 1, .input 1⟩
  let p3 := p2.snoc ⟨.input 2, .input 2⟩
  let p4 := p3.snoc ⟨.input 0, .gate 3⟩
  let p5 := p4.snoc ⟨.gate 4, .gate 4⟩
  let p6 := p5.snoc ⟨.gate 5, .input 1⟩
  p6.snoc ⟨.gate 2, .gate 6⟩

def smaller : Candidate 3 8 8 :=
  Candidate.ofDirectWireWord smallerProgram ⟨fun output =>
    match output.val with
    | 0 => .gate 7 | 1 => .gate 0 | 2 => .gate 1 | 3 => .gate 2
    | 4 => .gate 3 | 5 => .gate 4 | 6 => .gate 5 | _ => .gate 6⟩

def valuation (index : Fin 16) : Valuation 4 :=
  fun input => index.val.testBit input.val

def openValuation (index : Fin 8) : Valuation 3 :=
  fun input => index.val.testBit input.val

/-- Exactly the available values before the first physical gate. -/
def freeValue (source : Fin 6) (input : Valuation 4) : Bool :=
  if within : source.val < 4 then input ⟨source.val, within⟩
  else source.val == 5

/-- A direct Boolean expression for the literal word, used to keep finite
    kernel checks from repeatedly expanding the program representation. -/
def formula (input : Valuation 4) (output : Fin 10) : Bool :=
  let hidden := boolNand (input 0) (input 1)
  let ab := boolNand hidden hidden
  let q := boolNand ab (input 2)
  let z := boolNand q (input 3)
  let azNot := boolNand (input 0) z
  let az := boolNand azNot azNot
  let azbNot := boolNand az (input 1)
  let zNot := boolNand z z
  let anNot := boolNand (input 0) zNot
  let an := boolNand anNot anNot
  let anbNot := boolNand an (input 1)
  match output.val with
  | 0 => ab | 1 => q | 2 => z | 3 => azNot | 4 => az
  | 5 => azbNot | 6 => zNot | 7 => anNot | 8 => an | _ => anbNot

theorem formula_exact (input : Valuation 4) (output : Fin 10) :
    original.semantics input output = formula input output := by
  have options : output = 0 ∨ output = 1 ∨ output = 2 ∨ output = 3 ∨
      output = 4 ∨ output = 5 ∨ output = 6 ∨ output = 7 ∨
      output = 8 ∨ output = 9 := by omega
  rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Suggested finite witnesses are data only; each use is checked below
    against the actual literal word through formula_exact. -/
private def truthVector (output : Fin 10) : Nat :=
  match output.val with
  | 0 => 34952 | 1 => 32639 | 2 => 33023 | 3 => 32597 | 4 => 32938
  | 5 => 32631 | 6 => 32512 | 7 => 54783 | 8 => 10752 | _ => 63487

private def freeVector (source : Fin 6) : Nat :=
  match source.val with
  | 0 => 43690 | 1 => 52428 | 2 => 61680 | 3 => 65280 | 4 => 0 | _ => 65535

private def difference (left right : Nat) : Fin 16 :=
  if (Nat.xor left right).testBit 0 then 0
  else if (Nat.xor left right).testBit 1 then 1
  else if (Nat.xor left right).testBit 2 then 2
  else if (Nat.xor left right).testBit 3 then 3
  else if (Nat.xor left right).testBit 4 then 4
  else if (Nat.xor left right).testBit 5 then 5
  else if (Nat.xor left right).testBit 6 then 6
  else if (Nat.xor left right).testBit 7 then 7
  else if (Nat.xor left right).testBit 8 then 8
  else if (Nat.xor left right).testBit 9 then 9
  else if (Nat.xor left right).testBit 10 then 10
  else if (Nat.xor left right).testBit 11 then 11
  else if (Nat.xor left right).testBit 12 then 12
  else if (Nat.xor left right).testBit 13 then 13
  else if (Nat.xor left right).testBit 14 then 14
  else 15

private def nonconstantPoint (output : Fin 10) : Fin 16 :=
  difference (truthVector output)
    (if (truthVector output).testBit 0 then 65535 else 0)

private def projectionPoint (output : Fin 10) (input : Fin 4) : Fin 16 :=
  difference (truthVector output) (freeVector (input.castAdd 2))

private def pairPoint (left right : Fin 10) : Fin 16 :=
  difference (truthVector left) (truthVector right)

private def nandPoint (output : Fin 10) (left right : Fin 6) : Fin 16 :=
  difference (truthVector output)
    (Nat.xor 65535 (freeVector left &&& freeVector right))

private theorem nonconstant_witness : ∀ output : Fin 10, ∃ left right : Fin 16,
    original.semantics (valuation left) output ≠
      original.semantics (valuation right) output := by
  intro output
  refine ⟨0, nonconstantPoint output, ?_⟩
  simp only [formula_exact]
  exact (by decide +kernel : ∀ index : Fin 10,
    formula (valuation 0) index ≠
      formula (valuation (nonconstantPoint index)) index) output

private theorem nonprojection_witness : ∀ (output : Fin 10) (input : Fin 4),
    ∃ value : Fin 16,
      original.semantics (valuation value) output ≠ valuation value input := by
  intro output input
  refine ⟨projectionPoint output input, ?_⟩
  simp only [formula_exact]
  exact (by decide +kernel : ∀ (index : Fin 10) (port : Fin 4),
    formula (valuation (projectionPoint index port)) index ≠
      valuation (projectionPoint index port) port) output input

private theorem distinct_witness : ∀ left right : Fin 10, left ≠ right →
    ∃ value : Fin 16,
      original.semantics (valuation value) left ≠
        original.semantics (valuation value) right := by
  intro left right unequal
  refine ⟨pairPoint left right, ?_⟩
  simp only [formula_exact]
  exact (by decide +kernel : ∀ left right : Fin 10, left ≠ right →
    formula (valuation (pairPoint left right)) left ≠
      formula (valuation (pairPoint left right)) right) left right unequal

theorem baseline : BaselineOutputConditions original := by
  constructor
  · intro output
    obtain ⟨left, right, different⟩ := nonconstant_witness output
    exact ⟨valuation left, valuation right, different⟩
  · intro output input
    obtain ⟨value, different⟩ := nonprojection_witness output input
    exact ⟨valuation value, different⟩
  · intro left right unequal
    obtain ⟨value, different⟩ := distinct_witness left right unequal
    exact ⟨valuation value, different⟩

private theorem nand_witness_0 : ∀ (left right : Fin 6),
    formula (valuation (nandPoint 0 left right)) 0 ≠
      boolNand (freeValue left (valuation (nandPoint 0 left right)))
        (freeValue right (valuation (nandPoint 0 left right))) := by
  decide +kernel

private theorem nand_witness_1 : ∀ (left right : Fin 6),
    formula (valuation (nandPoint 1 left right)) 1 ≠
      boolNand (freeValue left (valuation (nandPoint 1 left right)))
        (freeValue right (valuation (nandPoint 1 left right))) := by
  decide +kernel

private theorem nand_witness_2 : ∀ (left right : Fin 6),
    formula (valuation (nandPoint 2 left right)) 2 ≠
      boolNand (freeValue left (valuation (nandPoint 2 left right)))
        (freeValue right (valuation (nandPoint 2 left right))) := by
  decide +kernel

private theorem nand_witness_3 : ∀ (left right : Fin 6),
    formula (valuation (nandPoint 3 left right)) 3 ≠
      boolNand (freeValue left (valuation (nandPoint 3 left right)))
        (freeValue right (valuation (nandPoint 3 left right))) := by
  decide +kernel

private theorem nand_witness_4 : ∀ (left right : Fin 6),
    formula (valuation (nandPoint 4 left right)) 4 ≠
      boolNand (freeValue left (valuation (nandPoint 4 left right)))
        (freeValue right (valuation (nandPoint 4 left right))) := by
  decide +kernel

private theorem nand_witness_5 : ∀ (left right : Fin 6),
    formula (valuation (nandPoint 5 left right)) 5 ≠
      boolNand (freeValue left (valuation (nandPoint 5 left right)))
        (freeValue right (valuation (nandPoint 5 left right))) := by
  decide +kernel

private theorem nand_witness_6 : ∀ (left right : Fin 6),
    formula (valuation (nandPoint 6 left right)) 6 ≠
      boolNand (freeValue left (valuation (nandPoint 6 left right)))
        (freeValue right (valuation (nandPoint 6 left right))) := by
  decide +kernel

private theorem nand_witness_7 : ∀ (left right : Fin 6),
    formula (valuation (nandPoint 7 left right)) 7 ≠
      boolNand (freeValue left (valuation (nandPoint 7 left right)))
        (freeValue right (valuation (nandPoint 7 left right))) := by
  decide +kernel

private theorem nand_witness_8 : ∀ (left right : Fin 6),
    formula (valuation (nandPoint 8 left right)) 8 ≠
      boolNand (freeValue left (valuation (nandPoint 8 left right)))
        (freeValue right (valuation (nandPoint 8 left right))) := by
  decide +kernel

private theorem nand_witness_9 : ∀ (left right : Fin 6),
    formula (valuation (nandPoint 9 left right)) 9 ≠
      boolNand (freeValue left (valuation (nandPoint 9 left right)))
        (freeValue right (valuation (nandPoint 9 left right))) := by
  decide +kernel

theorem no_output_is_first_nand : ∀ (output : Fin 10) (left right : Fin 6),
    ∃ value : Fin 16,
      original.semantics (valuation value) output ≠
        boolNand (freeValue left (valuation value))
          (freeValue right (valuation value)) := by
  intro output left right
  refine ⟨nandPoint output left right, ?_⟩
  simp only [formula_exact]
  have options : output = 0 ∨ output = 1 ∨ output = 2 ∨ output = 3 ∨
      output = 4 ∨ output = 5 ∨ output = 6 ∨ output = 7 ∨
      output = 8 ∨ output = 9 := by omega
  rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nand_witness_0 left right
  · exact nand_witness_1 left right
  · exact nand_witness_2 left right
  · exact nand_witness_3 left right
  · exact nand_witness_4 left right
  · exact nand_witness_5 left right
  · exact nand_witness_6 left right
  · exact nand_witness_7 left right
  · exact nand_witness_8 left right
  · exact nand_witness_9 left right

private theorem first_source {gates : Nat} (program : Program 4 gates)
    (positive : 0 < gates) (wire : Source 4 gates)
    (edge : (program.terminalGateSources ⟨0, positive⟩).1 = wire ∨
      (program.terminalGateSources ⟨0, positive⟩).2 = wire) :
    ∃ source : Fin 6, ∀ input,
      wire.eval input (program.eval input) = freeValue source input := by
  cases wire with
  | input index =>
      refine ⟨index.castAdd 2, ?_⟩
      intro input
      change input index =
        (if within : index.val < 4 then input ⟨index.val, within⟩
          else index.val == 5)
      rw [dif_pos index.isLt]
  | constant value =>
      cases value with
      | false => exact ⟨4, fun _ => rfl⟩
      | true => exact ⟨5, fun _ => rfl⟩
  | gate index =>
      have impossible := ArbitrarySupportSplice.sources_ordered
        program ⟨0, positive⟩ index edge
      exact False.elim (Nat.not_lt_zero index.val impossible)

/-- The lower bound is universal over all equivalent implementations, not a
    finite synthesis search or an assumed optimality certificate. -/
theorem gate_lower_bound {gates : Nat} (offered : Candidate 4 gates 10)
    (same : Equivalent offered.program offered.directWireWord
      original.program original.directWireWord) : 11 ≤ gates := by
  let conditions := baseline.of_equivalent same
  have ten := outputCount_le_gateCount offered conditions
  have positive : 0 < gates := by omega
  let first : Fin gates := ⟨0, positive⟩
  obtain ⟨left, leftValue⟩ := first_source offered.program positive
    (offered.program.terminalGateSources first).1 (Or.inl rfl)
  obtain ⟨right, rightValue⟩ := first_source offered.program positive
    (offered.program.terminalGateSources first).2 (Or.inr rfl)
  have notFirst : ∀ output, outputGateIndex offered conditions output ≠ first := by
    intro output atFirst
    obtain ⟨value, different⟩ := no_output_is_first_nand output left right
    have atOutput := same (valuation value) output
    change (offered.directWireWord.source output).eval (valuation value)
        (offered.program.eval (valuation value)) =
      original.semantics (valuation value) output at atOutput
    rw [outputGateIndex_source offered conditions output, atFirst] at atOutput
    have atGate := ArbitrarySupportSplice.sources_eval
      offered.program (valuation value) first
    rw [leftValue (valuation value), rightValue (valuation value)] at atGate
    exact different (atOutput.symm.trans atGate.symm)
  let embedding : Fin (10 + 1) → Fin gates :=
    splitFin (outputGateIndex offered conditions) (fun _ : Fin 1 => first)
  have injective : Function.Injective embedding := by
    intro leftIndex rightIndex sameGate
    rcases finSum_decompose leftIndex with ⟨leftOutput, rfl⟩ | ⟨leftExtra, rfl⟩
    · rcases finSum_decompose rightIndex with ⟨rightOutput, rfl⟩ | ⟨rightExtra, rfl⟩
      · simp only [embedding, splitFin_left] at sameGate
        exact congrArg (Fin.castAdd 1)
          (outputGateIndex_injective offered conditions sameGate)
      · simp only [embedding, splitFin_left, splitFin_right] at sameGate
        exact False.elim (notFirst leftOutput sameGate)
    · rcases finSum_decompose rightIndex with ⟨rightOutput, rfl⟩ | ⟨rightExtra, rfl⟩
      · simp only [embedding, splitFin_left, splitFin_right] at sameGate
        exact False.elim (notFirst rightOutput sameGate.symm)
      · have extraEqual : leftExtra = rightExtra := by
          apply Fin.ext
          have leftBound := leftExtra.isLt
          have rightBound := rightExtra.isLt
          omega
        exact congrArg (Fin.natAdd 10) extraEqual
  exact finCard_le_of_injective embedding injective

theorem original_is_minimum : IsSemanticallyMinimum original.toImplementation := by
  intro gates offered same
  exact gate_lower_bound offered same

theorem original_reference_minimum : referenceMinimum original.toImplementation = 11 := by
  have lower := gate_lower_bound (referenceMinimumWitness original.toImplementation)
    (equivalentBool_sound (referenceMinimumWitness_equivalent original.toImplementation))
  exact Nat.le_antisymm (referenceMinimum_le_target original.toImplementation) lower

theorem global_slack_zero : residualSlack original.toImplementation = 0 :=
  (residualSlack_eq_zero_iff_minimum original.toImplementation).mpr original_is_minimum


end PNP.DirectWire.CompatibleSupportSlackObstruction
