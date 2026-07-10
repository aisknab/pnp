/-
Copyright (c) 2026 PNP Labs.

Concrete serial composition and framed replacement for the typed direct-wire
NAND language.  A framed support is an actual middle program block: this file
does not model arbitrary gate subsets, support profiles, or trusted support
annotations.
-/

import PNP.NANDTruthTable

namespace PNP
namespace DirectWire

/-! ## Structural maps -/

theorem natSub_lt_right_of_lt_add {value leftWidth rightWidth : Nat}
    (leftWithin : leftWidth ≤ value)
    (upper : value < leftWidth + rightWidth) :
    value - leftWidth < rightWidth := by
  induction leftWidth generalizing value with
  | zero =>
      rw [Nat.sub_zero]
      rw [Nat.zero_add] at upper
      exact upper
  | succ leftWidth ih =>
      cases value with
      | zero => exact False.elim (Nat.not_succ_le_zero leftWidth leftWithin)
      | succ value =>
          rw [Nat.succ_sub_succ_eq_sub]
          apply ih (Nat.le_of_succ_le_succ leftWithin)
          rw [Nat.succ_add] at upper
          exact Nat.lt_of_succ_lt_succ upper

theorem natAdd_sub_of_le {leftWidth value : Nat}
    (leftWithin : leftWidth ≤ value) :
    leftWidth + (value - leftWidth) = value := by
  induction leftWidth generalizing value with
  | zero => rw [Nat.sub_zero, Nat.zero_add]
  | succ leftWidth ih =>
      cases value with
      | zero => exact False.elim (Nat.not_succ_le_zero leftWidth leftWithin)
      | succ value =>
          rw [Nat.succ_sub_succ_eq_sub, Nat.succ_add]
          exact congrArg Nat.succ (ih (Nat.le_of_succ_le_succ leftWithin))

theorem natAdd_sub_cancel_left (leftWidth value : Nat) :
    (leftWidth + value) - leftWidth = value := by
  induction leftWidth with
  | zero => rw [Nat.zero_add, Nat.sub_zero]
  | succ leftWidth ih =>
      rw [Nat.succ_add, Nat.succ_sub_succ_eq_sub]
      exact ih

/-- Non-dependent case analysis for a finite sum, implemented directly from
    the numeric index.  Unlike the dependent core eliminator, this operation
    has no quotient or propositional-extensionality dependency. -/
def splitFin {leftWidth rightWidth : Nat} {result : Type}
    (onLeft : Fin leftWidth → result) (onRight : Fin rightWidth → result)
    (index : Fin (leftWidth + rightWidth)) : result :=
  if isLeft : index.val < leftWidth then
    onLeft ⟨index.val, isLeft⟩
  else
    onRight ⟨index.val - leftWidth,
      natSub_lt_right_of_lt_add (Nat.le_of_not_gt isLeft) index.isLt⟩

theorem splitFin_left {leftWidth rightWidth : Nat} {result : Type}
    (onLeft : Fin leftWidth → result) (onRight : Fin rightWidth → result)
    (index : Fin leftWidth) :
    splitFin onLeft onRight (Fin.castAdd rightWidth index) = onLeft index := by
  unfold splitFin
  split
  · rename_i isLeft
    apply congrArg onLeft
    exact Fin.ext rfl
  · rename_i notLeft
    exact False.elim (notLeft index.isLt)

theorem splitFin_right {leftWidth rightWidth : Nat} {result : Type}
    (onLeft : Fin leftWidth → result) (onRight : Fin rightWidth → result)
    (index : Fin rightWidth) :
    splitFin onLeft onRight (Fin.natAdd leftWidth index) = onRight index := by
  unfold splitFin
  split
  · rename_i impossible
    exact False.elim (Nat.not_lt_of_ge
      (Nat.le_add_right leftWidth index.val) impossible)
  · apply congrArg onRight
    apply Fin.ext
    exact natAdd_sub_cancel_left leftWidth index.val

/-- Every finite-sum index is concretely a left or right injection. -/
theorem finSum_decompose {leftWidth rightWidth : Nat}
    (index : Fin (leftWidth + rightWidth)) :
    (∃ left : Fin leftWidth, index = Fin.castAdd rightWidth left) ∨
      ∃ right : Fin rightWidth, index = Fin.natAdd leftWidth right := by
  if isLeft : index.val < leftWidth then
    exact Or.inl ⟨⟨index.val, isLeft⟩, Fin.ext rfl⟩
  else
    let right : Fin rightWidth :=
      ⟨index.val - leftWidth,
        natSub_lt_right_of_lt_add (Nat.le_of_not_gt isLeft) index.isLt⟩
    apply Or.inr
    refine ⟨right, ?_⟩
    apply Fin.ext
    exact (natAdd_sub_of_le (Nat.le_of_not_gt isLeft)).symm

/-- Rename primary inputs while leaving constants and gate indices unchanged. -/
def Source.renameInputs {fromInputs toInputs gates : Nat}
    (rename : Fin fromInputs → Fin toInputs) :
    Source fromInputs gates → Source toInputs gates
  | .input index => .input (rename index)
  | .constant value => .constant value
  | .gate index => .gate index

/-- Make a source available after `extra` more gates have been allocated. -/
def Source.weakenGates {inputs gates : Nat} (extra : Nat) :
    Source inputs gates → Source inputs (gates + extra)
  | .input index => .input index
  | .constant value => .constant value
  | .gate index => .gate (Fin.castAdd extra index)

/-- Shift a source into the suffix following `offset` gates. -/
def Source.shiftGates {inputs gates : Nat} (offset : Nat) :
    Source inputs gates → Source inputs (offset + gates)
  | .input index => .input index
  | .constant value => .constant value
  | .gate index => .gate (Fin.natAdd offset index)

/-- Replace each primary input by a source produced by a concrete prefix. -/
def Source.substituteInputs {innerInputs outerInputs prefixGates suffixGates : Nat}
    (binding : Fin innerInputs → Source outerInputs prefixGates) :
    Source innerInputs suffixGates → Source outerInputs (prefixGates + suffixGates)
  | .input index => (binding index).weakenGates suffixGates
  | .constant value => .constant value
  | .gate index => .gate (Fin.natAdd prefixGates index)

def Gate.renameInputs {fromInputs toInputs gates : Nat}
    (rename : Fin fromInputs → Fin toInputs) (gate : Gate fromInputs gates) :
    Gate toInputs gates :=
  ⟨gate.left.renameInputs rename, gate.right.renameInputs rename⟩

def Gate.substituteInputs {innerInputs outerInputs prefixGates suffixGates : Nat}
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (gate : Gate innerInputs suffixGates) :
    Gate outerInputs (prefixGates + suffixGates) :=
  ⟨gate.left.substituteInputs binding, gate.right.substituteInputs binding⟩

def Program.renameInputs {fromInputs toInputs gates : Nat}
    (rename : Fin fromInputs → Fin toInputs)
    (program : Program fromInputs gates) : Program toInputs gates :=
  match program with
  | .empty => .empty
  | .snoc initial gate =>
      .snoc (initial.renameInputs rename) (gate.renameInputs rename)

/-- Append a program after a prefix, substituting the appended inputs by
    sources already available at the end of the prefix. -/
def Program.appendSubstituted {outerInputs innerInputs prefixGates : Nat}
    (initialProgram : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    {suffixGates : Nat} (suffix : Program innerInputs suffixGates) :
    Program outerInputs (prefixGates + suffixGates) :=
  match suffix with
  | .empty => initialProgram
  | .snoc initial gate =>
      .snoc (appendSubstituted initialProgram binding initial)
        (gate.substituteInputs binding)

def DirectWireWord.renameInputs {fromInputs toInputs gates outputs : Nat}
    (rename : Fin fromInputs → Fin toInputs)
    (word : DirectWireWord fromInputs gates outputs) :
    DirectWireWord toInputs gates outputs :=
  ⟨fun output => (word.source output).renameInputs rename⟩

/-! ## Pointwise structural semantics -/

theorem Source.eval_renameInputs {fromInputs toInputs gates : Nat}
    (source : Source fromInputs gates) (rename : Fin fromInputs → Fin toInputs)
    (input : Valuation toInputs) (gateValues : Valuation gates) :
    (source.renameInputs rename).eval input gateValues =
      source.eval (fun index => input (rename index)) gateValues := by
  cases source <;> rfl

theorem Gate.eval_renameInputs {fromInputs toInputs gates : Nat}
    (gate : Gate fromInputs gates) (rename : Fin fromInputs → Fin toInputs)
    (input : Valuation toInputs) (gateValues : Valuation gates) :
    (gate.renameInputs rename).eval input gateValues =
      gate.eval (fun index => input (rename index)) gateValues := by
  unfold Gate.eval Gate.renameInputs
  rw [Source.eval_renameInputs, Source.eval_renameInputs]

theorem Source.eval_weakenGates {inputs gates : Nat}
    (source : Source inputs gates) (extra : Nat)
    (input : Valuation inputs) (gateValues : Valuation (gates + extra)) :
    (source.weakenGates extra).eval input gateValues =
      source.eval input (fun index => gateValues (Fin.castAdd extra index)) := by
  cases source <;> rfl

theorem Source.eval_shiftGates {inputs gates : Nat}
    (source : Source inputs gates) (offset : Nat)
    (input : Valuation inputs) (gateValues : Valuation (offset + gates)) :
    (source.shiftGates offset).eval input gateValues =
      source.eval input (fun index => gateValues (Fin.natAdd offset index)) := by
  cases source <;> rfl

theorem Source.eval_substituteInputs
    {innerInputs outerInputs prefixGates suffixGates : Nat}
    (source : Source innerInputs suffixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (input : Valuation outerInputs)
    (gateValues : Valuation (prefixGates + suffixGates)) :
    (source.substituteInputs binding).eval input gateValues =
      source.eval
        (fun index => (binding index).eval input
          (fun gate => gateValues (Fin.castAdd suffixGates gate)))
        (fun gate => gateValues (Fin.natAdd prefixGates gate)) := by
  cases source with
  | input index => exact Source.eval_weakenGates (binding index) suffixGates input gateValues
  | constant value => rfl
  | gate index => rfl

theorem Program.eval_renameInputs {fromInputs toInputs gates : Nat}
    (program : Program fromInputs gates) (rename : Fin fromInputs → Fin toInputs)
    (input : Valuation toInputs) (gate : Fin gates) :
    (program.renameInputs rename).eval input gate =
      program.eval (fun index => input (rename index)) gate := by
  induction program with
  | empty => exact Fin.elim0 gate
  | @snoc gates initial nextGate ih =>
      unfold Program.renameInputs Program.eval Valuation.snoc
      split
      · exact ih _
      · rw [Gate.eval_renameInputs]
        exact nextGate.eval_congr (fun _ => rfl) (fun index => ih index)

theorem Program.size_renameInputs {fromInputs toInputs gates : Nat}
    (program : Program fromInputs gates) (rename : Fin fromInputs → Fin toInputs) :
    (program.renameInputs rename).size = program.size := by
  rw [Program.size_eq_gateCount, Program.size_eq_gateCount]

theorem renameInputs_semantics
    {fromInputs toInputs gates outputs : Nat}
    (program : Program fromInputs gates)
    (word : DirectWireWord fromInputs gates outputs)
    (rename : Fin fromInputs → Fin toInputs)
    (input : Valuation toInputs) (output : Fin outputs) :
    semantics (program.renameInputs rename) (word.renameInputs rename) input output =
      semantics program word (fun index => input (rename index)) output := by
  unfold semantics DirectWireWord.eval DirectWireWord.renameInputs
  rw [Source.eval_renameInputs]
  exact (word.source output).eval_congr (fun _ => rfl)
    (fun gate => Program.eval_renameInputs program rename input gate)

theorem Program.size_appendSubstituted
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initialProgram : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (suffix : Program innerInputs suffixGates) :
    (initialProgram.appendSubstituted binding suffix).size =
      initialProgram.size + suffix.size := by
  rw [Program.size_eq_gateCount, Program.size_eq_gateCount,
    Program.size_eq_gateCount]

theorem Program.eval_appendSubstituted_prefix
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initialProgram : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (suffix : Program innerInputs suffixGates)
    (input : Valuation outerInputs) (gate : Fin prefixGates) :
    (initialProgram.appendSubstituted binding suffix).eval input
        (Fin.castAdd suffixGates gate) =
      initialProgram.eval input gate := by
  induction suffix with
  | empty => rfl
  | @snoc gates initial nextGate ih =>
      change (Program.snoc (initialProgram.appendSubstituted binding initial)
          (nextGate.substituteInputs binding)).eval input
        (Fin.castSucc (Fin.castAdd gates gate)) = initialProgram.eval input gate
      rw [Program.eval_snoc_castSucc]
      exact ih

theorem Program.eval_appendSubstituted_suffix
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initialProgram : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (suffix : Program innerInputs suffixGates)
    (input : Valuation outerInputs) (gate : Fin suffixGates) :
    (initialProgram.appendSubstituted binding suffix).eval input
        (Fin.natAdd prefixGates gate) =
      suffix.eval
        (fun index => (binding index).eval input (initialProgram.eval input)) gate := by
  induction suffix with
  | empty => exact Fin.elim0 gate
  | @snoc gates initial nextGate ih =>
      unfold Program.appendSubstituted Program.eval Valuation.snoc
      split
      · rename_i compositeEarlier
        split
        · rename_i suffixEarlier
          exact ih ⟨gate.val, suffixEarlier⟩
        · rename_i suffixNotEarlier
          exact False.elim (suffixNotEarlier
            (Nat.lt_of_add_lt_add_left compositeEarlier))
      · rename_i compositeNotEarlier
        split
        · rename_i suffixEarlier
          exact False.elim (compositeNotEarlier
            (Nat.add_lt_add_left suffixEarlier prefixGates))
        · change boolNand
              ((nextGate.left.substituteInputs binding).eval input
                ((initialProgram.appendSubstituted binding initial).eval input))
              ((nextGate.right.substituteInputs binding).eval input
                ((initialProgram.appendSubstituted binding initial).eval input)) =
            boolNand
              (nextGate.left.eval
                (fun index => (binding index).eval input (initialProgram.eval input))
                (initial.eval
                  (fun index => (binding index).eval input (initialProgram.eval input))))
              (nextGate.right.eval
                (fun index => (binding index).eval input (initialProgram.eval input))
                (initial.eval
                  (fun index => (binding index).eval input (initialProgram.eval input))))
          rw [Source.eval_substituteInputs, Source.eval_substituteInputs]
          let inputEqual : ∀ index,
              (binding index).eval input
                  (fun prefixGate =>
                    (initialProgram.appendSubstituted binding initial).eval input
                      (Fin.castAdd gates prefixGate)) =
                (binding index).eval input (initialProgram.eval input) :=
            fun index => (binding index).eval_congr
              (leftInput := input) (rightInput := input) (fun _ => rfl)
              (fun prefixGate =>
                Program.eval_appendSubstituted_prefix initialProgram binding initial input prefixGate)
          let gateEqual : ∀ suffixGate,
              (initialProgram.appendSubstituted binding initial).eval input
                  (Fin.natAdd prefixGates suffixGate) =
                initial.eval
                  (fun index => (binding index).eval input (initialProgram.eval input))
                  suffixGate := fun suffixGate => ih suffixGate
          rw [nextGate.left.eval_congr inputEqual gateEqual]
          rw [nextGate.right.eval_congr inputEqual gateEqual]

/-! ## Sequential composition -/

def sequentialProgram {inputs middle leftGates rightGates : Nat}
    (leftProgram : Program inputs leftGates)
    (leftWord : DirectWireWord inputs leftGates middle)
    (rightProgram : Program middle rightGates) :
    Program inputs (leftGates + rightGates) :=
  leftProgram.appendSubstituted leftWord.source rightProgram

def sequentialWord {inputs middle outputs leftGates rightGates : Nat}
    (leftWord : DirectWireWord inputs leftGates middle)
    (rightWord : DirectWireWord middle rightGates outputs) :
    DirectWireWord inputs (leftGates + rightGates) outputs :=
  ⟨fun output => (rightWord.source output).substituteInputs leftWord.source⟩

theorem sequentialProgram_size {inputs middle leftGates rightGates : Nat}
    (leftProgram : Program inputs leftGates)
    (leftWord : DirectWireWord inputs leftGates middle)
    (rightProgram : Program middle rightGates) :
    (sequentialProgram leftProgram leftWord rightProgram).size =
      leftProgram.size + rightProgram.size :=
  Program.size_appendSubstituted leftProgram leftWord.source rightProgram

theorem sequential_semantics
    {inputs middle outputs leftGates rightGates : Nat}
    (leftProgram : Program inputs leftGates)
    (leftWord : DirectWireWord inputs leftGates middle)
    (rightProgram : Program middle rightGates)
    (rightWord : DirectWireWord middle rightGates outputs)
    (input : Valuation inputs) (output : Fin outputs) :
    semantics (sequentialProgram leftProgram leftWord rightProgram)
        (sequentialWord leftWord rightWord) input output =
      semantics rightProgram rightWord
        (semantics leftProgram leftWord input) output := by
  unfold semantics DirectWireWord.eval sequentialProgram sequentialWord
  rw [Source.eval_substituteInputs]
  exact (rightWord.source output).eval_congr
    (fun index => (leftWord.source index).eval_congr (fun _ => rfl)
      (fun leftGate =>
        Program.eval_appendSubstituted_prefix leftProgram leftWord.source
          rightProgram input leftGate))
    (fun rightGate =>
      Program.eval_appendSubstituted_suffix leftProgram leftWord.source
        rightProgram input rightGate)

def Candidate.sequential {inputs middle outputs leftGates rightGates : Nat}
    (left : Candidate inputs leftGates middle)
    (right : Candidate middle rightGates outputs) :
    Candidate inputs (leftGates + rightGates) outputs :=
  Candidate.ofDirectWireWord
    (sequentialProgram left.program left.directWireWord right.program)
    (sequentialWord left.directWireWord right.directWireWord)

theorem Candidate.sequential_program {inputs middle outputs leftGates rightGates : Nat}
    (left : Candidate inputs leftGates middle)
    (right : Candidate middle rightGates outputs) :
    (left.sequential right).program =
      sequentialProgram left.program left.directWireWord right.program := rfl

theorem Candidate.sequential_size {inputs middle outputs leftGates rightGates : Nat}
    (left : Candidate inputs leftGates middle)
    (right : Candidate middle rightGates outputs) :
    (left.sequential right).program.size =
      left.program.size + right.program.size :=
  sequentialProgram_size left.program left.directWireWord right.program

theorem Candidate.ofDirectWireWord_semantics
    {inputs gates outputs : Nat}
    (program : Program inputs gates)
    (word : DirectWireWord inputs gates outputs)
    (input : Valuation inputs) (output : Fin outputs) :
    (Candidate.ofDirectWireWord program word).semantics input output =
      DirectWire.semantics program word input output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  change ((Candidate.ofDirectWireWord program word).directWireWord.source output).eval
      input (program.eval input) =
    (word.source output).eval input (program.eval input)
  rw [Candidate.ofDirectWireWord_pointwise]

theorem Candidate.sequential_semantics
    {inputs middle outputs leftGates rightGates : Nat}
    (left : Candidate inputs leftGates middle)
    (right : Candidate middle rightGates outputs)
    (input : Valuation inputs) (output : Fin outputs) :
    (left.sequential right).semantics input output =
      right.semantics (left.semantics input) output := by
  unfold Candidate.sequential
  rw [Candidate.ofDirectWireWord_semantics]
  exact DirectWire.sequential_semantics left.program left.directWireWord
    right.program right.directWireWord input output

/-! ## Concrete framed support blocks -/

/-- Rename the primary inputs of a complete candidate. -/
def Candidate.renameInputs {fromInputs toInputs gates outputs : Nat}
    (rename : Fin fromInputs → Fin toInputs)
    (candidate : Candidate fromInputs gates outputs) :
    Candidate toInputs gates outputs :=
  Candidate.ofDirectWireWord
    (candidate.program.renameInputs rename)
    (candidate.directWireWord.renameInputs rename)

theorem Candidate.renameInputs_size {fromInputs toInputs gates outputs : Nat}
    (rename : Fin fromInputs → Fin toInputs)
    (candidate : Candidate fromInputs gates outputs) :
    (candidate.renameInputs rename).program.size = candidate.program.size :=
  Program.size_renameInputs candidate.program rename

theorem Candidate.renameInputs_semantics
    {fromInputs toInputs gates outputs : Nat}
    (rename : Fin fromInputs → Fin toInputs)
    (candidate : Candidate fromInputs gates outputs)
    (input : Valuation toInputs) (output : Fin outputs) :
    (candidate.renameInputs rename).semantics input output =
      candidate.semantics (fun index => input (rename index)) output := by
  unfold Candidate.renameInputs
  rw [Candidate.ofDirectWireWord_semantics]
  exact DirectWire.renameInputs_semantics candidate.program
    candidate.directWireWord rename input output

/-- Output wiring for a support block extended by concrete bypass inputs. -/
def withBypassWord {supportInputs supportOutputs supportGates bypass : Nat}
    (support : Candidate supportInputs supportGates supportOutputs) :
    DirectWireWord (supportInputs + bypass) supportGates
      (supportOutputs + bypass) :=
  ⟨splitFin
    (fun output => (support.directWireWord.source output).renameInputs
      (Fin.castAdd bypass))
    (fun bypassIndex => .input (Fin.natAdd supportInputs bypassIndex))⟩

theorem withBypassWord_support_source
    {supportInputs supportOutputs supportGates bypass : Nat}
    (support : Candidate supportInputs supportGates supportOutputs)
    (output : Fin supportOutputs) :
    (withBypassWord (bypass := bypass) support).source
        (Fin.castAdd bypass output) =
      (support.directWireWord.source output).renameInputs
        (Fin.castAdd bypass) := by
  unfold withBypassWord
  change splitFin
      (fun output => (support.directWireWord.source output).renameInputs
        (Fin.castAdd bypass))
      (fun bypassIndex => Source.input (Fin.natAdd supportInputs bypassIndex))
      (Fin.castAdd bypass output) = _
  exact splitFin_left _ _ output

theorem withBypassWord_bypass_source
    {supportInputs supportOutputs supportGates bypass : Nat}
    (support : Candidate supportInputs supportGates supportOutputs)
    (bypassIndex : Fin bypass) :
    (withBypassWord (bypass := bypass) support).source
        (Fin.natAdd supportOutputs bypassIndex) =
      .input (Fin.natAdd supportInputs bypassIndex) := by
  unfold withBypassWord
  change splitFin
      (fun output => (support.directWireWord.source output).renameInputs
        (Fin.castAdd bypass))
      (fun bypassIndex => Source.input (Fin.natAdd supportInputs bypassIndex))
      (Fin.natAdd supportOutputs bypassIndex) = _
  exact splitFin_right _ _ bypassIndex

/-- Extend a support candidate with identity bypass wires.  Its gates are
    exactly the renamed support program; bypass wiring adds no gates. -/
def Candidate.withBypass {supportInputs supportOutputs supportGates : Nat}
    (bypass : Nat) (support : Candidate supportInputs supportGates supportOutputs) :
    Candidate (supportInputs + bypass) supportGates (supportOutputs + bypass) :=
  Candidate.ofDirectWireWord
    (support.program.renameInputs (Fin.castAdd bypass))
    (withBypassWord (bypass := bypass) support)

theorem Candidate.withBypass_size
    {supportInputs supportOutputs supportGates : Nat}
    (bypass : Nat) (support : Candidate supportInputs supportGates supportOutputs) :
    (support.withBypass bypass).program.size = support.program.size :=
  Program.size_renameInputs support.program (Fin.castAdd bypass)

/-- A support-plus-bypass block computes support outputs on the left and
    forwards the bypass portion on the right. -/
theorem Candidate.withBypass_semantics
    {supportInputs supportOutputs supportGates bypass : Nat}
    (support : Candidate supportInputs supportGates supportOutputs)
    (input : Valuation (supportInputs + bypass))
    (output : Fin (supportOutputs + bypass)) :
    (support.withBypass bypass).semantics input output =
      splitFin
        (fun supportOutput =>
          support.semantics
            (fun supportInput => input (Fin.castAdd bypass supportInput))
            supportOutput)
        (fun bypassIndex => input (Fin.natAdd supportInputs bypassIndex))
        output := by
  unfold Candidate.withBypass
  rw [Candidate.ofDirectWireWord_semantics]
  cases finSum_decompose output with
  | inl supportCase =>
      rcases supportCase with ⟨supportOutput, outputEqual⟩
      subst output
      unfold DirectWire.semantics DirectWireWord.eval
      unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
      rw [withBypassWord_support_source, splitFin_left]
      rw [Source.eval_renameInputs]
      exact (support.directWireWord.source supportOutput).eval_congr (fun _ => rfl)
        (fun gate => Program.eval_renameInputs support.program
          (Fin.castAdd bypass) input gate)
  | inr bypassCase =>
      rcases bypassCase with ⟨bypassIndex, outputEqual⟩
      subst output
      unfold DirectWire.semantics DirectWireWord.eval
      rw [withBypassWord_bypass_source, splitFin_right]
      rfl

/-- A concrete serial context around a replaceable support block.

`environment` computes both the support inputs and the bypass wires;
`continuation` consumes the support outputs followed by those bypass wires.
There is deliberately no arbitrary gate-subset, profile, or trusted support
field: plugging physically constructs the serial middle block. -/
structure FramedContext
    (externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates : Nat) where
  environment :
    Candidate externalInputs environmentGates (supportInputs + bypass)
  continuation :
    Candidate (supportOutputs + bypass) continuationGates outputs

/-- Plug a support candidate into its concrete environment/continuation frame. -/
def FramedContext.plug
    {externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates supportGates : Nat}
    (context : FramedContext externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates)
    (support : Candidate supportInputs supportGates supportOutputs) :
    Candidate externalInputs
      ((environmentGates + supportGates) + continuationGates) outputs :=
  (context.environment.sequential (support.withBypass bypass)).sequential
    context.continuation

theorem FramedContext.plug_size
    {externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates supportGates : Nat}
    (context : FramedContext externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates)
    (support : Candidate supportInputs supportGates supportOutputs) :
    (context.plug support).program.size =
      (context.environment.program.size + support.program.size) +
        context.continuation.program.size := by
  unfold FramedContext.plug
  rw [Candidate.sequential_size, Candidate.sequential_size,
    Candidate.withBypass_size]

/-- Pointwise semantics of the physical environment/support/continuation
    serialization used by `plug`. -/
theorem FramedContext.plug_semantics
    {externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates supportGates : Nat}
    (context : FramedContext externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates)
    (support : Candidate supportInputs supportGates supportOutputs)
    (input : Valuation externalInputs) (output : Fin outputs) :
    (context.plug support).semantics input output =
      context.continuation.semantics
        (fun joined => splitFin
          (fun supportOutput =>
            support.semantics
              (fun supportInput =>
                context.environment.semantics input
                  (Fin.castAdd bypass supportInput))
              supportOutput)
          (fun bypassIndex =>
            context.environment.semantics input
              (Fin.natAdd supportInputs bypassIndex))
          joined)
        output := by
  unfold FramedContext.plug
  rw [Candidate.sequential_semantics]
  apply context.continuation.semantics_input_congr
  intro joined
  rw [Candidate.sequential_semantics]
  exact Candidate.withBypass_semantics support
    (context.environment.semantics input) joined

/-- Semantic replacement inside a concrete frame.  The hypothesis is exactly
    direct-wire equivalence of the two support implementations; the frame
    contributes no support oracle or trusted compatibility flag. -/
theorem compatibleReplacement_framed
    {externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates leftSupportGates rightSupportGates : Nat}
    (context : FramedContext externalInputs supportInputs supportOutputs bypass outputs
      environmentGates continuationGates)
    (leftSupport : Candidate supportInputs leftSupportGates supportOutputs)
    (rightSupport : Candidate supportInputs rightSupportGates supportOutputs)
    (equivalent : Equivalent leftSupport.program leftSupport.directWireWord
      rightSupport.program rightSupport.directWireWord) :
    Equivalent (context.plug leftSupport).program
        (context.plug leftSupport).directWireWord
      (context.plug rightSupport).program
        (context.plug rightSupport).directWireWord := by
  intro input output
  change (context.plug leftSupport).semantics input output =
    (context.plug rightSupport).semantics input output
  rw [FramedContext.plug_semantics, FramedContext.plug_semantics]
  apply context.continuation.semantics_input_congr
  intro joined
  cases finSum_decompose joined with
  | inl supportCase =>
      rcases supportCase with ⟨supportOutput, joinedEqual⟩
      subst joined
      rw [splitFin_left, splitFin_left]
      exact equivalent
        (fun supportInput =>
          context.environment.semantics input
            (Fin.castAdd bypass supportInput))
        supportOutput
  | inr bypassCase =>
      rcases bypassCase with ⟨bypassIndex, joinedEqual⟩
      subst joined
      rw [splitFin_right, splitFin_right]

end DirectWire
end PNP
