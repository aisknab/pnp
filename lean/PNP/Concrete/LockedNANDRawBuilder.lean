/-
Copyright (c) 2026 PNP Labs.

Direct untyped reconstruction of the complete locked-NAND target instance.
The executable definitions in this file use only lists, natural-number
coordinates, and the six closed NAND templates from the legacy construction.
They do not call the semantic decoder, satisfiability predicate, reference
minimum, or typed global builder.
-/

import PNP.Concrete.LockedNANDReduction

/-! ### File-local typed reconstruction bridge

The legacy module intentionally keeps its assembly constructors private.
The direct raw builder needs their structure only to prove byte-for-byte
reification, so this module reconstructs the same finite typed operations
from the public candidate, program, source, and coordinate APIs.  These
definitions are proof-side only; `rawLockedInstance` remains the independent
list-and-natural-number executable below.
-/

namespace PNP.DirectWire.LockedNANDGlobalCandidates

open LockedNANDTrace

def binding2 {alpha : Type} (first second : alpha) :
    Fin 2 → alpha :=
  fun index => if index.val = 0 then first else second

def binding3 {alpha : Type} (first second third : alpha) :
    Fin 3 → alpha :=
  fun index =>
    if index.val = 0 then first
    else if index.val = 1 then second
    else third

def binding4 {alpha : Type} (first second third fourth : alpha) :
    Fin 4 → alpha :=
  fun index =>
    if index.val = 0 then first
    else if index.val = 1 then second
    else if index.val = 2 then third
    else fourth

def appendCandidateProgram
    {outerInputs innerInputs prefixGates suffixGates outputs : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (candidate : Candidate innerInputs suffixGates outputs) :
    Program outerInputs (prefixGates + suffixGates) :=
  sequentialProgram initial ⟨binding⟩ candidate.program

def appendCandidateSource
    {outerInputs innerInputs prefixGates suffixGates outputs : Nat}
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (candidate : Candidate innerInputs suffixGates outputs)
    (output : Fin outputs) :
    Source outerInputs (prefixGates + suffixGates) :=
  (candidate.directWireWord.source output).substituteInputs binding

def reconstructedAppendSourceMacro
    {inputs priorGates totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (source : Source inputs priorGates)
    (priorWithin : priorGates ≤ totalGates)
    (gate : Fin totalGates) (side : OccurrenceSide) :
    SourceMacroAppend (carrierWidth inputs totalGates) prefixGates
      (sourceMacroGateCount source) :=
  let occurrenceCoordinate := occurrenceCoordinate gate side
  let lock : Source (carrierWidth inputs totalGates) prefixGates :=
    .input (sourceLockSlot occurrenceCoordinate)
  let occurrence : Source (carrierWidth inputs totalGates) prefixGates :=
    .input (occurrenceSlot occurrenceCoordinate)
  match source with
  | .input index =>
      let sourceValue :
          Source (carrierWidth inputs totalGates) prefixGates :=
        .input (primarySlot (gates := totalGates) index)
      let binding := binding3 lock occurrence sourceValue
      { program := appendCandidateProgram initial binding equalityDirect
        check := appendCandidateSource binding equalityDirect
          ⟨7, by decide⟩ }
  | .constant false =>
      let binding := binding2 lock occurrence
      { program :=
          appendCandidateProgram initial binding constantZeroDirect
        check := appendCandidateSource binding constantZeroDirect
          ⟨2, by decide⟩ }
  | .constant true =>
      let binding := binding2 lock occurrence
      { program :=
          appendCandidateProgram initial binding constantOneDirect
        check := appendCandidateSource binding constantOneDirect
          ⟨1, by decide⟩ }
  | .gate index =>
      let sourceValue :
          Source (carrierWidth inputs totalGates) prefixGates :=
        .input
          (traceSlot (inputs := inputs)
            (Fin.castLE priorWithin index))
      let binding := binding3 lock occurrence sourceValue
      { program := appendCandidateProgram initial binding equalityDirect
        check := appendCandidateSource binding equalityDirect
          ⟨7, by decide⟩ }

/-- The stable source-macro API reduces to the file-local reconstruction. -/
theorem appendSourceMacro_reconstruction
    {inputs priorGates totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (source : Source inputs priorGates)
    (priorWithin : priorGates ≤ totalGates)
    (gate : Fin totalGates) (side : OccurrenceSide) :
    appendSourceMacro initial source priorWithin gate side =
      reconstructedAppendSourceMacro initial source priorWithin gate side := by
  rfl

def reconstructedAppendTraceMacro
    {inputs totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (gate : Fin totalGates) :
    TraceMacroAppend (carrierWidth inputs totalGates) prefixGates :=
  let leftCoordinate := occurrenceCoordinate gate .left
  let rightCoordinate := occurrenceCoordinate gate .right
  let binding : Fin 4 →
      Source (carrierWidth inputs totalGates) prefixGates :=
    binding4
      (.input (traceLockSlot (inputs := inputs) gate))
      (.input (traceSlot (inputs := inputs) gate))
      (.input (occurrenceSlot (inputs := inputs) leftCoordinate))
      (.input (occurrenceSlot (inputs := inputs) rightCoordinate))
  { program := appendCandidateProgram initial binding traceDirect
    check := appendCandidateSource binding traceDirect ⟨15, by decide⟩ }

/-- The stable trace-macro API reduces to the file-local reconstruction. -/
theorem appendTraceMacro_reconstruction
    {inputs totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (gate : Fin totalGates) :
    appendTraceMacro initial gate =
      reconstructedAppendTraceMacro initial gate := by
  rfl

structure NonemptyPrefixAssembly (tailChecks : Nat) where
  program : Program (tailChecks + 1) (2 * tailChecks)
  output : Source (tailChecks + 1) (2 * tailChecks)

def nonemptyPrefixAssembly :
    (tailChecks : Nat) → NonemptyPrefixAssembly tailChecks
  | 0 =>
      { program := .empty
        output := .input fin1Zero }
  | tailChecks + 1 =>
      let earlier := nonemptyPrefixAssembly tailChecks
      let renamedProgram := earlier.program.renameInputs Fin.succ
      let renamedOutput := earlier.output.renameInputs Fin.succ
      let newest : Source ((tailChecks + 1) + 1) (2 * tailChecks) :=
        .input ⟨0, by omega⟩
      let binding := binding2 renamedOutput newest
      { program :=
          appendCandidateProgram renamedProgram binding prefixAndDirect
        output :=
          appendCandidateSource binding prefixAndDirect ⟨1, by decide⟩ }

def finalBinding {inputs : Nat} (circuit : Circuit inputs) :
    Fin 3 → Source (carrierWidth inputs circuit.gateCount)
      (lockedBaselineCount circuit.program) :=
  binding3
    (.input (finalLockSlot inputs circuit.gateCount))
    (baselinePrefixSource circuit)
    (.input (traceSlot (inputs := inputs) circuit.outputGate))

/-- File-local candidate wrapper around the reconstructed prefix assembly. -/
def reconstructedNonemptyPrefixCandidate (tailChecks : Nat) :
    Candidate (tailChecks + 1) (2 * tailChecks) 1 :=
  let assembly := nonemptyPrefixAssembly tailChecks
  Candidate.ofDirectWireWord assembly.program
    ⟨fun _ => assembly.output⟩

/-- The public prefix candidate is propositionally identical to the
file-local reconstruction.  The induction crosses the private legacy
assembly boundary through the public candidate itself. -/
theorem nonemptyPrefixCandidate_reconstruction (tailChecks : Nat) :
    nonemptyPrefixCandidate tailChecks =
      reconstructedNonemptyPrefixCandidate tailChecks := by
  induction tailChecks with
  | zero =>
      rfl
  | succ tailChecks ih =>
      change
        (let previous := nonemptyPrefixCandidate tailChecks
         let renamedProgram := previous.program.renameInputs Fin.succ
         let renamedOutput :=
           (previous.directWireWord.source fin1Zero).renameInputs Fin.succ
         let newest : Source ((tailChecks + 1) + 1) (2 * tailChecks) :=
           .input ⟨0, by omega⟩
         let binding := binding2 renamedOutput newest
         Candidate.ofDirectWireWord
           (appendCandidateProgram renamedProgram binding prefixAndDirect)
           ⟨fun _ =>
             appendCandidateSource binding prefixAndDirect
               ⟨1, by decide⟩⟩) =
        (let previous :=
           reconstructedNonemptyPrefixCandidate tailChecks
         let renamedProgram := previous.program.renameInputs Fin.succ
         let renamedOutput :=
           (previous.directWireWord.source fin1Zero).renameInputs Fin.succ
         let newest : Source ((tailChecks + 1) + 1) (2 * tailChecks) :=
           .input ⟨0, by omega⟩
         let binding := binding2 renamedOutput newest
         Candidate.ofDirectWireWord
           (appendCandidateProgram renamedProgram binding prefixAndDirect)
           ⟨fun _ =>
             appendCandidateSource binding prefixAndDirect
               ⟨1, by decide⟩⟩)
      rw [ih]

/-- The public raw baseline program reduces to the exposed macro assembly
through the file-local generic append operation. -/
theorem rawBaselineProgram_reconstruction {inputs : Nat}
    (circuit : Circuit inputs) :
    rawBaselineProgram circuit =
      let assembly :=
        macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
      appendCandidateProgram assembly.program (macroCheckSource circuit)
        (circuitPrefixCandidate circuit) := by
  rfl

/-- The public raw baseline output reduces through the exposed ordered macro
check binding. -/
theorem rawBaselinePrefixSource_reconstruction {inputs : Nat}
    (circuit : Circuit inputs) :
    rawBaselinePrefixSource circuit =
      appendCandidateSource (macroCheckSource circuit)
        (circuitPrefixCandidate circuit) fin1Zero := by
  rfl

/-- The public full program reduces to the reconstructed final binding. -/
theorem fullProgram_reconstruction {inputs : Nat}
    (circuit : Circuit inputs) :
    fullProgram circuit =
      appendCandidateProgram (baselineProgram circuit)
        (finalBinding circuit) finalConjunctionDirect := by
  rfl

/-- The public final output source reduces to the reconstructed final
binding. -/
theorem fullCandidate_final_source_reconstruction {inputs : Nat}
    (circuit : Circuit inputs) :
    (fullCandidate circuit).directWireWord.source
        (conditionalFinalOutput
          (lockedBaselineCount circuit.program)) =
      appendCandidateSource (finalBinding circuit)
        finalConjunctionDirect fin1Zero := by
  rw [fullCandidate_final_source]
  rfl

end PNP.DirectWire.LockedNANDGlobalCandidates

namespace PNP.Concrete.LockedNAND
namespace RawBuilder

open DirectWire
open DirectWire.LockedNANDTrace

/-! ### Elaboration/reification inversion -/

/-- Successful source elaboration loses no raw syntax. -/
theorem ofSource_elaborate_eq
    {inputs gates : Nat} {raw : RawSource} {source : Source inputs gates}
    (elaborated : raw.elaborate inputs gates = some source) :
    RawSource.ofSource source = raw := by
  cases raw with
  | input index =>
      simp only [RawSource.elaborate] at elaborated
      split at elaborated
      · cases elaborated
        rfl
      · contradiction
  | constant value =>
      simp only [RawSource.elaborate] at elaborated
      cases elaborated
      rfl
  | gate index =>
      simp only [RawSource.elaborate] at elaborated
      split at elaborated
      · cases elaborated
        rfl
      · contradiction

/-- Successful gate elaboration loses neither ordered source. -/
theorem ofGate_elaborate_eq
    {inputs gates : Nat} {raw : RawGate} {gate : Gate inputs gates}
    (elaborated : raw.elaborate inputs gates = some gate) :
    RawGate.ofGate gate = raw := by
  cases raw with
  | mk left right =>
      unfold RawGate.elaborate at elaborated
      cases leftElaborated : left.elaborate inputs gates with
      | none => simp [leftElaborated] at elaborated
      | some typedLeft =>
          cases rightElaborated : right.elaborate inputs gates with
          | none => simp [leftElaborated, rightElaborated] at elaborated
          | some typedRight =>
              simp [leftElaborated, rightElaborated] at elaborated
              cases elaborated
              simp [RawGate.ofGate,
                ofSource_elaborate_eq leftElaborated,
                ofSource_elaborate_eq rightElaborated]

/-- Reifying a successfully elaborated raw suffix gives the original
intrinsic prefix followed by that exact suffix. -/
theorem rawProgramGates_eq_append_of_elaborateGatesAux
    {inputs gates : Nat} (program : Program inputs gates)
    (rawGates : List RawGate) (packed : PackedProgram inputs)
    (elaborated : elaborateGatesAux program rawGates = some packed) :
    rawProgramGates packed.program =
      rawProgramGates program ++ rawGates := by
  induction rawGates generalizing gates program with
  | nil =>
      simp only [elaborateGatesAux] at elaborated
      cases elaborated
      simp
  | cons rawGate rest ih =>
      simp only [elaborateGatesAux] at elaborated
      cases gateElaborated : rawGate.elaborate inputs gates with
      | none =>
          rw [gateElaborated] at elaborated
          contradiction
      | some gate =>
          rw [gateElaborated] at elaborated
          have tail :=
            ih (program := Program.snoc program gate) elaborated
          rw [tail, rawProgramGates]
          simp only [List.append_assoc, List.singleton_append]
          rw [ofGate_elaborate_eq gateElaborated]

/-- Reifying a successfully elaborated raw gate list is exactly the original
list. -/
theorem rawProgramGates_eq_of_elaborateGates
    {inputs : Nat} (rawGates : List RawGate) (packed : PackedProgram inputs)
    (elaborated : elaborateGates inputs rawGates = some packed) :
    rawProgramGates packed.program = rawGates := by
  have full :=
    rawProgramGates_eq_append_of_elaborateGatesAux
      (Program.empty : Program inputs 0) rawGates packed elaborated
  change rawProgramGates packed.program = [] ++ rawGates at full
  simpa only [List.nil_append] using full

/-- Every normalized raw circuit names an actual gate as its output. -/
theorem normalize_output_isGate (raw : RawCircuit) :
    ∃ index, raw.normalize.output = .gate index := by
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index => exact ⟨index, rfl⟩
      | input index => exact ⟨gates.length + 1, rfl⟩
      | constant value =>
          cases value <;> exact ⟨gates.length, rfl⟩

/-- A gate-output raw circuit is exactly recovered after successful intrinsic
elaboration and reification. -/
theorem ofCircuit_eq_of_gate_output
    (raw : RawCircuit) (index : Nat)
    (output : raw.output = .gate index)
    (packed : PackedCircuit)
    (elaborated : raw.elaborate = some packed) :
    RawCircuit.ofCircuit packed.circuit = raw := by
  cases raw with
  | mk inputs gates rawOutput =>
      simp only at output
      subst rawOutput
      unfold RawCircuit.elaborate at elaborated
      simp only [RawCircuit.normalize] at elaborated
      cases gatesElaborated : elaborateGates inputs gates with
      | none =>
          rw [gatesElaborated] at elaborated
          contradiction
      | some packedProgram =>
          rw [gatesElaborated] at elaborated
          by_cases valid : index < packedProgram.gateCount
          · simp [RawSource.elaborate, valid] at elaborated
            cases elaborated
            simp only [RawCircuit.ofCircuit]
            rw [rawProgramGates_eq_of_elaborateGates
              gates packedProgram gatesElaborated]
          · simp [RawSource.elaborate, valid] at elaborated

/-- Central normalization round trip used by the raw/typed construction
bridge. -/
theorem ofCircuit_eq_normalize_of_elaborate
    (raw : RawCircuit) (packed : PackedCircuit)
    (elaborated : raw.elaborate = some packed) :
    RawCircuit.ofCircuit packed.circuit = raw.normalize := by
  have normalizedElaborated :
      raw.normalize.elaborate = some packed := by
    rw [RawCircuit.elaborate_normalize]
    exact elaborated
  rcases normalize_output_isGate raw with ⟨index, output⟩
  exact ofCircuit_eq_of_gate_output raw.normalize index output packed
    normalizedElaborated

/-! ### Closed raw templates -/

/-- A finite raw binding, totalized only outside its declared fixed arity. -/
def listBinding (sources : List RawSource) (index : Nat) : RawSource :=
  sources.getD index (.constant false)

def rawBinding2 (first second : RawSource) (index : Nat) : RawSource :=
  if index = 0 then first
  else if index = 1 then second
  else .constant false

def rawBinding3 (first second third : RawSource) (index : Nat) : RawSource :=
  if index = 0 then first
  else if index = 1 then second
  else if index = 2 then third
  else .constant false

def rawBinding4 (first second third fourth : RawSource)
    (index : Nat) : RawSource :=
  if index = 0 then first
  else if index = 1 then second
  else if index = 2 then third
  else if index = 3 then fourth
  else .constant false

/-- Replace a template input by its external binding and shift every
template-local gate by the length of the already emitted prefix. -/
def instantiateSource (offset : Nat) (binding : Nat → RawSource) :
    RawSource → RawSource
  | .input index => binding index
  | .constant value => .constant value
  | .gate index => .gate (offset + index)

def instantiateGate (offset : Nat) (binding : Nat → RawSource)
    (gate : RawGate) : RawGate :=
  { left := instantiateSource offset binding gate.left
    right := instantiateSource offset binding gate.right }

/-- Append one closed template in topological order. -/
def appendTemplate (gatePrefix : List RawGate) (binding : Nat → RawSource)
    (template : List RawGate) : List RawGate :=
  gatePrefix ++ template.map (instantiateGate gatePrefix.length binding)

theorem rawProgramGates_length {inputs gates : Nat}
    (program : Program inputs gates) :
    (rawProgramGates program).length = gates := by
  induction program with
  | empty => rfl
  | @snoc gates initial gate ih =>
      simp only [rawProgramGates, List.length_append, List.length_cons,
        List.length_nil, ih]

theorem ofSource_weakenGates {inputs gates : Nat}
    (source : Source inputs gates) (extra : Nat) :
    RawSource.ofSource (source.weakenGates extra) =
      RawSource.ofSource source := by
  cases source <;> rfl

/-- Reify a finite typed binding as a total natural-number binding. -/
def rawFinBinding
    {innerInputs outerInputs prefixGates : Nat}
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (index : Nat) : RawSource :=
  if valid : index < innerInputs then
    RawSource.ofSource (binding ⟨index, valid⟩)
  else
    .constant false

theorem ofSource_substituteInputs
    {innerInputs outerInputs prefixGates suffixGates : Nat}
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (source : Source innerInputs suffixGates) :
    RawSource.ofSource (source.substituteInputs binding) =
      instantiateSource prefixGates (rawFinBinding binding)
        (RawSource.ofSource source) := by
  cases source with
  | input index =>
      change
        RawSource.ofSource ((binding index).weakenGates suffixGates) =
          rawFinBinding binding index.val
      rw [ofSource_weakenGates]
      simp [rawFinBinding, index.isLt]
  | constant value => rfl
  | gate index => rfl

theorem ofGate_substituteInputs
    {innerInputs outerInputs prefixGates suffixGates : Nat}
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (gate : Gate innerInputs suffixGates) :
    RawGate.ofGate (gate.substituteInputs binding) =
      instantiateGate prefixGates (rawFinBinding binding)
        (RawGate.ofGate gate) := by
  cases gate with
  | mk left right =>
      simp only [Gate.substituteInputs, RawGate.ofGate, instantiateGate]
      rw [ofSource_substituteInputs, ofSource_substituteInputs]

/-- Reification commutes exactly with typed block append. -/
theorem rawProgramGates_appendSubstituted
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (suffix : Program innerInputs suffixGates) :
    rawProgramGates (initial.appendSubstituted binding suffix) =
      appendTemplate (rawProgramGates initial) (rawFinBinding binding)
        (rawProgramGates suffix) := by
  induction suffix with
  | empty =>
      simp [Program.appendSubstituted, rawProgramGates, appendTemplate]
  | @snoc gates suffix gate ih =>
      simp only [Program.appendSubstituted, rawProgramGates]
      rw [ih, ofGate_substituteInputs]
      unfold appendTemplate
      rw [List.map_append]
      simp only [List.map_cons, List.map_nil, List.append_assoc]
      rw [rawProgramGates_length initial]

theorem rawFinBinding_binding2
    {outerInputs prefixGates : Nat}
    (first second : Source outerInputs prefixGates) :
    rawFinBinding
        (DirectWire.LockedNANDGlobalCandidates.binding2 first second) =
      rawBinding2 (RawSource.ofSource first) (RawSource.ofSource second) := by
  funext index
  by_cases valid : index < 2
  · have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;>
      simp [rawFinBinding, rawBinding2,
        DirectWire.LockedNANDGlobalCandidates.binding2]
  · have notZero : index ≠ 0 := by omega
    have notOne : index ≠ 1 := by omega
    simp [rawFinBinding, rawBinding2, valid, notZero, notOne]

theorem rawFinBinding_binding3
    {outerInputs prefixGates : Nat}
    (first second third : Source outerInputs prefixGates) :
    rawFinBinding
        (DirectWire.LockedNANDGlobalCandidates.binding3
          first second third) =
      rawBinding3 (RawSource.ofSource first) (RawSource.ofSource second)
        (RawSource.ofSource third) := by
  funext index
  by_cases valid : index < 3
  · have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases cases with rfl | rfl | rfl <;>
      simp [rawFinBinding, rawBinding3,
        DirectWire.LockedNANDGlobalCandidates.binding3]
  · have notZero : index ≠ 0 := by omega
    have notOne : index ≠ 1 := by omega
    have notTwo : index ≠ 2 := by omega
    simp [rawFinBinding, rawBinding3, valid, notZero, notOne, notTwo]

theorem rawFinBinding_binding4
    {outerInputs prefixGates : Nat}
    (first second third fourth : Source outerInputs prefixGates) :
    rawFinBinding
        (DirectWire.LockedNANDGlobalCandidates.binding4
          first second third fourth) =
      rawBinding4 (RawSource.ofSource first) (RawSource.ofSource second)
        (RawSource.ofSource third) (RawSource.ofSource fourth) := by
  funext index
  by_cases valid : index < 4
  · have cases :
        index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [rawFinBinding, rawBinding4,
        DirectWire.LockedNANDGlobalCandidates.binding4]
  · have notZero : index ≠ 0 := by omega
    have notOne : index ≠ 1 := by omega
    have notTwo : index ≠ 2 := by omega
    have notThree : index ≠ 3 := by omega
    simp [rawFinBinding, rawBinding4, valid, notZero, notOne, notTwo,
      notThree]

/-- Exact raw gate list of the public typed block append operation. -/
theorem rawProgramGates_appendCandidateProgram
    {outerInputs innerInputs prefixGates suffixGates outputs : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (candidate : Candidate innerInputs suffixGates outputs) :
    rawProgramGates
        (DirectWire.LockedNANDGlobalCandidates.appendCandidateProgram
          initial binding candidate) =
      appendTemplate (rawProgramGates initial) (rawFinBinding binding)
        (rawProgramGates candidate.program) := by
  unfold DirectWire.LockedNANDGlobalCandidates.appendCandidateProgram
    sequentialProgram
  exact rawProgramGates_appendSubstituted initial binding candidate.program

/-- Exact raw source of the public typed block-output transport. -/
theorem ofSource_appendCandidateSource
    {outerInputs innerInputs prefixGates suffixGates outputs : Nat}
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (candidate : Candidate innerInputs suffixGates outputs)
    (output : Fin outputs) :
    RawSource.ofSource
        (DirectWire.LockedNANDGlobalCandidates.appendCandidateSource
          binding candidate output) =
      instantiateSource prefixGates (rawFinBinding binding)
        (RawSource.ofSource (candidate.directWireWord.source output)) := by
  unfold DirectWire.LockedNANDGlobalCandidates.appendCandidateSource
  exact ofSource_substituteInputs binding
    (candidate.directWireWord.source output)

/-- Closed blocks in this construction expose each local gate directly. -/
theorem rawProgramGates_appendExposeAllGates
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (suffix : Program innerInputs suffixGates) :
    rawProgramGates
        (DirectWire.LockedNANDGlobalCandidates.appendCandidateProgram
          initial binding (exposeAllGates suffix)) =
      appendTemplate (rawProgramGates initial) (rawFinBinding binding)
        (rawProgramGates suffix) := by
  simpa only [exposeAllGates_program] using
    rawProgramGates_appendCandidateProgram initial binding
      (exposeAllGates suffix)

theorem ofSource_appendExposeAllGates
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (suffix : Program innerInputs suffixGates)
    (output : Fin suffixGates) :
    RawSource.ofSource
        (DirectWire.LockedNANDGlobalCandidates.appendCandidateSource
          binding (exposeAllGates suffix) output) =
      .gate (prefixGates + output.val) := by
  rw [ofSource_appendCandidateSource, exposeAllGates_source]
  rfl

/-- The exact ten-gate equality macro from the legacy construction. -/
def equalityTemplate : List RawGate :=
  rawProgramGates equalityDirectProgram

/-- The exact three-gate locked-false macro. -/
def constantZeroTemplate : List RawGate :=
  rawProgramGates constantZeroDirectProgram

/-- The exact two-gate locked-true macro. -/
def constantOneTemplate : List RawGate :=
  rawProgramGates constantOneDirectProgram

/-- The exact eighteen-gate trace macro. -/
def traceTemplate : List RawGate :=
  rawProgramGates traceDirectProgram

/-- The exact two-gate prefix-conjunction node. -/
def prefixTemplate : List RawGate :=
  rawProgramGates prefixAndDirectProgram

/-- The exact final four-gate conjunction. -/
def finalTemplate : List RawGate :=
  rawProgramGates finalConjunctionDirectProgram

theorem equalityTemplate_length : equalityTemplate.length = 10 := by
  rfl

theorem constantZeroTemplate_length : constantZeroTemplate.length = 3 := by
  rfl

theorem constantOneTemplate_length : constantOneTemplate.length = 2 := by
  rfl

theorem traceTemplate_length : traceTemplate.length = 18 := by
  rfl

theorem prefixTemplate_length : prefixTemplate.length = 2 := by
  rfl

theorem finalTemplate_length : finalTemplate.length = 4 := by
  rfl

/-! ### Numeric carrier coordinates -/

def primaryCoordinate (_inputs _gates index : Nat) : Nat :=
  index

def traceCoordinate (inputs _gates index : Nat) : Nat :=
  inputs + index

def occurrenceCoordinate (inputs gates gate side : Nat) : Nat :=
  inputs + gates + (2 * gate + side)

def sourceLockCoordinate (inputs gates gate side : Nat) : Nat :=
  inputs + 3 * gates + (2 * gate + side)

def traceLockCoordinate (inputs gates gate : Nat) : Nat :=
  inputs + 5 * gates + gate

def finalLockCoordinate (inputs gates : Nat) : Nat :=
  inputs + 6 * gates

def sourceValueCoordinate (inputs gates : Nat) : RawSource → RawSource
  | .input index => .input (primaryCoordinate inputs gates index)
  | .constant value => .constant value
  | .gate index => .input (traceCoordinate inputs gates index)

/-! ### Source and trace macro traversal -/

structure MacroAssembly where
  gates : List RawGate
  checks : List RawSource
deriving BEq, DecidableEq, Repr

/-- Fieldwise equality for raw macro assemblies. -/
theorem MacroAssembly.ext
    (left right : MacroAssembly)
    (gates : left.gates = right.gates)
    (checks : left.checks = right.checks) :
    left = right := by
  cases left
  cases right
  simp_all

def emptyAssembly : MacroAssembly :=
  { gates := []
    checks := [] }

/-- Exact number of gates selected by one raw source occurrence. -/
def sourceMacroGateCount : RawSource → Nat
  | .input _ => 10
  | .constant false => 3
  | .constant true => 2
  | .gate _ => 10

/-- Append the selected source macro for one ordered source occurrence. -/
def appendSourceMacro (inputs totalGates gate side : Nat)
    (assembly : MacroAssembly) (source : RawSource) : MacroAssembly :=
  let lock : RawSource :=
    .input (sourceLockCoordinate inputs totalGates gate side)
  let occurrence : RawSource :=
    .input (occurrenceCoordinate inputs totalGates gate side)
  let offset := assembly.gates.length
  match source with
  | .input index =>
      { gates := appendTemplate assembly.gates
          (rawBinding3 lock occurrence
            (sourceValueCoordinate inputs totalGates (.input index)))
          equalityTemplate
        checks := assembly.checks ++ [.gate (offset + 7)] }
  | .constant false =>
      { gates := appendTemplate assembly.gates
          (rawBinding2 lock occurrence) constantZeroTemplate
        checks := assembly.checks ++ [.gate (offset + 2)] }
  | .constant true =>
      { gates := appendTemplate assembly.gates
          (rawBinding2 lock occurrence) constantOneTemplate
        checks := assembly.checks ++ [.gate (offset + 1)] }
  | .gate index =>
      { gates := appendTemplate assembly.gates
          (rawBinding3 lock occurrence
            (sourceValueCoordinate inputs totalGates (.gate index)))
          equalityTemplate
        checks := assembly.checks ++ [.gate (offset + 7)] }

/-- The direct source selector adds exactly the gate count advertised by its
raw source tag. -/
theorem appendSourceMacro_gates_length
    (inputs totalGates gate side : Nat)
    (assembly : MacroAssembly) (source : RawSource) :
    (appendSourceMacro inputs totalGates gate side assembly source).gates.length =
      assembly.gates.length + sourceMacroGateCount source := by
  cases source with
  | input index =>
      simp [appendSourceMacro, appendTemplate, sourceMacroGateCount,
        equalityTemplate_length]
  | constant value =>
      cases value <;>
        simp [appendSourceMacro, appendTemplate, sourceMacroGateCount,
          constantZeroTemplate_length, constantOneTemplate_length]
  | gate index =>
      simp [appendSourceMacro, appendTemplate, sourceMacroGateCount,
        equalityTemplate_length]

/-- Append the fixed trace macro for one source gate. -/
def appendTraceMacro (inputs totalGates gate : Nat)
    (assembly : MacroAssembly) : MacroAssembly :=
  let offset := assembly.gates.length
  { gates := appendTemplate assembly.gates
      (rawBinding4
        (.input (traceLockCoordinate inputs totalGates gate))
        (.input (traceCoordinate inputs totalGates gate))
        (.input (occurrenceCoordinate inputs totalGates gate 0))
        (.input (occurrenceCoordinate inputs totalGates gate 1)))
      traceTemplate
    checks := assembly.checks ++ [.gate (offset + 15)] }

/-- The trace selector always adds its fixed eighteen-gate template. -/
theorem appendTraceMacro_gates_length
    (inputs totalGates gate : Nat) (assembly : MacroAssembly) :
    (appendTraceMacro inputs totalGates gate assembly).gates.length =
      assembly.gates.length + 18 := by
  simp [appendTraceMacro, appendTemplate, traceTemplate_length]

theorem appendSourceMacro_checks_length
    (inputs totalGates gate side : Nat)
    (assembly : MacroAssembly) (source : RawSource) :
    (appendSourceMacro inputs totalGates gate side assembly source).checks.length =
      assembly.checks.length + 1 := by
  cases source with
  | input index => simp [appendSourceMacro]
  | constant value =>
      cases value <;> simp [appendSourceMacro]
  | gate index => simp [appendSourceMacro]

theorem appendTraceMacro_checks_length
    (inputs totalGates gate : Nat) (assembly : MacroAssembly) :
    (appendTraceMacro inputs totalGates gate assembly).checks.length =
      assembly.checks.length + 1 := by
  simp [appendTraceMacro]

/-- One raw selected-source append is the exact reification of the public
typed selected-source append. -/
theorem appendSourceMacro_reifies
    {inputs priorGates totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (source : Source inputs priorGates)
    (priorWithin : priorGates ≤ totalGates)
    (gate : Fin totalGates) (side : OccurrenceSide)
    (checkPrefix : List RawSource) :
    let typed :=
      DirectWire.LockedNANDGlobalCandidates.appendSourceMacro
        initial source priorWithin gate side
    let raw :=
      appendSourceMacro inputs totalGates gate.val side.offset
        { gates := rawProgramGates initial
          checks := checkPrefix }
        (RawSource.ofSource source)
    raw.gates = rawProgramGates typed.program ∧
      raw.checks =
        checkPrefix ++ [RawSource.ofSource typed.check] := by
  rw [
    DirectWire.LockedNANDGlobalCandidates.appendSourceMacro_reconstruction]
  cases source with
  | input index =>
      cases side <;>
        dsimp [DirectWire.LockedNANDGlobalCandidates.reconstructedAppendSourceMacro,
          appendSourceMacro, sourceValueCoordinate, primaryCoordinate,
          occurrenceCoordinate, sourceLockCoordinate,
          DirectWire.LockedNANDTrace.occurrenceCoordinate,
          DirectWire.LockedNANDTrace.primarySlot,
          DirectWire.LockedNANDTrace.occurrenceSlot,
          DirectWire.LockedNANDTrace.sourceLockSlot,
          equalityTemplate, OccurrenceSide.offset]
      all_goals
        rw [rawProgramGates_appendCandidateProgram,
          ofSource_appendCandidateSource, rawFinBinding_binding3]
        simp only [
          DirectWire.LockedNANDGlobalCandidates.sourceMacroGateCount,
          RawSource.ofSource]
        constructor
        · rfl
        · rw [equalityDirect_output_source,
            rawProgramGates_length]
          rfl
  | constant value =>
      cases value <;> cases side <;>
        dsimp [DirectWire.LockedNANDGlobalCandidates.reconstructedAppendSourceMacro,
          appendSourceMacro, occurrenceCoordinate, sourceLockCoordinate,
          DirectWire.LockedNANDTrace.occurrenceCoordinate,
          DirectWire.LockedNANDTrace.occurrenceSlot,
          DirectWire.LockedNANDTrace.sourceLockSlot,
          constantZeroTemplate, constantOneTemplate,
          OccurrenceSide.offset]
      all_goals
        rw [rawProgramGates_appendCandidateProgram,
          ofSource_appendCandidateSource, rawFinBinding_binding2]
        simp only [
          DirectWire.LockedNANDGlobalCandidates.sourceMacroGateCount,
          RawSource.ofSource]
        constructor
        · rfl
        · first
          | rw [constantZeroDirect_output_source,
              rawProgramGates_length]
            rfl
          | rw [constantOneDirect_output_source,
              rawProgramGates_length]
            rfl
  | gate index =>
      cases side <;>
        dsimp [DirectWire.LockedNANDGlobalCandidates.reconstructedAppendSourceMacro,
          appendSourceMacro, sourceValueCoordinate, traceCoordinate,
          occurrenceCoordinate, sourceLockCoordinate,
          DirectWire.LockedNANDTrace.occurrenceCoordinate,
          DirectWire.LockedNANDTrace.traceSlot,
          DirectWire.LockedNANDTrace.occurrenceSlot,
          DirectWire.LockedNANDTrace.sourceLockSlot,
          equalityTemplate, OccurrenceSide.offset]
      all_goals
        rw [rawProgramGates_appendCandidateProgram,
          ofSource_appendCandidateSource, rawFinBinding_binding3]
        simp only [
          DirectWire.LockedNANDGlobalCandidates.sourceMacroGateCount,
          RawSource.ofSource]
        constructor
        · rfl
        · rw [equalityDirect_output_source,
            rawProgramGates_length]
          rfl

/-- One raw trace append is the exact reification of the public typed trace
append. -/
theorem appendTraceMacro_reifies
    {inputs totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (gate : Fin totalGates) (checkPrefix : List RawSource) :
    let typed :=
      DirectWire.LockedNANDGlobalCandidates.appendTraceMacro initial gate
    let raw :=
      appendTraceMacro inputs totalGates gate.val
        { gates := rawProgramGates initial
          checks := checkPrefix }
    raw.gates = rawProgramGates typed.program ∧
      raw.checks =
        checkPrefix ++ [RawSource.ofSource typed.check] := by
  rw [
    DirectWire.LockedNANDGlobalCandidates.appendTraceMacro_reconstruction]
  dsimp [DirectWire.LockedNANDGlobalCandidates.reconstructedAppendTraceMacro,
    appendTraceMacro, traceLockCoordinate, traceCoordinate,
    occurrenceCoordinate,
    DirectWire.LockedNANDTrace.occurrenceCoordinate,
    DirectWire.LockedNANDTrace.traceLockSlot,
    DirectWire.LockedNANDTrace.traceSlot,
    DirectWire.LockedNANDTrace.occurrenceSlot,
    traceTemplate, OccurrenceSide.offset]
  constructor
  · rw [rawProgramGates_appendCandidateProgram,
      rawFinBinding_binding4]
    rfl
  · rw [ofSource_appendCandidateSource,
      rawFinBinding_binding4, traceDirect_output_source,
      rawProgramGates_length]
    rfl

/-- Emit left-source, right-source, and trace blocks for every gate in source
order. -/
def assembleGates (inputs totalGates : Nat) :
    Nat → MacroAssembly → List RawGate → MacroAssembly
  | _, assembly, [] => assembly
  | gate, assembly, sourceGate :: rest =>
      let left :=
        appendSourceMacro inputs totalGates gate 0 assembly sourceGate.left
      let right :=
        appendSourceMacro inputs totalGates gate 1 left sourceGate.right
      let trace := appendTraceMacro inputs totalGates gate right
      assembleGates inputs totalGates (gate + 1) trace rest

/-- Exact data-dependent macro cost of one raw NAND gate. -/
def gateMacroGateCount (gate : RawGate) : Nat :=
  sourceMacroGateCount gate.left +
    sourceMacroGateCount gate.right + 18

/-- Exact macro cost of a raw gate word in source order. -/
def gateListMacroGateCount : List RawGate → Nat
  | [] => 0
  | gate :: rest => gateMacroGateCount gate + gateListMacroGateCount rest

/-- Forward macro traversal adds exactly the sum of the selected closed
templates; no semantic well-formedness premise is needed. -/
theorem assembleGates_gates_length
    (inputs totalGates gate : Nat) (assembly : MacroAssembly)
    (sourceGates : List RawGate) :
    (assembleGates inputs totalGates gate assembly sourceGates).gates.length =
      assembly.gates.length + gateListMacroGateCount sourceGates := by
  induction sourceGates generalizing gate assembly with
  | nil =>
      simp [assembleGates, gateListMacroGateCount]
  | cons sourceGate rest ih =>
      simp only [assembleGates]
      rw [ih, appendTraceMacro_gates_length,
        appendSourceMacro_gates_length,
        appendSourceMacro_gates_length]
      simp only [gateListMacroGateCount, gateMacroGateCount]
      omega

theorem assembleGates_checks_length
    (inputs totalGates gate : Nat) (assembly : MacroAssembly)
    (sourceGates : List RawGate) :
    (assembleGates inputs totalGates gate assembly sourceGates).checks.length =
      assembly.checks.length + 3 * sourceGates.length := by
  induction sourceGates generalizing gate assembly with
  | nil =>
      simp [assembleGates]
  | cons sourceGate rest ih =>
      simp only [assembleGates]
      rw [ih, appendTraceMacro_checks_length,
        appendSourceMacro_checks_length,
        appendSourceMacro_checks_length]
      simp only [List.length_cons]
      omega

theorem assembleGates_append
    (inputs totalGates gate : Nat) (assembly : MacroAssembly)
    (first second : List RawGate) :
    assembleGates inputs totalGates gate assembly (first ++ second) =
      assembleGates inputs totalGates (gate + first.length)
        (assembleGates inputs totalGates gate assembly first) second := by
  induction first generalizing gate assembly with
  | nil =>
      simp [assembleGates]
  | cons sourceGate rest ih =>
      simp only [List.cons_append, List.length_cons, assembleGates]
      rw [ih]
      have nextGate :
          (gate + 1) + rest.length = gate + (rest.length + 1) := by
        omega
      rw [nextGate]

theorem map_ofSource_weakenGates
    {inputs gates : Nat} (sources : List (Source inputs gates))
    (extra : Nat) :
    (sources.map (fun source => source.weakenGates extra)).map
        RawSource.ofSource =
      sources.map RawSource.ofSource := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
      simp [ofSource_weakenGates, ih]

theorem list_ofFn_get_map
    {alpha beta : Type} (items : List alpha) (mapValue : alpha → beta) :
    List.ofFn (fun index : Fin items.length =>
      mapValue (items.get index)) =
        items.map mapValue := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.ofFn_succ]
      simp only [List.map_cons]
      congr

theorem list_ofFn_get_cast_map
    {alpha beta : Type} (items : List alpha) (count : Nat)
    (lengthEqual : items.length = count) (mapValue : alpha → beta) :
    List.ofFn (fun index : Fin count =>
      mapValue (items.get (Fin.cast lengthEqual.symm index))) =
        items.map mapValue := by
  cases lengthEqual
  exact list_ofFn_get_map items mapValue

/-- Substituting after a typed input rename composes the two input maps. -/
theorem Source.substituteInputs_renameInputs
    {fromInputs toInputs outerInputs prefixGates gates : Nat}
    (source : Source fromInputs gates)
    (rename : Fin fromInputs → Fin toInputs)
    (binding : Fin toInputs → Source outerInputs prefixGates) :
    (source.renameInputs rename).substituteInputs binding =
      source.substituteInputs (fun index => binding (rename index)) := by
  cases source <;> rfl

/-- Gate substitution obeys the same input-map composition law. -/
theorem Gate.substituteInputs_renameInputs
    {fromInputs toInputs outerInputs prefixGates gates : Nat}
    (gate : Gate fromInputs gates)
    (rename : Fin fromInputs → Fin toInputs)
    (binding : Fin toInputs → Source outerInputs prefixGates) :
    (gate.renameInputs rename).substituteInputs binding =
      gate.substituteInputs (fun index => binding (rename index)) := by
  cases gate with
  | mk left right =>
      simp only [Gate.renameInputs, Gate.substituteInputs]
      rw [Source.substituteInputs_renameInputs,
        Source.substituteInputs_renameInputs]

/-- Program append after input renaming is append with the composed
binding. -/
theorem Program.appendSubstituted_renameInputs
    {fromInputs toInputs outerInputs prefixGates gates : Nat}
    (initial : Program outerInputs prefixGates)
    (program : Program fromInputs gates)
    (rename : Fin fromInputs → Fin toInputs)
    (binding : Fin toInputs → Source outerInputs prefixGates) :
    initial.appendSubstituted binding (program.renameInputs rename) =
      initial.appendSubstituted (fun index => binding (rename index))
        program := by
  induction program with
  | empty => rfl
  | @snoc gates earlier gate ih =>
      simp only [Program.renameInputs, Program.appendSubstituted]
      rw [ih, Gate.substituteInputs_renameInputs]

/-- Appending a renamed template at the raw boundary is the same as using
the composed typed binding directly. -/
theorem appendTemplate_renameInputs
    {fromInputs toInputs outerInputs prefixGates gates : Nat}
    (initial : Program outerInputs prefixGates)
    (program : Program fromInputs gates)
    (rename : Fin fromInputs → Fin toInputs)
    (binding : Fin toInputs → Source outerInputs prefixGates) :
    appendTemplate (rawProgramGates initial) (rawFinBinding binding)
        (rawProgramGates (program.renameInputs rename)) =
      appendTemplate (rawProgramGates initial)
        (rawFinBinding fun index => binding (rename index))
        (rawProgramGates program) := by
  rw [← rawProgramGates_appendSubstituted,
    Program.appendSubstituted_renameInputs,
    rawProgramGates_appendSubstituted]

/-- Raw source instantiation after input renaming uses the composed typed
binding. -/
theorem instantiateSource_ofSource_renameInputs
    {fromInputs toInputs outerInputs prefixGates gates : Nat}
    (source : Source fromInputs gates)
    (rename : Fin fromInputs → Fin toInputs)
    (binding : Fin toInputs → Source outerInputs prefixGates) :
    instantiateSource prefixGates (rawFinBinding binding)
        (RawSource.ofSource (source.renameInputs rename)) =
      instantiateSource prefixGates
        (rawFinBinding fun index => binding (rename index))
        (RawSource.ofSource source) := by
  rw [← ofSource_substituteInputs,
    Source.substituteInputs_renameInputs,
    ofSource_substituteInputs]

/-- Reifying a finite binding commutes with one outer substitution. -/
theorem instantiateSource_rawFinBinding
    {innerInputs middleInputs outerInputs prefixGates suffixGates : Nat}
    (outerBinding :
      Fin middleInputs → Source outerInputs prefixGates)
    (innerBinding :
      Fin innerInputs → Source middleInputs suffixGates)
    (index : Nat) :
    instantiateSource prefixGates (rawFinBinding outerBinding)
        (rawFinBinding innerBinding index) =
      rawFinBinding
        (fun inner => (innerBinding inner).substituteInputs outerBinding)
        index := by
  by_cases valid : index < innerInputs
  · have substituted :=
      ofSource_substituteInputs outerBinding
        (innerBinding ⟨index, valid⟩)
    simpa [rawFinBinding, valid] using substituted.symm
  · simp [rawFinBinding, valid, instantiateSource]

/-- Nested raw source instantiation composes offsets and bindings. -/
theorem instantiateSource_instantiateSource
    (outerOffset innerOffset : Nat)
    (outerBinding innerBinding : Nat → RawSource)
    (source : RawSource) :
    instantiateSource outerOffset outerBinding
        (instantiateSource innerOffset innerBinding source) =
      instantiateSource (outerOffset + innerOffset)
        (fun index =>
          instantiateSource outerOffset outerBinding
            (innerBinding index))
        source := by
  cases source <;> simp [instantiateSource, Nat.add_assoc]

/-- Nested raw gate instantiation obeys the source composition law. -/
theorem instantiateGate_instantiateGate
    (outerOffset innerOffset : Nat)
    (outerBinding innerBinding : Nat → RawSource)
    (gate : RawGate) :
    instantiateGate outerOffset outerBinding
        (instantiateGate innerOffset innerBinding gate) =
      instantiateGate (outerOffset + innerOffset)
        (fun index =>
          instantiateSource outerOffset outerBinding
            (innerBinding index))
        gate := by
  cases gate with
  | mk left right =>
      simp only [instantiateGate]
      rw [instantiateSource_instantiateSource,
        instantiateSource_instantiateSource]

/-- Raw template append is associative when the later input binding is
substituted through the earlier one. -/
theorem appendTemplate_appendTemplate
    (gatePrefix middleGates suffixGates : List RawGate)
    (outerBinding innerBinding : Nat → RawSource) :
    appendTemplate gatePrefix outerBinding
        (appendTemplate middleGates innerBinding suffixGates) =
      appendTemplate
        (appendTemplate gatePrefix outerBinding middleGates)
        (fun index =>
          instantiateSource gatePrefix.length outerBinding
            (innerBinding index))
        suffixGates := by
  unfold appendTemplate
  rw [List.map_append, List.map_map]
  simp only [List.length_append, List.length_map, List.append_assoc]
  have mapped :
      suffixGates.map
          (instantiateGate gatePrefix.length outerBinding ∘
            instantiateGate middleGates.length innerBinding) =
        suffixGates.map
          (instantiateGate (gatePrefix.length + middleGates.length)
            fun index =>
              instantiateSource gatePrefix.length outerBinding
                (innerBinding index)) := by
    apply List.map_congr_left
    intro gate member
    exact instantiateGate_instantiateGate
      gatePrefix.length middleGates.length outerBinding innerBinding gate
  exact congrArg (fun rest => gatePrefix ++ rest)
    (congrArg
      (fun tail =>
        middleGates.map
            (instantiateGate gatePrefix.length outerBinding) ++ tail)
      mapped)

def macroAssembly (circuit : RawCircuit) : MacroAssembly :=
  assembleGates circuit.inputCount circuit.gates.length 0 emptyAssembly
    circuit.gates

/-- The complete macro prefix has the exact data-dependent gate count. -/
theorem macroAssembly_gates_length (circuit : RawCircuit) :
    (macroAssembly circuit).gates.length =
      gateListMacroGateCount circuit.gates := by
  rw [macroAssembly, assembleGates_gates_length]
  simp [emptyAssembly]

/-- Every raw NAND gate contributes its left, right, and trace check. -/
theorem macroAssembly_checks_length (circuit : RawCircuit) :
    (macroAssembly circuit).checks.length =
      3 * circuit.gates.length := by
  rw [macroAssembly, assembleGates_checks_length]
  simp [emptyAssembly]

/-- Forward raw macro traversal exactly reifies the typed global macro
assembly, including the three checks per source gate. -/
theorem macroAssembly_reifies
    {inputs gates totalGates : Nat}
    (program : Program inputs gates) (within : gates ≤ totalGates) :
    let typed :=
      DirectWire.LockedNANDGlobalCandidates.macroAssembly program within
    let raw :=
      assembleGates inputs totalGates 0 emptyAssembly
        (rawProgramGates program)
    raw.gates = rawProgramGates typed.program ∧
      raw.checks = typed.checks.map RawSource.ofSource := by
  induction program with
  | empty =>
      change
        ([] : List RawGate) = rawProgramGates Program.empty ∧
          ([] : List RawSource) = []
      exact ⟨rfl, rfl⟩
  | @snoc gates initial gate ih =>
      let earlierWithin : gates ≤ totalGates :=
        Nat.le_trans (Nat.le_succ gates) within
      let coordinate : Fin totalGates :=
        Fin.castLE within (Fin.last gates)
      let earlier :=
        DirectWire.LockedNANDGlobalCandidates.macroAssembly
          initial earlierWithin
      let left :=
        DirectWire.LockedNANDGlobalCandidates.appendSourceMacro
          earlier.program gate.left earlierWithin coordinate .left
      let right :=
        DirectWire.LockedNANDGlobalCandidates.appendSourceMacro
          left.program gate.right earlierWithin coordinate .right
      let trace :=
        DirectWire.LockedNANDGlobalCandidates.appendTraceMacro
          right.program coordinate
      let rawEarlier :=
        assembleGates inputs totalGates 0 emptyAssembly
          (rawProgramGates initial)
      let rawLeft :=
        appendSourceMacro inputs totalGates gates 0 rawEarlier
          (RawSource.ofSource gate.left)
      let rawRight :=
        appendSourceMacro inputs totalGates gates 1 rawLeft
          (RawSource.ofSource gate.right)
      let rawTrace :=
        appendTraceMacro inputs totalGates gates rawRight
      have earlierFields := ih earlierWithin
      have rawEarlierEq :
          rawEarlier =
            { gates := rawProgramGates earlier.program
              checks := earlier.checks.map RawSource.ofSource } := by
        apply MacroAssembly.ext
        · exact earlierFields.1
        · exact earlierFields.2
      have leftFields :=
        appendSourceMacro_reifies earlier.program gate.left earlierWithin
          coordinate .left (earlier.checks.map RawSource.ofSource)
      have rawLeftEq :
          rawLeft =
            { gates := rawProgramGates left.program
              checks :=
                earlier.checks.map RawSource.ofSource ++
                  [RawSource.ofSource left.check] } := by
        unfold rawLeft
        rw [rawEarlierEq]
        apply MacroAssembly.ext
        · exact leftFields.1
        · exact leftFields.2
      have rightFields :=
        appendSourceMacro_reifies left.program gate.right earlierWithin
          coordinate .right
          (earlier.checks.map RawSource.ofSource ++
            [RawSource.ofSource left.check])
      have rawRightEq :
          rawRight =
            { gates := rawProgramGates right.program
              checks :=
                (earlier.checks.map RawSource.ofSource ++
                  [RawSource.ofSource left.check]) ++
                  [RawSource.ofSource right.check] } := by
        unfold rawRight
        rw [rawLeftEq]
        apply MacroAssembly.ext
        · exact rightFields.1
        · exact rightFields.2
      have traceFields :=
        appendTraceMacro_reifies right.program coordinate
          ((earlier.checks.map RawSource.ofSource ++
            [RawSource.ofSource left.check]) ++
            [RawSource.ofSource right.check])
      have rawTraceEq :
          rawTrace =
            { gates := rawProgramGates trace.program
              checks :=
                ((earlier.checks.map RawSource.ofSource ++
                  [RawSource.ofSource left.check]) ++
                  [RawSource.ofSource right.check]) ++
                  [RawSource.ofSource trace.check] } := by
        unfold rawTrace
        rw [rawRightEq]
        apply MacroAssembly.ext
        · exact traceFields.1
        · exact traceFields.2
      have traversal :
          assembleGates inputs totalGates 0 emptyAssembly
              (rawProgramGates (Program.snoc initial gate)) =
            rawTrace := by
        rw [rawProgramGates, assembleGates_append,
          rawProgramGates_length]
        simp [assembleGates, rawTrace, rawRight, rawLeft,
          rawEarlier, RawGate.ofGate]
      rw [traversal, rawTraceEq]
      constructor
      · rfl
      · let earlierChecks :=
          ((earlier.checks.map fun source =>
              source.weakenGates
                (DirectWire.LockedNANDGlobalCandidates.sourceMacroGateCount
                  gate.left)).map
            fun source =>
              source.weakenGates
                (DirectWire.LockedNANDGlobalCandidates.sourceMacroGateCount
                  gate.right)).map
            fun source => source.weakenGates 18
        let leftCheck :=
          (left.check.weakenGates
            (DirectWire.LockedNANDGlobalCandidates.sourceMacroGateCount
              gate.right)).weakenGates 18
        let rightCheck := right.check.weakenGates 18
        have typedChecks :
            (DirectWire.LockedNANDGlobalCandidates.macroAssembly
              (Program.snoc initial gate) within).checks =
              earlierChecks ++ [leftCheck, rightCheck, trace.check] := by
          rfl
        have earlierChecksEq :
            earlierChecks.map RawSource.ofSource =
              earlier.checks.map RawSource.ofSource := by
          dsimp only [earlierChecks]
          rw [map_ofSource_weakenGates, map_ofSource_weakenGates,
            map_ofSource_weakenGates]
        have leftCheckEq :
            RawSource.ofSource leftCheck =
              RawSource.ofSource left.check := by
          simp [leftCheck, ofSource_weakenGates]
        have rightCheckEq :
            RawSource.ofSource rightCheck =
              RawSource.ofSource right.check := by
          simp [rightCheck, ofSource_weakenGates]
        have mappedTypedChecks :
            (DirectWire.LockedNANDGlobalCandidates.macroAssembly
              (Program.snoc initial gate) within).checks.map
                RawSource.ofSource =
              earlierChecks.map RawSource.ofSource ++
                [RawSource.ofSource leftCheck,
                  RawSource.ofSource rightCheck,
                  RawSource.ofSource trace.check] := by
          have mapped :=
            congrArg (fun checks => checks.map RawSource.ofSource)
              typedChecks
          have distributed :
              (earlierChecks ++
                [leftCheck, rightCheck, trace.check]).map
                  RawSource.ofSource =
                earlierChecks.map RawSource.ofSource ++
                  [RawSource.ofSource leftCheck,
                    RawSource.ofSource rightCheck,
                    RawSource.ofSource trace.check] := by
            simp only [List.map_append, List.map_cons, List.map_nil]
          exact mapped.trans distributed
        rw [mappedTypedChecks]
        rw [earlierChecksEq, leftCheckEq, rightCheckEq]
        simp [List.append_assoc]

/-! ### Exact right-folded prefix -/

structure PrefixAssembly where
  gates : List RawGate
  output : RawSource
deriving BEq, DecidableEq, Repr

/-- Fieldwise equality for raw prefix assemblies. -/
theorem PrefixAssembly.ext
    (left right : PrefixAssembly)
    (gates : left.gates = right.gates)
    (output : left.output = right.output) :
    left = right := by
  cases left
  cases right
  simp_all

/-- The typed construction inserts each newest check at the front and first
folds the tail.  This right recursion preserves that exact gate order.  The
empty branch makes the raw builder total; successful circuit elaboration
never reaches it. -/
def appendPrefix : List RawGate → List RawSource → PrefixAssembly
  | gates, [] =>
      { gates := gates
        output := .constant false }
  | gates, [check] =>
      { gates := gates
        output := check }
  | gates, head :: next :: rest =>
      let tail := appendPrefix gates (next :: rest)
      let offset := tail.gates.length
      { gates := appendTemplate tail.gates
          (rawBinding2 tail.output head) prefixTemplate
        output := .gate (offset + 1) }

/-- Exact number of two-gate conjunction nodes added by the right-folded
prefix.  Natural subtraction makes the empty and singleton cases explicit. -/
theorem appendPrefix_gates_length
    (gates : List RawGate) (checks : List RawSource) :
    (appendPrefix gates checks).gates.length =
      gates.length + 2 * (checks.length - 1) := by
  induction checks generalizing gates with
  | nil =>
      simp [appendPrefix]
  | cons head rest ih =>
      cases rest with
      | nil =>
          simp [appendPrefix]
      | cons next tail =>
          simp only [appendPrefix]
          simp only [appendTemplate, List.length_append, List.length_map]
          rw [show
            (appendPrefix gates (next :: tail)).gates.length =
              gates.length + 2 * ((next :: tail).length - 1) from
                ih gates]
          rw [prefixTemplate_length]
          simp only [List.length_cons]
          omega

/-- The one-check raw prefix is the exact reification of the zero-tail
typed prefix append. -/
theorem appendPrefix_reifies_zero
    {outerInputs prefixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin 1 → Source outerInputs prefixGates) :
    appendPrefix (rawProgramGates initial)
        (List.ofFn fun index => RawSource.ofSource (binding index)) =
      { gates :=
          rawProgramGates
            (DirectWire.LockedNANDGlobalCandidates.appendCandidateProgram
              initial binding
              (DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate
                0))
        output :=
          RawSource.ofSource
            (DirectWire.LockedNANDGlobalCandidates.appendCandidateSource
              binding
              (DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate
                0)
              fin1Zero) } := by
  simp only [
    DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate_reconstruction]
  apply PrefixAssembly.ext
  · rw [
      rawProgramGates_appendCandidateProgram]
    simp [
      DirectWire.LockedNANDGlobalCandidates.reconstructedNonemptyPrefixCandidate,
      DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixAssembly,
      Candidate.ofDirectWireWord, appendPrefix, appendTemplate]
    rfl
  · rw [ofSource_appendCandidateSource]
    rfl

/-- Appending one newest check to the typed nonempty prefix has exactly the
same raw gate order as appending the two-gate prefix template after the
already-built tail. -/
theorem nonemptyPrefix_succ_gates
    (tailChecks : Nat)
    {outerInputs prefixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding :
      Fin (tailChecks + 1 + 1) → Source outerInputs prefixGates) :
    rawProgramGates
        (DirectWire.LockedNANDGlobalCandidates.appendCandidateProgram
          initial binding
          (DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate
            (tailChecks + 1))) =
      appendTemplate
        (rawProgramGates
          (DirectWire.LockedNANDGlobalCandidates.appendCandidateProgram
            initial (fun index => binding index.succ)
            (DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate
              tailChecks)))
        (rawBinding2
          (RawSource.ofSource
            (DirectWire.LockedNANDGlobalCandidates.appendCandidateSource
              (fun index => binding index.succ)
              (DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate
                tailChecks)
              fin1Zero))
          (RawSource.ofSource (binding ⟨0, by omega⟩)))
        prefixTemplate := by
  simp only [
    DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate_reconstruction]
  rw [rawProgramGates_appendCandidateProgram]
  simp [
    DirectWire.LockedNANDGlobalCandidates.reconstructedNonemptyPrefixCandidate,
    DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixAssembly,
    Candidate.ofDirectWireWord]
  rw [rawProgramGates_appendCandidateProgram,
    rawFinBinding_binding2, appendTemplate_appendTemplate,
    appendTemplate_renameInputs]
  rw [rawProgramGates_appendCandidateProgram, rawProgramGates_length]
  have earlierOutputEq :
      instantiateSource prefixGates (rawFinBinding binding)
          (RawSource.ofSource
            ((DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixAssembly
              tailChecks).output.renameInputs Fin.succ)) =
        RawSource.ofSource
          (DirectWire.LockedNANDGlobalCandidates.appendCandidateSource
            (fun index => binding index.succ)
            (DirectWire.LockedNANDGlobalCandidates.reconstructedNonemptyPrefixCandidate
              tailChecks)
            fin1Zero) := by
    rw [← ofSource_substituteInputs]
    unfold DirectWire.LockedNANDGlobalCandidates.appendCandidateSource
      DirectWire.LockedNANDGlobalCandidates.reconstructedNonemptyPrefixCandidate
    rw [Candidate.ofDirectWireWord_pointwise]
    rw [Source.substituteInputs_renameInputs]
  have newestEq :
      instantiateSource prefixGates (rawFinBinding binding) (.input 0) =
        RawSource.ofSource (binding ⟨0, by omega⟩) := by
    simp [instantiateSource, rawFinBinding]
  unfold prefixTemplate
  congr 1
  funext index
  by_cases zero : index = 0
  · subst index
    simp [rawBinding2, earlierOutputEq,
      DirectWire.LockedNANDGlobalCandidates.reconstructedNonemptyPrefixCandidate,
      Candidate.ofDirectWireWord]
  by_cases one : index = 1
  · subst index
    simp [rawBinding2, RawSource.ofSource, instantiateSource, rawFinBinding]
  · simp [rawBinding2, zero, one, instantiateSource]

/-- The newest typed prefix node exposes the second gate of the exact
two-gate template. -/
theorem nonemptyPrefix_succ_output
    (tailChecks : Nat)
    {outerInputs prefixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding :
      Fin (tailChecks + 1 + 1) → Source outerInputs prefixGates) :
    RawSource.ofSource
        (DirectWire.LockedNANDGlobalCandidates.appendCandidateSource
          binding
          (DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate
            (tailChecks + 1))
          fin1Zero) =
      .gate
        ((rawProgramGates
          (DirectWire.LockedNANDGlobalCandidates.appendCandidateProgram
            initial (fun index => binding index.succ)
          (DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate
            tailChecks))).length + 1) := by
  simp only [
    DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate_reconstruction]
  rw [ofSource_appendCandidateSource]
  dsimp only [
    DirectWire.LockedNANDGlobalCandidates.reconstructedNonemptyPrefixCandidate,
    DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixAssembly]
  rw [Candidate.ofDirectWireWord_pointwise]
  rw [ofSource_appendCandidateSource,
    prefixAndDirect_output_source, rawProgramGates_length]
  rfl

/-- The raw right fold exactly reifies every nonempty typed prefix append. -/
theorem appendPrefix_reifies
    (tailChecks : Nat)
    {outerInputs prefixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding :
      Fin (tailChecks + 1) → Source outerInputs prefixGates) :
    appendPrefix (rawProgramGates initial)
        (List.ofFn fun index => RawSource.ofSource (binding index)) =
      { gates :=
          rawProgramGates
            (DirectWire.LockedNANDGlobalCandidates.appendCandidateProgram
              initial binding
              (DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate
                tailChecks))
        output :=
          RawSource.ofSource
            (DirectWire.LockedNANDGlobalCandidates.appendCandidateSource
              binding
              (DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate
                tailChecks)
              fin1Zero) } := by
  induction tailChecks generalizing prefixGates with
  | zero =>
      exact appendPrefix_reifies_zero initial binding
  | succ tailChecks ih =>
      rw [List.ofFn_succ]
      rw [List.ofFn_succ]
      simp only [appendPrefix]
      have earlier :=
        ih initial (fun index => binding index.succ)
      rw [List.ofFn_succ] at earlier
      rw [earlier]
      apply PrefixAssembly.ext
      · have zeroEq :
            (⟨0, by omega⟩ : Fin (tailChecks + 1 + 1)) = 0 := by
          apply Fin.ext
          rfl
        simpa only [zeroEq] using
          (nonemptyPrefix_succ_gates tailChecks initial binding).symm
      · simpa only using
          (nonemptyPrefix_succ_output tailChecks initial binding).symm

/-- Macro traversal followed by the raw right fold is exactly the typed raw
baseline program and its final prefix source. -/
theorem circuitPrefix_reifies
    {inputs : Nat} (circuit : Circuit inputs) :
    let rawMacros := macroAssembly (RawCircuit.ofCircuit circuit)
    let rawPrefix := appendPrefix rawMacros.gates rawMacros.checks
    rawPrefix.gates =
        rawProgramGates
          (DirectWire.LockedNANDGlobalCandidates.rawBaselineProgram
            circuit) ∧
      rawPrefix.output =
        RawSource.ofSource
          (DirectWire.LockedNANDGlobalCandidates.rawBaselinePrefixSource
            circuit) := by
  let typedMacros :=
    DirectWire.LockedNANDGlobalCandidates.macroAssembly
      circuit.program (Nat.le_refl circuit.gateCount)
  let rawMacros := macroAssembly (RawCircuit.ofCircuit circuit)
  have macroFields :=
    macroAssembly_reifies circuit.program
      (Nat.le_refl circuit.gateCount)
  have rawMacrosEq :
      rawMacros =
        { gates := rawProgramGates typedMacros.program
          checks := typedMacros.checks.map RawSource.ofSource } := by
    apply MacroAssembly.ext
    · simpa [rawMacros, macroAssembly, RawCircuit.ofCircuit,
        typedMacros, rawProgramGates_length] using macroFields.1
    · simpa [rawMacros, macroAssembly, RawCircuit.ofCircuit,
        typedMacros, rawProgramGates_length] using macroFields.2
  have rawChecksLength :
      rawMacros.checks.length = 3 * circuit.gateCount := by
    unfold rawMacros macroAssembly RawCircuit.ofCircuit
    rw [assembleGates_checks_length]
    simp [emptyAssembly, rawProgramGates_length]
  have typedChecksLength :
      typedMacros.checks.length = 3 * circuit.gateCount := by
    have mappedLength := congrArg List.length macroFields.2
    rw [List.length_map] at mappedLength
    simpa [rawMacros, macroAssembly, RawCircuit.ofCircuit,
      assembleGates_checks_length, emptyAssembly,
      rawProgramGates_length] using mappedLength.symm
  have countEqual :
      typedMacros.checks.length =
        DirectWire.LockedNANDGlobalCandidates.checkTailCount circuit + 1 :=
    typedChecksLength.trans
      (DirectWire.LockedNANDGlobalCandidates.checkTailCount_add_one
        circuit).symm
  let prefixBinding :
      Fin
          (DirectWire.LockedNANDGlobalCandidates.checkTailCount circuit +
            1) →
        Source (carrierWidth inputs circuit.gateCount)
          (DirectWire.LockedNANDGlobalCandidates.macroGateCount
            circuit.program) :=
    fun index =>
      typedMacros.checks.get (Fin.cast countEqual.symm index)
  have bindingList :
      List.ofFn
          (fun index =>
            RawSource.ofSource (prefixBinding index)) =
        typedMacros.checks.map RawSource.ofSource := by
    exact list_ofFn_get_cast_map typedMacros.checks
      (DirectWire.LockedNANDGlobalCandidates.checkTailCount circuit + 1)
      countEqual RawSource.ofSource
  have rawPrefixEq :=
    appendPrefix_reifies
      (DirectWire.LockedNANDGlobalCandidates.checkTailCount circuit)
      typedMacros.program prefixBinding
  have rawPrefixTyped :
      appendPrefix rawMacros.gates rawMacros.checks =
        { gates :=
            rawProgramGates
              (DirectWire.LockedNANDGlobalCandidates.appendCandidateProgram
                typedMacros.program prefixBinding
                (DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate
                  (DirectWire.LockedNANDGlobalCandidates.checkTailCount
                    circuit)))
          output :=
            RawSource.ofSource
              (DirectWire.LockedNANDGlobalCandidates.appendCandidateSource
                prefixBinding
                (DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate
                  (DirectWire.LockedNANDGlobalCandidates.checkTailCount
                    circuit))
                fin1Zero) } := by
    rw [rawMacrosEq, ← bindingList]
    exact rawPrefixEq
  have bindingEqual :
      (fun index :
          Fin
            (DirectWire.LockedNANDGlobalCandidates.checkTailCount circuit +
              1) =>
        DirectWire.LockedNANDGlobalCandidates.macroCheckSource circuit
          (Fin.cast
            (DirectWire.LockedNANDGlobalCandidates.checkTailCount_add_one
              circuit)
            index)) =
        prefixBinding := by
    funext index
    dsimp [prefixBinding, typedMacros,
      DirectWire.LockedNANDGlobalCandidates.macroCheckSource]
  change
    (appendPrefix rawMacros.gates rawMacros.checks).gates =
        rawProgramGates
          (DirectWire.LockedNANDGlobalCandidates.rawBaselineProgram
            circuit) ∧
      (appendPrefix rawMacros.gates rawMacros.checks).output =
        RawSource.ofSource
          (DirectWire.LockedNANDGlobalCandidates.rawBaselinePrefixSource
            circuit)
  rw [rawPrefixTyped]
  constructor
  · unfold DirectWire.LockedNANDGlobalCandidates.rawBaselineGateCount
    rw [
      DirectWire.LockedNANDGlobalCandidates.rawBaselineProgram_reconstruction]
    rw [rawProgramGates_appendCandidateProgram,
      rawProgramGates_appendCandidateProgram]
    unfold DirectWire.LockedNANDGlobalCandidates.circuitPrefixCandidate
    simp only [Candidate.renameInputs, Candidate.ofDirectWireWord]
    rw [appendTemplate_renameInputs, bindingEqual]
  · unfold DirectWire.LockedNANDGlobalCandidates.rawBaselineGateCount
    rw [
      DirectWire.LockedNANDGlobalCandidates.rawBaselinePrefixSource_reconstruction]
    rw [ofSource_appendCandidateSource,
      ofSource_appendCandidateSource]
    unfold DirectWire.LockedNANDGlobalCandidates.circuitPrefixCandidate
    simp only [Candidate.renameInputs,
      Candidate.ofDirectWireWord_pointwise,
      DirectWireWord.renameInputs]
    rw [DirectWire.LockedNANDGlobalCandidates.nonemptyPrefixCandidate_output_source]
    rw [instantiateSource_ofSource_renameInputs, bindingEqual]

def outputGateIndex : RawSource → Nat
  | .gate index => index
  | _ => 0

private theorem rawProgramGates_cast
    {inputs left right : Nat} (equal : left = right)
    (program : Program inputs left) :
    rawProgramGates (equal ▸ program) = rawProgramGates program := by
  cases equal
  rfl

private theorem ofSource_cast
    {inputs left right : Nat} (equal : left = right)
    (source : Source inputs left) :
    RawSource.ofSource (equal ▸ source) = RawSource.ofSource source := by
  cases equal
  rfl

/-- Gate-count transport does not alter the reified baseline gate list. -/
theorem baselineProgram_reifies_rawBaselineProgram
    {inputs : Nat} (circuit : Circuit inputs) :
    rawProgramGates
        (DirectWire.LockedNANDGlobalCandidates.baselineProgram circuit) =
      rawProgramGates
        (DirectWire.LockedNANDGlobalCandidates.rawBaselineProgram circuit) := by
  unfold DirectWire.LockedNANDGlobalCandidates.baselineProgram
  exact rawProgramGates_cast
    (DirectWire.LockedNANDGlobalCandidates.rawBaselineGateCount_eq_lockedBaselineCount
      circuit)
    (DirectWire.LockedNANDGlobalCandidates.rawBaselineProgram circuit)

/-- Gate-count transport does not alter the reified prefix source. -/
theorem baselinePrefixSource_reifies_rawBaselinePrefixSource
    {inputs : Nat} (circuit : Circuit inputs) :
    RawSource.ofSource
        (DirectWire.LockedNANDGlobalCandidates.baselinePrefixSource circuit) =
      RawSource.ofSource
        (DirectWire.LockedNANDGlobalCandidates.rawBaselinePrefixSource
          circuit) := by
  unfold DirectWire.LockedNANDGlobalCandidates.baselinePrefixSource
  exact ofSource_cast
    (DirectWire.LockedNANDGlobalCandidates.rawBaselineGateCount_eq_lockedBaselineCount
      circuit)
    (DirectWire.LockedNANDGlobalCandidates.rawBaselinePrefixSource circuit)

private theorem rawFullGates_reifies
    {inputs : Nat} (circuit : Circuit inputs) :
    let rawMacros := macroAssembly (RawCircuit.ofCircuit circuit)
    let rawPrefix := appendPrefix rawMacros.gates rawMacros.checks
    appendTemplate rawPrefix.gates
        (rawBinding3
          (.input (finalLockCoordinate inputs circuit.gateCount))
          rawPrefix.output
          (.input
            (traceCoordinate inputs circuit.gateCount
              circuit.outputGate.val)))
        finalTemplate =
      rawProgramGates
        (DirectWire.LockedNANDGlobalCandidates.fullProgram circuit) := by
  let rawMacros := macroAssembly (RawCircuit.ofCircuit circuit)
  let rawPrefix := appendPrefix rawMacros.gates rawMacros.checks
  have prefixFact := circuitPrefix_reifies circuit
  have gatesEqual :
      rawPrefix.gates =
        rawProgramGates
          (DirectWire.LockedNANDGlobalCandidates.baselineProgram circuit) :=
    prefixFact.1.trans
      (baselineProgram_reifies_rawBaselineProgram circuit).symm
  have outputEqual :
      rawPrefix.output =
        RawSource.ofSource
          (DirectWire.LockedNANDGlobalCandidates.baselinePrefixSource
            circuit) :=
    prefixFact.2.trans
      (baselinePrefixSource_reifies_rawBaselinePrefixSource circuit).symm
  rw [DirectWire.LockedNANDGlobalCandidates.fullProgram_reconstruction]
  unfold DirectWire.LockedNANDGlobalCandidates.finalBinding
  rw [rawProgramGates_appendCandidateProgram, rawFinBinding_binding3]
  rw [← gatesEqual, ← outputEqual]
  rfl

private theorem rawOutputSources_ofFn
    {inputs gates outputs : Nat}
    (source : Fin outputs → Source inputs gates) :
    rawOutputSources (OutputWord.ofFn source) =
      List.ofFn (fun output => RawSource.ofSource (source output)) := by
  induction outputs with
  | zero =>
      rfl
  | succ outputs ih =>
      rw [List.ofFn_succ]
      simp only [OutputWord.ofFn, rawOutputSources]
      congr
      exact ih (fun output => source output.succ)

private theorem rawOutputSources_eq_ofFn_get
    {inputs gates outputs : Nat}
    (word : OutputWord inputs gates outputs) :
    rawOutputSources word =
      List.ofFn (fun output => RawSource.ofSource (word.get output)) := by
  induction word with
  | nil =>
      rfl
  | @cons outputs head tail ih =>
      rw [List.ofFn_succ]
      change
        RawSource.ofSource head :: rawOutputSources tail =
          RawSource.ofSource head ::
            List.ofFn
              (fun output => RawSource.ofSource (tail.get output))
      rw [ih]

private theorem list_ofFn_snoc
    {α : Type} (count : Nat) (value : Fin (count + 1) → α) :
    List.ofFn value =
      List.ofFn (fun index : Fin count =>
        value (Fin.castAdd 1 index)) ++
        [value (Fin.last count)] := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_ofFn, List.getElem?_append,
    List.length_ofFn]
  by_cases within : index < count
  · have total : index < count + 1 := by omega
    simp [within, total]
  · by_cases last : index = count
    · subst index
      have total : count < count + 1 := by omega
      simp [within, total]
      apply congrArg value
      apply Fin.ext
      rfl
    · have outside : ¬ index < count + 1 := by omega
      have shifted : index - count ≠ 0 := by omega
      simp [within, outside, shifted]

private theorem list_ofFn_gate_eq_range (count : Nat) :
    List.ofFn (fun index : Fin count => RawSource.gate index.val) =
      (List.range count).map RawSource.gate := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_ofFn, List.getElem?_map]
  by_cases valid : index < count <;> simp [valid]

private theorem rawFullOutputs_reifies
    {inputs : Nat} (circuit : Circuit inputs) :
    rawOutputSources
        (DirectWire.LockedNANDGlobalCandidates.fullCandidate circuit).outputs =
      (List.range (lockedBaselineCount circuit.program)).map
          RawSource.gate ++
        [.gate (lockedBaselineCount circuit.program + 3)] := by
  let baseline := lockedBaselineCount circuit.program
  rw [rawOutputSources_eq_ofFn_get]
  rw [list_ofFn_snoc]
  have initialFunction :
      (fun index : Fin baseline =>
        RawSource.ofSource
          ((DirectWire.LockedNANDGlobalCandidates.fullCandidate circuit).outputs.get
            (Fin.castAdd 1 index))) =
        (fun index : Fin baseline => RawSource.gate index.val) := by
    funext index
    change
      RawSource.ofSource
          ((DirectWire.LockedNANDGlobalCandidates.fullCandidate circuit).directWireWord.source
            (baselineOutputEmbedding index)) =
        RawSource.gate index.val
    rw [DirectWire.LockedNANDGlobalCandidates.fullCandidate_initial_source]
    rfl
  rw [initialFunction, list_ofFn_gate_eq_range]
  congr 1
  congr 1
  change
    RawSource.ofSource
        ((DirectWire.LockedNANDGlobalCandidates.fullCandidate circuit).directWireWord.source
          (Fin.last baseline)) =
      RawSource.gate (baseline + 3)
  rw [← conditionalFinalOutput_eq_last]
  rw [
    DirectWire.LockedNANDGlobalCandidates.fullCandidate_final_source_reconstruction]
  rw [ofSource_appendCandidateSource,
    finalConjunctionDirect_output_source]
  rfl

private theorem rawPrefix_length_reifies
    {inputs : Nat} (circuit : Circuit inputs) :
    let rawMacros := macroAssembly (RawCircuit.ofCircuit circuit)
    (appendPrefix rawMacros.gates rawMacros.checks).gates.length =
      lockedBaselineCount circuit.program := by
  have gatesEqual := (circuitPrefix_reifies circuit).1
  dsimp only
  rw [gatesEqual, rawProgramGates_length]
  exact
    DirectWire.LockedNANDGlobalCandidates.rawBaselineGateCount_eq_lockedBaselineCount
      circuit

/-- Complete direct raw target.  It normalizes the legacy source output,
emits every macro and prefix gate, computes the baseline from the emitted
list, appends the final four gates, exposes every baseline gate plus the final
gate, and stores the exact baseline. -/
def rawLockedInstance (raw : RawCircuit) : RawLockedInstance :=
  let circuit := raw.normalize
  let macros := macroAssembly circuit
  let prefixAssembly := appendPrefix macros.gates macros.checks
  let baseline := prefixAssembly.gates.length
  let outputTrace : RawSource :=
    .input (traceCoordinate circuit.inputCount circuit.gates.length
      (outputGateIndex circuit.output))
  let finalGates := appendTemplate prefixAssembly.gates
    (rawBinding3
      (.input (finalLockCoordinate circuit.inputCount circuit.gates.length))
      prefixAssembly.output
      outputTrace)
    finalTemplate
  { candidate :=
      { inputCount :=
          circuit.inputCount + 6 * circuit.gates.length + 1
        gates := finalGates
        outputs :=
          (List.range baseline).map RawSource.gate ++
            [.gate (baseline + 3)] }
    baseline := baseline }

/-- Exact grammar-computable baseline ledger: selected source/trace templates
followed by two gates for every right-fold link between the three checks per
normalized source gate. -/
theorem rawLockedInstance_baseline (raw : RawCircuit) :
    (rawLockedInstance raw).baseline =
      gateListMacroGateCount raw.normalize.gates +
        2 * (3 * raw.normalize.gates.length - 1) := by
  let circuit := raw.normalize
  let macros := macroAssembly circuit
  have prefixLength :=
    appendPrefix_gates_length macros.gates macros.checks
  have macroGates := macroAssembly_gates_length circuit
  have macroChecks := macroAssembly_checks_length circuit
  dsimp [rawLockedInstance, circuit]
  rw [prefixLength, macroGates, macroChecks]

/-- The raw construction retains the exact manuscript carrier width after
normalizing the source circuit's output form. -/
theorem rawLockedInstance_inputCount (raw : RawCircuit) :
    (rawLockedInstance raw).candidate.inputCount =
      raw.normalize.inputCount + 6 * raw.normalize.gates.length + 1 := by
  rfl

/-- Exactly four gates follow the computed macro-and-prefix baseline. -/
theorem rawLockedInstance_gate_length (raw : RawCircuit) :
    (rawLockedInstance raw).candidate.gates.length =
      (rawLockedInstance raw).baseline + 4 := by
  simp [rawLockedInstance, appendTemplate, finalTemplate_length]

/-- The exposed output tuple contains every baseline gate and exactly one
additional final gate. -/
theorem rawLockedInstance_output_length (raw : RawCircuit) :
    (rawLockedInstance raw).candidate.outputs.length =
      (rawLockedInstance raw).baseline + 1 := by
  simp [rawLockedInstance]

/-- Exact output ordering: baseline gates in increasing order, followed by
the fourth and final newly appended gate. -/
theorem rawLockedInstance_outputs (raw : RawCircuit) :
    (rawLockedInstance raw).candidate.outputs =
      (List.range (rawLockedInstance raw).baseline).map RawSource.gate ++
        [.gate ((rawLockedInstance raw).baseline + 3)] := by
  rfl

/-- On reified intrinsic syntax, the direct list builder is exactly the
legacy typed construction, including gate order, output order, and baseline. -/
theorem rawLockedInstance_ofCircuit
    {inputs : Nat} (circuit : Circuit inputs) :
    rawLockedInstance (RawCircuit.ofCircuit circuit) =
      lockedInstanceOfCircuit circuit := by
  have fullGates := rawFullGates_reifies circuit
  have fullOutputs := rawFullOutputs_reifies circuit
  have prefixLength := rawPrefix_length_reifies circuit
  simp only [RawCircuit.ofCircuit] at fullGates prefixLength
  simp only [rawLockedInstance, RawCircuit.ofCircuit,
    RawCircuit.normalize, outputGateIndex, rawProgramGates_length,
    lockedInstanceOfCircuit, RawLockedInstance.ofCandidate,
    RawCandidate.ofCandidate]
  rw [fullGates, fullOutputs, prefixLength]
  rfl

/-- Normalization is already built into the direct raw construction. -/
theorem rawLockedInstance_normalize (raw : RawCircuit) :
    rawLockedInstance raw.normalize = rawLockedInstance raw := by
  simp [rawLockedInstance, RawCircuit.normalize_idempotent]

/-- Successful intrinsic elaboration identifies the exact legacy target,
not merely a semantically equivalent candidate. -/
theorem rawLockedInstance_of_elaborate
    (raw : RawCircuit) (packed : PackedCircuit)
    (elaborated : raw.elaborate = some packed) :
    rawLockedInstance raw =
      lockedInstanceOfCircuit packed.circuit := by
  rw [← rawLockedInstance_normalize raw]
  rw [← ofCircuit_eq_normalize_of_elaborate raw packed elaborated]
  exact rawLockedInstance_ofCircuit packed.circuit

/-- Total target bytes for the direct raw builder.  Framing or grammar
failure is the sole empty-output branch. -/
def targetBytes (bits : BitString) : BitString :=
  match decodeCircuit bits with
  | none => []
  | some raw => encodeLockedInstance (rawLockedInstance raw)

theorem targetBytes_of_decoded (bits : BitString) (raw : RawCircuit)
    (decoded : decodeCircuit bits = some raw) :
    targetBytes bits =
      encodeLockedInstance (rawLockedInstance raw) := by
  simp [targetBytes, decoded]

theorem targetBytes_of_malformed (bits : BitString)
    (malformed : decodeCircuit bits = none) :
    targetBytes bits = [] := by
  simp [targetBytes, malformed]

theorem targetBytes_encodeCircuit (raw : RawCircuit) :
    targetBytes (encodeCircuit raw) =
      encodeLockedInstance (rawLockedInstance raw) := by
  exact targetBytes_of_decoded _ raw (decodeCircuit_encodeCircuit raw)

/-- On every successfully decoded and elaborated strict source, the direct
emitter target is byte-for-byte the established legacy semantic builder. -/
theorem targetBytes_of_elaborated
    (bits : BitString) (raw : RawCircuit) (packed : PackedCircuit)
    (decoded : decodeCircuit bits = some raw)
    (elaborated : raw.elaborate = some packed) :
    targetBytes bits =
      buildLockedNANDInstance bits := by
  rw [targetBytes_of_decoded bits raw decoded]
  rw [rawLockedInstance_of_elaborate raw packed elaborated]
  unfold buildLockedNANDInstance decodeElaboratedCircuit
  simp [decoded, elaborated]

end RawBuilder
end PNP.Concrete.LockedNAND
