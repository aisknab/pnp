/-
Copyright (c) 2026 PNP Labs.

Pure structural schedule for the locked-NAND target emitter.

This module is specification-only.  It recursively schedules literal closed
gate templates, check coordinates, the right-folded prefix, final gates,
exposed outputs, and strict-v0 tokens from raw circuit syntax.  Its executable
definitions do not call a decoder, `RawBuilder.rawLockedInstance`,
`RawBuilder.targetBytes`, or a semantic source-to-target builder.

The equality theorems at the end compare this independent schedule with the
existing direct raw construction.  They are proof interfaces, not authority
for host-side schedule lookup by a later machine.
-/

import PNP.Concrete.LockedNANDRawBuilder

namespace PNP.Concrete.LockedNAND.TargetEmitterSchedule

/-! ### Literal closed templates and structural substitution -/

private def binding2
    (first second : RawSource) (index : Nat) : RawSource :=
  if index = 0 then first
  else if index = 1 then second
  else .constant false

private def binding3
    (first second third : RawSource) (index : Nat) : RawSource :=
  if index = 0 then first
  else if index = 1 then second
  else if index = 2 then third
  else .constant false

private def binding4
    (first second third fourth : RawSource)
    (index : Nat) : RawSource :=
  if index = 0 then first
  else if index = 1 then second
  else if index = 2 then third
  else if index = 3 then fourth
  else .constant false

private def instantiateSource
    (offset : Nat) (binding : Nat → RawSource) :
    RawSource → RawSource
  | .input index => binding index
  | .constant value => .constant value
  | .gate index => .gate (offset + index)

private def instantiateGate
    (offset : Nat) (binding : Nat → RawSource)
    (gate : RawGate) : RawGate :=
  { left := instantiateSource offset binding gate.left
    right := instantiateSource offset binding gate.right }

private def templateSuffix
    (offset : Nat) (binding : Nat → RawSource)
    (template : List RawGate) : List RawGate :=
  template.map (instantiateGate offset binding)

private def equalityTemplate : List RawGate :=
  [ { left := .input 0, right := .input 1 }
  , { left := .input 0, right := .input 2 }
  , { left := .gate 0, right := .gate 0 }
  , { left := .gate 2, right := .input 2 }
  , { left := .input 0, right := .gate 0 }
  , { left := .gate 4, right := .gate 4 }
  , { left := .gate 5, right := .gate 1 }
  , { left := .gate 3, right := .gate 6 }
  , { left := .input 0, right := .input 0 }
  , { left := .gate 8, right := .input 1 }
  ]

private def constantZeroTemplate : List RawGate :=
  [ { left := .input 0, right := .input 1 }
  , { left := .input 0, right := .gate 0 }
  , { left := .gate 1, right := .gate 1 }
  ]

private def constantOneTemplate : List RawGate :=
  [ { left := .input 0, right := .input 1 }
  , { left := .gate 0, right := .gate 0 }
  ]

private def traceTemplate : List RawGate :=
  [ { left := .input 0, right := .input 1 }
  , { left := .gate 0, right := .gate 0 }
  , { left := .input 0, right := .input 2 }
  , { left := .input 0, right := .input 3 }
  , { left := .gate 1, right := .gate 2 }
  , { left := .gate 1, right := .input 2 }
  , { left := .gate 5, right := .gate 5 }
  , { left := .gate 6, right := .gate 3 }
  , { left := .input 0, right := .gate 0 }
  , { left := .gate 8, right := .gate 8 }
  , { left := .gate 9, right := .input 2 }
  , { left := .gate 10, right := .gate 10 }
  , { left := .gate 11, right := .input 3 }
  , { left := .gate 4, right := .gate 7 }
  , { left := .gate 13, right := .gate 13 }
  , { left := .gate 14, right := .gate 12 }
  , { left := .input 0, right := .input 0 }
  , { left := .gate 16, right := .input 1 }
  ]

private def prefixTemplate : List RawGate :=
  [ { left := .input 0, right := .input 1 }
  , { left := .gate 0, right := .gate 0 }
  ]

private def finalTemplate : List RawGate :=
  [ { left := .input 1, right := .input 2 }
  , { left := .gate 0, right := .gate 0 }
  , { left := .input 0, right := .gate 1 }
  , { left := .gate 2, right := .gate 2 }
  ]

private theorem binding2_eq_builder
    (first second : RawSource) :
    binding2 first second =
      RawBuilder.rawBinding2 first second := by
  rfl

private theorem binding3_eq_builder
    (first second third : RawSource) :
    binding3 first second third =
      RawBuilder.rawBinding3 first second third := by
  rfl

private theorem binding4_eq_builder
    (first second third fourth : RawSource) :
    binding4 first second third fourth =
      RawBuilder.rawBinding4 first second third fourth := by
  rfl

private theorem instantiateSource_eq_builder
    (offset : Nat) (sourceBinding : Nat → RawSource)
    (source : RawSource) :
    instantiateSource offset sourceBinding source =
      RawBuilder.instantiateSource offset sourceBinding source := by
  cases source <;> rfl

private theorem instantiateGate_eq_builder
    (offset : Nat) (sourceBinding : Nat → RawSource)
    (gate : RawGate) :
    instantiateGate offset sourceBinding gate =
      RawBuilder.instantiateGate offset sourceBinding gate := by
  cases gate
  simp [instantiateGate, RawBuilder.instantiateGate,
    instantiateSource_eq_builder]

private theorem templateSuffix_eq_builder
    (offset : Nat) (sourceBinding : Nat → RawSource)
    (template : List RawGate) :
    templateSuffix offset sourceBinding template =
      template.map
        (RawBuilder.instantiateGate offset sourceBinding) := by
  unfold templateSuffix
  apply List.map_congr_left
  intro gate _member
  exact instantiateGate_eq_builder offset sourceBinding gate

private theorem equalityTemplate_eq_builder :
    equalityTemplate = RawBuilder.equalityTemplate := by
  rfl

private theorem constantZeroTemplate_eq_builder :
    constantZeroTemplate = RawBuilder.constantZeroTemplate := by
  rfl

private theorem constantOneTemplate_eq_builder :
    constantOneTemplate = RawBuilder.constantOneTemplate := by
  rfl

private theorem traceTemplate_eq_builder :
    traceTemplate = RawBuilder.traceTemplate := by
  rfl

private theorem prefixTemplate_eq_builder :
    prefixTemplate = RawBuilder.prefixTemplate := by
  rfl

private theorem finalTemplate_eq_builder :
    finalTemplate = RawBuilder.finalTemplate := by
  rfl

/-! ### Source/trace suffixes and recursive gate-list offsets -/

private def primaryCoordinate
    (_inputs _gates index : Nat) : Nat :=
  index

private def traceCoordinate
    (inputs _gates index : Nat) : Nat :=
  inputs + index

private def occurrenceCoordinate
    (inputs gates gate side : Nat) : Nat :=
  inputs + gates + (2 * gate + side)

private def sourceLockCoordinate
    (inputs gates gate side : Nat) : Nat :=
  inputs + 3 * gates + (2 * gate + side)

private def traceLockCoordinate
    (inputs gates gate : Nat) : Nat :=
  inputs + 5 * gates + gate

private def finalLockCoordinate
    (inputs gates : Nat) : Nat :=
  inputs + 6 * gates

private def sourceValueCoordinate
    (inputs gates : Nat) : RawSource → RawSource
  | .input index => .input (primaryCoordinate inputs gates index)
  | .constant value => .constant value
  | .gate index => .input (traceCoordinate inputs gates index)

private structure MacroSchedule where
  gates : List RawGate
  checks : List RawSource
deriving BEq, DecidableEq, Repr

private def emptyMacroSchedule : MacroSchedule :=
  { gates := [], checks := [] }

private def appendMacroSchedule
    (first second : MacroSchedule) : MacroSchedule :=
  { gates := first.gates ++ second.gates
    checks := first.checks ++ second.checks }

private def sourceMacroSuffix
    (inputs totalGates gate side offset : Nat)
    (source : RawSource) : MacroSchedule :=
  let lock : RawSource :=
    .input (sourceLockCoordinate inputs totalGates gate side)
  let occurrence : RawSource :=
    .input (occurrenceCoordinate inputs totalGates gate side)
  match source with
  | .input index =>
      { gates := templateSuffix offset
          (binding3 lock occurrence
            (sourceValueCoordinate inputs totalGates (.input index)))
          equalityTemplate
        checks := [.gate (offset + 7)] }
  | .constant false =>
      { gates := templateSuffix offset
          (binding2 lock occurrence) constantZeroTemplate
        checks := [.gate (offset + 2)] }
  | .constant true =>
      { gates := templateSuffix offset
          (binding2 lock occurrence) constantOneTemplate
        checks := [.gate (offset + 1)] }
  | .gate index =>
      { gates := templateSuffix offset
          (binding3 lock occurrence
            (sourceValueCoordinate inputs totalGates (.gate index)))
          equalityTemplate
        checks := [.gate (offset + 7)] }

private def traceMacroSuffix
    (inputs totalGates gate offset : Nat) : MacroSchedule :=
  { gates := templateSuffix offset
      (binding4
        (.input (traceLockCoordinate inputs totalGates gate))
        (.input (traceCoordinate inputs totalGates gate))
        (.input (occurrenceCoordinate inputs totalGates gate 0))
        (.input (occurrenceCoordinate inputs totalGates gate 1)))
      traceTemplate
    checks := [.gate (offset + 15)] }

private def gateMacroSuffix
    (inputs totalGates gate offset : Nat)
    (sourceGate : RawGate) : MacroSchedule :=
  let left :=
    sourceMacroSuffix inputs totalGates gate 0 offset sourceGate.left
  let rightOffset := offset + left.gates.length
  let right :=
    sourceMacroSuffix inputs totalGates gate 1 rightOffset
      sourceGate.right
  let traceOffset := rightOffset + right.gates.length
  let trace :=
    traceMacroSuffix inputs totalGates gate traceOffset
  appendMacroSchedule left (appendMacroSchedule right trace)

private def gateListSchedule
    (inputs totalGates : Nat) :
    Nat → Nat → List RawGate → MacroSchedule
  | _, _, [] => emptyMacroSchedule
  | gate, offset, sourceGate :: rest =>
      let current :=
        gateMacroSuffix inputs totalGates gate offset sourceGate
      let tail :=
        gateListSchedule inputs totalGates (gate + 1)
          (offset + current.gates.length) rest
      appendMacroSchedule current tail

private def macroSchedule (circuit : RawCircuit) : MacroSchedule :=
  gateListSchedule circuit.inputCount circuit.gates.length
    0 0 circuit.gates

private def applyMacroSchedule
    (assembly : RawBuilder.MacroAssembly)
    (scheduled : MacroSchedule) : RawBuilder.MacroAssembly :=
  { gates := assembly.gates ++ scheduled.gates
    checks := assembly.checks ++ scheduled.checks }

private theorem applyMacroSchedule_append
    (assembly : RawBuilder.MacroAssembly)
    (first second : MacroSchedule) :
    applyMacroSchedule assembly
        (appendMacroSchedule first second) =
      applyMacroSchedule
        (applyMacroSchedule assembly first) second := by
  apply RawBuilder.MacroAssembly.ext
  · simp [applyMacroSchedule, appendMacroSchedule, List.append_assoc]
  · simp [applyMacroSchedule, appendMacroSchedule, List.append_assoc]

private theorem apply_sourceMacroSuffix_eq
    (inputs totalGates gate side offset : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (source : RawSource)
    (offsetEq : offset = assembly.gates.length) :
    applyMacroSchedule assembly
        (sourceMacroSuffix inputs totalGates gate side offset source) =
      RawBuilder.appendSourceMacro
        inputs totalGates gate side assembly source := by
  subst offset
  cases source with
  | input index =>
      rfl
  | constant value =>
      cases value <;> rfl
  | gate index =>
      rfl

private theorem apply_traceMacroSuffix_eq
    (inputs totalGates gate offset : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (offsetEq : offset = assembly.gates.length) :
    applyMacroSchedule assembly
        (traceMacroSuffix inputs totalGates gate offset) =
      RawBuilder.appendTraceMacro
        inputs totalGates gate assembly := by
  subst offset
  rfl

private theorem sourceMacroSuffix_gates_length
    (inputs totalGates gate side offset : Nat)
    (source : RawSource) :
    (sourceMacroSuffix
      inputs totalGates gate side offset source).gates.length =
        RawBuilder.sourceMacroGateCount source := by
  cases source with
  | input index =>
      rfl
  | constant value =>
      cases value <;> rfl
  | gate index =>
      rfl

private theorem traceMacroSuffix_gates_length
    (inputs totalGates gate offset : Nat) :
    (traceMacroSuffix inputs totalGates gate offset).gates.length =
      18 := by
  rfl

private theorem apply_gateMacroSuffix_eq
    (inputs totalGates gate offset : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (sourceGate : RawGate)
    (offsetEq : offset = assembly.gates.length) :
    applyMacroSchedule assembly
        (gateMacroSuffix
          inputs totalGates gate offset sourceGate) =
      let left :=
        RawBuilder.appendSourceMacro
          inputs totalGates gate 0 assembly sourceGate.left
      let right :=
        RawBuilder.appendSourceMacro
          inputs totalGates gate 1 left sourceGate.right
      RawBuilder.appendTraceMacro
        inputs totalGates gate right := by
  let leftSchedule :=
    sourceMacroSuffix
      inputs totalGates gate 0 offset sourceGate.left
  let afterLeft :=
    RawBuilder.appendSourceMacro
      inputs totalGates gate 0 assembly sourceGate.left
  let rightOffset := offset + leftSchedule.gates.length
  let rightSchedule :=
    sourceMacroSuffix
      inputs totalGates gate 1 rightOffset sourceGate.right
  let afterRight :=
    RawBuilder.appendSourceMacro
      inputs totalGates gate 1 afterLeft sourceGate.right
  let traceOffset := rightOffset + rightSchedule.gates.length
  let traceSchedule :=
    traceMacroSuffix inputs totalGates gate traceOffset
  have leftApplied :
      applyMacroSchedule assembly leftSchedule = afterLeft := by
    exact apply_sourceMacroSuffix_eq
      inputs totalGates gate 0 offset assembly sourceGate.left offsetEq
  have leftLength :
      afterLeft.gates.length =
        assembly.gates.length + leftSchedule.gates.length := by
    have builderLength :=
      RawBuilder.appendSourceMacro_gates_length
        inputs totalGates gate 0 assembly sourceGate.left
    have scheduleLength :
        leftSchedule.gates.length =
          RawBuilder.sourceMacroGateCount sourceGate.left := by
      exact sourceMacroSuffix_gates_length
        inputs totalGates gate 0 offset sourceGate.left
    dsimp only [afterLeft]
    omega
  have rightOffsetEq :
      rightOffset = afterLeft.gates.length := by
    dsimp only [rightOffset]
    omega
  have rightApplied :
      applyMacroSchedule afterLeft rightSchedule = afterRight := by
    exact apply_sourceMacroSuffix_eq
      inputs totalGates gate 1 rightOffset afterLeft
      sourceGate.right rightOffsetEq
  have rightLength :
      afterRight.gates.length =
        afterLeft.gates.length + rightSchedule.gates.length := by
    have builderLength :=
      RawBuilder.appendSourceMacro_gates_length
        inputs totalGates gate 1 afterLeft sourceGate.right
    have scheduleLength :
        rightSchedule.gates.length =
          RawBuilder.sourceMacroGateCount sourceGate.right := by
      exact sourceMacroSuffix_gates_length
        inputs totalGates gate 1 rightOffset sourceGate.right
    dsimp only [afterRight]
    omega
  have traceOffsetEq :
      traceOffset = afterRight.gates.length := by
    dsimp only [traceOffset]
    omega
  have traceApplied :
      applyMacroSchedule afterRight traceSchedule =
        RawBuilder.appendTraceMacro
          inputs totalGates gate afterRight := by
    exact apply_traceMacroSuffix_eq
      inputs totalGates gate traceOffset afterRight traceOffsetEq
  have scheduledShape :
      gateMacroSuffix inputs totalGates gate offset sourceGate =
        appendMacroSchedule leftSchedule
          (appendMacroSchedule rightSchedule traceSchedule) := by
    rfl
  rw [scheduledShape, applyMacroSchedule_append, leftApplied,
    applyMacroSchedule_append, rightApplied, traceApplied]

private theorem apply_gateListSchedule_eq
    (inputs totalGates gate offset : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (sourceGates : List RawGate)
    (offsetEq : offset = assembly.gates.length) :
    applyMacroSchedule assembly
        (gateListSchedule
          inputs totalGates gate offset sourceGates) =
      RawBuilder.assembleGates
        inputs totalGates gate assembly sourceGates := by
  induction sourceGates generalizing gate offset assembly with
  | nil =>
      cases assembly
      unfold RawBuilder.assembleGates
      simp [gateListSchedule, applyMacroSchedule, emptyMacroSchedule]
  | cons sourceGate rest ih =>
      let current :=
        gateMacroSuffix inputs totalGates gate offset sourceGate
      let afterCurrent :=
        RawBuilder.appendTraceMacro inputs totalGates gate
          (RawBuilder.appendSourceMacro inputs totalGates gate 1
            (RawBuilder.appendSourceMacro inputs totalGates gate 0
              assembly sourceGate.left)
            sourceGate.right)
      let tailOffset := offset + current.gates.length
      have currentApplied :
          applyMacroSchedule assembly current = afterCurrent := by
        exact apply_gateMacroSuffix_eq
          inputs totalGates gate offset assembly sourceGate offsetEq
      have tailOffsetEq :
          tailOffset = afterCurrent.gates.length := by
        have lengths :=
          congrArg
            (fun result : RawBuilder.MacroAssembly =>
              result.gates.length)
            currentApplied
        simp only [applyMacroSchedule, List.length_append] at lengths
        dsimp only [tailOffset]
        omega
      have tailApplied :
          applyMacroSchedule afterCurrent
              (gateListSchedule inputs totalGates
                (gate + 1) tailOffset rest) =
            RawBuilder.assembleGates inputs totalGates
              (gate + 1) afterCurrent rest :=
        ih (gate + 1) tailOffset afterCurrent tailOffsetEq
      change
        applyMacroSchedule assembly
            (appendMacroSchedule current
              (gateListSchedule inputs totalGates
                (gate + 1) tailOffset rest)) =
          RawBuilder.assembleGates inputs totalGates
            (gate + 1) afterCurrent rest
      rw [applyMacroSchedule_append, currentApplied, tailApplied]

private theorem macroSchedule_eq_builder (circuit : RawCircuit) :
    applyMacroSchedule RawBuilder.emptyAssembly
        (macroSchedule circuit) =
      RawBuilder.macroAssembly circuit := by
  exact apply_gateListSchedule_eq
    circuit.inputCount circuit.gates.length 0 0
    RawBuilder.emptyAssembly circuit.gates rfl

private theorem macroSchedule_gates_eq_builder
    (circuit : RawCircuit) :
    (macroSchedule circuit).gates =
      (RawBuilder.macroAssembly circuit).gates := by
  have equality :=
    congrArg (fun assembly : RawBuilder.MacroAssembly => assembly.gates)
      (macroSchedule_eq_builder circuit)
  simpa [applyMacroSchedule, RawBuilder.emptyAssembly] using equality

private theorem macroSchedule_checks_eq_builder
    (circuit : RawCircuit) :
    (macroSchedule circuit).checks =
      (RawBuilder.macroAssembly circuit).checks := by
  have equality :=
    congrArg (fun assembly : RawBuilder.MacroAssembly => assembly.checks)
      (macroSchedule_eq_builder circuit)
  simpa [applyMacroSchedule, RawBuilder.emptyAssembly] using equality

/-! ### Right-folded prefix and final instance schedule -/

private structure PrefixSchedule where
  gates : List RawGate
  output : RawSource
deriving BEq, DecidableEq, Repr

private def prefixSchedule :
    Nat → List RawSource → PrefixSchedule
  | _, [] =>
      { gates := []
        output := .constant false }
  | _, [check] =>
      { gates := []
        output := check }
  | offset, head :: next :: rest =>
      let tail := prefixSchedule offset (next :: rest)
      let linkOffset := offset + tail.gates.length
      { gates := tail.gates ++
          templateSuffix linkOffset
            (binding2 tail.output head) prefixTemplate
        output := .gate (linkOffset + 1) }

private def applyPrefixSchedule
    (baseGates : List RawGate)
    (scheduled : PrefixSchedule) :
    RawBuilder.PrefixAssembly :=
  { gates := baseGates ++ scheduled.gates
    output := scheduled.output }

private theorem apply_prefixSchedule_eq
    (offset : Nat) (baseGates : List RawGate)
    (checks : List RawSource)
    (offsetEq : offset = baseGates.length) :
    applyPrefixSchedule baseGates
        (prefixSchedule offset checks) =
      RawBuilder.appendPrefix baseGates checks := by
  induction checks generalizing offset baseGates with
  | nil =>
      cases baseGates <;>
        simp [prefixSchedule, applyPrefixSchedule,
          RawBuilder.appendPrefix]
  | cons head rest ih =>
      cases rest with
      | nil =>
          cases baseGates <;>
            simp [prefixSchedule, applyPrefixSchedule,
              RawBuilder.appendPrefix]
      | cons next tail =>
          let tailSchedule :=
            prefixSchedule offset (next :: tail)
          have tailEq :
              applyPrefixSchedule baseGates tailSchedule =
                RawBuilder.appendPrefix baseGates (next :: tail) := by
            exact ih offset baseGates offsetEq
          simp only [prefixSchedule, RawBuilder.appendPrefix]
          rw [← tailEq]
          apply RawBuilder.PrefixAssembly.ext
          · simp [applyPrefixSchedule, tailSchedule,
              RawBuilder.appendTemplate, templateSuffix_eq_builder,
              prefixTemplate_eq_builder, binding2_eq_builder,
              offsetEq, List.append_assoc]
          · simp [applyPrefixSchedule, tailSchedule, offsetEq]

private theorem prefixSchedule_full_gates_eq_builder
    (baseGates : List RawGate) (checks : List RawSource) :
    baseGates ++
        (prefixSchedule baseGates.length checks).gates =
      (RawBuilder.appendPrefix baseGates checks).gates := by
  have equality :=
    congrArg (fun assembly : RawBuilder.PrefixAssembly => assembly.gates)
      (apply_prefixSchedule_eq
        baseGates.length baseGates checks rfl)
  exact equality

private theorem prefixSchedule_output_eq_builder
    (baseGates : List RawGate) (checks : List RawSource) :
    (prefixSchedule baseGates.length checks).output =
      (RawBuilder.appendPrefix baseGates checks).output := by
  have equality :=
    congrArg (fun assembly : RawBuilder.PrefixAssembly => assembly.output)
      (apply_prefixSchedule_eq
        baseGates.length baseGates checks rfl)
  exact equality

private theorem prefixSchedule_baseline_eq_builder
    (baseGates : List RawGate) (checks : List RawSource) :
    baseGates.length +
        (prefixSchedule baseGates.length checks).gates.length =
      (RawBuilder.appendPrefix baseGates checks).gates.length := by
  have equality :=
    congrArg List.length
      (prefixSchedule_full_gates_eq_builder baseGates checks)
  simpa using equality

private def outputGateIndex : RawSource → Nat
  | .gate index => index
  | _ => 0

/-- Structurally scheduled raw locked-NAND target.  This is pure data
recursion over `raw.normalize`; it is not an executable machine claim. -/
def scheduledInstance (raw : RawCircuit) : RawLockedInstance :=
  let circuit := raw.normalize
  let macros := macroSchedule circuit
  let prefixAssembly :=
    prefixSchedule macros.gates.length macros.checks
  let baseline :=
    macros.gates.length + prefixAssembly.gates.length
  let prefixGates := macros.gates ++ prefixAssembly.gates
  let outputTrace : RawSource :=
    .input
      (traceCoordinate circuit.inputCount circuit.gates.length
        (outputGateIndex circuit.output))
  let finalGates :=
    prefixGates ++
      templateSuffix baseline
        (binding3
          (.input
            (finalLockCoordinate
              circuit.inputCount circuit.gates.length))
          prefixAssembly.output outputTrace)
        finalTemplate
  { candidate :=
      { inputCount :=
          circuit.inputCount + 6 * circuit.gates.length + 1
        gates := finalGates
        outputs :=
          (List.range baseline).map RawSource.gate ++
            [.gate (baseline + 3)] }
    baseline := baseline }

private theorem finalGates_eq_builder
    (prefixAssembly : RawBuilder.PrefixAssembly)
    (first second third : RawSource) :
    prefixAssembly.gates ++
        templateSuffix prefixAssembly.gates.length
          (binding3 first second third) finalTemplate =
      RawBuilder.appendTemplate prefixAssembly.gates
        (RawBuilder.rawBinding3 first second third)
        RawBuilder.finalTemplate := by
  rw [binding3_eq_builder, finalTemplate_eq_builder,
    templateSuffix_eq_builder]
  rfl

/-- The pure structural schedule reconstructs the complete direct raw target
exactly for every raw circuit, including normalization-only inputs. -/
theorem scheduledInstance_eq_rawLockedInstance (raw : RawCircuit) :
    scheduledInstance raw =
      RawBuilder.rawLockedInstance raw := by
  unfold scheduledInstance RawBuilder.rawLockedInstance
  simp only
  rw [macroSchedule_gates_eq_builder,
    macroSchedule_checks_eq_builder]
  rw [prefixSchedule_baseline_eq_builder,
    prefixSchedule_full_gates_eq_builder,
    prefixSchedule_output_eq_builder]
  rw [finalGates_eq_builder]
  simp [finalLockCoordinate, RawBuilder.finalLockCoordinate,
    traceCoordinate, RawBuilder.traceCoordinate,
    outputGateIndex, RawBuilder.outputGateIndex]
  rfl

/-! ### Header, gate, output, and final token schedule -/

private def headerTokenSchedule
    (inputCount gateCount outputCount : Nat) : List Token :=
  .version0 ::
    (encodeNatTokens inputCount ++
      encodeNatTokens gateCount ++
      encodeNatTokens outputCount)

private def outputTokenSchedule
    (outputs : List RawSource) (baseline : Nat) : List Token :=
  [.programEnd] ++
    encodeSourceListTokens outputs ++
    [.outputsEnd, .threshold] ++
    encodeNatTokens baseline ++
    [.instanceEnd]

/-- Independent strict-v0 token schedule for the structurally scheduled
instance. -/
def scheduledTokens (raw : RawCircuit) : List Token :=
  let scheduled := scheduledInstance raw
  headerTokenSchedule
      scheduled.candidate.inputCount
      scheduled.candidate.gates.length
      scheduled.candidate.outputs.length ++
    encodeGateListTokens scheduled.candidate.gates ++
    outputTokenSchedule scheduled.candidate.outputs scheduled.baseline

/-- Header, gate, output, threshold, and terminator schedules concatenate to
the canonical strict-v0 token word of the direct raw target. -/
theorem scheduledTokens_eq_encodeLockedInstanceTokens
    (raw : RawCircuit) :
    scheduledTokens raw =
      encodeLockedInstanceTokens
        (RawBuilder.rawLockedInstance raw) := by
  unfold scheduledTokens
  rw [scheduledInstance_eq_rawLockedInstance]
  unfold headerTokenSchedule outputTokenSchedule
    encodeLockedInstanceTokens
  simp [List.append_assoc]

end PNP.Concrete.LockedNAND.TargetEmitterSchedule
