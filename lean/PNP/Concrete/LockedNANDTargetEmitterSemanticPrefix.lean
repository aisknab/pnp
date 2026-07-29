/-
Copyright (c) 2026 PNP Labs.

Pure right-fold semantics for the locked-NAND target-emitter prefix.

This file relates the controller's logical natural-number check stack to the
independent raw builder.  It executes no work machine and supplies no schedule
or certificate to the executable controller.
-/

import PNP.Concrete.LockedNANDTargetEmitterSemanticSchedule

namespace PNP.Concrete.LockedNAND.TargetEmitterSemanticPrefix

open PNP.Concrete

abbrev Runtime := TargetEmitterProgramSemantics.Runtime
abbrev PrefixAssembly := RawBuilder.PrefixAssembly

def gateChecks (coordinates : List Nat) : List RawSource :=
  coordinates.map RawSource.gate

/-- Builder-independent right-fold suffix at a fixed pre-existing gate
offset.  Its gates are exactly the two-gate raw prefix template at each link. -/
def prefixSchedule (offset : Nat) :
    List RawSource → PrefixAssembly
  | [] =>
      { gates := []
        output := .constant false }
  | [check] =>
      { gates := []
        output := check }
  | head :: next :: rest =>
      let tail := prefixSchedule offset (next :: rest)
      let linkOffset := offset + tail.gates.length
      { gates :=
          tail.gates ++
            RawBuilder.prefixTemplate.map
              (RawBuilder.instantiateGate linkOffset
                (RawBuilder.rawBinding2 tail.output head))
        output := .gate (linkOffset + 1) }

private def applyPrefixSchedule
    (baseGates : List RawGate)
    (scheduled : PrefixAssembly) : PrefixAssembly :=
  { gates := baseGates ++ scheduled.gates
    output := scheduled.output }

private theorem applyPrefixSchedule_eq
    (offset : Nat) (baseGates : List RawGate)
    (checks : List RawSource)
    (offsetEq : offset = baseGates.length) :
    applyPrefixSchedule baseGates (prefixSchedule offset checks) =
      RawBuilder.appendPrefix baseGates checks := by
  induction checks generalizing offset baseGates with
  | nil =>
      cases baseGates <;>
        simp [prefixSchedule, applyPrefixSchedule,
          RawBuilder.appendPrefix]
  | cons head rest inductionHypothesis =>
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
            exact inductionHypothesis offset baseGates offsetEq
          simp only [prefixSchedule, RawBuilder.appendPrefix]
          rw [← tailEq]
          apply RawBuilder.PrefixAssembly.ext
          · simp [applyPrefixSchedule, tailSchedule,
              RawBuilder.appendTemplate, offsetEq,
              List.append_assoc]
          · simp [applyPrefixSchedule, tailSchedule, offsetEq]

theorem prefixSchedule_gates_eq_appendPrefix
    (baseGates : List RawGate) (checks : List RawSource) :
    baseGates ++
        (prefixSchedule baseGates.length checks).gates =
      (RawBuilder.appendPrefix baseGates checks).gates := by
  have equality :=
    congrArg (fun assembly : PrefixAssembly => assembly.gates)
      (applyPrefixSchedule_eq
        baseGates.length baseGates checks rfl)
  exact equality

theorem prefixSchedule_output_eq_appendPrefix
    (baseGates : List RawGate) (checks : List RawSource) :
    (prefixSchedule baseGates.length checks).output =
      (RawBuilder.appendPrefix baseGates checks).output := by
  have equality :=
    congrArg (fun assembly : PrefixAssembly => assembly.output)
      (applyPrefixSchedule_eq
        baseGates.length baseGates checks rfl)
  exact equality

theorem prefixSchedule_gates_length
    (offset : Nat) (checks : List RawSource) :
    (prefixSchedule offset checks).gates.length =
      2 * (checks.length - 1) := by
  induction checks with
  | nil =>
      rfl
  | cons head rest inductionHypothesis =>
      cases rest with
      | nil =>
          rfl
      | cons next tail =>
          simp only [prefixSchedule, List.length_append,
            List.length_map, inductionHypothesis,
            RawBuilder.prefixTemplate_length, List.length_cons]
          omega

private theorem encodeGateListTokens_append
    (first second : List RawGate) :
    encodeGateListTokens (first ++ second) =
      encodeGateListTokens first ++ encodeGateListTokens second := by
  induction first with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      simp only [List.cons_append, encodeGateListTokens,
        inductionHypothesis, List.append_assoc]

structure PrefixRun where
  runtime : Runtime
  output : RawSource

/-- Pure counterpart of the controller's right fold.  The recursion first
folds the tail, exactly as `RawBuilder.appendPrefix` does.  The first link uses
`firstPrefixResult`; every later link uses `nextPrefixResult`. -/
def runPrefix : List Nat → Runtime → PrefixRun
  | [], runtime =>
      { runtime := runtime
        output := .constant false }
  | [check], runtime =>
      { runtime :=
          { runtime with scratch := check, checks := [] }
        output := .gate check }
  | head :: next :: rest, runtime =>
      let tailInput := { runtime with checks := next :: rest }
      let tail := runPrefix (next :: rest) tailInput
      let final :=
        match rest with
        | [] =>
            TargetEmitterProgramSemantics.firstPrefixResult
              { tail.runtime with checks := [head] } [] head
        | _ :: _ =>
            TargetEmitterProgramSemantics.nextPrefixResult
              { tail.runtime with scratch := head, checks := [] }
      { runtime := final
        output := .gate final.registers.outputIndex }
termination_by checks => checks.length

private theorem firstPrefix_appends_link
    (runtime : Runtime) (newest : Nat) :
    (TargetEmitterProgramSemantics.firstPrefixResult
      runtime [] newest).targetTokens =
        runtime.targetTokens ++
          encodeGateListTokens
            (RawBuilder.prefixTemplate.map
              (RawBuilder.instantiateGate
                runtime.registers.outputIndex
                (RawBuilder.rawBinding2
                  (.gate runtime.scratch) (.gate newest)))) := by
  rw [TargetEmitterProgramSemantics.firstPrefixResult_targetTokens]
  rfl

private theorem nextPrefix_appends_link
    (runtime : Runtime) :
    (TargetEmitterProgramSemantics.nextPrefixResult
      runtime).targetTokens =
        runtime.targetTokens ++
          encodeGateListTokens
            (RawBuilder.prefixTemplate.map
              (RawBuilder.instantiateGate
                (runtime.registers.outputIndex + 1)
                (RawBuilder.rawBinding2
                  (.gate runtime.registers.outputIndex)
                  (.gate runtime.scratch)))) := by
  rw [TargetEmitterProgramSemantics.nextPrefixResult_targetTokens]
  rfl

/-- Compact invariant relating the pure controller fold to its raw suffix. -/
structure PrefixCorrect
    (offset : Nat) (coordinates : List Nat)
    (initialTokens : List Token) (result : PrefixRun) : Prop where
  output :
    result.output =
      (prefixSchedule offset (gateChecks coordinates)).output
  targetTokens :
    result.runtime.targetTokens =
      initialTokens ++
        encodeGateListTokens
          (prefixSchedule offset (gateChecks coordinates)).gates
  outputIndex :
    result.runtime.registers.outputIndex =
      offset +
        ((prefixSchedule offset
          (gateChecks coordinates)).gates.length - 1)
  checks :
    result.runtime.checks = []
  output_is_gate :
    (prefixSchedule offset
        (gateChecks coordinates)).gates ≠ [] →
      result.output =
        .gate result.runtime.registers.outputIndex

theorem runPrefix_correct
    (offset : Nat) (coordinates : List Nat)
    (initialTokens : List Token) (runtime : Runtime)
    (scratch : runtime.scratch = 0)
    (outputIndex : runtime.registers.outputIndex = offset)
    (checks : runtime.checks = coordinates)
    (targetTokens : runtime.targetTokens = initialTokens) :
    PrefixCorrect offset coordinates initialTokens
      (runPrefix coordinates runtime) := by
  induction coordinates generalizing runtime with
  | nil =>
      refine
        { output := ?_
          targetTokens := ?_
          outputIndex := ?_
          checks := ?_
          output_is_gate := ?_ }
      · simp [runPrefix, gateChecks, prefixSchedule]
      · simpa [runPrefix, gateChecks, prefixSchedule,
          encodeGateListTokens] using targetTokens
      · simpa [runPrefix, gateChecks, prefixSchedule] using outputIndex
      · simpa [runPrefix] using checks
      · simp [gateChecks, prefixSchedule]
  | cons head rest inductionHypothesis =>
      cases rest with
      | nil =>
          refine
            { output := ?_
              targetTokens := ?_
              outputIndex := ?_
              checks := ?_
              output_is_gate := ?_ }
          · simp [runPrefix, gateChecks, prefixSchedule]
          · simpa [runPrefix, gateChecks, prefixSchedule,
              encodeGateListTokens] using targetTokens
          · simpa [runPrefix, gateChecks, prefixSchedule] using outputIndex
          · simp [runPrefix]
          · simp [gateChecks, prefixSchedule]
      | cons next tail =>
          let tailInput : Runtime :=
            { runtime with checks := next :: tail }
          have tailCorrect :
              PrefixCorrect offset (next :: tail) initialTokens
                (runPrefix (next :: tail) tailInput) := by
            apply inductionHypothesis
            · simpa [tailInput] using scratch
            · simpa [tailInput] using outputIndex
            · simp [tailInput]
            · simpa [tailInput] using targetTokens
          cases tail with
          | nil =>
              let tailRun := runPrefix [next] tailInput
              let finalInput : Runtime :=
                { tailRun.runtime with checks := [head] }
              let final :=
                TargetEmitterProgramSemantics.firstPrefixResult
                  finalInput [] head
              rw [runPrefix]
              change
                PrefixCorrect offset [head, next] initialTokens
                  { runtime := final
                    output := .gate final.registers.outputIndex }
              have finalInput_targetTokens :
                  finalInput.targetTokens = initialTokens := by
                simpa [finalInput, tailRun, gateChecks,
                  prefixSchedule, encodeGateListTokens] using
                  tailCorrect.targetTokens
              have finalInput_outputIndex :
                  finalInput.registers.outputIndex = offset := by
                simpa [finalInput, tailRun, gateChecks,
                  prefixSchedule] using
                  tailCorrect.outputIndex
              have appended :=
                firstPrefix_appends_link finalInput head
              refine
                { output := ?_
                  targetTokens := ?_
                  outputIndex := ?_
                  checks := ?_
                  output_is_gate := ?_ }
              · simp [final,
                  TargetEmitterProgramSemantics.firstPrefixResult_registers,
                  finalInput_outputIndex, gateChecks, prefixSchedule]
              · rw [appended]
                rw [finalInput_targetTokens, finalInput_outputIndex]
                simp [finalInput, tailRun, runPrefix, tailInput,
                  gateChecks, prefixSchedule]
              · simp [final,
                  TargetEmitterProgramSemantics.firstPrefixResult_registers,
                  finalInput_outputIndex, gateChecks, prefixSchedule,
                  RawBuilder.prefixTemplate_length]
              · simp [final, finalInput,
                  TargetEmitterProgramSemantics.firstPrefixResult_checks]
              · intro nonempty
                simp [final,
                  TargetEmitterProgramSemantics.firstPrefixResult_registers]
          | cons third more =>
              let tailRun :=
                runPrefix (next :: third :: more) tailInput
              let tailSchedule :=
                prefixSchedule offset
                  (gateChecks (next :: third :: more))
              have tailNonempty :
                  tailSchedule.gates ≠ [] := by
                intro empty
                have lengths := congrArg List.length empty
                simp [tailSchedule, prefixSchedule_gates_length,
                  gateChecks] at lengths
              have tailOutput :=
                tailCorrect.output_is_gate tailNonempty
              have tailScheduleOutput :
                  tailSchedule.output =
                    .gate tailRun.runtime.registers.outputIndex := by
                exact tailCorrect.output.symm.trans tailOutput
              have tailLengthPositive :
                  0 < tailSchedule.gates.length := by
                cases gateListEq : tailSchedule.gates with
                | nil =>
                    exact False.elim (tailNonempty gateListEq)
                | cons gate rest =>
                    simp
              have linkOffset :
                  tailRun.runtime.registers.outputIndex + 1 =
                    offset + tailSchedule.gates.length := by
                rw [show
                  tailRun.runtime.registers.outputIndex =
                    offset + (tailSchedule.gates.length - 1) from
                      tailCorrect.outputIndex]
                omega
              let finalInput : Runtime :=
                { tailRun.runtime with
                  scratch := head
                  checks := [] }
              let final :=
                TargetEmitterProgramSemantics.nextPrefixResult finalInput
              let scheduledLink : List RawGate :=
                RawBuilder.prefixTemplate.map
                  (RawBuilder.instantiateGate
                    (offset + tailSchedule.gates.length)
                    (RawBuilder.rawBinding2 tailSchedule.output
                      (.gate head)))
              have scheduleEq :
                  prefixSchedule offset
                      (gateChecks (head :: next :: third :: more)) =
                    { gates := tailSchedule.gates ++ scheduledLink
                      output :=
                        .gate
                          (offset + tailSchedule.gates.length + 1) } := by
                rfl
              have emittedLinkEq :
                  RawBuilder.prefixTemplate.map
                      (RawBuilder.instantiateGate
                        (finalInput.registers.outputIndex + 1)
                        (RawBuilder.rawBinding2
                          (.gate finalInput.registers.outputIndex)
                          (.gate finalInput.scratch))) =
                    scheduledLink := by
                simp only [finalInput, scheduledLink]
                rw [tailScheduleOutput, linkOffset]
              have scheduledLinkLength :
                  scheduledLink.length = 2 := by
                simp [scheduledLink,
                  RawBuilder.prefixTemplate_length]
              rw [runPrefix]
              change
                PrefixCorrect offset (head :: next :: third :: more)
                  initialTokens
                  { runtime := final
                    output := .gate final.registers.outputIndex }
              have appended :=
                nextPrefix_appends_link finalInput
              refine
                { output := ?_
                  targetTokens := ?_
                  outputIndex := ?_
                  checks := ?_
                  output_is_gate := ?_ }
              · rw [scheduleEq]
                simp only
                rw [show
                  final.registers =
                    { finalInput.registers with
                      outputIndex :=
                        finalInput.registers.outputIndex + 2 } by
                    exact
                      TargetEmitterProgramSemantics.nextPrefixResult_registers
                        finalInput]
                simp only [finalInput]
                exact congrArg RawSource.gate
                  (by
                    simpa [Nat.add_assoc] using
                      congrArg Nat.succ linkOffset)
              · rw [appended]
                rw [scheduleEq, encodeGateListTokens_append,
                  emittedLinkEq]
                simp only [finalInput]
                rw [show
                  tailRun.runtime.targetTokens =
                    initialTokens ++
                      encodeGateListTokens tailSchedule.gates from
                        tailCorrect.targetTokens]
                simp [List.append_assoc]
              · rw [scheduleEq]
                simp only [List.length_append]
                rw [show
                  final.registers =
                    { finalInput.registers with
                      outputIndex :=
                        finalInput.registers.outputIndex + 2 } by
                    exact
                      TargetEmitterProgramSemantics.nextPrefixResult_registers
                        finalInput]
                simp only [finalInput]
                rw [scheduledLinkLength]
                omega
              · simp [final, finalInput,
                  TargetEmitterProgramSemantics.nextPrefixResult_checks]
              · intro nonempty
                rfl

/-- The total builder branch for an empty check stack emits no prefix gate
and retains the explicit false source used by the final-zero block. -/
theorem runPrefix_empty (runtime : Runtime) :
    runPrefix [] runtime =
      { runtime := runtime
        output := .constant false } := by
  simp [runPrefix]

/-- Exact raw-builder boundary for an arbitrary logical gate-check stack.
The pre-existing token prefix and gates are retained verbatim. -/
theorem runPrefix_appends_builder
    (baseGates : List RawGate) (coordinates : List Nat)
    (tokenPrefix : List Token) (runtime : Runtime)
    (scratch : runtime.scratch = 0)
    (outputIndex :
      runtime.registers.outputIndex = baseGates.length)
    (checks : runtime.checks = coordinates)
    (targetTokens :
      runtime.targetTokens =
        tokenPrefix ++ encodeGateListTokens baseGates) :
    let result := runPrefix coordinates runtime
    let built :=
      RawBuilder.appendPrefix baseGates (gateChecks coordinates)
    result.output = built.output ∧
      result.runtime.targetTokens =
        tokenPrefix ++ encodeGateListTokens built.gates := by
  let result := runPrefix coordinates runtime
  let scheduled :=
    prefixSchedule baseGates.length (gateChecks coordinates)
  let built :=
    RawBuilder.appendPrefix baseGates (gateChecks coordinates)
  have correct :=
    runPrefix_correct baseGates.length coordinates
      (tokenPrefix ++ encodeGateListTokens baseGates)
      runtime scratch outputIndex checks targetTokens
  refine ⟨?_, ?_⟩
  · exact correct.output.trans
      (prefixSchedule_output_eq_appendPrefix
        baseGates (gateChecks coordinates))
  · calc
      result.runtime.targetTokens =
          (tokenPrefix ++ encodeGateListTokens baseGates) ++
            encodeGateListTokens scheduled.gates :=
        correct.targetTokens
      _ =
          tokenPrefix ++
            (encodeGateListTokens baseGates ++
              encodeGateListTokens scheduled.gates) := by
        simp [List.append_assoc]
      _ =
          tokenPrefix ++
            encodeGateListTokens
              (baseGates ++ scheduled.gates) := by
        rw [encodeGateListTokens_append]
      _ =
          tokenPrefix ++ encodeGateListTokens built.gates := by
        rw [prefixSchedule_gates_eq_appendPrefix]

private def GateEncodedChecks
    (assembly : RawBuilder.MacroAssembly) : Prop :=
  gateChecks
      (TargetEmitterSemanticSchedule.checkCoordinates
        assembly.checks) =
    assembly.checks

private theorem gateEncodedChecks_append
    (checks : List RawSource) (index : Nat)
    (encoded :
      gateChecks
          (TargetEmitterSemanticSchedule.checkCoordinates checks) =
        checks) :
    gateChecks
        (TargetEmitterSemanticSchedule.checkCoordinates
          (checks ++ [.gate index])) =
      checks ++ [.gate index] := by
  have base := encoded
  simp only [gateChecks,
    TargetEmitterSemanticSchedule.checkCoordinates,
    List.map_map] at base
  simp [gateChecks,
    TargetEmitterSemanticSchedule.checkCoordinates,
    List.map_map, RawBuilder.outputGateIndex, base]

private theorem appendSourceMacro_preserves_gateEncodedChecks
    (inputs totalGates gate side : Nat)
    (assembly : RawBuilder.MacroAssembly) (source : RawSource)
    (encoded : GateEncodedChecks assembly) :
    GateEncodedChecks
      (RawBuilder.appendSourceMacro
        inputs totalGates gate side assembly source) := by
  cases source with
  | input index =>
      simpa [GateEncodedChecks, RawBuilder.appendSourceMacro] using
        gateEncodedChecks_append assembly.checks
          (assembly.gates.length + 7) encoded
  | constant value =>
      cases value with
      | false =>
          simpa [GateEncodedChecks,
            RawBuilder.appendSourceMacro] using
              gateEncodedChecks_append assembly.checks
                (assembly.gates.length + 2) encoded
      | true =>
          simpa [GateEncodedChecks,
            RawBuilder.appendSourceMacro] using
              gateEncodedChecks_append assembly.checks
                (assembly.gates.length + 1) encoded
  | gate index =>
      simpa [GateEncodedChecks, RawBuilder.appendSourceMacro] using
        gateEncodedChecks_append assembly.checks
          (assembly.gates.length + 7) encoded

private theorem appendTraceMacro_preserves_gateEncodedChecks
    (inputs totalGates gate : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (encoded : GateEncodedChecks assembly) :
    GateEncodedChecks
      (RawBuilder.appendTraceMacro
        inputs totalGates gate assembly) := by
  simpa [GateEncodedChecks, RawBuilder.appendTraceMacro] using
    gateEncodedChecks_append assembly.checks
      (assembly.gates.length + 15) encoded

private theorem assembleGates_preserves_gateEncodedChecks
    (inputs totalGates gate : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (sourceGates : List RawGate)
    (encoded : GateEncodedChecks assembly) :
    GateEncodedChecks
      (RawBuilder.assembleGates
        inputs totalGates gate assembly sourceGates) := by
  induction sourceGates generalizing gate assembly with
  | nil =>
      simpa [RawBuilder.assembleGates] using encoded
  | cons sourceGate rest inductionHypothesis =>
      simp only [RawBuilder.assembleGates]
      apply inductionHypothesis
      apply appendTraceMacro_preserves_gateEncodedChecks
      apply appendSourceMacro_preserves_gateEncodedChecks
      apply appendSourceMacro_preserves_gateEncodedChecks
      exact encoded

/-- Every check emitted by the raw macro builder is a gate check, so mapping
through the controller's natural-number stack loses no source information. -/
theorem macroAssembly_gateChecks
    (circuit : RawCircuit) :
    gateChecks
        (TargetEmitterSemanticSchedule.checkCoordinates
          (RawBuilder.macroAssembly circuit).checks) =
      (RawBuilder.macroAssembly circuit).checks := by
  apply assembleGates_preserves_gateEncodedChecks
  rfl

/-- The logical controller stack contains exactly the builder's three checks
per source gate. -/
theorem macroAssembly_checkCoordinates_length
    (circuit : RawCircuit) :
    (TargetEmitterSemanticSchedule.checkCoordinates
      (RawBuilder.macroAssembly circuit).checks).length =
        3 * circuit.gates.length := by
  rw [TargetEmitterSemanticSchedule.checkCoordinates,
    List.length_map, RawBuilder.macroAssembly_checks_length]

/-- Exact prefix boundary for any macro assembly whose check list has the
builder's gate-only shape. -/
theorem runMacroPrefix_appends_builder
    (inputs totalGates gate : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (tokenPrefix : List Token) (runtime : Runtime)
    (invariant :
      TargetEmitterSemanticSchedule.MacroInvariant
        inputs totalGates gate assembly tokenPrefix runtime)
    (gateShape :
      gateChecks
          (TargetEmitterSemanticSchedule.checkCoordinates
            assembly.checks) =
        assembly.checks) :
    let result :=
      runPrefix
        (TargetEmitterSemanticSchedule.checkCoordinates
          assembly.checks)
        runtime
    let built :=
      RawBuilder.appendPrefix assembly.gates assembly.checks
    result.output = built.output ∧
      result.runtime.targetTokens =
        tokenPrefix ++ encodeGateListTokens built.gates := by
  have exactRun :=
    runPrefix_appends_builder assembly.gates
      (TargetEmitterSemanticSchedule.checkCoordinates
        assembly.checks)
      tokenPrefix runtime invariant.scratch invariant.outputIndex
      invariant.checks invariant.targetTokens
  rw [gateShape] at exactRun
  exact exactRun

end PNP.Concrete.LockedNAND.TargetEmitterSemanticPrefix
