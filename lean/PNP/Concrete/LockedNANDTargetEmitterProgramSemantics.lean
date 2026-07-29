/-
Copyright (c) 2026 PNP Labs.

Pure operational semantics for the closed locked-NAND target-emitter plan.

This module interprets `TargetEmitterPlan.Primitive` over logical data only:
the captured source coordinate, unary scratch value, six retained registers,
LIFO check stack, and emitted target-token prefix.  It contains no work
machine, controller graph, decoder call, or host-side schedule lookup.

The semantics deliberately records both local accept and local reject
outcomes.  In particular, an empty check-stack pop is the controller branch
which selects the zero-check final block; it is not treated as an interpreter
failure.
-/

import PNP.Concrete.LockedNANDTargetEmitterPlan

namespace PNP.Concrete.LockedNAND.TargetEmitterProgramSemantics

open PNP.Concrete
open TargetEmitterPlan

/-! ### Pure logical runtime -/

structure Runtime where
  captured : Nat
  scratch : Nat
  registers : TargetEmitter.UnaryRegisters
  checks : List Nat
  targetTokens : List Token
deriving BEq, DecidableEq, Repr

inductive Outcome where
  | accepted (runtime : Runtime)
  | rejected (runtime : Runtime)
deriving BEq, DecidableEq, Repr

def registerValue
    (registers : TargetEmitter.UnaryRegisters) :
    Counter → Option Nat
  | .inputCount => some registers.inputCount
  | .normalizedGateCount =>
      some registers.normalizedGateCount
  | .carrierWidth => some registers.carrierWidth
  | .baseline => some registers.baseline
  | .currentGate => some registers.currentGate
  | .outputIndex => some registers.outputIndex
  | .captured | .scratch => none

def incrementRegister
    (registers : TargetEmitter.UnaryRegisters) :
    Counter → Option TargetEmitter.UnaryRegisters
  | .inputCount =>
      some { registers with
        inputCount := registers.inputCount + 1 }
  | .normalizedGateCount =>
      some { registers with
        normalizedGateCount :=
          registers.normalizedGateCount + 1 }
  | .carrierWidth =>
      some { registers with
        carrierWidth := registers.carrierWidth + 1 }
  | .baseline =>
      some { registers with
        baseline := registers.baseline + 1 }
  | .currentGate =>
      some { registers with
        currentGate := registers.currentGate + 1 }
  | .outputIndex =>
      some { registers with
        outputIndex := registers.outputIndex + 1 }
  | .captured | .scratch => none

/-- Remove the newest (farthest physical) check record. -/
def popNewest : List Nat → Option (List Nat × Nat)
  | [] => none
  | value :: rest =>
      match popNewest rest with
      | none => some ([], value)
      | some (prior, newest) =>
          some (value :: prior, newest)

theorem popNewest_append_singleton
    (prior : List Nat) (value : Nat) :
    popNewest (prior ++ [value]) = some (prior, value) := by
  induction prior with
  | nil =>
      rfl
  | cons head rest ih =>
      simp only [List.cons_append, popNewest, ih]

def addCounter
    (counter : Counter) (runtime : Runtime) :
    Option Runtime :=
  match counter with
  | .captured =>
      some { runtime with
        scratch := runtime.scratch + runtime.captured }
  | .scratch => none
  | counter =>
      match registerValue runtime.registers counter with
      | none => none
      | some value =>
          some { runtime with
            scratch := runtime.scratch + value }

/-- One primitive's abstract local-machine outcome.

`reloadCaptured` is additive: the literal reload primitive scans the existing
scratch payload before extending it by the captured unary coordinate. -/
def step (primitive : Primitive)
    (runtime : Runtime) : Option Outcome :=
  match primitive with
  | .append _mode token =>
      some (.accepted
        { runtime with
          targetTokens := runtime.targetTokens ++ [token] })
  | .resetScratch =>
      some (.accepted { runtime with scratch := 0 })
  | .addRegister counter =>
      (addCounter counter runtime).map .accepted
  | .reloadCaptured =>
      some (.accepted
        { runtime with
          scratch := runtime.scratch + runtime.captured })
  | .incrementScratch =>
      some (.accepted
        { runtime with scratch := runtime.scratch + 1 })
  | .emitScratchNat _mode =>
      some (.accepted
        { runtime with
          targetTokens :=
            runtime.targetTokens ++
              encodeNatTokens runtime.scratch })
  | .pushCheck =>
      some (.accepted
        { runtime with
          checks := runtime.checks ++ [runtime.scratch] })
  | .popCheck =>
      match popNewest runtime.checks with
      | none =>
          some (.rejected runtime)
      | some (prior, newest) =>
          some (.accepted
            { runtime with
              scratch := newest
              checks := prior })
  | .compareRegister counter =>
      match registerValue runtime.registers counter with
      | none => none
      | some value =>
          if runtime.scratch = value then
            some (.accepted runtime)
          else
            some (.rejected runtime)
  | .incrementRegister counter =>
      match incrementRegister runtime.registers counter with
      | none => none
      | some registers =>
          some (.accepted { runtime with registers := registers })

/-- Sequential interpretation stops at the first local rejection.  `none`
means that the closed program requested a non-materializable counter
operation, matching the primitive compiler's rejected cases. -/
def run : List Primitive → Runtime → Option Outcome
  | [], runtime => some (.accepted runtime)
  | primitive :: rest, runtime =>
      match step primitive runtime with
      | none => none
      | some (.rejected final) =>
          some (.rejected final)
      | some (.accepted next) =>
          run rest next

theorem run_nil (runtime : Runtime) :
    run [] runtime = some (.accepted runtime) := by
  rfl

theorem run_cons (primitive : Primitive)
    (rest : List Primitive) (runtime : Runtime) :
    run (primitive :: rest) runtime =
      match step primitive runtime with
      | none => none
      | some (.rejected final) =>
          some (.rejected final)
      | some (.accepted next) =>
          run rest next := by
  rfl

theorem run_append
    (first second : List Primitive) (runtime : Runtime) :
    run (first ++ second) runtime =
      match run first runtime with
      | none => none
      | some (.rejected final) =>
          some (.rejected final)
      | some (.accepted middle) =>
          run second middle := by
  induction first generalizing runtime with
  | nil =>
      rfl
  | cons primitive rest ih =>
      simp only [List.cons_append, run]
      cases step primitive runtime with
      | none =>
          rfl
      | some outcome =>
          cases outcome with
          | rejected final =>
              rfl
          | accepted next =>
              exact ih next

theorem run_append_of_accepted
    (first second : List Primitive)
    (initial middle : Runtime)
    (accepted :
      run first initial = some (.accepted middle)) :
    run (first ++ second) initial = run second middle := by
  rw [run_append, accepted]

theorem run_append_of_rejected
    (first second : List Primitive)
    (initial final : Runtime)
    (rejected :
      run first initial = some (.rejected final)) :
    run (first ++ second) initial =
      some (.rejected final) := by
  rw [run_append, rejected]

/-! ### Repeated arithmetic primitives -/

theorem run_repeat_incrementScratch
    (count : Nat) (runtime : Runtime) :
    run (repeatPrimitive count .incrementScratch) runtime =
      some (.accepted
        { runtime with
          scratch := runtime.scratch + count }) := by
  induction count generalizing runtime with
  | zero =>
      rfl
  | succ count ih =>
      unfold repeatPrimitive
      rw [List.replicate_succ]
      simp only [run, step]
      simpa [repeatPrimitive, Nat.add_assoc,
        Nat.add_comm 1 count] using
        ih { runtime with scratch := runtime.scratch + 1 }

theorem run_repeat_incrementOutputIndex
    (count : Nat) (runtime : Runtime) :
    run
        (repeatPrimitive count
          (.incrementRegister .outputIndex))
        runtime =
      some (.accepted
        { runtime with
          registers :=
            { runtime.registers with
              outputIndex :=
                runtime.registers.outputIndex + count } }) := by
  induction count generalizing runtime with
  | zero =>
      rfl
  | succ count ih =>
      unfold repeatPrimitive
      rw [List.replicate_succ]
      simp only [run, step,
        incrementRegister]
      simpa [repeatPrimitive, Nat.add_assoc,
        Nat.add_comm 1 count] using
        ih
          { runtime with
            registers :=
              { runtime.registers with
                outputIndex :=
                  runtime.registers.outputIndex + 1 } }

/-! ### Compiled natural expressions -/

def termsValue
    (registers : TargetEmitter.UnaryRegisters)
    (captured : Nat) (terms : List Counter) : Nat :=
  (terms.map
    (NatExpression.evaluateCounter registers captured 0)).sum

theorem step_counterOperation
    (counter : Counter) (operation : Primitive)
    (runtime : Runtime)
    (materialized :
      counterOperation counter = some operation) :
    step operation runtime =
      some (.accepted
        { runtime with
          scratch :=
            runtime.scratch +
              NatExpression.evaluateCounter
                runtime.registers runtime.captured 0 counter }) := by
  cases counter <;>
    simp [counterOperation] at materialized
  all_goals
    subst operation
    rfl

theorem compileTerms_correct
    (terms : List Counter) (program : List Primitive)
    (runtime : Runtime)
    (compiled : compileTerms terms = some program) :
    run program runtime =
      some (.accepted
        { runtime with
          scratch :=
            runtime.scratch +
              termsValue runtime.registers
                runtime.captured terms }) := by
  induction terms generalizing program runtime with
  | nil =>
      have programEq : program = [] := by
        simpa [compileTerms] using compiled.symm
      subst program
      rfl
  | cons term rest ih =>
      cases operationEq : counterOperation term with
      | none =>
          simp [compileTerms, operationEq] at compiled
      | some operation =>
          cases tailEq : compileTerms rest with
          | none =>
              simp [compileTerms, operationEq, tailEq] at compiled
          | some tail =>
              have programEq :
                  program = operation :: tail := by
                simpa [compileTerms, operationEq, tailEq] using
                  compiled.symm
              subst program
              simp only [run,
                step_counterOperation term operation runtime
                  operationEq]
              have tailRun :=
                ih tail
                  { runtime with
                    scratch :=
                      runtime.scratch +
                        NatExpression.evaluateCounter
                          runtime.registers runtime.captured 0 term }
                  tailEq
              simpa [termsValue, Nat.add_assoc] using tailRun

def naturalValue (runtime : Runtime)
    (expression : NatExpression) : Nat :=
  expression.evaluate runtime.registers runtime.captured 0

theorem naturalValue_eq
    (runtime : Runtime) (expression : NatExpression) :
    naturalValue runtime expression =
      expression.offset +
        termsValue runtime.registers runtime.captured
          expression.terms := by
  rfl

theorem computeNatural_correct
    (expression : NatExpression)
    (program : List Primitive) (runtime : Runtime)
    (computed :
      computeNatural expression = some program) :
    run program runtime =
      some (.accepted
        { runtime with
          scratch := naturalValue runtime expression }) := by
  unfold computeNatural at computed
  cases termsEq : compileTerms expression.terms with
  | none =>
      simp [termsEq] at computed
  | some termsProgram =>
      have programEq :
          program =
            [.resetScratch] ++ termsProgram ++
              repeatPrimitive expression.offset
                .incrementScratch :=
        by simpa [termsEq] using computed.symm
      subst program
      simp only [List.singleton_append]
      change
        run
            (termsProgram ++
              repeatPrimitive expression.offset
                .incrementScratch)
            { runtime with scratch := 0 } =
          some (.accepted
            { runtime with
              scratch := naturalValue runtime expression })
      rw [run_append_of_accepted
        termsProgram
        (repeatPrimitive expression.offset
          .incrementScratch)
        { runtime with scratch := 0 }
        { runtime with
          scratch :=
            termsValue runtime.registers
              runtime.captured expression.terms }]
      · simpa [naturalValue_eq, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc] using
          run_repeat_incrementScratch expression.offset
            { runtime with
              scratch :=
                termsValue runtime.registers
                  runtime.captured expression.terms }
      · simpa using
          compileTerms_correct expression.terms
            termsProgram
            { runtime with scratch := 0 } termsEq

theorem compileNatural_correct
    (mode : CursorMode) (expression : NatExpression)
    (program : List Primitive) (runtime : Runtime)
    (compiled :
      compileNatural mode expression = some program) :
    run program runtime =
      some (.accepted
        { runtime with
          scratch := naturalValue runtime expression
          targetTokens :=
            runtime.targetTokens ++
              encodeNatTokens
                (naturalValue runtime expression) }) := by
  unfold compileNatural at compiled
  cases computationEq : computeNatural expression with
  | none =>
      simp [computationEq] at compiled
  | some computation =>
      have programEq :
          program = computation ++ [.emitScratchNat mode] :=
        by simpa [computationEq] using compiled.symm
      subst program
      rw [run_append_of_accepted
        computation [.emitScratchNat mode] runtime
        { runtime with
          scratch := naturalValue runtime expression }]
      · simp [run, step]
      · exact computeNatural_correct expression computation
          runtime computationEq

/-! ### Planned sources and gates -/

def evaluatedSource
    (runtime : Runtime) (source : PlannedSource) :
    RawSource :=
  source.evaluate runtime.registers runtime.captured 0

def sourceScratch
    (runtime : Runtime) : PlannedSource → Nat
  | .constant _ => runtime.scratch
  | .input coordinate =>
      naturalValue runtime coordinate
  | .gate coordinate =>
      naturalValue runtime coordinate

def sourceResult
    (runtime : Runtime) (source : PlannedSource) :
    Runtime :=
  { runtime with
    scratch := sourceScratch runtime source
    targetTokens :=
      runtime.targetTokens ++
        encodeSourceTokens (evaluatedSource runtime source) }

theorem compileSource_correct
    (mode : CursorMode) (source : PlannedSource)
    (program : List Primitive) (runtime : Runtime)
    (compiled :
      compileSource mode source = some program) :
    run program runtime =
      some (.accepted (sourceResult runtime source)) := by
  cases source with
  | constant value =>
      cases value with
      | false =>
          have programEq :
              program = [.append mode .constantFalse] := by
            simpa [compileSource] using compiled.symm
          subst program
          rfl
      | true =>
          have programEq :
              program = [.append mode .constantTrue] := by
            simpa [compileSource] using compiled.symm
          subst program
          rfl
  | input coordinate =>
      unfold compileSource at compiled
      cases naturalEq :
          compileNatural mode coordinate with
      | none =>
          simp [naturalEq] at compiled
      | some naturalProgram =>
          have programEq :
              program =
                .append mode .input :: naturalProgram :=
            by simpa [naturalEq] using compiled.symm
          subst program
          simp only [run, step]
          have natural :=
            compileNatural_correct mode coordinate
              naturalProgram
              { runtime with
                targetTokens :=
                  runtime.targetTokens ++ [.input] }
              naturalEq
          simpa [sourceResult, sourceScratch, evaluatedSource,
            PlannedSource.evaluate, naturalValue,
            encodeSourceTokens,
            List.append_assoc] using natural
  | gate coordinate =>
      unfold compileSource at compiled
      cases naturalEq :
          compileNatural mode coordinate with
      | none =>
          simp [naturalEq] at compiled
      | some naturalProgram =>
          have programEq :
              program =
                .append mode .gate :: naturalProgram :=
            by simpa [naturalEq] using compiled.symm
          subst program
          simp only [run, step]
          have natural :=
            compileNatural_correct mode coordinate
              naturalProgram
              { runtime with
                targetTokens :=
                  runtime.targetTokens ++ [.gate] }
              naturalEq
          simpa [sourceResult, sourceScratch, evaluatedSource,
            PlannedSource.evaluate, naturalValue,
            encodeSourceTokens,
            List.append_assoc] using natural

/-- Canonical token fragment emitted by the closed gate compiler. -/
def compiledGateTokens
    (runtime : Runtime) (gate : PlannedGate) : List Token :=
  encodeGateTokens
    (gate.evaluate runtime.registers runtime.captured 0)

def gateScratch
    (runtime : Runtime) (gate : PlannedGate) : Nat :=
  let afterLeft :=
    { runtime with
      scratch := sourceScratch runtime gate.left }
  sourceScratch afterLeft gate.right

def gateResult
    (runtime : Runtime) (gate : PlannedGate) : Runtime :=
  let afterLeft := sourceResult runtime gate.left
  let afterRight := sourceResult afterLeft gate.right
  { afterRight with
    targetTokens := afterRight.targetTokens ++ [.gateEnd] }

theorem gateResult_eq
    (runtime : Runtime) (gate : PlannedGate) :
    gateResult runtime gate =
      { runtime with
        scratch := gateScratch runtime gate
        targetTokens :=
          runtime.targetTokens ++
            compiledGateTokens runtime gate } := by
  cases gate with
  | mk left right =>
      simp [gateResult, gateScratch, sourceResult,
        sourceScratch, compiledGateTokens,
        evaluatedSource, naturalValue,
        PlannedGate.evaluate,
        encodeGateTokens, List.append_assoc]

theorem compileGate_correct
    (mode : CursorMode) (gate : PlannedGate)
    (program : List Primitive) (runtime : Runtime)
    (compiled : compileGate mode gate = some program) :
    run program runtime =
      some (.accepted (gateResult runtime gate)) := by
  cases gate with
  | mk left right =>
      unfold compileGate at compiled
      cases leftEq : compileSource mode left with
      | none =>
          simp [leftEq] at compiled
      | some leftProgram =>
          cases rightEq : compileSource mode right with
          | none =>
              simp [leftEq, rightEq] at compiled
          | some rightProgram =>
              have programEq :
                  program =
                    leftProgram ++ rightProgram ++
                      [.append mode .gateEnd] :=
                by simpa [leftEq, rightEq] using compiled.symm
              subst program
              have leftRun :=
                compileSource_correct mode left leftProgram
                  runtime leftEq
              have rightRun :=
                compileSource_correct mode right rightProgram
                  (sourceResult runtime left) rightEq
              have bothRun :
                  run (leftProgram ++ rightProgram) runtime =
                    some (.accepted
                      (sourceResult
                        (sourceResult runtime left) right)) := by
                rw [run_append_of_accepted
                  leftProgram rightProgram runtime
                  (sourceResult runtime left) leftRun]
                exact rightRun
              rw [run_append_of_accepted
                (leftProgram ++ rightProgram)
                [.append mode .gateEnd] runtime
                (sourceResult
                  (sourceResult runtime left) right)
                bothRun]
              simp [run, step, gateResult]

def gatesResult
    (runtime : Runtime) : List PlannedGate → Runtime
  | [] => runtime
  | gate :: rest =>
      gatesResult (gateResult runtime gate) rest

theorem compileGates_correct
    (mode : CursorMode) (gates : List PlannedGate)
    (program : List Primitive) (runtime : Runtime)
    (compiled : compileGates mode gates = some program) :
    run program runtime =
      some (.accepted (gatesResult runtime gates)) := by
  induction gates generalizing program runtime with
  | nil =>
      have programEq : program = [] := by
        simpa [compileGates] using compiled.symm
      subst program
      rfl
  | cons gate rest ih =>
      unfold compileGates at compiled
      cases gateEq : compileGate mode gate with
      | none =>
          simp [gateEq] at compiled
      | some gateProgram =>
          cases restEq : compileGates mode rest with
          | none =>
              simp [gateEq, restEq] at compiled
          | some restProgram =>
              have programEq :
                  program = gateProgram ++ restProgram := by
                simpa [gateEq, restEq] using compiled.symm
              subst program
              rw [run_append_of_accepted
                gateProgram restProgram runtime
                (gateResult runtime gate)]
              · exact ih restProgram (gateResult runtime gate)
                  restEq
              · exact compileGate_correct mode gate gateProgram
                  runtime gateEq

theorem gatesResult_registers
    (runtime : Runtime) (gates : List PlannedGate) :
    (gatesResult runtime gates).registers =
      runtime.registers := by
  induction gates generalizing runtime with
  | nil =>
      rfl
  | cons gate rest ih =>
      change
        (gatesResult (gateResult runtime gate) rest).registers =
          runtime.registers
      rw [ih]
      rfl

theorem gatesResult_checks
    (runtime : Runtime) (gates : List PlannedGate) :
    (gatesResult runtime gates).checks = runtime.checks := by
  induction gates generalizing runtime with
  | nil =>
      rfl
  | cons gate rest ih =>
      change
        (gatesResult (gateResult runtime gate) rest).checks =
          runtime.checks
      rw [ih]
      rfl

theorem gatesResult_targetTokens
    (runtime : Runtime) (gates : List PlannedGate) :
    (gatesResult runtime gates).targetTokens =
      runtime.targetTokens ++
        (gates.map
          (compiledGateTokens runtime)).flatten := by
  induction gates generalizing runtime with
  | nil =>
      simp [gatesResult]
  | cons gate rest ih =>
      rw [gatesResult, ih]
      rw [gateResult_eq]
      simp only [List.map_cons, List.flatten_cons,
        List.append_assoc]
      congr 1

def evaluatedGates
    (runtime : Runtime) (gates : List PlannedGate) :
    List RawGate :=
  gates.map
    (PlannedGate.evaluate
      runtime.registers runtime.captured 0)

def plannedGateTokens
    (runtime : Runtime) (gates : List PlannedGate) :
    List Token :=
  encodeGateListTokens (evaluatedGates runtime gates)

theorem flattened_compiledGateTokens_eq_plannedGateTokens
    (runtime : Runtime) (gates : List PlannedGate) :
    (gates.map (compiledGateTokens runtime)).flatten =
      plannedGateTokens runtime gates := by
  induction gates with
  | nil =>
      rfl
  | cons gate rest ih =>
      simp [plannedGateTokens, evaluatedGates,
        compiledGateTokens, encodeGateListTokens, ih]

theorem gatesResult_targetTokens_eq
    (runtime : Runtime) (gates : List PlannedGate) :
    (gatesResult runtime gates).targetTokens =
      runtime.targetTokens ++ plannedGateTokens runtime gates := by
  rw [gatesResult_targetTokens,
    flattened_compiledGateTokens_eq_plannedGateTokens]

/-! ### Check-pushing macro programs -/

def checkPushResult
    (runtime : Runtime) (relative : Nat) : Runtime :=
  { runtime with
    scratch := runtime.registers.outputIndex + relative
    checks :=
      runtime.checks ++
        [runtime.registers.outputIndex + relative] }

theorem compileCheckPush_correct
    (relative : Nat) (program : List Primitive)
    (runtime : Runtime)
    (compiled :
      compileCheckPush relative = some program) :
    run program runtime =
      some (.accepted (checkPushResult runtime relative)) := by
  unfold compileCheckPush at compiled
  cases coordinateEq :
      computeNatural (checkAt relative) with
  | none =>
      simp [coordinateEq] at compiled
  | some coordinateProgram =>
      have programEq :
          program = coordinateProgram ++ [.pushCheck] := by
        simpa [coordinateEq] using compiled.symm
      subst program
      have coordinateRun :=
        computeNatural_correct (checkAt relative)
          coordinateProgram runtime coordinateEq
      rw [run_append_of_accepted
        coordinateProgram [.pushCheck] runtime
        { runtime with
          scratch := naturalValue runtime (checkAt relative) }
        coordinateRun]
      have coordinateValue :
          naturalValue runtime (checkAt relative) =
            runtime.registers.outputIndex + relative := by
        simpa [naturalValue] using
          checkAt_evaluated runtime.registers
            runtime.captured 0 relative
      simp [run, step, checkPushResult, coordinateValue]

def incrementOutputResult
    (runtime : Runtime) (count : Nat) : Runtime :=
  { runtime with
    registers :=
      { runtime.registers with
        outputIndex :=
          runtime.registers.outputIndex + count } }

def resetScratchResult (runtime : Runtime) : Runtime :=
  { runtime with scratch := 0 }

def macroResult
    (runtime : Runtime) (gates : List PlannedGate)
    (relative count : Nat) : Runtime :=
  resetScratchResult
    (incrementOutputResult
      (checkPushResult (gatesResult runtime gates) relative)
      count)

theorem macroResult_scratch
    (runtime : Runtime) (gates : List PlannedGate)
    (relative count : Nat) :
    (macroResult runtime gates relative count).scratch = 0 := by
  rfl

theorem macroResult_registers
    (runtime : Runtime) (gates : List PlannedGate)
    (relative count : Nat) :
    (macroResult runtime gates relative count).registers =
      { runtime.registers with
        outputIndex :=
          runtime.registers.outputIndex + count } := by
  simp [macroResult, resetScratchResult,
    incrementOutputResult, checkPushResult,
    gatesResult_registers]

theorem macroResult_checks
    (runtime : Runtime) (gates : List PlannedGate)
    (relative count : Nat) :
    (macroResult runtime gates relative count).checks =
      runtime.checks ++
        [runtime.registers.outputIndex + relative] := by
  simp [macroResult, resetScratchResult,
    incrementOutputResult, checkPushResult,
    gatesResult_registers, gatesResult_checks]

theorem macroResult_targetTokens
    (runtime : Runtime) (gates : List PlannedGate)
    (relative count : Nat) :
    (macroResult runtime gates relative count).targetTokens =
      runtime.targetTokens ++ plannedGateTokens runtime gates := by
  simp [macroResult, resetScratchResult,
    incrementOutputResult, checkPushResult,
    gatesResult_targetTokens_eq]

theorem run_compiledMacro
    (gates : List PlannedGate) (relative count : Nat)
    (gatesProgram checkProgram : List Primitive)
    (runtime : Runtime)
    (gatesCompiled :
      compileGates .marked gates = some gatesProgram)
    (checkCompiled :
      compileCheckPush relative = some checkProgram) :
    run
        (gatesProgram ++ checkProgram ++
          repeatPrimitive count
            (.incrementRegister .outputIndex) ++
          [.resetScratch])
        runtime =
      some (.accepted
        (macroResult runtime gates relative count)) := by
  let afterGates := gatesResult runtime gates
  let afterCheck := checkPushResult afterGates relative
  let afterIncrement :=
    incrementOutputResult afterCheck count
  have gatesRun :
      run gatesProgram runtime =
        some (.accepted afterGates) :=
    compileGates_correct .marked gates gatesProgram
      runtime gatesCompiled
  have checkRun :
      run checkProgram afterGates =
        some (.accepted afterCheck) :=
    compileCheckPush_correct relative checkProgram
      afterGates checkCompiled
  have incrementRun :
      run
          (repeatPrimitive count
            (.incrementRegister .outputIndex))
          afterCheck =
        some (.accepted afterIncrement) := by
    exact run_repeat_incrementOutputIndex count afterCheck
  simp only [List.append_assoc]
  calc
    run
        (gatesProgram ++
          (checkProgram ++
            (repeatPrimitive count
              (.incrementRegister .outputIndex) ++
              [.resetScratch])))
        runtime =
      run
        (checkProgram ++
          (repeatPrimitive count
            (.incrementRegister .outputIndex) ++
            [.resetScratch]))
        afterGates :=
      run_append_of_accepted gatesProgram _ runtime
        afterGates gatesRun
    _ =
      run
        (repeatPrimitive count
          (.incrementRegister .outputIndex) ++
          [.resetScratch])
        afterCheck :=
      run_append_of_accepted checkProgram _ afterGates
        afterCheck checkRun
    _ = run [.resetScratch] afterIncrement :=
      run_append_of_accepted
        (repeatPrimitive count
          (.incrementRegister .outputIndex))
        [.resetScratch] afterCheck afterIncrement incrementRun
    _ = some (.accepted
        (macroResult runtime gates relative count)) := by
      rfl

/-! ### Named gate-producing programs -/

theorem sourceProgram_correct
    (kind : SourceKind) (side : Nat)
    (program : List Primitive) (runtime : Runtime)
    (compiled :
      sourceProgram kind side = some program) :
    run program runtime =
      some (.accepted
        (macroResult runtime
          (sourcePlan kind side)
          (sourceCheckRelative kind)
          (sourceGateCount kind))) := by
  unfold sourceProgram at compiled
  cases gatesEq :
      compileGates .marked (sourcePlan kind side) with
  | none =>
      simp [gatesEq] at compiled
  | some gatesProgram =>
      cases checkEq :
          compileCheckPush (sourceCheckRelative kind) with
      | none =>
          simp [gatesEq, checkEq] at compiled
      | some checkProgram =>
          have programEq :
              program =
                gatesProgram ++ checkProgram ++
                  repeatPrimitive (sourceGateCount kind)
                    (.incrementRegister .outputIndex) ++
                  [.resetScratch] := by
            simpa [gatesEq, checkEq] using compiled.symm
          subst program
          exact run_compiledMacro
            (sourcePlan kind side)
            (sourceCheckRelative kind)
            (sourceGateCount kind)
            gatesProgram checkProgram runtime gatesEq checkEq

theorem traceProgram_correct
    (program : List Primitive) (runtime : Runtime)
    (compiled : traceProgram = some program) :
    run program runtime =
      some (.accepted
        (macroResult runtime tracePlan
          traceCheckRelative traceGateCount)) := by
  unfold traceProgram at compiled
  cases gatesEq : compileGates .marked tracePlan with
  | none =>
      simp [gatesEq] at compiled
  | some gatesProgram =>
      cases checkEq :
          compileCheckPush traceCheckRelative with
      | none =>
          simp [gatesEq, checkEq] at compiled
      | some checkProgram =>
          have programEq :
              program =
                gatesProgram ++ checkProgram ++
                  repeatPrimitive traceGateCount
                    (.incrementRegister .outputIndex) ++
                  [.resetScratch] := by
            simpa [gatesEq, checkEq] using compiled.symm
          subst program
          exact run_compiledMacro tracePlan
            traceCheckRelative traceGateCount
            gatesProgram checkProgram runtime gatesEq checkEq

theorem syntheticGateSourceProgram_correct
    (gateBias sourceGateBias side : Nat)
    (program : List Primitive) (runtime : Runtime)
    (compiled :
      syntheticGateSourceProgram gateBias sourceGateBias side =
        some program) :
    run program runtime =
      some (.accepted
        (macroResult runtime
          (syntheticGatePlan gateBias sourceGateBias side)
          (sourceCheckRelative .gate)
          (sourceGateCount .gate))) := by
  unfold syntheticGateSourceProgram at compiled
  cases gatesEq :
      compileGates .marked
        (syntheticGatePlan gateBias sourceGateBias side) with
  | none =>
      simp [gatesEq] at compiled
  | some gatesProgram =>
      cases checkEq :
          compileCheckPush (sourceCheckRelative .gate) with
      | none =>
          simp [gatesEq, checkEq] at compiled
      | some checkProgram =>
          have programEq :
              program =
                gatesProgram ++ checkProgram ++
                  repeatPrimitive (sourceGateCount .gate)
                    (.incrementRegister .outputIndex) ++
                  [.resetScratch] := by
            simpa [gatesEq, checkEq] using compiled.symm
          subst program
          exact run_compiledMacro
            (syntheticGatePlan gateBias sourceGateBias side)
            (sourceCheckRelative .gate)
            (sourceGateCount .gate)
            gatesProgram checkProgram runtime gatesEq checkEq

theorem traceProgramAt_correct
    (gateBias : Nat) (program : List Primitive)
    (runtime : Runtime)
    (compiled :
      traceProgramAt gateBias = some program) :
    run program runtime =
      some (.accepted
        (macroResult runtime (tracePlanAt gateBias)
          traceCheckRelative traceGateCount)) := by
  unfold traceProgramAt at compiled
  cases gatesEq :
      compileGates .marked (tracePlanAt gateBias) with
  | none =>
      simp [gatesEq] at compiled
  | some gatesProgram =>
      cases checkEq :
          compileCheckPush traceCheckRelative with
      | none =>
          simp [gatesEq, checkEq] at compiled
      | some checkProgram =>
          have programEq :
              program =
                gatesProgram ++ checkProgram ++
                  repeatPrimitive traceGateCount
                    (.incrementRegister .outputIndex) ++
                  [.resetScratch] := by
            simpa [gatesEq, checkEq] using compiled.symm
          subst program
          exact run_compiledMacro (tracePlanAt gateBias)
            traceCheckRelative traceGateCount
            gatesProgram checkProgram runtime gatesEq checkEq

/-! ### Normalization and final-gate programs -/

def incrementCurrentGateResult (runtime : Runtime) : Runtime :=
  { runtime with
    registers :=
      { runtime.registers with
        currentGate := runtime.registers.currentGate + 1 } }

def inputNormalizationResult (runtime : Runtime) : Runtime :=
  let firstLeft :=
    macroResult runtime
      (sourcePlan .input 0)
      (sourceCheckRelative .input)
      (sourceGateCount .input)
  let firstRight :=
    macroResult firstLeft
      (sourcePlan .constantTrue 1)
      (sourceCheckRelative .constantTrue)
      (sourceGateCount .constantTrue)
  let firstTrace :=
    macroResult firstRight tracePlan
      traceCheckRelative traceGateCount
  let secondLeft :=
    macroResult firstTrace
      (syntheticGatePlan 1 0 0)
      (sourceCheckRelative .gate)
      (sourceGateCount .gate)
  let secondRight :=
    macroResult secondLeft
      (syntheticGatePlan 1 0 1)
      (sourceCheckRelative .gate)
      (sourceGateCount .gate)
  let secondTrace :=
    macroResult secondRight (tracePlanAt 1)
      traceCheckRelative traceGateCount
  incrementCurrentGateResult secondTrace

theorem inputNormalizationProgram_correct
    (program : List Primitive) (runtime : Runtime)
    (compiled :
      inputNormalizationProgram = some program) :
    run program runtime =
      some (.accepted (inputNormalizationResult runtime)) := by
  unfold inputNormalizationProgram at compiled
  cases firstLeftEq : sourceProgram .input 0 with
  | none =>
      simp [firstLeftEq] at compiled
  | some firstLeftProgram =>
      cases firstRightEq :
          sourceProgram .constantTrue 1 with
      | none =>
          simp [firstLeftEq, firstRightEq] at compiled
      | some firstRightProgram =>
          cases firstTraceEq : traceProgram with
          | none =>
              simp [firstLeftEq, firstRightEq,
                firstTraceEq] at compiled
          | some firstTraceProgram =>
              cases secondLeftEq :
                  syntheticGateSourceProgram 1 0 0 with
              | none =>
                  simp [firstLeftEq, firstRightEq,
                    firstTraceEq, secondLeftEq] at compiled
              | some secondLeftProgram =>
                  cases secondRightEq :
                      syntheticGateSourceProgram 1 0 1 with
                  | none =>
                      simp [firstLeftEq, firstRightEq,
                        firstTraceEq, secondLeftEq,
                        secondRightEq] at compiled
                  | some secondRightProgram =>
                      cases secondTraceEq : traceProgramAt 1 with
                      | none =>
                          simp [firstLeftEq, firstRightEq,
                            firstTraceEq, secondLeftEq,
                            secondRightEq, secondTraceEq] at compiled
                      | some secondTraceProgram =>
                          have programEq :
                              program =
                                firstLeftProgram ++
                                  firstRightProgram ++
                                  firstTraceProgram ++
                                  secondLeftProgram ++
                                  secondRightProgram ++
                                  secondTraceProgram ++
                                  [.incrementRegister
                                    .currentGate] := by
                            simpa [firstLeftEq, firstRightEq,
                              firstTraceEq, secondLeftEq,
                              secondRightEq, secondTraceEq] using
                              compiled.symm
                          subst program
                          let afterFirstLeft :=
                            macroResult runtime
                              (sourcePlan .input 0)
                              (sourceCheckRelative .input)
                              (sourceGateCount .input)
                          let afterFirstRight :=
                            macroResult afterFirstLeft
                              (sourcePlan .constantTrue 1)
                              (sourceCheckRelative .constantTrue)
                              (sourceGateCount .constantTrue)
                          let afterFirstTrace :=
                            macroResult afterFirstRight tracePlan
                              traceCheckRelative traceGateCount
                          let afterSecondLeft :=
                            macroResult afterFirstTrace
                              (syntheticGatePlan 1 0 0)
                              (sourceCheckRelative .gate)
                              (sourceGateCount .gate)
                          let afterSecondRight :=
                            macroResult afterSecondLeft
                              (syntheticGatePlan 1 0 1)
                              (sourceCheckRelative .gate)
                              (sourceGateCount .gate)
                          let afterSecondTrace :=
                            macroResult afterSecondRight
                              (tracePlanAt 1)
                              traceCheckRelative traceGateCount
                          have firstLeftRun :
                              run firstLeftProgram runtime =
                                some (.accepted afterFirstLeft) :=
                            sourceProgram_correct .input 0
                              firstLeftProgram runtime firstLeftEq
                          have firstRightRun :
                              run firstRightProgram afterFirstLeft =
                                some (.accepted afterFirstRight) :=
                            sourceProgram_correct .constantTrue 1
                              firstRightProgram afterFirstLeft
                              firstRightEq
                          have firstTraceRun :
                              run firstTraceProgram afterFirstRight =
                                some (.accepted afterFirstTrace) :=
                            traceProgram_correct firstTraceProgram
                              afterFirstRight firstTraceEq
                          have secondLeftRun :
                              run secondLeftProgram afterFirstTrace =
                                some (.accepted afterSecondLeft) :=
                            syntheticGateSourceProgram_correct
                              1 0 0 secondLeftProgram
                              afterFirstTrace secondLeftEq
                          have secondRightRun :
                              run secondRightProgram afterSecondLeft =
                                some (.accepted afterSecondRight) :=
                            syntheticGateSourceProgram_correct
                              1 0 1 secondRightProgram
                              afterSecondLeft secondRightEq
                          have secondTraceRun :
                              run secondTraceProgram afterSecondRight =
                                some (.accepted afterSecondTrace) :=
                            traceProgramAt_correct 1
                              secondTraceProgram afterSecondRight
                              secondTraceEq
                          simp only [List.append_assoc]
                          calc
                            run
                                (firstLeftProgram ++
                                  (firstRightProgram ++
                                    (firstTraceProgram ++
                                      (secondLeftProgram ++
                                        (secondRightProgram ++
                                          (secondTraceProgram ++
                                            [.incrementRegister
                                              .currentGate]))))))
                                runtime =
                              run
                                (firstRightProgram ++
                                  (firstTraceProgram ++
                                    (secondLeftProgram ++
                                      (secondRightProgram ++
                                        (secondTraceProgram ++
                                          [.incrementRegister
                                            .currentGate])))))
                                afterFirstLeft :=
                              run_append_of_accepted firstLeftProgram _
                                runtime afterFirstLeft firstLeftRun
                            _ =
                              run
                                (firstTraceProgram ++
                                  (secondLeftProgram ++
                                    (secondRightProgram ++
                                      (secondTraceProgram ++
                                        [.incrementRegister
                                          .currentGate]))))
                                afterFirstRight :=
                              run_append_of_accepted firstRightProgram _
                                afterFirstLeft afterFirstRight
                                firstRightRun
                            _ =
                              run
                                (secondLeftProgram ++
                                  (secondRightProgram ++
                                    (secondTraceProgram ++
                                      [.incrementRegister
                                        .currentGate])))
                                afterFirstTrace :=
                              run_append_of_accepted firstTraceProgram _
                                afterFirstRight afterFirstTrace
                                firstTraceRun
                            _ =
                              run
                                (secondRightProgram ++
                                  (secondTraceProgram ++
                                    [.incrementRegister .currentGate]))
                                afterSecondLeft :=
                              run_append_of_accepted secondLeftProgram _
                                afterFirstTrace afterSecondLeft
                                secondLeftRun
                            _ =
                              run
                                (secondTraceProgram ++
                                  [.incrementRegister .currentGate])
                                afterSecondRight :=
                              run_append_of_accepted secondRightProgram _
                                afterSecondLeft afterSecondRight
                                secondRightRun
                            _ =
                              run [.incrementRegister .currentGate]
                                afterSecondTrace :=
                              run_append_of_accepted secondTraceProgram _
                                afterSecondRight afterSecondTrace
                                secondTraceRun
                            _ = some (.accepted
                                (inputNormalizationResult runtime)) := by
                              rfl

theorem inputNormalizationResult_scratch (runtime : Runtime) :
    (inputNormalizationResult runtime).scratch = 0 := by
  rfl

theorem inputNormalizationResult_outputIndex
    (runtime : Runtime) :
    (inputNormalizationResult runtime).registers.outputIndex =
      runtime.registers.outputIndex + 68 := by
  simp [inputNormalizationResult,
    incrementCurrentGateResult, macroResult,
    resetScratchResult, incrementOutputResult,
    checkPushResult, gatesResult_registers,
    sourceGateCount, traceGateCount]

theorem inputNormalizationResult_currentGate
    (runtime : Runtime) :
    (inputNormalizationResult runtime).registers.currentGate =
      runtime.registers.currentGate + 1 := by
  simp [inputNormalizationResult,
    incrementCurrentGateResult, macroResult,
    resetScratchResult, incrementOutputResult,
    checkPushResult, gatesResult_registers]

theorem inputNormalizationResult_checks
    (runtime : Runtime) :
    (inputNormalizationResult runtime).checks =
      runtime.checks ++
        [ runtime.registers.outputIndex + 7
        , runtime.registers.outputIndex + 11
        , runtime.registers.outputIndex + 27
        , runtime.registers.outputIndex + 37
        , runtime.registers.outputIndex + 47
        , runtime.registers.outputIndex + 65
        ] := by
  simp [inputNormalizationResult,
    incrementCurrentGateResult,
    macroResult_checks, macroResult_registers,
    sourceGateCount,
    sourceCheckRelative, traceGateCount,
    traceCheckRelative, List.append_assoc]

def constantNormalizationResult
    (value : Bool) (runtime : Runtime) : Runtime :=
  let kind := constantNormalizationKind value
  let afterLeft :=
    macroResult runtime (sourcePlan kind 0)
      (sourceCheckRelative kind)
      (sourceGateCount kind)
  let afterRight :=
    macroResult afterLeft (sourcePlan kind 1)
      (sourceCheckRelative kind)
      (sourceGateCount kind)
  macroResult afterRight tracePlan
    traceCheckRelative traceGateCount

theorem constantNormalizationProgram_correct
    (value : Bool) (program : List Primitive)
    (runtime : Runtime)
    (compiled :
      constantNormalizationProgram value = some program) :
    run program runtime =
      some (.accepted
        (constantNormalizationResult value runtime)) := by
  unfold constantNormalizationProgram at compiled
  cases leftEq :
      sourceProgram (constantNormalizationKind value) 0 with
  | none =>
      simp [leftEq] at compiled
  | some leftProgram =>
      cases rightEq :
          sourceProgram (constantNormalizationKind value) 1 with
      | none =>
          simp [leftEq, rightEq] at compiled
      | some rightProgram =>
          cases traceEq : traceProgram with
          | none =>
              simp [leftEq, rightEq, traceEq] at compiled
          | some traceProgramValue =>
              have programEq :
                  program =
                    leftProgram ++ rightProgram ++
                      traceProgramValue := by
                simpa [leftEq, rightEq, traceEq] using
                  compiled.symm
              subst program
              let kind := constantNormalizationKind value
              let afterLeft :=
                macroResult runtime (sourcePlan kind 0)
                  (sourceCheckRelative kind)
                  (sourceGateCount kind)
              let afterRight :=
                macroResult afterLeft (sourcePlan kind 1)
                  (sourceCheckRelative kind)
                  (sourceGateCount kind)
              have leftRun :
                  run leftProgram runtime =
                    some (.accepted afterLeft) :=
                sourceProgram_correct kind 0 leftProgram
                  runtime leftEq
              have rightRun :
                  run rightProgram afterLeft =
                    some (.accepted afterRight) :=
                sourceProgram_correct kind 1 rightProgram
                  afterLeft rightEq
              have traceRun :
                  run traceProgramValue afterRight =
                    some (.accepted
                      (macroResult afterRight tracePlan
                        traceCheckRelative traceGateCount)) :=
                traceProgram_correct traceProgramValue
                  afterRight traceEq
              simp only [List.append_assoc]
              calc
                run
                    (leftProgram ++
                      (rightProgram ++ traceProgramValue))
                    runtime =
                  run (rightProgram ++ traceProgramValue)
                    afterLeft :=
                  run_append_of_accepted leftProgram _
                    runtime afterLeft leftRun
                _ = run traceProgramValue afterRight :=
                  run_append_of_accepted rightProgram _
                    afterLeft afterRight rightRun
                _ = some (.accepted
                    (constantNormalizationResult value runtime)) := by
                  simpa [constantNormalizationResult, kind,
                    afterLeft, afterRight] using traceRun

theorem constantNormalizationResult_scratch
    (value : Bool) (runtime : Runtime) :
    (constantNormalizationResult value runtime).scratch = 0 := by
  rfl

theorem constantNormalizationResult_false_outputIndex
    (runtime : Runtime) :
    (constantNormalizationResult false runtime).registers.outputIndex =
      runtime.registers.outputIndex + 22 := by
  simp [constantNormalizationResult,
    constantNormalizationKind, macroResult,
    resetScratchResult, incrementOutputResult,
    checkPushResult, gatesResult_registers,
    sourceGateCount, traceGateCount]

theorem constantNormalizationResult_true_outputIndex
    (runtime : Runtime) :
    (constantNormalizationResult true runtime).registers.outputIndex =
      runtime.registers.outputIndex + 24 := by
  simp [constantNormalizationResult,
    constantNormalizationKind, macroResult,
    resetScratchResult, incrementOutputResult,
    checkPushResult, gatesResult_registers,
    sourceGateCount, traceGateCount]

theorem constantNormalizationResult_false_checks
    (runtime : Runtime) :
    (constantNormalizationResult false runtime).checks =
      runtime.checks ++
        [ runtime.registers.outputIndex + 1
        , runtime.registers.outputIndex + 3
        , runtime.registers.outputIndex + 19
        ] := by
  simp [constantNormalizationResult,
    constantNormalizationKind, macroResult,
    resetScratchResult, incrementOutputResult,
    checkPushResult, gatesResult_registers,
    gatesResult_checks, sourceGateCount,
    sourceCheckRelative, traceGateCount,
    traceCheckRelative, List.append_assoc]

theorem constantNormalizationResult_true_checks
    (runtime : Runtime) :
    (constantNormalizationResult true runtime).checks =
      runtime.checks ++
        [ runtime.registers.outputIndex + 2
        , runtime.registers.outputIndex + 5
        , runtime.registers.outputIndex + 21
        ] := by
  simp [constantNormalizationResult,
    constantNormalizationKind, macroResult,
    resetScratchResult, incrementOutputResult,
    checkPushResult, gatesResult_registers,
    gatesResult_checks, sourceGateCount,
    sourceCheckRelative, traceGateCount,
    traceCheckRelative, List.append_assoc]

def finalResult
    (runtime : Runtime) (gates : List PlannedGate) : Runtime :=
  resetScratchResult (gatesResult runtime gates)

theorem finalResult_targetTokens
    (runtime : Runtime) (gates : List PlannedGate) :
    (finalResult runtime gates).targetTokens =
      runtime.targetTokens ++ plannedGateTokens runtime gates := by
  simp [finalResult, resetScratchResult,
    gatesResult_targetTokens_eq]

theorem finalResult_scratch
    (runtime : Runtime) (gates : List PlannedGate) :
    (finalResult runtime gates).scratch = 0 := by
  rfl

theorem finalResult_registers
    (runtime : Runtime) (gates : List PlannedGate) :
    (finalResult runtime gates).registers =
      runtime.registers := by
  simp [finalResult, resetScratchResult,
    gatesResult_registers]

theorem finalResult_checks
    (runtime : Runtime) (gates : List PlannedGate) :
    (finalResult runtime gates).checks = runtime.checks := by
  simp [finalResult, resetScratchResult,
    gatesResult_checks]

theorem run_compiledFinal
    (gates : List PlannedGate)
    (gatesProgram : List Primitive) (runtime : Runtime)
    (compiled :
      compileGates .marked gates = some gatesProgram) :
    run (gatesProgram ++ [.resetScratch]) runtime =
      some (.accepted (finalResult runtime gates)) := by
  rw [run_append_of_accepted
    gatesProgram [.resetScratch] runtime
    (gatesResult runtime gates)
    (compileGates_correct .marked gates gatesProgram
      runtime compiled)]
  rfl

theorem finalPositiveProgram_correct
    (outputTrace : NatExpression)
    (program : List Primitive) (runtime : Runtime)
    (compiled :
      finalPositiveProgram outputTrace = some program) :
    run program runtime =
      some (.accepted
        (finalResult runtime (finalPositivePlan outputTrace))) := by
  unfold finalPositiveProgram at compiled
  cases gatesEq :
      compileGates .marked (finalPositivePlan outputTrace) with
  | none =>
      simp [gatesEq] at compiled
  | some gatesProgram =>
      have programEq :
          program = gatesProgram ++ [.resetScratch] := by
        simpa [gatesEq] using compiled.symm
      subst program
      exact run_compiledFinal
        (finalPositivePlan outputTrace)
        gatesProgram runtime gatesEq

theorem finalZeroProgram_correct
    (program : List Primitive) (runtime : Runtime)
    (compiled : finalZeroProgram = some program) :
    run program runtime =
      some (.accepted
        (finalResult runtime finalZeroPlan)) := by
  unfold finalZeroProgram at compiled
  cases gatesEq : compileGates .marked finalZeroPlan with
  | none =>
      simp [gatesEq] at compiled
  | some gatesProgram =>
      have programEq :
          program = gatesProgram ++ [.resetScratch] := by
        simpa [gatesEq] using compiled.symm
      subst program
      exact run_compiledFinal finalZeroPlan
        gatesProgram runtime gatesEq

/-! ### Header program -/

def naturalResult
    (runtime : Runtime) (expression : NatExpression) : Runtime :=
  { runtime with
    scratch := naturalValue runtime expression
    targetTokens :=
      runtime.targetTokens ++
        encodeNatTokens (naturalValue runtime expression) }

def headerResult (runtime : Runtime) : Runtime :=
  let afterVersion :=
    { runtime with
      targetTokens := runtime.targetTokens ++ [.version0] }
  let afterWidth := naturalResult afterVersion carrierWidth
  let afterGateCount :=
    naturalResult afterWidth
      (NatExpression.addOffset baseline 4)
  naturalResult afterGateCount
    (NatExpression.addOffset baseline 1)

theorem headerResult_scratch (runtime : Runtime) :
    (headerResult runtime).scratch =
      runtime.registers.baseline + 1 := by
  simp [headerResult, naturalResult, naturalValue,
    baseline, NatExpression.addOffset,
    NatExpression.counter, NatExpression.evaluate,
    NatExpression.evaluateCounter]
  omega

theorem headerResult_targetTokens (runtime : Runtime) :
    (headerResult runtime).targetTokens =
      runtime.targetTokens ++ [.version0] ++
        encodeNatTokens runtime.registers.carrierWidth ++
        encodeNatTokens (runtime.registers.baseline + 4) ++
        encodeNatTokens (runtime.registers.baseline + 1) := by
  simp [headerResult, naturalResult, naturalValue,
    carrierWidth, baseline, NatExpression.addOffset,
    NatExpression.counter, NatExpression.evaluate,
    NatExpression.evaluateCounter, List.append_assoc,
    Nat.add_comm]

theorem headerResult_registers (runtime : Runtime) :
    (headerResult runtime).registers = runtime.registers := by
  rfl

theorem headerResult_checks (runtime : Runtime) :
    (headerResult runtime).checks = runtime.checks := by
  rfl

theorem headerProgram_correct
    (program : List Primitive) (runtime : Runtime)
    (compiled : headerProgram = some program) :
    run program runtime =
      some (.accepted (headerResult runtime)) := by
  unfold headerProgram at compiled
  cases widthEq :
      compileNatural .plain carrierWidth with
  | none =>
      simp [widthEq] at compiled
  | some widthProgram =>
      cases gateCountEq :
          compileNatural .plain
            (NatExpression.addOffset baseline 4) with
      | none =>
          simp [widthEq, gateCountEq] at compiled
      | some gateCountProgram =>
          cases outputCountEq :
              compileNatural .plain
                (NatExpression.addOffset baseline 1) with
          | none =>
              simp [widthEq, gateCountEq,
                outputCountEq] at compiled
          | some outputCountProgram =>
              have programEq :
                  program =
                    [.append .plain .version0] ++
                      widthProgram ++ gateCountProgram ++
                      outputCountProgram := by
                simpa [widthEq, gateCountEq,
                  outputCountEq] using compiled.symm
              subst program
              let afterVersion : Runtime :=
                { runtime with
                  targetTokens :=
                    runtime.targetTokens ++ [Token.version0] }
              let afterWidth :=
                naturalResult afterVersion carrierWidth
              let afterGateCount :=
                naturalResult afterWidth
                  (NatExpression.addOffset baseline 4)
              have versionRun :
                  run [.append .plain .version0] runtime =
                    some (.accepted afterVersion) := by
                simp [afterVersion, run, step]
              have widthRun :
                  run widthProgram afterVersion =
                    some (.accepted afterWidth) := by
                simpa [afterWidth, naturalResult] using
                  compileNatural_correct .plain carrierWidth
                    widthProgram afterVersion widthEq
              have gateCountRun :
                  run gateCountProgram afterWidth =
                    some (.accepted afterGateCount) := by
                simpa [afterGateCount, naturalResult] using
                  compileNatural_correct .plain
                    (NatExpression.addOffset baseline 4)
                    gateCountProgram afterWidth gateCountEq
              have outputCountRun :
                  run outputCountProgram afterGateCount =
                    some (.accepted
                      (naturalResult afterGateCount
                        (NatExpression.addOffset baseline 1))) := by
                simpa [naturalResult] using
                  compileNatural_correct .plain
                    (NatExpression.addOffset baseline 1)
                    outputCountProgram afterGateCount
                    outputCountEq
              simp only [List.append_assoc]
              calc
                run
                    ([.append .plain .version0] ++
                      (widthProgram ++
                        (gateCountProgram ++ outputCountProgram)))
                    runtime =
                  run
                    (widthProgram ++
                      (gateCountProgram ++ outputCountProgram))
                    afterVersion :=
                  run_append_of_accepted _ _ runtime
                    afterVersion versionRun
                _ =
                  run (gateCountProgram ++ outputCountProgram)
                    afterWidth :=
                  run_append_of_accepted widthProgram _
                    afterVersion afterWidth widthRun
                _ = run outputCountProgram afterGateCount :=
                  run_append_of_accepted gateCountProgram _
                    afterWidth afterGateCount gateCountRun
                _ = some (.accepted (headerResult runtime)) := by
                  simpa [headerResult, afterVersion,
                    afterWidth, afterGateCount] using outputCountRun

/-! ### Output suffix programs -/

def beginOutputResult (runtime : Runtime) : Runtime :=
  { runtime with
    scratch := 0
    targetTokens :=
      runtime.targetTokens ++ [.programEnd] }

theorem beginOutputProgram_correct (runtime : Runtime) :
    run beginOutputProgram runtime =
      some (.accepted (beginOutputResult runtime)) := by
  rfl

def outputLoopItemResult (runtime : Runtime) : Runtime :=
  { runtime with
    scratch := runtime.scratch + 1
    targetTokens :=
      runtime.targetTokens ++
        encodeSourceTokens (.gate runtime.scratch) }

theorem outputLoopItemProgram_correct (runtime : Runtime) :
    run outputLoopItemProgram runtime =
      some (.accepted (outputLoopItemResult runtime)) := by
  simp [outputLoopItemProgram, run, step,
    outputLoopItemResult, encodeSourceTokens,
    List.append_assoc]

def outputLoopFinishResult (runtime : Runtime) : Runtime :=
  { runtime with
    scratch := runtime.registers.baseline
    targetTokens :=
      runtime.targetTokens ++
        encodeSourceTokens (.gate (runtime.scratch + 3)) ++
        [.outputsEnd, .threshold] ++
        encodeNatTokens runtime.registers.baseline ++
        [.instanceEnd] }

theorem outputLoopFinishProgram_correct (runtime : Runtime) :
    run outputLoopFinishProgram runtime =
      some (.accepted (outputLoopFinishResult runtime)) := by
  simp [outputLoopFinishProgram, run, step,
    addCounter, registerValue, outputLoopFinishResult,
    encodeSourceTokens, List.append_assoc]

/-! ### Prefix-fold programs -/

def emittedPoppedSourceResult (runtime : Runtime) : Runtime :=
  { runtime with
    targetTokens :=
      runtime.targetTokens ++
        encodeSourceTokens (.gate runtime.scratch) }

theorem emitPoppedGateSource_correct
    (mode : CursorMode) (runtime : Runtime) :
    run (emitPoppedGateSource mode) runtime =
      some (.accepted (emittedPoppedSourceResult runtime)) := by
  simp [emitPoppedGateSource, run, step,
    emittedPoppedSourceResult, encodeSourceTokens,
    List.append_assoc]

def appendedGateEndResult (runtime : Runtime) : Runtime :=
  { runtime with
    targetTokens := runtime.targetTokens ++ [.gateEnd] }

theorem appendGateEnd_correct
    (mode : CursorMode) (runtime : Runtime) :
    run [.append mode .gateEnd] runtime =
      some (.accepted (appendedGateEndResult runtime)) := by
  rfl

def prefixCloseProgram (count : Nat) : List Primitive :=
  [.append .marked .gateEnd] ++
    repeatPrimitive count
      (.incrementRegister .outputIndex) ++
    [.resetScratch]

def prefixCloseResult
    (runtime : Runtime) (count : Nat) : Runtime :=
  resetScratchResult
    (incrementOutputResult
      (appendedGateEndResult runtime) count)

theorem prefixCloseProgram_correct
    (count : Nat) (runtime : Runtime) :
    run (prefixCloseProgram count) runtime =
      some (.accepted (prefixCloseResult runtime count)) := by
  let afterEnd := appendedGateEndResult runtime
  let afterIncrement :=
    incrementOutputResult afterEnd count
  have endRun :
      run [.append .marked .gateEnd] runtime =
        some (.accepted afterEnd) :=
    appendGateEnd_correct .marked runtime
  have incrementRun :
      run
          (repeatPrimitive count
            (.incrementRegister .outputIndex))
          afterEnd =
        some (.accepted afterIncrement) :=
    run_repeat_incrementOutputIndex count afterEnd
  simp only [prefixCloseProgram, List.append_assoc]
  calc
    run
        ([.append .marked .gateEnd] ++
          (repeatPrimitive count
            (.incrementRegister .outputIndex) ++
            [.resetScratch]))
        runtime =
      run
        (repeatPrimitive count
          (.incrementRegister .outputIndex) ++
          [.resetScratch])
        afterEnd :=
      run_append_of_accepted _ _ runtime afterEnd endRun
    _ = run [.resetScratch] afterIncrement :=
      run_append_of_accepted
        (repeatPrimitive count
          (.incrementRegister .outputIndex))
        [.resetScratch] afterEnd afterIncrement incrementRun
    _ = some (.accepted (prefixCloseResult runtime count)) := by
      rfl

def firstPrefixOpeningProgram : List Primitive :=
  emitPoppedGateSource .marked ++
    [.resetScratch, .popCheck] ++
    emitPoppedGateSource .marked ++
    [.append .marked .gateEnd]

def firstPrefixOpeningResult
    (runtime : Runtime) (prior : List Nat)
    (newest : Nat) : Runtime :=
  { runtime with
    scratch := newest
    checks := prior
    targetTokens :=
      runtime.targetTokens ++
        encodeGateTokens
          { left := .gate runtime.scratch
            right := .gate newest } }

theorem firstPrefixOpeningProgram_correct
    (runtime : Runtime) (prior : List Nat)
    (newest : Nat)
    (shape : runtime.checks = prior ++ [newest]) :
    run firstPrefixOpeningProgram runtime =
      some (.accepted
        (firstPrefixOpeningResult runtime prior newest)) := by
  let afterLeft := emittedPoppedSourceResult runtime
  let afterPop :=
    { afterLeft with scratch := newest, checks := prior }
  let afterRight := emittedPoppedSourceResult afterPop
  let afterEnd := appendedGateEndResult afterRight
  have leftRun :
      run (emitPoppedGateSource .marked) runtime =
        some (.accepted afterLeft) :=
    emitPoppedGateSource_correct .marked runtime
  have popRun :
      run [.resetScratch, .popCheck] afterLeft =
        some (.accepted afterPop) := by
    simp [run, step, afterLeft,
      emittedPoppedSourceResult, shape,
      popNewest_append_singleton, afterPop]
  have rightRun :
      run (emitPoppedGateSource .marked) afterPop =
        some (.accepted afterRight) :=
    emitPoppedGateSource_correct .marked afterPop
  have endRun :
      run [.append .marked .gateEnd] afterRight =
        some (.accepted afterEnd) :=
    appendGateEnd_correct .marked afterRight
  simp only [firstPrefixOpeningProgram, List.append_assoc]
  calc
    run
        (emitPoppedGateSource .marked ++
          ([.resetScratch, .popCheck] ++
            (emitPoppedGateSource .marked ++
              [.append .marked .gateEnd])))
        runtime =
      run
        ([.resetScratch, .popCheck] ++
          (emitPoppedGateSource .marked ++
            [.append .marked .gateEnd]))
        afterLeft :=
      run_append_of_accepted _ _ runtime afterLeft leftRun
    _ =
      run
        (emitPoppedGateSource .marked ++
          [.append .marked .gateEnd])
        afterPop :=
      run_append_of_accepted _ _ afterLeft afterPop popRun
    _ = run [.append .marked .gateEnd] afterRight :=
      run_append_of_accepted _ _ afterPop afterRight rightRun
    _ = some (.accepted
        (firstPrefixOpeningResult runtime prior newest)) := by
      simpa [firstPrefixOpeningResult, afterLeft, afterPop,
        afterRight, afterEnd, emittedPoppedSourceResult,
        appendedGateEndResult, encodeGateTokens,
        encodeSourceTokens, List.append_assoc] using endRun

def firstPrefixResult
    (runtime : Runtime) (prior : List Nat)
    (newest : Nat) : Runtime :=
  let afterOpening :=
    firstPrefixOpeningResult runtime prior newest
  let afterLocalLeft :=
    sourceResult afterOpening (.gate outputIndex)
  let afterLocalRight :=
    sourceResult afterLocalLeft (.gate outputIndex)
  prefixCloseResult afterLocalRight 1

theorem firstPrefixResult_targetTokens
    (runtime : Runtime) (prior : List Nat)
    (newest : Nat) :
    (firstPrefixResult runtime prior newest).targetTokens =
      runtime.targetTokens ++
        encodeGateListTokens
          [ { left := .gate runtime.scratch
              right := .gate newest }
          , { left := .gate runtime.registers.outputIndex
              right := .gate runtime.registers.outputIndex }
          ] := by
  simp [firstPrefixResult, firstPrefixOpeningResult,
    prefixCloseResult, resetScratchResult,
    incrementOutputResult, appendedGateEndResult,
    sourceResult, sourceScratch, evaluatedSource,
    naturalValue, outputIndex, NatExpression.counter,
    NatExpression.evaluate, NatExpression.evaluateCounter,
    PlannedSource.evaluate, encodeGateListTokens,
    encodeGateTokens, encodeSourceTokens, List.append_assoc]

theorem firstPrefixResult_scratch
    (runtime : Runtime) (prior : List Nat)
    (newest : Nat) :
    (firstPrefixResult runtime prior newest).scratch = 0 := by
  rfl

theorem firstPrefixResult_registers
    (runtime : Runtime) (prior : List Nat)
    (newest : Nat) :
    (firstPrefixResult runtime prior newest).registers =
      { runtime.registers with
        outputIndex := runtime.registers.outputIndex + 1 } := by
  simp [firstPrefixResult, firstPrefixOpeningResult,
    prefixCloseResult, resetScratchResult,
    incrementOutputResult, appendedGateEndResult,
    sourceResult]

theorem firstPrefixResult_checks
    (runtime : Runtime) (prior : List Nat)
    (newest : Nat) :
    (firstPrefixResult runtime prior newest).checks = prior := by
  rfl

theorem firstPrefixProgram_correct
    (program : List Primitive) (runtime : Runtime)
    (prior : List Nat) (newest : Nat)
    (shape : runtime.checks = prior ++ [newest])
    (compiled : firstPrefixProgram = some program) :
    run program runtime =
      some (.accepted
        (firstPrefixResult runtime prior newest)) := by
  unfold firstPrefixProgram at compiled
  cases localEq :
      compileSource .marked (.gate outputIndex) with
  | none =>
      simp [localEq] at compiled
  | some localProgram =>
      have programEq :
          program =
            firstPrefixOpeningProgram ++
              localProgram ++ localProgram ++
              prefixCloseProgram 1 := by
        simpa [localEq, firstPrefixOpeningProgram,
          prefixCloseProgram, repeatPrimitive,
          List.append_assoc] using compiled.symm
      subst program
      let afterOpening :=
        firstPrefixOpeningResult runtime prior newest
      let afterLocalLeft :=
        sourceResult afterOpening (.gate outputIndex)
      let afterLocalRight :=
        sourceResult afterLocalLeft (.gate outputIndex)
      have openingRun :
          run firstPrefixOpeningProgram runtime =
            some (.accepted afterOpening) :=
        firstPrefixOpeningProgram_correct runtime
          prior newest shape
      have localLeftRun :
          run localProgram afterOpening =
            some (.accepted afterLocalLeft) :=
        compileSource_correct .marked (.gate outputIndex)
          localProgram afterOpening localEq
      have localRightRun :
          run localProgram afterLocalLeft =
            some (.accepted afterLocalRight) :=
        compileSource_correct .marked (.gate outputIndex)
          localProgram afterLocalLeft localEq
      have closeRun :
          run (prefixCloseProgram 1) afterLocalRight =
            some (.accepted
              (prefixCloseResult afterLocalRight 1)) :=
        prefixCloseProgram_correct 1 afterLocalRight
      simp only [List.append_assoc]
      calc
        run
            (firstPrefixOpeningProgram ++
              (localProgram ++
                (localProgram ++ prefixCloseProgram 1)))
            runtime =
          run
            (localProgram ++
              (localProgram ++ prefixCloseProgram 1))
            afterOpening :=
          run_append_of_accepted _ _ runtime
            afterOpening openingRun
        _ =
          run (localProgram ++ prefixCloseProgram 1)
            afterLocalLeft :=
          run_append_of_accepted _ _ afterOpening
            afterLocalLeft localLeftRun
        _ = run (prefixCloseProgram 1) afterLocalRight :=
          run_append_of_accepted _ _ afterLocalLeft
            afterLocalRight localRightRun
        _ = some (.accepted
            (firstPrefixResult runtime prior newest)) := by
          simpa [firstPrefixResult, afterOpening,
            afterLocalLeft, afterLocalRight] using closeRun

def nextPrefixOpeningProgram
    (accumulatorProgram : List Primitive) :
    List Primitive :=
  [.pushCheck] ++ accumulatorProgram ++
    [.resetScratch, .popCheck] ++
    emitPoppedGateSource .marked ++
    [.append .marked .gateEnd]

def nextPrefixOpeningResult (runtime : Runtime) : Runtime :=
  { runtime with
    targetTokens :=
      runtime.targetTokens ++
        encodeGateTokens
          { left := .gate runtime.registers.outputIndex
            right := .gate runtime.scratch } }

theorem nextPrefixOpeningProgram_correct
    (accumulatorProgram : List Primitive)
    (runtime : Runtime)
    (compiled :
      compileSource .marked (.gate outputIndex) =
        some accumulatorProgram) :
    run (nextPrefixOpeningProgram accumulatorProgram) runtime =
      some (.accepted (nextPrefixOpeningResult runtime)) := by
  let afterPush :=
    { runtime with
      checks := runtime.checks ++ [runtime.scratch] }
  let afterAccumulator :=
    sourceResult afterPush (.gate outputIndex)
  let afterPop :=
    { afterAccumulator with
      scratch := runtime.scratch
      checks := runtime.checks }
  let afterPoppedSource :=
    emittedPoppedSourceResult afterPop
  let afterEnd := appendedGateEndResult afterPoppedSource
  have pushRun :
      run [.pushCheck] runtime =
        some (.accepted afterPush) := by
    rfl
  have accumulatorRun :
      run accumulatorProgram afterPush =
        some (.accepted afterAccumulator) :=
    compileSource_correct .marked (.gate outputIndex)
      accumulatorProgram afterPush compiled
  have popRun :
      run [.resetScratch, .popCheck] afterAccumulator =
        some (.accepted afterPop) := by
    simp [run, step, afterAccumulator, afterPush,
      sourceResult, popNewest_append_singleton, afterPop]
  have poppedSourceRun :
      run (emitPoppedGateSource .marked) afterPop =
        some (.accepted afterPoppedSource) :=
    emitPoppedGateSource_correct .marked afterPop
  have endRun :
      run [.append .marked .gateEnd] afterPoppedSource =
        some (.accepted afterEnd) :=
    appendGateEnd_correct .marked afterPoppedSource
  simp only [nextPrefixOpeningProgram, List.append_assoc]
  calc
    run
        ([.pushCheck] ++
          (accumulatorProgram ++
            ([.resetScratch, .popCheck] ++
              (emitPoppedGateSource .marked ++
                [.append .marked .gateEnd]))))
        runtime =
      run
        (accumulatorProgram ++
          ([.resetScratch, .popCheck] ++
            (emitPoppedGateSource .marked ++
              [.append .marked .gateEnd])))
        afterPush :=
      run_append_of_accepted _ _ runtime afterPush pushRun
    _ =
      run
        ([.resetScratch, .popCheck] ++
          (emitPoppedGateSource .marked ++
            [.append .marked .gateEnd]))
        afterAccumulator :=
      run_append_of_accepted _ _ afterPush
        afterAccumulator accumulatorRun
    _ =
      run
        (emitPoppedGateSource .marked ++
          [.append .marked .gateEnd])
        afterPop :=
      run_append_of_accepted _ _ afterAccumulator
        afterPop popRun
    _ = run [.append .marked .gateEnd] afterPoppedSource :=
      run_append_of_accepted _ _ afterPop
        afterPoppedSource poppedSourceRun
    _ = some (.accepted (nextPrefixOpeningResult runtime)) := by
      simpa [nextPrefixOpeningResult, afterPush,
        afterAccumulator, afterPop, afterPoppedSource,
        afterEnd, sourceResult, sourceScratch,
        evaluatedSource, emittedPoppedSourceResult,
        appendedGateEndResult, naturalValue, outputIndex,
        NatExpression.counter, NatExpression.evaluate,
        NatExpression.evaluateCounter, PlannedSource.evaluate,
        encodeGateTokens, encodeSourceTokens,
        List.append_assoc] using endRun

def nextPrefixResult (runtime : Runtime) : Runtime :=
  let afterOpening := nextPrefixOpeningResult runtime
  let localSource :=
    PlannedSource.gate
      (NatExpression.addOffset outputIndex 1)
  let afterLocalLeft := sourceResult afterOpening localSource
  let afterLocalRight := sourceResult afterLocalLeft localSource
  prefixCloseResult afterLocalRight 2

theorem nextPrefixResult_targetTokens (runtime : Runtime) :
    (nextPrefixResult runtime).targetTokens =
      runtime.targetTokens ++
        encodeGateListTokens
          [ { left := .gate runtime.registers.outputIndex
              right := .gate runtime.scratch }
          , { left :=
                .gate (runtime.registers.outputIndex + 1)
              right :=
                .gate (runtime.registers.outputIndex + 1) }
          ] := by
  simp [nextPrefixResult, nextPrefixOpeningResult,
    prefixCloseResult, resetScratchResult,
    incrementOutputResult, appendedGateEndResult,
    sourceResult, sourceScratch, evaluatedSource,
    naturalValue, outputIndex, NatExpression.addOffset,
    NatExpression.counter, NatExpression.evaluate,
    NatExpression.evaluateCounter, PlannedSource.evaluate,
    encodeGateListTokens, encodeGateTokens,
    encodeSourceTokens, List.append_assoc, Nat.add_comm]

theorem nextPrefixResult_scratch (runtime : Runtime) :
    (nextPrefixResult runtime).scratch = 0 := by
  rfl

theorem nextPrefixResult_registers (runtime : Runtime) :
    (nextPrefixResult runtime).registers =
      { runtime.registers with
        outputIndex := runtime.registers.outputIndex + 2 } := by
  simp [nextPrefixResult, nextPrefixOpeningResult,
    prefixCloseResult, resetScratchResult,
    incrementOutputResult, appendedGateEndResult,
    sourceResult]

theorem nextPrefixResult_checks (runtime : Runtime) :
    (nextPrefixResult runtime).checks = runtime.checks := by
  rfl

theorem nextPrefixTailProgram_correct
    (program : List Primitive) (runtime : Runtime)
    (compiled : nextPrefixTailProgram = some program) :
    run program runtime =
      some (.accepted (nextPrefixResult runtime)) := by
  unfold nextPrefixTailProgram at compiled
  cases accumulatorEq :
      compileSource .marked (.gate outputIndex) with
  | none =>
      simp [accumulatorEq] at compiled
  | some accumulatorProgram =>
      cases localEq :
          compileSource .marked
            (.gate (NatExpression.addOffset outputIndex 1)) with
      | none =>
          simp [accumulatorEq, localEq] at compiled
      | some localProgram =>
          have programEq :
              program =
                nextPrefixOpeningProgram accumulatorProgram ++
                  localProgram ++ localProgram ++
                  prefixCloseProgram 2 := by
            simpa [accumulatorEq, localEq,
              nextPrefixOpeningProgram,
              prefixCloseProgram, repeatPrimitive,
              List.append_assoc] using compiled.symm
          subst program
          let afterOpening := nextPrefixOpeningResult runtime
          let localSource :=
            PlannedSource.gate
              (NatExpression.addOffset outputIndex 1)
          let afterLocalLeft :=
            sourceResult afterOpening localSource
          let afterLocalRight :=
            sourceResult afterLocalLeft localSource
          have openingRun :
              run
                  (nextPrefixOpeningProgram accumulatorProgram)
                  runtime =
                some (.accepted afterOpening) :=
            nextPrefixOpeningProgram_correct
              accumulatorProgram runtime accumulatorEq
          have localLeftRun :
              run localProgram afterOpening =
                some (.accepted afterLocalLeft) := by
            exact compileSource_correct .marked localSource
              localProgram afterOpening localEq
          have localRightRun :
              run localProgram afterLocalLeft =
                some (.accepted afterLocalRight) := by
            exact compileSource_correct .marked localSource
              localProgram afterLocalLeft localEq
          have closeRun :
              run (prefixCloseProgram 2) afterLocalRight =
                some (.accepted
                  (prefixCloseResult afterLocalRight 2)) :=
            prefixCloseProgram_correct 2 afterLocalRight
          simp only [List.append_assoc]
          calc
            run
                (nextPrefixOpeningProgram accumulatorProgram ++
                  (localProgram ++
                    (localProgram ++ prefixCloseProgram 2)))
                runtime =
              run
                (localProgram ++
                  (localProgram ++ prefixCloseProgram 2))
                afterOpening :=
              run_append_of_accepted _ _ runtime
                afterOpening openingRun
            _ =
              run (localProgram ++ prefixCloseProgram 2)
                afterLocalLeft :=
              run_append_of_accepted _ _ afterOpening
                afterLocalLeft localLeftRun
            _ = run (prefixCloseProgram 2) afterLocalRight :=
              run_append_of_accepted _ _ afterLocalLeft
                afterLocalRight localRightRun
            _ = some (.accepted (nextPrefixResult runtime)) := by
              simpa [nextPrefixResult, localSource, afterOpening,
                afterLocalLeft, afterLocalRight] using closeRun

/-! ### Branch semantics used by controller control nodes -/

theorem popCheck_empty_rejects
    (runtime : Runtime) (empty : runtime.checks = []) :
    step .popCheck runtime = some (.rejected runtime) := by
  simp [step, empty, popNewest]

theorem popCheck_nonempty_accepts
    (runtime : Runtime) (prior : List Nat) (newest : Nat)
    (shape : runtime.checks = prior ++ [newest]) :
    step .popCheck runtime =
      some (.accepted
        { runtime with
          scratch := newest
          checks := prior }) := by
  simp [step, shape, popNewest_append_singleton]

inductive InitialCheckBranch where
  | zero (runtime : Runtime)
  | positive (runtime : Runtime)
deriving BEq, DecidableEq, Repr

/-- Pure counterpart of `rawInitialPop`: rejection on the empty stack selects
the materialized zero-check final block, while a successful pop selects the
positive prefix fold. -/
def initialCheckBranch (runtime : Runtime) :
    InitialCheckBranch :=
  match step .popCheck runtime with
  | some (.accepted next) => .positive next
  | _ => .zero runtime

theorem initialCheckBranch_zero
    (runtime : Runtime) (empty : runtime.checks = []) :
    initialCheckBranch runtime = .zero runtime := by
  simp [initialCheckBranch,
    popCheck_empty_rejects runtime empty]

theorem initialCheckBranch_positive
    (runtime : Runtime) (prior : List Nat) (newest : Nat)
    (shape : runtime.checks = prior ++ [newest]) :
    initialCheckBranch runtime =
      .positive
        { runtime with
          scratch := newest
          checks := prior } := by
  simp [initialCheckBranch,
    popCheck_nonempty_accepts runtime prior newest shape]

theorem initialCheckBranch_zero_runs_finalZero
    (runtime : Runtime) (program : List Primitive)
    (empty : runtime.checks = [])
    (compiled : finalZeroProgram = some program) :
    initialCheckBranch runtime = .zero runtime ∧
      run program runtime =
        some (.accepted
          (finalResult runtime finalZeroPlan)) := by
  exact
    ⟨initialCheckBranch_zero runtime empty,
      finalZeroProgram_correct program runtime compiled⟩

theorem initialCheckBranch_zero_finalTokens
    (runtime : Runtime) (program : List Primitive)
    (empty : runtime.checks = [])
    (compiled : finalZeroProgram = some program) :
    ∃ final,
      initialCheckBranch runtime = .zero runtime ∧
      run program runtime = some (.accepted final) ∧
      final.targetTokens =
        runtime.targetTokens ++
          plannedGateTokens runtime finalZeroPlan := by
  refine ⟨finalResult runtime finalZeroPlan,
    initialCheckBranch_zero runtime empty,
    finalZeroProgram_correct program runtime compiled, ?_⟩
  exact finalResult_targetTokens runtime finalZeroPlan

end PNP.Concrete.LockedNAND.TargetEmitterProgramSemantics
