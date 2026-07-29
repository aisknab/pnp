/-
Copyright (c) 2026 PNP Labs.

Capacity-safe executions of the closed locked-NAND target-emitter programs.

The executable programs and graph are defined elsewhere.  This module only
assembles proof witnesses for the existing `ProgramSafe` relation, using the
source-derived bounds in `TargetEmitterCapacity` and the constructive marked
source layouts in `TargetEmitterRuntimeLayout`.
-/

import PNP.Concrete.LockedNANDTargetEmitterCapacity
import PNP.Concrete.LockedNANDTargetEmitterRuntimeLayout

namespace PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgramSafety

open PNP.Concrete
open TargetEmitterPlan
open TargetEmitterProgramSemantics

abbrev ProgramSafe := TargetEmitterRuntimeProgram.ProgramSafe
abbrev PrimitiveSafe := TargetEmitterRuntimeProgram.PrimitiveSafe
abbrev SourceContext := TargetEmitterRuntimeProgram.SourceContext
abbrev CursorLayout := TargetEmitterRuntimeProgram.CursorLayout
abbrev ReloadLayout := TargetEmitterRuntimeProgram.ReloadLayout
abbrev ControllerRange := TargetEmitterCapacity.ControllerRange
abbrev PlanBounds := TargetEmitterCapacity.PlanBounds
abbrev BlockBounds := TargetEmitterCapacity.BlockBounds

/-! ### Shared proof-only inputs -/

/-- Cursor and source-head facts shared by every marked controller block. -/
structure MarkedWorkspace (source : List WorkSymbol) where
  context : SourceContext source
  cursor : CursorLayout source

/-- Extra input/gate unary view needed exactly when a plan expression reloads
the captured source coordinate. -/
structure CapturedReady
    (raw : RawCircuit) (source : List WorkSymbol)
    (captured : Nat) where
  layout : ReloadLayout source
  capturedEq : captured = layout.value
  valueBound :
    layout.value + 1 ≤ TargetEmitterLedger.slotCapacity raw

private inductive ModeReady
    (source : List WorkSymbol) : CursorMode → Type where
  | plain
      (sourcePacked :
        ∀ symbol, symbol ∈ source →
          TargetEmitter.PackedSymbol symbol) :
      ModeReady source .plain
  | marked (layout : CursorLayout source) :
      ModeReady source .marked

private theorem ModeReady.append
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {mode : CursorMode}
    (ready : ModeReady source mode)
    (runtime : Runtime) (token : Token) :
    PrimitiveSafe capacity source context
      (.append mode token) runtime
      { runtime with
        targetTokens := runtime.targetTokens ++ [token] } := by
  cases ready with
  | plain sourcePacked =>
      exact TargetEmitterRuntimeProgram.PrimitiveSafe.appendPlain runtime token sourcePacked
  | marked layout =>
      exact TargetEmitterRuntimeProgram.PrimitiveSafe.appendMarked runtime token layout

private theorem ModeReady.emitScratch
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {mode : CursorMode}
    (ready : ModeReady source mode)
    (runtime : Runtime)
    (countBound : runtime.scratch ≤ capacity) :
    PrimitiveSafe capacity source context
      (.emitScratchNat mode) runtime
      { runtime with
        targetTokens :=
          runtime.targetTokens ++
            encodeNatTokens runtime.scratch } := by
  cases ready with
  | plain sourcePacked =>
      exact
        TargetEmitterRuntimeProgram.PrimitiveSafe.emitScratchNatPlain runtime
          countBound sourcePacked
  | marked layout =>
      exact
        TargetEmitterRuntimeProgram.PrimitiveSafe.emitScratchNatMarked runtime
          countBound layout

private theorem ProgramSafe.singleton
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitive : Primitive} {initial final : Runtime}
    (safe :
      PrimitiveSafe capacity source context
        primitive initial final) :
    ProgramSafe capacity source context
      [primitive] initial final :=
  .cons primitive [] initial final final safe (.nil final)

private theorem ProgramSafe.append
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {first second : List Primitive}
    {initial middle final : Runtime}
    (left :
      ProgramSafe capacity source context
        first initial middle)
    (right :
      ProgramSafe capacity source context
        second middle final) :
    ProgramSafe capacity source context
      (first ++ second) initial final := by
  induction left with
  | nil =>
      exact right
  | cons primitive rest initial next middle head tail ih =>
      exact .cons primitive (rest ++ second)
        initial next final head (ih right)

private theorem repeatIncrementScratch_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (count : Nat) (runtime : Runtime)
    (bound : runtime.scratch + count < capacity) :
    ProgramSafe capacity source context
      (repeatPrimitive count .incrementScratch)
      runtime
      { runtime with scratch := runtime.scratch + count } := by
  induction count generalizing runtime with
  | zero =>
      simpa [repeatPrimitive] using
        (TargetEmitterRuntimeProgram.ProgramSafe.nil runtime :
          ProgramSafe capacity source context [] runtime runtime)
  | succ count inductionHypothesis =>
      rw [show
        repeatPrimitive (Nat.succ count) .incrementScratch =
          .incrementScratch ::
            repeatPrimitive count .incrementScratch by
        simp [repeatPrimitive, List.replicate_succ]]
      let middle : Runtime :=
        { runtime with scratch := runtime.scratch + 1 }
      refine
        .cons .incrementScratch
          (repeatPrimitive count .incrementScratch)
          runtime middle
          { runtime with
            scratch := runtime.scratch + Nat.succ count }
          (TargetEmitterRuntimeProgram.PrimitiveSafe.incrementScratch runtime (by omega)) ?_
      have tail :=
        inductionHypothesis middle (by
          simp [middle]
          omega)
      simpa [middle, Nat.add_assoc, Nat.add_comm 1 count] using tail

private theorem repeatIncrementOutputIndex_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (count : Nat) (runtime : Runtime)
    (fits : TargetEmitterRuntimeProgram.LedgerFits
      capacity runtime.registers)
    (bound :
      runtime.registers.outputIndex + count < capacity) :
    ProgramSafe capacity source context
      (repeatPrimitive count
        (.incrementRegister .outputIndex))
      runtime
      (incrementOutputResult runtime count) := by
  induction count generalizing runtime with
  | zero =>
      simpa [repeatPrimitive, incrementOutputResult] using
        (TargetEmitterRuntimeProgram.ProgramSafe.nil runtime :
          ProgramSafe capacity source context [] runtime runtime)
  | succ count inductionHypothesis =>
      rw [show
        repeatPrimitive (Nat.succ count)
            (.incrementRegister .outputIndex) =
          .incrementRegister .outputIndex ::
            repeatPrimitive count
              (.incrementRegister .outputIndex) by
        simp [repeatPrimitive, List.replicate_succ]]
      let middle : Runtime :=
        { runtime with
          registers :=
            TargetEmitterRuntimePrimitives.incrementRegisters
              .outputIndex runtime.registers }
      have available :
          runtime.registers.outputIndex < capacity := by
        omega
      have primitiveFits :=
        TargetEmitterRuntimePrimitives.incrementRegisters_fits
          capacity runtime.registers .outputIndex
          fits.toPrimitive available
      have middleFits :
          TargetEmitterRuntimeProgram.LedgerFits
            capacity middle.registers := by
        exact
          { inputCount := primitiveFits.inputCount
            normalizedGateCount :=
              primitiveFits.normalizedGateCount
            carrierWidth := primitiveFits.carrierWidth
            baseline := primitiveFits.baseline
            currentGate := primitiveFits.currentGate
            outputIndex := primitiveFits.outputIndex }
      refine
        .cons (.incrementRegister .outputIndex)
          (repeatPrimitive count
            (.incrementRegister .outputIndex))
          runtime middle
          (incrementOutputResult runtime (Nat.succ count))
          (TargetEmitterRuntimeProgram.PrimitiveSafe.incrementRegister runtime
            .outputIndex .outputIndex rfl fits available) ?_
      have tail :=
        inductionHypothesis middle middleFits (by
          simp [middle,
            TargetEmitterRuntimePrimitives.incrementRegisters]
          omega)
      simpa [middle, incrementOutputResult,
        TargetEmitterRuntimePrimitives.incrementRegisters,
        Nat.add_assoc, Nat.add_comm 1 count] using tail

/-! ### Safe compiled natural expressions -/

private def RegisterTerms (terms : List Counter) : Prop :=
  ∀ counter, counter ∈ terms →
    counter ≠ .captured ∧ counter ≠ .scratch

private theorem registerCounter_slot
    {counter : Counter}
    (register : counter ≠ .captured ∧ counter ≠ .scratch) :
    ∃ slot : TargetEmitterLedger.Slot,
      TargetEmitterPrimitiveCompiler.counterSlot counter =
        some slot := by
  cases counter with
  | inputCount =>
      exact ⟨.inputCount, rfl⟩
  | normalizedGateCount =>
      exact ⟨.normalizedGateCount, rfl⟩
  | carrierWidth =>
      exact ⟨.carrierWidth, rfl⟩
  | baseline =>
      exact ⟨.baseline, rfl⟩
  | currentGate =>
      exact ⟨.currentGate, rfl⟩
  | outputIndex =>
      exact ⟨.outputIndex, rfl⟩
  | captured =>
      exact False.elim (register.1 rfl)
  | scratch =>
      exact False.elim (register.2 rfl)

private theorem evaluateCounter_eq_slotValue
    (registers : TargetEmitter.UnaryRegisters)
    (captured : Nat) (counter : Counter)
    (slot : TargetEmitterLedger.Slot)
    (slotEq :
      TargetEmitterPrimitiveCompiler.counterSlot counter =
        some slot) :
    NatExpression.evaluateCounter registers captured 0 counter =
      TargetEmitterLedger.slotValue registers slot := by
  cases counter <;> cases slot <;>
    simp [TargetEmitterPrimitiveCompiler.counterSlot,
      NatExpression.evaluateCounter,
      TargetEmitterLedger.slotValue] at slotEq ⊢

private theorem compileRegisterTerms_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    (terms : List Counter) (program : List Primitive)
    (runtime : Runtime)
    (registerTerms : RegisterTerms terms)
    (compiled : compileTerms terms = some program)
    (fits :
      TargetEmitterRuntimeProgram.LedgerFits
        capacity runtime.registers)
    (bound :
      runtime.scratch +
          termsValue runtime.registers runtime.captured terms ≤
        capacity) :
    ProgramSafe capacity source context program runtime
      { runtime with
        scratch :=
          runtime.scratch +
            termsValue runtime.registers runtime.captured terms } := by
  induction terms generalizing program runtime with
  | nil =>
      have programEq : program = [] := by
        simpa [compileTerms] using compiled.symm
      subst program
      simpa [termsValue] using
        (TargetEmitterRuntimeProgram.ProgramSafe.nil runtime :
          ProgramSafe capacity source context [] runtime runtime)
  | cons counter rest inductionHypothesis =>
      have counterRegister :=
        registerTerms counter (List.Mem.head rest)
      rcases registerCounter_slot counterRegister with
        ⟨slot, slotEq⟩
      have operationEq :
          counterOperation counter =
            some (.addRegister counter) := by
        cases counter <;>
          simp [counterOperation,
            TargetEmitterPrimitiveCompiler.counterSlot] at slotEq ⊢
      cases tailEq : compileTerms rest with
      | none =>
          simp [compileTerms, operationEq, tailEq] at compiled
      | some tailProgram =>
          have programEq :
              program =
                .addRegister counter :: tailProgram := by
            simpa [compileTerms, operationEq, tailEq] using
              compiled.symm
          subst program
          let value :=
            TargetEmitterLedger.slotValue runtime.registers slot
          let middle : Runtime :=
            { runtime with
              scratch := runtime.scratch + value }
          have valueEq :
              NatExpression.evaluateCounter
                  runtime.registers runtime.captured 0 counter =
                value :=
            evaluateCounter_eq_slotValue
              runtime.registers runtime.captured counter slot slotEq
          have enough :
              runtime.scratch + value ≤ capacity := by
            simp only [termsValue, List.map_cons, List.sum_cons] at bound
            omega
          have restRegister : RegisterTerms rest := by
            intro item member
            exact registerTerms item (List.Mem.tail counter member)
          have tailBound :
              middle.scratch +
                  termsValue middle.registers middle.captured rest ≤
                capacity := by
            simp only [termsValue, List.map_cons,
              List.sum_cons] at bound
            rw [valueEq] at bound
            simpa only [middle, termsValue, Nat.add_assoc] using bound
          refine
            .cons (.addRegister counter) tailProgram
              runtime middle
              { runtime with
                scratch :=
                  runtime.scratch +
                    termsValue runtime.registers
                      runtime.captured (counter :: rest) }
              (TargetEmitterRuntimeProgram.PrimitiveSafe.addRegister runtime counter slot
                slotEq fits enough) ?_
          have tail :=
            inductionHypothesis tailProgram middle restRegister
              tailEq fits tailBound
          simpa [middle, value, valueEq, termsValue,
            Nat.add_assoc] using tail

private theorem compileCapturedTerms_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {context : SourceContext source}
    (rest : List Counter) (program : List Primitive)
    (runtime : Runtime)
    (registerTerms : RegisterTerms rest)
    (compiled :
      compileTerms (.captured :: rest) = some program)
    (fits :
      TargetEmitterRuntimeProgram.LedgerFits
        (TargetEmitterLedger.slotCapacity raw) runtime.registers)
    (ready : CapturedReady raw source runtime.captured)
    (bound :
      runtime.captured +
          termsValue runtime.registers runtime.captured rest ≤
        TargetEmitterLedger.slotCapacity raw) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source context
      program { runtime with scratch := 0 }
      { runtime with
        scratch :=
          termsValue runtime.registers runtime.captured
            (.captured :: rest) } := by
  cases tailEq : compileTerms rest with
  | none =>
      simp [compileTerms, counterOperation, tailEq] at compiled
  | some tailProgram =>
      have programEq :
          program = .reloadCaptured :: tailProgram := by
        simpa [compileTerms, counterOperation, tailEq] using
          compiled.symm
      subst program
      let initial : Runtime := { runtime with scratch := 0 }
      let middle : Runtime :=
        { runtime with scratch := runtime.captured }
      have head :
          PrimitiveSafe
            (TargetEmitterLedger.slotCapacity raw) source context
            .reloadCaptured initial middle := by
        simpa [initial, middle] using
          (TargetEmitterRuntimeProgram.PrimitiveSafe.reloadCaptured initial ready.layout
            rfl ready.capturedEq ready.valueBound)
      have tailBound :
          middle.scratch +
              termsValue middle.registers middle.captured rest ≤
            TargetEmitterLedger.slotCapacity raw := by
        simpa [middle] using bound
      have tail :=
        compileRegisterTerms_safe
          (source := source) (context := context)
          rest tailProgram middle
          registerTerms tailEq fits tailBound
      refine
        .cons .reloadCaptured tailProgram initial middle
          { runtime with
            scratch :=
              termsValue runtime.registers runtime.captured
                (.captured :: rest) }
          head ?_
      simpa [initial, middle, termsValue,
        NatExpression.evaluateCounter, Nat.add_assoc] using tail

private inductive CoordinateSafe
    (raw : RawCircuit) (source : List WorkSymbol)
    (registers : TargetEmitter.UnaryRegisters)
    (captured : Nat) :
    NatExpression → Prop where
  | registers
      (expression : NatExpression)
      (registerTerms : RegisterTerms expression.terms)
      (valueBound :
        expression.evaluate registers captured 0 <
          TargetEmitterLedger.slotCapacity raw) :
      CoordinateSafe raw source registers captured expression
  | captured
      (expression : NatExpression) (rest : List Counter)
      (termsEq : expression.terms = .captured :: rest)
      (registerTerms : RegisterTerms rest)
      (ready : CapturedReady raw source captured)
      (valueBound :
        expression.evaluate registers captured 0 <
          TargetEmitterLedger.slotCapacity raw) :
      CoordinateSafe raw source registers captured expression

private theorem computeNatural_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {context : SourceContext source}
    (expression : NatExpression)
    (program : List Primitive) (runtime : Runtime)
    (compiled : computeNatural expression = some program)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (fits :
      TargetEmitterRuntimeProgram.LedgerFits
        (TargetEmitterLedger.slotCapacity raw) runtime.registers)
    (coordinate :
      CoordinateSafe raw source runtime.registers
        runtime.captured expression) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source context
      program runtime
      { runtime with
        scratch := naturalValue runtime expression } := by
  unfold computeNatural at compiled
  cases termsEq : compileTerms expression.terms with
  | none =>
      simp [termsEq] at compiled
  | some termsProgram =>
      have programEq :
          program =
            [.resetScratch] ++ termsProgram ++
              repeatPrimitive expression.offset
                .incrementScratch := by
        simpa [termsEq] using compiled.symm
      subst program
      let resetRuntime : Runtime := { runtime with scratch := 0 }
      let termsRuntime : Runtime :=
        { runtime with
          scratch :=
            termsValue runtime.registers runtime.captured
              expression.terms }
      have resetSafe :
          ProgramSafe
            (TargetEmitterLedger.slotCapacity raw) source context
            [.resetScratch] runtime resetRuntime := by
        exact ProgramSafe.singleton
          (TargetEmitterRuntimeProgram.PrimitiveSafe.resetScratch runtime scratchBound)
      have termsSafe :
          ProgramSafe
            (TargetEmitterLedger.slotCapacity raw) source context
            termsProgram resetRuntime termsRuntime := by
        cases coordinate with
        | registers registerTerms valueBound =>
            have sumBound :
                termsValue runtime.registers runtime.captured
                    expression.terms ≤
                  TargetEmitterLedger.slotCapacity raw := by
              have evaluation :
                  expression.offset +
                      termsValue runtime.registers runtime.captured
                        expression.terms =
                    expression.evaluate
                      runtime.registers runtime.captured 0 := by
                rfl
              omega
            have safe :=
              compileRegisterTerms_safe
                (source := source) (context := context)
                expression.terms
                termsProgram resetRuntime registerTerms termsEq
                fits (by simpa [resetRuntime] using sumBound)
            simpa [resetRuntime, termsRuntime] using safe
        | captured rest capturedTermsEq registerTerms ready
            valueBound =>
            have termsEq' :
                compileTerms (.captured :: rest) =
                  some termsProgram := by
              simpa [capturedTermsEq] using termsEq
            have sumBound :
                runtime.captured +
                    termsValue runtime.registers runtime.captured rest ≤
                  TargetEmitterLedger.slotCapacity raw := by
              have evaluation :
                  expression.offset +
                        (runtime.captured +
                          termsValue runtime.registers
                            runtime.captured rest) =
                    expression.evaluate
                      runtime.registers runtime.captured 0 := by
                simp [NatExpression.evaluate, termsValue,
                  capturedTermsEq,
                  NatExpression.evaluateCounter]
              omega
            have safe :=
              compileCapturedTerms_safe (context := context)
                rest termsProgram runtime
                registerTerms termsEq' fits ready sumBound
            simpa [resetRuntime, termsRuntime,
              capturedTermsEq] using safe
      have incrementsSafe :
          ProgramSafe
            (TargetEmitterLedger.slotCapacity raw) source context
            (repeatPrimitive expression.offset .incrementScratch)
            termsRuntime
            { runtime with
              scratch := naturalValue runtime expression } := by
        have valueBound :
            naturalValue runtime expression <
              TargetEmitterLedger.slotCapacity raw := by
          cases coordinate with
          | registers registerTerms coordinateBound =>
              simpa [naturalValue] using coordinateBound
          | captured rest termsEq registerTerms ready
              coordinateBound =>
              simpa [naturalValue] using coordinateBound
        have incrementBound :
            termsRuntime.scratch + expression.offset <
              TargetEmitterLedger.slotCapacity raw := by
          simp only [termsRuntime]
          have valueEq := naturalValue_eq runtime expression
          omega
        have safe :=
          repeatIncrementScratch_safe
            (source := source) (context := context)
            expression.offset termsRuntime
            incrementBound
        simpa [termsRuntime, naturalValue_eq,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using safe
      simpa only [List.append_assoc] using
        resetSafe.append (termsSafe.append incrementsSafe)

private theorem compileNatural_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {context : SourceContext source}
    {mode : CursorMode}
    (ready : ModeReady source mode)
    (expression : NatExpression)
    (program : List Primitive) (runtime : Runtime)
    (compiled : compileNatural mode expression = some program)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (fits :
      TargetEmitterRuntimeProgram.LedgerFits
        (TargetEmitterLedger.slotCapacity raw) runtime.registers)
    (coordinate :
      CoordinateSafe raw source runtime.registers
        runtime.captured expression) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source context
      program runtime
      { runtime with
        scratch := naturalValue runtime expression
        targetTokens :=
          runtime.targetTokens ++
            encodeNatTokens (naturalValue runtime expression) } := by
  unfold compileNatural at compiled
  cases computationEq : computeNatural expression with
  | none =>
      simp [computationEq] at compiled
  | some computation =>
      have programEq :
          program = computation ++ [.emitScratchNat mode] := by
        simpa [computationEq] using compiled.symm
      subst program
      let middle : Runtime :=
        { runtime with
          scratch := naturalValue runtime expression }
      have computationSafe :=
        computeNatural_safe (context := context)
          expression computation runtime
          computationEq scratchBound fits coordinate
      have valueBound :
          naturalValue runtime expression ≤
            TargetEmitterLedger.slotCapacity raw := by
        cases coordinate with
        | registers registerTerms coordinateBound =>
            have :
                naturalValue runtime expression <
                  TargetEmitterLedger.slotCapacity raw := by
              simpa [naturalValue] using coordinateBound
            omega
        | captured rest termsEq registerTerms ready
            coordinateBound =>
            have :
                naturalValue runtime expression <
                  TargetEmitterLedger.slotCapacity raw := by
              simpa [naturalValue] using coordinateBound
            omega
      have emitSafe :
          ProgramSafe
            (TargetEmitterLedger.slotCapacity raw) source context
            [.emitScratchNat mode] middle
            { runtime with
              scratch := naturalValue runtime expression
              targetTokens :=
                runtime.targetTokens ++
                  encodeNatTokens
                    (naturalValue runtime expression) } := by
        exact ProgramSafe.singleton <|
          by simpa [middle] using
            ready.emitScratch middle valueBound
      exact computationSafe.append emitSafe

/-! ### Safe planned sources and gate lists -/

private inductive PlannedSourceSafe
    (raw : RawCircuit) (source : List WorkSymbol)
    (registers : TargetEmitter.UnaryRegisters)
    (captured : Nat) : PlannedSource → Prop where
  | constant (value : Bool) :
      PlannedSourceSafe raw source registers captured (.constant value)
  | input
      (coordinate : NatExpression)
      (safe :
        CoordinateSafe raw source registers captured coordinate) :
      PlannedSourceSafe raw source registers captured
        (.input coordinate)
  | gate
      (coordinate : NatExpression)
      (safe :
        CoordinateSafe raw source registers captured coordinate) :
      PlannedSourceSafe raw source registers captured
        (.gate coordinate)

private theorem plannedSourceSafe_scratch
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime} {planned : PlannedSource}
    (safe :
      PlannedSourceSafe raw source runtime.registers
        runtime.captured planned)
    (initialBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw) :
    (sourceResult runtime planned).scratch <
      TargetEmitterLedger.slotCapacity raw := by
  cases safe with
  | constant =>
      exact initialBound
  | input coordinate coordinateSafe =>
      simpa [sourceResult, sourceScratch] using
        (by cases coordinateSafe <;> assumption)
  | gate coordinate coordinateSafe =>
      simpa [sourceResult, sourceScratch] using
        (by cases coordinateSafe <;> assumption)

private theorem compileSource_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {context : SourceContext source}
    {mode : CursorMode}
    (ready : ModeReady source mode)
    (planned : PlannedSource)
    (program : List Primitive) (runtime : Runtime)
    (compiled : compileSource mode planned = some program)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (fits :
      TargetEmitterRuntimeProgram.LedgerFits
        (TargetEmitterLedger.slotCapacity raw) runtime.registers)
    (safe :
      PlannedSourceSafe raw source runtime.registers
        runtime.captured planned) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source context
      program runtime (sourceResult runtime planned) := by
  cases safe with
  | constant value =>
      cases value with
      | false =>
          have programEq :
              program = [.append mode .constantFalse] := by
            simpa [compileSource] using compiled.symm
          subst program
          simpa [sourceResult, sourceScratch, evaluatedSource,
            PlannedSource.evaluate, encodeSourceTokens] using
            (ProgramSafe.singleton
              (ready.append runtime .constantFalse))
      | true =>
          have programEq :
              program = [.append mode .constantTrue] := by
            simpa [compileSource] using compiled.symm
          subst program
          simpa [sourceResult, sourceScratch, evaluatedSource,
            PlannedSource.evaluate, encodeSourceTokens] using
            (ProgramSafe.singleton
              (ready.append runtime .constantTrue))
  | input coordinate coordinateSafe =>
      unfold compileSource at compiled
      cases naturalEq : compileNatural mode coordinate with
      | none =>
          simp [naturalEq] at compiled
      | some naturalProgram =>
          have programEq :
              program =
                .append mode .input :: naturalProgram := by
            simpa [naturalEq] using compiled.symm
          subst program
          let middle : Runtime :=
            { runtime with
              targetTokens := runtime.targetTokens ++ [.input] }
          have head :
              PrimitiveSafe
                (TargetEmitterLedger.slotCapacity raw) source context
                (.append mode .input) runtime middle := by
            simpa [middle] using
              ready.append
                (capacity := TargetEmitterLedger.slotCapacity raw)
                (context := context) runtime .input
          have coordinateSafe' :
              CoordinateSafe raw source middle.registers
                middle.captured coordinate := by
            simpa [middle] using coordinateSafe
          have tail :=
            compileNatural_safe (context := context)
              ready coordinate naturalProgram
              middle naturalEq (by simpa [middle] using scratchBound)
              fits coordinateSafe'
          refine
            .cons (.append mode .input) naturalProgram
              runtime middle (sourceResult runtime (.input coordinate))
              head ?_
          simpa [middle, sourceResult, sourceScratch,
            evaluatedSource, PlannedSource.evaluate,
            naturalValue, encodeSourceTokens,
            List.append_assoc] using tail
  | gate coordinate coordinateSafe =>
      unfold compileSource at compiled
      cases naturalEq : compileNatural mode coordinate with
      | none =>
          simp [naturalEq] at compiled
      | some naturalProgram =>
          have programEq :
              program =
                .append mode .gate :: naturalProgram := by
            simpa [naturalEq] using compiled.symm
          subst program
          let middle : Runtime :=
            { runtime with
              targetTokens := runtime.targetTokens ++ [.gate] }
          have head :
              PrimitiveSafe
                (TargetEmitterLedger.slotCapacity raw) source context
                (.append mode .gate) runtime middle := by
            simpa [middle] using
              ready.append
                (capacity := TargetEmitterLedger.slotCapacity raw)
                (context := context) runtime .gate
          have coordinateSafe' :
              CoordinateSafe raw source middle.registers
                middle.captured coordinate := by
            simpa [middle] using coordinateSafe
          have tail :=
            compileNatural_safe (context := context)
              ready coordinate naturalProgram
              middle naturalEq (by simpa [middle] using scratchBound)
              fits coordinateSafe'
          refine
            .cons (.append mode .gate) naturalProgram
              runtime middle (sourceResult runtime (.gate coordinate))
              head ?_
          simpa [middle, sourceResult, sourceScratch,
            evaluatedSource, PlannedSource.evaluate,
            naturalValue, encodeSourceTokens,
            List.append_assoc] using tail

private structure PlannedGateSafe
    (raw : RawCircuit) (source : List WorkSymbol)
    (registers : TargetEmitter.UnaryRegisters)
    (captured : Nat) (gate : PlannedGate) : Prop where
  left :
    PlannedSourceSafe raw source registers captured gate.left
  right :
    PlannedSourceSafe raw source registers captured gate.right

private theorem compileGate_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {context : SourceContext source}
    {mode : CursorMode}
    (ready : ModeReady source mode)
    (gate : PlannedGate) (program : List Primitive)
    (runtime : Runtime)
    (compiled : compileGate mode gate = some program)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (fits :
      TargetEmitterRuntimeProgram.LedgerFits
        (TargetEmitterLedger.slotCapacity raw) runtime.registers)
    (safe :
      PlannedGateSafe raw source runtime.registers
        runtime.captured gate) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source context
      program runtime (gateResult runtime gate) := by
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
                      [.append mode .gateEnd] := by
                simpa [leftEq, rightEq] using compiled.symm
              subst program
              have leftSafe :=
                compileSource_safe (context := context)
                  ready left leftProgram runtime
                  leftEq scratchBound fits safe.left
              have afterLeftBound :=
                plannedSourceSafe_scratch safe.left scratchBound
              have rightCoordinate :
                  PlannedSourceSafe raw source
                    (sourceResult runtime left).registers
                    (sourceResult runtime left).captured right := by
                simpa [sourceResult] using safe.right
              have rightSafe :=
                compileSource_safe (context := context)
                  ready right rightProgram
                  (sourceResult runtime left) rightEq afterLeftBound
                  fits rightCoordinate
              have endSafe :
                  ProgramSafe
                    (TargetEmitterLedger.slotCapacity raw) source
                    context [.append mode .gateEnd]
                    (sourceResult (sourceResult runtime left) right)
                    (gateResult runtime { left := left, right := right }) := by
                simpa [gateResult] using
                  (ProgramSafe.singleton
                    (ready.append
                      (sourceResult
                        (sourceResult runtime left) right)
                      .gateEnd))
              simpa only [List.append_assoc] using
                leftSafe.append (rightSafe.append endSafe)

private theorem compileGates_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {context : SourceContext source}
    {mode : CursorMode}
    (ready : ModeReady source mode)
    (gates : List PlannedGate) (program : List Primitive)
    (runtime : Runtime)
    (compiled : compileGates mode gates = some program)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (fits :
      TargetEmitterRuntimeProgram.LedgerFits
        (TargetEmitterLedger.slotCapacity raw) runtime.registers)
    (safe :
      ∀ gate, gate ∈ gates →
        PlannedGateSafe raw source runtime.registers
          runtime.captured gate) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source context
      program runtime (gatesResult runtime gates) := by
  induction gates generalizing program runtime with
  | nil =>
      have programEq : program = [] := by
        simpa [compileGates] using compiled.symm
      subst program
      exact .nil runtime
  | cons gate rest inductionHypothesis =>
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
              have gateSafe := safe gate (List.Mem.head rest)
              have first :=
                compileGate_safe (context := context)
                  ready gate gateProgram runtime
                  gateEq scratchBound fits gateSafe
              have nextScratch :
                  (gateResult runtime gate).scratch <
                    TargetEmitterLedger.slotCapacity raw := by
                cases gateSafe with
                | mk leftSafe rightSafe =>
                    have leftBound :=
                      plannedSourceSafe_scratch leftSafe scratchBound
                    have rightSafe' :
                        PlannedSourceSafe raw source
                          (sourceResult runtime gate.left).registers
                          (sourceResult runtime gate.left).captured
                          gate.right := by
                      simpa [sourceResult] using rightSafe
                    simpa [gateResult] using
                      plannedSourceSafe_scratch rightSafe' leftBound
              have restSafe :
                  ∀ next, next ∈ rest →
                    PlannedGateSafe raw source
                      (gateResult runtime gate).registers
                      (gateResult runtime gate).captured next := by
                intro next member
                simpa [gateResult, sourceResult] using
                  safe next (List.Mem.tail gate member)
              have tail :=
                inductionHypothesis restProgram
                  (gateResult runtime gate) restEq nextScratch fits
                  restSafe
              exact first.append tail

private theorem gatesResult_scratch_lt
    {raw : RawCircuit} {source : List WorkSymbol}
    (gates : List PlannedGate) (runtime : Runtime)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (safe :
      ∀ gate, gate ∈ gates →
        PlannedGateSafe raw source runtime.registers
          runtime.captured gate) :
    (gatesResult runtime gates).scratch <
      TargetEmitterLedger.slotCapacity raw := by
  induction gates generalizing runtime with
  | nil =>
      exact scratchBound
  | cons gate rest inductionHypothesis =>
      have gateSafe := safe gate (List.Mem.head rest)
      have leftBound :=
        plannedSourceSafe_scratch gateSafe.left scratchBound
      have rightSafe :
          PlannedSourceSafe raw source
            (sourceResult runtime gate.left).registers
            (sourceResult runtime gate.left).captured gate.right := by
        simpa [sourceResult] using gateSafe.right
      have gateBound :
          (gateResult runtime gate).scratch <
            TargetEmitterLedger.slotCapacity raw := by
        simpa [gateResult] using
          plannedSourceSafe_scratch rightSafe leftBound
      have restSafe :
          ∀ next, next ∈ rest →
            PlannedGateSafe raw source
              (gateResult runtime gate).registers
              (gateResult runtime gate).captured next := by
        intro next member
        simpa [gateResult, sourceResult] using
          safe next (List.Mem.tail gate member)
      exact inductionHypothesis (gateResult runtime gate)
        gateBound restSafe

private theorem gatesResult_captured
    (runtime : Runtime) (gates : List PlannedGate) :
    (gatesResult runtime gates).captured = runtime.captured := by
  induction gates generalizing runtime with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      change
        (gatesResult (gateResult runtime gate) rest).captured =
          runtime.captured
      rw [inductionHypothesis]
      rfl

/-! ### Capacity-backed named coordinates -/

private theorem coordinate_carrierWidth
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch) :
    CoordinateSafe raw source registers captured carrierWidth := by
  exact .registers carrierWidth
    (by
      intro counter member
      have equal : counter = .carrierWidth := by
        simpa [carrierWidth, NatExpression.counter] using member
      subst counter
      simp)
    bounds.carrierWidth

private theorem coordinate_baselineOffset
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured offset : Nat}
    (block : BlockBounds raw registers)
    (offsetBound : offset ≤ 4) :
    CoordinateSafe raw source registers captured
      (NatExpression.addOffset baseline offset) := by
  refine .registers _ ?_ ?_
  · intro counter member
    have equal : counter = .baseline := by
      simpa [baseline, NatExpression.addOffset,
        NatExpression.counter] using member
    subst counter
    simp
  · rw [NatExpression.evaluate_addOffset]
    have header := block.headerGateCount
    simp [baseline, NatExpression.evaluate,
      NatExpression.counter,
      NatExpression.evaluateCounter]
    omega

private theorem coordinate_capturedIndex
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (ready : CapturedReady raw source captured) :
    CoordinateSafe raw source registers captured capturedIndex := by
  exact .captured capturedIndex [] rfl
    (by
      intro counter member
      simp at member)
    ready bounds.capturedIndex

private theorem coordinate_sourceLock
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch side : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (sideBound : side ≤ 1) :
    CoordinateSafe raw source registers captured
      (sourceLock side) := by
  exact .registers (sourceLock side)
    (by
      intro counter member
      simp [sourceLock, inputCount, normalizedGateCount,
        currentGate, NatExpression.addOffset,
        NatExpression.add, NatExpression.scale,
        NatExpression.counter] at member
      rcases member with rfl | rfl | rfl <;> simp)
    (bounds.sourceLock side sideBound)

private theorem coordinate_occurrence
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch side : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (sideBound : side ≤ 1) :
    CoordinateSafe raw source registers captured
      (occurrence side) := by
  exact .registers (occurrence side)
    (by
      intro counter member
      simp [occurrence, inputCount, normalizedGateCount,
        currentGate, NatExpression.addOffset,
        NatExpression.add, NatExpression.scale,
        NatExpression.counter] at member
      rcases member with rfl | rfl | rfl <;> simp)
    (bounds.occurrence side sideBound)

private theorem coordinate_traceLock
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch) :
    CoordinateSafe raw source registers captured traceLock := by
  exact .registers traceLock
    (by
      intro counter member
      simp [traceLock, inputCount, normalizedGateCount,
        currentGate, NatExpression.add,
        NatExpression.scale, NatExpression.counter] at member
      rcases member with rfl | rfl | rfl <;> simp)
    bounds.traceLock

private theorem coordinate_traceCoordinate
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch) :
    CoordinateSafe raw source registers captured traceCoordinate := by
  exact .registers traceCoordinate
    (by
      intro counter member
      simp [traceCoordinate, inputCount, currentGate,
        NatExpression.add, NatExpression.counter] at member
      rcases member with rfl | rfl <;> simp)
    bounds.traceCoordinate

private theorem coordinate_rawGateTrace
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (ready : CapturedReady raw source captured) :
    CoordinateSafe raw source registers captured rawGateTrace := by
  exact .captured rawGateTrace [.inputCount] rfl
    (by
      intro counter member
      simp at member
      subst counter
      simp)
    ready bounds.rawGateTrace

private theorem coordinate_finalLock
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch) :
    CoordinateSafe raw source registers captured finalLock := by
  exact .registers finalLock
    (by
      intro counter member
      simp [finalLock, inputCount, normalizedGateCount,
        NatExpression.add, NatExpression.scale,
        NatExpression.counter] at member
      rcases member with rfl | rfl <;> simp)
    bounds.finalLock

private theorem coordinate_localGate
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch offset : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (offsetBound : offset ≤ 18) :
    CoordinateSafe raw source registers captured
      (localGate offset) := by
  exact .registers (localGate offset)
    (by
      intro counter member
      have equal : counter = .outputIndex := by
        simpa [localGate, outputIndex,
          NatExpression.addOffset, NatExpression.counter] using member
      subst counter
      simp)
    (bounds.localGate offset offsetBound)

private theorem coordinate_checkAt
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch relative : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (relativeBound : relative ≤ 18) :
    CoordinateSafe raw source registers captured
      (checkAt relative) := by
  exact .registers (checkAt relative)
    (by
      intro counter member
      have equal : counter = .outputIndex := by
        simpa [checkAt, outputIndex,
          NatExpression.addOffset, NatExpression.counter] using member
      subst counter
      simp)
    (bounds.checkAt relative relativeBound)

private theorem plannedInput_sourceLock
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch side : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (sideBound : side ≤ 1) :
    PlannedSourceSafe raw source registers captured
      (.input (sourceLock side)) :=
  .input _ (coordinate_sourceLock bounds sideBound)

private theorem plannedInput_occurrence
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch side : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (sideBound : side ≤ 1) :
    PlannedSourceSafe raw source registers captured
      (.input (occurrence side)) :=
  .input _ (coordinate_occurrence bounds sideBound)

private theorem plannedInput_traceLock
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch) :
    PlannedSourceSafe raw source registers captured
      (.input traceLock) :=
  .input _ (coordinate_traceLock bounds)

private theorem plannedInput_traceCoordinate
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch) :
    PlannedSourceSafe raw source registers captured
      (.input traceCoordinate) :=
  .input _ (coordinate_traceCoordinate bounds)

private theorem plannedInput_capturedIndex
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (ready : CapturedReady raw source captured) :
    PlannedSourceSafe raw source registers captured
      (.input capturedIndex) :=
  .input _ (coordinate_capturedIndex bounds ready)

private theorem plannedInput_rawGateTrace
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (ready : CapturedReady raw source captured) :
    PlannedSourceSafe raw source registers captured
      (.input rawGateTrace) :=
  .input _ (coordinate_rawGateTrace bounds ready)

private theorem plannedInput_finalLock
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch) :
    PlannedSourceSafe raw source registers captured
      (.input finalLock) :=
  .input _ (coordinate_finalLock bounds)

private theorem plannedGate_local
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch offset : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (offsetBound : offset ≤ 18) :
    PlannedSourceSafe raw source registers captured
      (.gate (localGate offset)) :=
  .gate _ (coordinate_localGate bounds offsetBound)

private theorem inputSourcePlan_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch side : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (ready : CapturedReady raw source captured)
    (sideBound : side ≤ 1) :
    ∀ gate, gate ∈ sourcePlan .input side →
      PlannedGateSafe raw source registers captured gate := by
  intro gate member
  simp [sourcePlan, instantiateTemplate,
    instantiateTemplateAt, sourceBindings, sourceTemplate,
    equalityTemplate, TemplateGate.instantiateAt,
    TemplateSource.instantiateAt] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact
      { left := plannedInput_sourceLock bounds sideBound
        right := plannedInput_occurrence bounds sideBound }
  · exact
      { left := plannedInput_sourceLock bounds sideBound
        right := plannedInput_capturedIndex bounds ready }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_capturedIndex bounds ready }
  · exact
      { left := plannedInput_sourceLock bounds sideBound
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedInput_sourceLock bounds sideBound
        right := plannedInput_sourceLock bounds sideBound }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_occurrence bounds sideBound }

private theorem gateSourcePlan_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch side : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (ready : CapturedReady raw source captured)
    (sideBound : side ≤ 1) :
    ∀ gate, gate ∈ sourcePlan .gate side →
      PlannedGateSafe raw source registers captured gate := by
  intro gate member
  simp [sourcePlan, instantiateTemplate,
    instantiateTemplateAt, sourceBindings, sourceTemplate,
    equalityTemplate, TemplateGate.instantiateAt,
    TemplateSource.instantiateAt] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact
      { left := plannedInput_sourceLock bounds sideBound
        right := plannedInput_occurrence bounds sideBound }
  · exact
      { left := plannedInput_sourceLock bounds sideBound
        right := plannedInput_rawGateTrace bounds ready }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_rawGateTrace bounds ready }
  · exact
      { left := plannedInput_sourceLock bounds sideBound
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedInput_sourceLock bounds sideBound
        right := plannedInput_sourceLock bounds sideBound }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_occurrence bounds sideBound }

private theorem constantFalseSourcePlan_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch side : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (sideBound : side ≤ 1) :
    ∀ gate, gate ∈ sourcePlan .constantFalse side →
      PlannedGateSafe raw source registers captured gate := by
  intro gate member
  simp [sourcePlan, instantiateTemplate,
    instantiateTemplateAt, sourceBindings, sourceTemplate,
    constantZeroTemplate, TemplateGate.instantiateAt,
    TemplateSource.instantiateAt] at member
  rcases member with rfl | rfl | rfl
  · exact
      { left := plannedInput_sourceLock bounds sideBound
        right := plannedInput_occurrence bounds sideBound }
  · exact
      { left := plannedInput_sourceLock bounds sideBound
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }

private theorem constantTrueSourcePlan_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch side : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (sideBound : side ≤ 1) :
    ∀ gate, gate ∈ sourcePlan .constantTrue side →
      PlannedGateSafe raw source registers captured gate := by
  intro gate member
  simp [sourcePlan, instantiateTemplate,
    instantiateTemplateAt, sourceBindings, sourceTemplate,
    constantOneTemplate, TemplateGate.instantiateAt,
    TemplateSource.instantiateAt] at member
  rcases member with rfl | rfl
  · exact
      { left := plannedInput_sourceLock bounds sideBound
        right := plannedInput_occurrence bounds sideBound }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }

private theorem compileCheckPush_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {context : SourceContext source}
    (relative : Nat) (program : List Primitive)
    (runtime : Runtime)
    (compiled : compileCheckPush relative = some program)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (fits :
      TargetEmitterRuntimeProgram.LedgerFits
        (TargetEmitterLedger.slotCapacity raw) runtime.registers)
    (coordinate :
      CoordinateSafe raw source runtime.registers runtime.captured
        (checkAt relative)) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source context
      program runtime (checkPushResult runtime relative) := by
  unfold compileCheckPush at compiled
  cases coordinateEq : computeNatural (checkAt relative) with
  | none =>
      simp [coordinateEq] at compiled
  | some coordinateProgram =>
      have programEq :
          program = coordinateProgram ++ [.pushCheck] := by
        simpa [coordinateEq] using compiled.symm
      subst program
      let middle : Runtime :=
        { runtime with
          scratch := runtime.registers.outputIndex + relative }
      have naturalSafe :=
        computeNatural_safe (context := context)
          (checkAt relative) coordinateProgram runtime
          coordinateEq scratchBound fits coordinate
      have coordinateValue :
          naturalValue runtime (checkAt relative) =
            runtime.registers.outputIndex + relative := by
        simpa [naturalValue] using
          checkAt_evaluated runtime.registers
            runtime.captured 0 relative
      have valueBound :
          runtime.registers.outputIndex + relative ≤
            TargetEmitterLedger.slotCapacity raw := by
        cases coordinate with
        | registers registerTerms coordinateBound =>
            have :
                naturalValue runtime (checkAt relative) <
                  TargetEmitterLedger.slotCapacity raw := by
              simpa [naturalValue] using coordinateBound
            omega
        | captured rest termsEq registerTerms ready
            coordinateBound =>
            have :
                naturalValue runtime (checkAt relative) <
                  TargetEmitterLedger.slotCapacity raw := by
              simpa [naturalValue] using coordinateBound
            omega
      have pushSafe :
          ProgramSafe
            (TargetEmitterLedger.slotCapacity raw) source context
            [.pushCheck] middle
            (checkPushResult runtime relative) := by
        simpa [middle, checkPushResult] using
          (ProgramSafe.singleton
            (TargetEmitterRuntimeProgram.PrimitiveSafe.pushCheck
              middle fits valueBound))
      have naturalSafe' :
          ProgramSafe
            (TargetEmitterLedger.slotCapacity raw) source context
            coordinateProgram runtime middle := by
        simpa [middle, coordinateValue] using naturalSafe
      exact naturalSafe'.append pushSafe

private theorem compiledMacro_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (gates : List PlannedGate) (relative count : Nat)
    (gatesProgram checkProgram : List Primitive)
    (runtime : Runtime)
    (gatesCompiled :
      compileGates .marked gates = some gatesProgram)
    (checkCompiled :
      compileCheckPush relative = some checkProgram)
    (range : ControllerRange raw runtime.registers)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (bounds : PlanBounds raw runtime.registers
      runtime.captured runtime.scratch)
    (relativeBound : relative ≤ 18)
    (countBound : count ≤ 18)
    (gatesSafe :
      ∀ gate, gate ∈ gates →
        PlannedGateSafe raw source runtime.registers
          runtime.captured gate) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      (gatesProgram ++ checkProgram ++
        repeatPrimitive count
          (.incrementRegister .outputIndex) ++
        [.resetScratch])
      runtime (macroResult runtime gates relative count) := by
  let afterGates := gatesResult runtime gates
  let afterCheck := checkPushResult afterGates relative
  let afterIncrement := incrementOutputResult afterCheck count
  have fits := range.ledgerFits
  have gateRun :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        gatesProgram runtime afterGates := by
    exact
      compileGates_safe (context := workspace.context)
        (ModeReady.marked workspace.cursor) gates gatesProgram
        runtime gatesCompiled scratchBound fits gatesSafe
  have gatesScratch :
      afterGates.scratch <
        TargetEmitterLedger.slotCapacity raw := by
    exact gatesResult_scratch_lt gates runtime scratchBound gatesSafe
  have fitsAfterGates :
      TargetEmitterRuntimeProgram.LedgerFits
        (TargetEmitterLedger.slotCapacity raw)
        afterGates.registers := by
    simpa [afterGates, gatesResult_registers] using fits
  have checkCoordinate :
      CoordinateSafe raw source afterGates.registers
        afterGates.captured (checkAt relative) := by
    simpa [afterGates, gatesResult_registers,
      gatesResult_captured] using
      (coordinate_checkAt (source := source)
        bounds relativeBound)
  have checkRun :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        checkProgram afterGates afterCheck := by
    exact
      compileCheckPush_safe (context := workspace.context)
        relative checkProgram afterGates checkCompiled gatesScratch
        fitsAfterGates checkCoordinate
  have checkValueLt :
      runtime.registers.outputIndex + relative <
        TargetEmitterLedger.slotCapacity raw := by
    simpa [checkAt_evaluated] using
      bounds.checkAt relative relativeBound
  have fitsAfterCheck :
      TargetEmitterRuntimeProgram.LedgerFits
        (TargetEmitterLedger.slotCapacity raw)
        afterCheck.registers := by
    simpa [afterCheck, afterGates, checkPushResult,
      gatesResult_registers] using fits
  have incrementBound :
      afterCheck.registers.outputIndex + count <
        TargetEmitterLedger.slotCapacity raw := by
    have envelope :=
      range.outputIndex_add_eighteen_lt_slotCapacity
    simp [afterCheck, afterGates, checkPushResult,
      gatesResult_registers]
    omega
  have incrementRun :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        (repeatPrimitive count
          (.incrementRegister .outputIndex))
        afterCheck afterIncrement := by
    exact
      repeatIncrementOutputIndex_safe
        (source := source) (context := workspace.context)
        count afterCheck fitsAfterCheck incrementBound
  have resetBound :
      afterIncrement.scratch <
        TargetEmitterLedger.slotCapacity raw := by
    simpa [afterIncrement, afterCheck, afterGates,
      incrementOutputResult, checkPushResult,
      gatesResult_registers] using checkValueLt
  have resetRun :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.resetScratch] afterIncrement
        (macroResult runtime gates relative count) := by
    simpa [macroResult, resetScratchResult, afterIncrement,
      afterCheck, afterGates] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.resetScratch
          afterIncrement resetBound))
  simpa only [List.append_assoc] using
    gateRun.append
      (checkRun.append (incrementRun.append resetRun))

private theorem sourceProgram_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime} {kind : SourceKind} {side : Nat}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (gatesSafe :
      ∀ gate, gate ∈ sourcePlan kind side →
        PlannedGateSafe raw source runtime.registers
          runtime.captured gate)
    (program : List Primitive)
    (compiled : sourceProgram kind side = some program) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      program runtime
      (macroResult runtime (sourcePlan kind side)
        (sourceCheckRelative kind) (sourceGateCount kind)) := by
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
          exact
            compiledMacro_safe workspace (sourcePlan kind side)
              (sourceCheckRelative kind) (sourceGateCount kind)
              gatesProgram checkProgram runtime gatesEq checkEq
              range scratchBound
              (TargetEmitterCapacity.planBounds
                range capturedBound scratchBound)
              (by cases kind <;> decide) (by cases kind <;> decide)
              gatesSafe

/-- The fixed input-source macro is capacity-safe for either literal side. -/
theorem sourceInput_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime} {side : Nat}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (captured : CapturedReady raw source runtime.captured)
    (sideBound : side ≤ 1) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      (TargetEmitterController.Plan.source .input side) runtime
      (macroResult runtime (sourcePlan .input side)
        (sourceCheckRelative .input) (sourceGateCount .input)) := by
  rcases sourceProgram_closed .input side with ⟨program, compiled⟩
  have safe :=
    sourceProgram_safe workspace range capturedBound scratchBound
      (inputSourcePlan_safe
        (TargetEmitterCapacity.planBounds
          range capturedBound scratchBound)
        captured sideBound)
      program compiled
  simpa [TargetEmitterController.Plan.source,
    TargetEmitterController.Plan.optionProgram, compiled] using safe

/-- The fixed gate-source macro is capacity-safe for either literal side. -/
theorem sourceGate_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime} {side : Nat}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (captured : CapturedReady raw source runtime.captured)
    (sideBound : side ≤ 1) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      (TargetEmitterController.Plan.source .gate side) runtime
      (macroResult runtime (sourcePlan .gate side)
        (sourceCheckRelative .gate) (sourceGateCount .gate)) := by
  rcases sourceProgram_closed .gate side with ⟨program, compiled⟩
  have safe :=
    sourceProgram_safe workspace range capturedBound scratchBound
      (gateSourcePlan_safe
        (TargetEmitterCapacity.planBounds
          range capturedBound scratchBound)
        captured sideBound)
      program compiled
  simpa [TargetEmitterController.Plan.source,
    TargetEmitterController.Plan.optionProgram, compiled] using safe

/-- The fixed false-constant source macro is capacity-safe for either side. -/
theorem sourceConstantFalse_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime} {side : Nat}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (sideBound : side ≤ 1) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      (TargetEmitterController.Plan.source .constantFalse side) runtime
      (macroResult runtime (sourcePlan .constantFalse side)
        (sourceCheckRelative .constantFalse)
        (sourceGateCount .constantFalse)) := by
  rcases sourceProgram_closed .constantFalse side with
    ⟨program, compiled⟩
  have safe :=
    sourceProgram_safe workspace range capturedBound scratchBound
      (constantFalseSourcePlan_safe
        (TargetEmitterCapacity.planBounds
          range capturedBound scratchBound)
        sideBound)
      program compiled
  simpa [TargetEmitterController.Plan.source,
    TargetEmitterController.Plan.optionProgram, compiled] using safe

/-- The fixed true-constant source macro is capacity-safe for either side. -/
theorem sourceConstantTrue_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime} {side : Nat}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (sideBound : side ≤ 1) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      (TargetEmitterController.Plan.source .constantTrue side) runtime
      (macroResult runtime (sourcePlan .constantTrue side)
        (sourceCheckRelative .constantTrue)
        (sourceGateCount .constantTrue)) := by
  rcases sourceProgram_closed .constantTrue side with
    ⟨program, compiled⟩
  have safe :=
    sourceProgram_safe workspace range capturedBound scratchBound
      (constantTrueSourcePlan_safe
        (TargetEmitterCapacity.planBounds
          range capturedBound scratchBound)
        sideBound)
      program compiled
  simpa [TargetEmitterController.Plan.source,
    TargetEmitterController.Plan.optionProgram, compiled] using safe

private theorem tracePlan_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch) :
    ∀ gate, gate ∈ tracePlan →
      PlannedGateSafe raw source registers captured gate := by
  intro gate member
  simp [tracePlan, instantiateTemplate,
    instantiateTemplateAt, traceBindings, traceTemplate,
    TemplateGate.instantiateAt,
    TemplateSource.instantiateAt] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact
      { left := plannedInput_traceLock bounds
        right := plannedInput_traceCoordinate bounds }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedInput_traceLock bounds
        right := plannedInput_occurrence bounds (by omega) }
  · exact
      { left := plannedInput_traceLock bounds
        right := plannedInput_occurrence bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_occurrence bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedInput_traceLock bounds
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_occurrence bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_occurrence bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedInput_traceLock bounds
        right := plannedInput_traceLock bounds }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_traceCoordinate bounds }

/-- The fixed eighteen-gate trace macro is capacity-safe. -/
theorem trace_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      TargetEmitterController.Plan.trace runtime
      (macroResult runtime tracePlan
        traceCheckRelative traceGateCount) := by
  rcases traceProgram_closed with ⟨program, compiled⟩
  have closed := compiled
  unfold traceProgram at compiled
  cases gatesEq : compileGates .marked tracePlan with
  | none =>
      simp [gatesEq] at compiled
  | some gatesProgram =>
      cases checkEq : compileCheckPush traceCheckRelative with
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
          have safe :=
            compiledMacro_safe workspace tracePlan
              traceCheckRelative traceGateCount
              gatesProgram checkProgram runtime gatesEq checkEq
              range scratchBound
              (TargetEmitterCapacity.planBounds
                range capturedBound scratchBound)
              (by decide) (by decide)
              (tracePlan_safe
                (TargetEmitterCapacity.planBounds
                  range capturedBound scratchBound))
          simpa [TargetEmitterController.Plan.trace,
            TargetEmitterController.Plan.optionProgram, closed] using safe

private theorem macroResult_ledgerFits
    {raw : RawCircuit} {runtime : Runtime}
    (range : ControllerRange raw runtime.registers)
    (gates : List PlannedGate) (relative count : Nat)
    (countBound : count ≤ 18) :
    TargetEmitterRuntimeProgram.LedgerFits
      (TargetEmitterLedger.slotCapacity raw)
      (macroResult runtime gates relative count).registers := by
  have fits := range.ledgerFits
  have outputBound :=
    range.outputIndex_add_eighteen_lt_slotCapacity
  refine
    { inputCount := ?_
      normalizedGateCount := ?_
      carrierWidth := ?_
      baseline := ?_
      currentGate := ?_
      outputIndex := ?_ }
  · simpa [macroResult, resetScratchResult,
      incrementOutputResult, checkPushResult,
      gatesResult_registers] using fits.inputCount
  · simpa [macroResult, resetScratchResult,
      incrementOutputResult, checkPushResult,
      gatesResult_registers] using fits.normalizedGateCount
  · simpa [macroResult, resetScratchResult,
      incrementOutputResult, checkPushResult,
      gatesResult_registers] using fits.carrierWidth
  · simpa [macroResult, resetScratchResult,
      incrementOutputResult, checkPushResult,
      gatesResult_registers] using fits.baseline
  · simpa [macroResult, resetScratchResult,
      incrementOutputResult, checkPushResult,
      gatesResult_registers] using fits.currentGate
  · simp [macroResult, resetScratchResult,
      incrementOutputResult, checkPushResult,
      gatesResult_registers]
    omega

/-- Runtime endpoint of the trace block followed by the controller's
current-gate advance. -/
def rightTraceResult (runtime : Runtime) : Runtime :=
  let traced :=
    macroResult runtime tracePlan
      traceCheckRelative traceGateCount
  { traced with
    registers :=
      TargetEmitterRuntimePrimitives.incrementRegisters
        .currentGate traced.registers }

/-- The controller's right-source trace block, including its final
current-gate advance, is capacity-safe. -/
theorem rightTrace_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (nextGate :
      runtime.registers.currentGate + 1 ≤
        TargetEmitterLedger.normalizedGateCount raw) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      TargetEmitterController.Plan.rightTrace runtime
      (rightTraceResult runtime) := by
  let traced :=
    macroResult runtime tracePlan
      traceCheckRelative traceGateCount
  have traceRun :=
    trace_safe workspace range capturedBound scratchBound
  have tracedFits :
      TargetEmitterRuntimeProgram.LedgerFits
        (TargetEmitterLedger.slotCapacity raw)
        traced.registers := by
    simpa [traced] using
      (macroResult_ledgerFits range tracePlan
        traceCheckRelative traceGateCount (by decide))
  have currentAvailable :
      traced.registers.currentGate <
        TargetEmitterLedger.slotCapacity raw := by
    have advancedRange :=
      range.incrementCurrentGate nextGate
    have available := advancedRange.ledgerFits.currentGate
    simp [traced, macroResult, resetScratchResult,
      incrementOutputResult, checkPushResult,
      gatesResult_registers,
      TargetEmitterRuntimePrimitives.incrementRegisters] at available ⊢
    omega
  have advanceRun :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.incrementRegister .currentGate] traced
        (rightTraceResult runtime) := by
    simpa [rightTraceResult, traced] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.incrementRegister
          traced .currentGate .currentGate rfl
          tracedFits currentAvailable))
  simpa [TargetEmitterController.Plan.rightTrace, traced] using
    traceRun.append advanceRun

private theorem plannedInput_sourceLockAt
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch gateBias side : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (gateBiasBound : gateBias ≤ 1)
    (sideBound : side ≤ 1) :
    PlannedSourceSafe raw source registers captured
      (.input (sourceLockAt gateBias side)) := by
  refine .input _ (.registers _ ?_ ?_)
  · intro counter member
    simp [sourceLockAt, sourceLock, inputCount,
      normalizedGateCount, currentGate,
      NatExpression.addOffset, NatExpression.add,
      NatExpression.scale, NatExpression.counter] at member
    rcases member with rfl | rfl | rfl <;> simp
  · exact bounds.sourceLockAt gateBias side
      gateBiasBound sideBound

private theorem plannedInput_occurrenceAt
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch gateBias side : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (gateBiasBound : gateBias ≤ 1)
    (sideBound : side ≤ 1) :
    PlannedSourceSafe raw source registers captured
      (.input (occurrenceAt gateBias side)) := by
  refine .input _ (.registers _ ?_ ?_)
  · intro counter member
    simp [occurrenceAt, occurrence, inputCount,
      normalizedGateCount, currentGate,
      NatExpression.addOffset, NatExpression.add,
      NatExpression.scale, NatExpression.counter] at member
    rcases member with rfl | rfl | rfl <;> simp
  · exact bounds.occurrenceAt gateBias side
      gateBiasBound sideBound

private theorem plannedInput_traceLockAt
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch gateBias : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (gateBiasBound : gateBias ≤ 1) :
    PlannedSourceSafe raw source registers captured
      (.input (traceLockAt gateBias)) := by
  refine .input _ (.registers _ ?_ ?_)
  · intro counter member
    simp [traceLockAt, traceLock, inputCount,
      normalizedGateCount, currentGate,
      NatExpression.addOffset, NatExpression.add,
      NatExpression.scale, NatExpression.counter] at member
    rcases member with rfl | rfl | rfl <;> simp
  · exact bounds.traceLockAt gateBias gateBiasBound

private theorem plannedInput_traceCoordinateAt
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch gateBias : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (gateBiasBound : gateBias ≤ 1) :
    PlannedSourceSafe raw source registers captured
      (.input (traceCoordinateAt gateBias)) := by
  refine .input _ (.registers _ ?_ ?_)
  · intro counter member
    simp [traceCoordinateAt, traceCoordinate, inputCount,
      currentGate, NatExpression.addOffset,
      NatExpression.add, NatExpression.counter] at member
    rcases member with rfl | rfl <;> simp
  · exact bounds.traceCoordinateAt gateBias gateBiasBound

private theorem syntheticGatePlan_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch gateBias sourceGateBias side : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (gateBiasBound : gateBias ≤ 1)
    (sourceGateBiasBound : sourceGateBias ≤ 1)
    (sideBound : side ≤ 1) :
    ∀ gate,
      gate ∈ syntheticGatePlan gateBias sourceGateBias side →
        PlannedGateSafe raw source registers captured gate := by
  intro gate member
  simp [syntheticGatePlan, syntheticGateBindings,
    equalityTemplate, instantiateTemplate,
    instantiateTemplateAt, TemplateGate.instantiateAt,
    TemplateSource.instantiateAt] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact
      { left := plannedInput_sourceLockAt bounds
          gateBiasBound sideBound
        right := plannedInput_occurrenceAt bounds
          gateBiasBound sideBound }
  · exact
      { left := plannedInput_sourceLockAt bounds
          gateBiasBound sideBound
        right := plannedInput_traceCoordinateAt bounds
          sourceGateBiasBound }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_traceCoordinateAt bounds
          sourceGateBiasBound }
  · exact
      { left := plannedInput_sourceLockAt bounds
          gateBiasBound sideBound
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedInput_sourceLockAt bounds
          gateBiasBound sideBound
        right := plannedInput_sourceLockAt bounds
          gateBiasBound sideBound }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_occurrenceAt bounds
          gateBiasBound sideBound }

private theorem tracePlanAt_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch gateBias : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (gateBiasBound : gateBias ≤ 1) :
    ∀ gate, gate ∈ tracePlanAt gateBias →
      PlannedGateSafe raw source registers captured gate := by
  intro gate member
  simp [tracePlanAt, traceBindingsAt, traceTemplate,
    instantiateTemplate, instantiateTemplateAt,
    TemplateGate.instantiateAt,
    TemplateSource.instantiateAt] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact
      { left := plannedInput_traceLockAt bounds gateBiasBound
        right := plannedInput_traceCoordinateAt bounds
          gateBiasBound }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedInput_traceLockAt bounds gateBiasBound
        right := plannedInput_occurrenceAt bounds
          gateBiasBound (by omega) }
  · exact
      { left := plannedInput_traceLockAt bounds gateBiasBound
        right := plannedInput_occurrenceAt bounds
          gateBiasBound (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_occurrenceAt bounds
          gateBiasBound (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedInput_traceLockAt bounds gateBiasBound
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_occurrenceAt bounds
          gateBiasBound (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_occurrenceAt bounds
          gateBiasBound (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedInput_traceLockAt bounds gateBiasBound
        right := plannedInput_traceLockAt bounds gateBiasBound }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedInput_traceCoordinateAt bounds
          gateBiasBound }

private theorem syntheticGateSourceProgram_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (gateBias sourceGateBias side : Nat)
    (gateBiasBound : gateBias ≤ 1)
    (sourceGateBiasBound : sourceGateBias ≤ 1)
    (sideBound : side ≤ 1)
    (program : List Primitive)
    (compiled :
      syntheticGateSourceProgram gateBias sourceGateBias side =
        some program) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      program runtime
      (macroResult runtime
        (syntheticGatePlan gateBias sourceGateBias side)
        (sourceCheckRelative .gate)
        (sourceGateCount .gate)) := by
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
          let bounds :=
            TargetEmitterCapacity.planBounds
              range capturedBound scratchBound
          exact
            compiledMacro_safe workspace
              (syntheticGatePlan gateBias sourceGateBias side)
              (sourceCheckRelative .gate)
              (sourceGateCount .gate)
              gatesProgram checkProgram runtime gatesEq checkEq
              range scratchBound bounds (by decide) (by decide)
              (syntheticGatePlan_safe bounds gateBiasBound
                sourceGateBiasBound sideBound)

private theorem traceProgramAt_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (gateBias : Nat) (gateBiasBound : gateBias ≤ 1)
    (program : List Primitive)
    (compiled : traceProgramAt gateBias = some program) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      program runtime
      (macroResult runtime (tracePlanAt gateBias)
        traceCheckRelative traceGateCount) := by
  unfold traceProgramAt at compiled
  cases gatesEq :
      compileGates .marked (tracePlanAt gateBias) with
  | none =>
      simp [gatesEq] at compiled
  | some gatesProgram =>
      cases checkEq : compileCheckPush traceCheckRelative with
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
          let bounds :=
            TargetEmitterCapacity.planBounds
              range capturedBound scratchBound
          exact
            compiledMacro_safe workspace
              (tracePlanAt gateBias)
              traceCheckRelative traceGateCount
              gatesProgram checkProgram runtime gatesEq checkEq
              range scratchBound bounds (by decide) (by decide)
              (tracePlanAt_safe bounds gateBiasBound)

/-! ### Normalization composites -/

/-- Controller ranges at the six closed macro boundaries of input
normalization.  They are stated explicitly because the composite advances
`outputIndex` by sixty-eight; an initial upper bound alone cannot justify
every later unary-register increment. -/
structure InputNormalizationRanges
    (raw : RawCircuit) (runtime : Runtime) : Prop where
  initial :
    ControllerRange raw runtime.registers
  afterFirstLeft :
    ControllerRange raw
      (macroResult runtime
        (sourcePlan .input 0)
        (sourceCheckRelative .input)
        (sourceGateCount .input)).registers
  afterFirstRight :
    ControllerRange raw
      (macroResult
        (macroResult runtime
          (sourcePlan .input 0)
          (sourceCheckRelative .input)
          (sourceGateCount .input))
        (sourcePlan .constantTrue 1)
        (sourceCheckRelative .constantTrue)
        (sourceGateCount .constantTrue)).registers
  afterFirstTrace :
    ControllerRange raw
      (macroResult
        (macroResult
          (macroResult runtime
            (sourcePlan .input 0)
            (sourceCheckRelative .input)
            (sourceGateCount .input))
          (sourcePlan .constantTrue 1)
          (sourceCheckRelative .constantTrue)
          (sourceGateCount .constantTrue))
        tracePlan traceCheckRelative traceGateCount).registers
  afterSecondLeft :
    ControllerRange raw
      (macroResult
        (macroResult
          (macroResult
            (macroResult runtime
              (sourcePlan .input 0)
              (sourceCheckRelative .input)
              (sourceGateCount .input))
            (sourcePlan .constantTrue 1)
            (sourceCheckRelative .constantTrue)
            (sourceGateCount .constantTrue))
          tracePlan traceCheckRelative traceGateCount)
        (syntheticGatePlan 1 0 0)
        (sourceCheckRelative .gate)
        (sourceGateCount .gate)).registers
  afterSecondRight :
    ControllerRange raw
      (macroResult
        (macroResult
          (macroResult
            (macroResult
              (macroResult runtime
                (sourcePlan .input 0)
                (sourceCheckRelative .input)
                (sourceGateCount .input))
              (sourcePlan .constantTrue 1)
              (sourceCheckRelative .constantTrue)
              (sourceGateCount .constantTrue))
            tracePlan traceCheckRelative traceGateCount)
          (syntheticGatePlan 1 0 0)
          (sourceCheckRelative .gate)
          (sourceGateCount .gate))
        (syntheticGatePlan 1 0 1)
        (sourceCheckRelative .gate)
        (sourceGateCount .gate)).registers
  afterSecondTrace :
    ControllerRange raw
      (macroResult
        (macroResult
          (macroResult
            (macroResult
              (macroResult
                (macroResult runtime
                  (sourcePlan .input 0)
                  (sourceCheckRelative .input)
                  (sourceGateCount .input))
                (sourcePlan .constantTrue 1)
                (sourceCheckRelative .constantTrue)
                (sourceGateCount .constantTrue))
              tracePlan traceCheckRelative traceGateCount)
            (syntheticGatePlan 1 0 0)
            (sourceCheckRelative .gate)
            (sourceGateCount .gate))
          (syntheticGatePlan 1 0 1)
          (sourceCheckRelative .gate)
          (sourceGateCount .gate))
        (tracePlanAt 1)
        traceCheckRelative traceGateCount).registers
  nextGate :
    (macroResult
      (macroResult
        (macroResult
          (macroResult
            (macroResult
              (macroResult runtime
                (sourcePlan .input 0)
                (sourceCheckRelative .input)
                (sourceGateCount .input))
              (sourcePlan .constantTrue 1)
              (sourceCheckRelative .constantTrue)
              (sourceGateCount .constantTrue))
            tracePlan traceCheckRelative traceGateCount)
          (syntheticGatePlan 1 0 0)
          (sourceCheckRelative .gate)
          (sourceGateCount .gate))
        (syntheticGatePlan 1 0 1)
        (sourceCheckRelative .gate)
        (sourceGateCount .gate))
      (tracePlanAt 1)
      traceCheckRelative traceGateCount).registers.currentGate + 1 ≤
        TargetEmitterLedger.normalizedGateCount raw

/-- Controller ranges at the three macro boundaries of constant
normalization. -/
structure ConstantNormalizationRanges
    (raw : RawCircuit) (value : Bool) (runtime : Runtime) : Prop where
  initial :
    ControllerRange raw runtime.registers
  afterLeft :
    ControllerRange raw
      (macroResult runtime
        (sourcePlan (constantNormalizationKind value) 0)
        (sourceCheckRelative
          (constantNormalizationKind value))
        (sourceGateCount
          (constantNormalizationKind value))).registers
  afterRight :
    ControllerRange raw
      (macroResult
        (macroResult runtime
          (sourcePlan (constantNormalizationKind value) 0)
          (sourceCheckRelative
            (constantNormalizationKind value))
          (sourceGateCount
            (constantNormalizationKind value)))
        (sourcePlan (constantNormalizationKind value) 1)
        (sourceCheckRelative
          (constantNormalizationKind value))
        (sourceGateCount
          (constantNormalizationKind value))).registers

private theorem macroResult_captured
    (runtime : Runtime) (gates : List PlannedGate)
    (relative count : Nat) :
    (macroResult runtime gates relative count).captured =
      runtime.captured := by
  simp [macroResult, resetScratchResult,
    incrementOutputResult, checkPushResult,
    gatesResult_captured]

private def CapturedReady.afterMacro
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (ready : CapturedReady raw source runtime.captured)
    (gates : List PlannedGate) (relative count : Nat) :
    CapturedReady raw source
      (macroResult runtime gates relative count).captured := by
  simpa [macroResult_captured] using ready

private theorem macroResult_scratch_lt
    (raw : RawCircuit) (runtime : Runtime)
    (gates : List PlannedGate) (relative count : Nat) :
    (macroResult runtime gates relative count).scratch <
      TargetEmitterLedger.slotCapacity raw := by
  simp [macroResult_scratch,
    TargetEmitterLedger.slotCapacity]

private theorem macroResult_capturedBound
    {raw : RawCircuit} (runtime : Runtime)
    (gates : List PlannedGate) (relative count : Nat)
    (bound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length) :
    (macroResult runtime gates relative count).captured + 1 ≤
      (SourceParser.circuitCells raw).length := by
  simpa [macroResult_captured] using bound

/-- The complete six-macro input-normalization program is capacity-safe when
the caller supplies the controller range at each literal macro boundary. -/
theorem inputNormalization_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (workspace : MarkedWorkspace source)
    (ranges : InputNormalizationRanges raw runtime)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (captured : CapturedReady raw source runtime.captured) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      TargetEmitterController.Plan.inputNormalization runtime
      (inputNormalizationResult runtime) := by
  rcases sourceProgram_closed .input 0 with
    ⟨firstLeftProgram, firstLeftEq⟩
  rcases sourceProgram_closed .constantTrue 1 with
    ⟨firstRightProgram, firstRightEq⟩
  rcases traceProgram_closed with
    ⟨firstTraceProgram, firstTraceEq⟩
  rcases syntheticGateSourceProgram_closed 1 0 0 with
    ⟨secondLeftProgram, secondLeftEq⟩
  rcases syntheticGateSourceProgram_closed 1 0 1 with
    ⟨secondRightProgram, secondRightEq⟩
  rcases traceProgramAt_closed 1 with
    ⟨secondTraceProgram, secondTraceEq⟩
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
    macroResult afterSecondRight (tracePlanAt 1)
      traceCheckRelative traceGateCount
  have firstLeftRange :
      ControllerRange raw afterFirstLeft.registers := by
    simpa [afterFirstLeft] using ranges.afterFirstLeft
  have firstRightRange :
      ControllerRange raw afterFirstRight.registers := by
    simpa [afterFirstRight, afterFirstLeft] using
      ranges.afterFirstRight
  have firstTraceRange :
      ControllerRange raw afterFirstTrace.registers := by
    simpa [afterFirstTrace, afterFirstRight,
      afterFirstLeft] using ranges.afterFirstTrace
  have secondLeftRange :
      ControllerRange raw afterSecondLeft.registers := by
    simpa [afterSecondLeft, afterFirstTrace,
      afterFirstRight, afterFirstLeft] using
      ranges.afterSecondLeft
  have secondRightRange :
      ControllerRange raw afterSecondRight.registers := by
    simpa [afterSecondRight, afterSecondLeft,
      afterFirstTrace, afterFirstRight, afterFirstLeft] using
      ranges.afterSecondRight
  have secondTraceRange :
      ControllerRange raw afterSecondTrace.registers := by
    simpa [afterSecondTrace, afterSecondRight,
      afterSecondLeft, afterFirstTrace,
      afterFirstRight, afterFirstLeft] using
      ranges.afterSecondTrace
  have capturedFirstLeft :
      afterFirstLeft.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    exact macroResult_capturedBound runtime
      (sourcePlan .input 0)
      (sourceCheckRelative .input)
      (sourceGateCount .input) capturedBound
  have capturedFirstRight :
      afterFirstRight.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    exact macroResult_capturedBound afterFirstLeft
      (sourcePlan .constantTrue 1)
      (sourceCheckRelative .constantTrue)
      (sourceGateCount .constantTrue) capturedFirstLeft
  have capturedFirstTrace :
      afterFirstTrace.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    exact macroResult_capturedBound afterFirstRight
      tracePlan traceCheckRelative traceGateCount
      capturedFirstRight
  have capturedSecondLeft :
      afterSecondLeft.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    exact macroResult_capturedBound afterFirstTrace
      (syntheticGatePlan 1 0 0)
      (sourceCheckRelative .gate)
      (sourceGateCount .gate) capturedFirstTrace
  have capturedSecondRight :
      afterSecondRight.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    exact macroResult_capturedBound afterSecondLeft
      (syntheticGatePlan 1 0 1)
      (sourceCheckRelative .gate)
      (sourceGateCount .gate) capturedSecondLeft
  have firstLeftSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        firstLeftProgram runtime afterFirstLeft := by
    simpa [afterFirstLeft] using
      (sourceProgram_safe workspace ranges.initial
        capturedBound scratchBound
        (inputSourcePlan_safe
          (TargetEmitterCapacity.planBounds
            ranges.initial capturedBound scratchBound)
          captured (by omega))
        firstLeftProgram firstLeftEq)
  have firstRightScratch :
      afterFirstLeft.scratch <
        TargetEmitterLedger.slotCapacity raw :=
    macroResult_scratch_lt raw runtime
      (sourcePlan .input 0)
      (sourceCheckRelative .input)
      (sourceGateCount .input)
  have firstRightSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        firstRightProgram afterFirstLeft afterFirstRight := by
    simpa [afterFirstRight] using
      (sourceProgram_safe workspace firstLeftRange
        capturedFirstLeft firstRightScratch
        (constantTrueSourcePlan_safe
          (TargetEmitterCapacity.planBounds firstLeftRange
            capturedFirstLeft firstRightScratch)
          (by omega))
        firstRightProgram firstRightEq)
  have firstTraceScratch :
      afterFirstRight.scratch <
        TargetEmitterLedger.slotCapacity raw :=
    macroResult_scratch_lt raw afterFirstLeft
      (sourcePlan .constantTrue 1)
      (sourceCheckRelative .constantTrue)
      (sourceGateCount .constantTrue)
  have firstTraceSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        firstTraceProgram afterFirstRight afterFirstTrace := by
    have safe :=
      trace_safe workspace firstRightRange
        capturedFirstRight firstTraceScratch
    simpa [TargetEmitterController.Plan.trace,
      TargetEmitterController.Plan.optionProgram,
      firstTraceEq, afterFirstTrace] using safe
  have secondLeftScratch :
      afterFirstTrace.scratch <
        TargetEmitterLedger.slotCapacity raw :=
    macroResult_scratch_lt raw afterFirstRight
      tracePlan traceCheckRelative traceGateCount
  have secondLeftSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        secondLeftProgram afterFirstTrace afterSecondLeft := by
    simpa [afterSecondLeft] using
      (syntheticGateSourceProgram_safe workspace
        firstTraceRange capturedFirstTrace secondLeftScratch
        1 0 0 (by omega) (by omega) (by omega)
        secondLeftProgram secondLeftEq)
  have secondRightScratch :
      afterSecondLeft.scratch <
        TargetEmitterLedger.slotCapacity raw :=
    macroResult_scratch_lt raw afterFirstTrace
      (syntheticGatePlan 1 0 0)
      (sourceCheckRelative .gate)
      (sourceGateCount .gate)
  have secondRightSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        secondRightProgram afterSecondLeft afterSecondRight := by
    simpa [afterSecondRight] using
      (syntheticGateSourceProgram_safe workspace
        secondLeftRange capturedSecondLeft secondRightScratch
        1 0 1 (by omega) (by omega) (by omega)
        secondRightProgram secondRightEq)
  have secondTraceScratch :
      afterSecondRight.scratch <
        TargetEmitterLedger.slotCapacity raw :=
    macroResult_scratch_lt raw afterSecondLeft
      (syntheticGatePlan 1 0 1)
      (sourceCheckRelative .gate)
      (sourceGateCount .gate)
  have secondTraceSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        secondTraceProgram afterSecondRight afterSecondTrace := by
    simpa [afterSecondTrace] using
      (traceProgramAt_safe workspace secondRightRange
        capturedSecondRight secondTraceScratch
        1 (by omega) secondTraceProgram secondTraceEq)
  have currentAvailable :
      afterSecondTrace.registers.currentGate <
        TargetEmitterLedger.slotCapacity raw :=
    secondTraceRange.currentGate_lt_slotCapacity
  have advanceSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.incrementRegister .currentGate] afterSecondTrace
        (inputNormalizationResult runtime) := by
    have nextGate :
        afterSecondTrace.registers.currentGate + 1 ≤
          TargetEmitterLedger.normalizedGateCount raw := by
      simpa [afterSecondTrace, afterSecondRight,
        afterSecondLeft, afterFirstTrace,
        afterFirstRight, afterFirstLeft] using ranges.nextGate
    have _advancedRange :=
      secondTraceRange.incrementCurrentGate nextGate
    simpa [inputNormalizationResult, afterFirstLeft,
      afterFirstRight, afterFirstTrace, afterSecondLeft,
      afterSecondRight, afterSecondTrace,
      incrementCurrentGateResult,
      TargetEmitterRuntimePrimitives.incrementRegisters] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.incrementRegister
          afterSecondTrace .currentGate .currentGate rfl
          secondTraceRange.ledgerFits currentAvailable))
  have allSafe :=
    firstLeftSafe.append
      (firstRightSafe.append
        (firstTraceSafe.append
          (secondLeftSafe.append
            (secondRightSafe.append
              (secondTraceSafe.append advanceSafe)))))
  simpa [TargetEmitterController.Plan.inputNormalization,
    TargetEmitterController.Plan.optionProgram,
    inputNormalizationProgram, firstLeftEq, firstRightEq,
    firstTraceEq, secondLeftEq, secondRightEq,
    secondTraceEq, List.append_assoc] using allSafe

private theorem constantNormalizationSourcePlan_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch side : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (value : Bool) (sideBound : side ≤ 1) :
    ∀ gate,
      gate ∈ sourcePlan (constantNormalizationKind value) side →
        PlannedGateSafe raw source registers captured gate := by
  cases value with
  | false =>
      exact constantTrueSourcePlan_safe bounds sideBound
  | true =>
      exact constantFalseSourcePlan_safe bounds sideBound

/-- Either closed constant-normalization program is capacity-safe when its
three literal macro-boundary ranges hold. -/
theorem constantNormalization_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime} (value : Bool)
    (workspace : MarkedWorkspace source)
    (ranges : ConstantNormalizationRanges raw value runtime)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      (TargetEmitterController.Plan.constantNormalization value)
      runtime (constantNormalizationResult value runtime) := by
  let kind := constantNormalizationKind value
  rcases sourceProgram_closed kind 0 with
    ⟨leftProgram, leftEq⟩
  rcases sourceProgram_closed kind 1 with
    ⟨rightProgram, rightEq⟩
  rcases traceProgram_closed with
    ⟨traceProgram, traceEq⟩
  let afterLeft :=
    macroResult runtime (sourcePlan kind 0)
      (sourceCheckRelative kind) (sourceGateCount kind)
  let afterRight :=
    macroResult afterLeft (sourcePlan kind 1)
      (sourceCheckRelative kind) (sourceGateCount kind)
  let afterTrace :=
    macroResult afterRight tracePlan
      traceCheckRelative traceGateCount
  have leftRange :
      ControllerRange raw afterLeft.registers := by
    simpa [afterLeft, kind] using ranges.afterLeft
  have rightRange :
      ControllerRange raw afterRight.registers := by
    simpa [afterRight, afterLeft, kind] using ranges.afterRight
  have capturedLeft :
      afterLeft.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    exact macroResult_capturedBound runtime
      (sourcePlan kind 0)
      (sourceCheckRelative kind)
      (sourceGateCount kind) capturedBound
  have capturedRight :
      afterRight.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    exact macroResult_capturedBound afterLeft
      (sourcePlan kind 1)
      (sourceCheckRelative kind)
      (sourceGateCount kind) capturedLeft
  have leftSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        leftProgram runtime afterLeft := by
    simpa [afterLeft] using
      (sourceProgram_safe workspace ranges.initial
        capturedBound scratchBound
        (constantNormalizationSourcePlan_safe
          (TargetEmitterCapacity.planBounds
            ranges.initial capturedBound scratchBound)
          value (by omega))
        leftProgram (by simpa [kind] using leftEq))
  have rightScratch :
      afterLeft.scratch <
        TargetEmitterLedger.slotCapacity raw :=
    macroResult_scratch_lt raw runtime
      (sourcePlan kind 0)
      (sourceCheckRelative kind) (sourceGateCount kind)
  have rightSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        rightProgram afterLeft afterRight := by
    simpa [afterRight] using
      (sourceProgram_safe workspace leftRange
        capturedLeft rightScratch
        (constantNormalizationSourcePlan_safe
          (TargetEmitterCapacity.planBounds
            leftRange capturedLeft rightScratch)
          value (by omega))
        rightProgram (by simpa [kind] using rightEq))
  have traceScratch :
      afterRight.scratch <
        TargetEmitterLedger.slotCapacity raw :=
    macroResult_scratch_lt raw afterLeft
      (sourcePlan kind 1)
      (sourceCheckRelative kind) (sourceGateCount kind)
  have traceSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        traceProgram afterRight afterTrace := by
    have safe :=
      trace_safe workspace rightRange capturedRight traceScratch
    simpa [TargetEmitterController.Plan.trace,
      TargetEmitterController.Plan.optionProgram,
      traceEq, afterTrace] using safe
  have allSafe :=
    leftSafe.append (rightSafe.append traceSafe)
  simpa [TargetEmitterController.Plan.constantNormalization,
    TargetEmitterController.Plan.optionProgram,
    constantNormalizationProgram, leftEq, rightEq, traceEq,
    constantNormalizationResult, kind,
    List.append_assoc] using allSafe

/-! ### Header block -/

/-- The closed plain-cursor header program is capacity-safe. -/
theorem header_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (context : SourceContext source)
    (sourcePacked :
      ∀ symbol, symbol ∈ source →
        TargetEmitter.PackedSymbol symbol)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source context
      TargetEmitterController.Plan.header runtime
      (headerResult runtime) := by
  rcases headerProgram_closed with ⟨program, compiled⟩
  have closed := compiled
  unfold headerProgram at compiled
  cases widthEq : compileNatural .plain carrierWidth with
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
                    runtime.targetTokens ++ [.version0] }
              let afterWidth :=
                naturalResult afterVersion carrierWidth
              let afterGateCount :=
                naturalResult afterWidth
                  (NatExpression.addOffset baseline 4)
              let bounds :=
                TargetEmitterCapacity.planBounds
                  range capturedBound scratchBound
              let block := TargetEmitterCapacity.blockBounds range
              have versionSafe :
                  ProgramSafe
                    (TargetEmitterLedger.slotCapacity raw)
                    source context [.append .plain .version0]
                    runtime afterVersion := by
                simpa [afterVersion] using
                  (ProgramSafe.singleton
                    ((ModeReady.plain sourcePacked).append
                      (capacity :=
                        TargetEmitterLedger.slotCapacity raw)
                      (context := context) runtime .version0))
              have widthSafe :
                  ProgramSafe
                    (TargetEmitterLedger.slotCapacity raw)
                    source context widthProgram afterVersion
                    afterWidth := by
                have safe :=
                  compileNatural_safe
                    (context := context)
                    (ModeReady.plain sourcePacked)
                    carrierWidth widthProgram afterVersion widthEq
                    (by simpa [afterVersion] using scratchBound)
                    range.ledgerFits
                    (by
                      simpa [afterVersion] using
                        (coordinate_carrierWidth
                          (source := source) bounds))
                simpa [afterWidth, naturalResult] using safe
              have afterWidthBound :
                  afterWidth.scratch <
                    TargetEmitterLedger.slotCapacity raw := by
                simpa [afterWidth, naturalResult, naturalValue,
                  carrierWidth, NatExpression.evaluate,
                  NatExpression.counter,
                  NatExpression.evaluateCounter] using
                  block.headerCarrierWidth
              have gateCountSafe :
                  ProgramSafe
                    (TargetEmitterLedger.slotCapacity raw)
                    source context gateCountProgram afterWidth
                    afterGateCount := by
                have safe :=
                  compileNatural_safe
                    (context := context)
                    (ModeReady.plain sourcePacked)
                    (NatExpression.addOffset baseline 4)
                    gateCountProgram afterWidth gateCountEq
                    afterWidthBound range.ledgerFits
                    (by
                      simpa [afterWidth, naturalResult,
                        afterVersion] using
                        (coordinate_baselineOffset
                          (source := source)
                          (captured := runtime.captured)
                          block (by omega)))
                simpa [afterGateCount, naturalResult] using safe
              have afterGateCountBound :
                  afterGateCount.scratch <
                    TargetEmitterLedger.slotCapacity raw := by
                simpa [afterGateCount, afterWidth, afterVersion,
                  naturalResult, naturalValue, baseline,
                  NatExpression.addOffset,
                  NatExpression.evaluate,
                  NatExpression.counter,
                  NatExpression.evaluateCounter,
                  Nat.add_comm] using
                  block.headerGateCount
              have outputCountSafe :
                  ProgramSafe
                    (TargetEmitterLedger.slotCapacity raw)
                    source context outputCountProgram afterGateCount
                    (naturalResult afterGateCount
                      (NatExpression.addOffset baseline 1)) := by
                have safe :=
                  compileNatural_safe
                    (context := context)
                    (ModeReady.plain sourcePacked)
                    (NatExpression.addOffset baseline 1)
                    outputCountProgram afterGateCount outputCountEq
                    afterGateCountBound range.ledgerFits
                    (by
                      simpa [afterGateCount, afterWidth,
                        afterVersion, naturalResult] using
                        (coordinate_baselineOffset
                          (source := source)
                          (captured := runtime.captured)
                          block (by omega)))
                simpa [naturalResult] using safe
              have allSafe :=
                versionSafe.append
                  (widthSafe.append
                    (gateCountSafe.append outputCountSafe))
              simpa [TargetEmitterController.Plan.header,
                TargetEmitterController.Plan.optionProgram, closed,
                headerResult, afterVersion, afterWidth,
                afterGateCount, List.append_assoc] using allSafe

/-! ### Final gate blocks -/

private theorem plannedGate_outputIndex
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch) :
    PlannedSourceSafe raw source registers captured
      (.gate outputIndex) := by
  exact .gate outputIndex <|
    .registers outputIndex
      (by
        intro counter member
        have equal : counter = .outputIndex := by
          simpa [outputIndex, NatExpression.counter] using member
        subst counter
        simp)
      bounds.outputIndex

private theorem finalZeroPlan_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (capturedReady : CapturedReady raw source captured) :
    ∀ gate, gate ∈ finalZeroPlan →
      PlannedGateSafe raw source registers captured gate := by
  intro gate member
  simp [finalZeroPlan, finalBindings, finalTemplate,
    instantiateTemplateAt, TemplateGate.instantiateAt,
    TemplateSource.instantiateAt] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact
      { left := .constant false
        right := plannedInput_rawGateTrace bounds capturedReady }
  · exact
      { left := plannedGate_outputIndex bounds
        right := plannedGate_outputIndex bounds }
  · exact
      { left := plannedInput_finalLock bounds
        right := plannedGate_local bounds (by omega) }
  · exact
      { left := plannedGate_local bounds (by omega)
        right := plannedGate_local bounds (by omega) }

private theorem finalPositivePlan_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (bounds : PlanBounds raw registers captured scratch)
    (outputTrace : NatExpression)
    (outputTraceSafe :
      PlannedSourceSafe raw source registers captured
        (.input outputTrace)) :
    ∀ gate, gate ∈ finalPositivePlan outputTrace →
      PlannedGateSafe raw source registers captured gate := by
  intro gate member
  simp [finalPositivePlan, finalBindings, finalTemplate,
    instantiateTemplateAt, TemplateGate.instantiateAt,
    TemplateSource.instantiateAt] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact
      { left := plannedGate_outputIndex bounds
        right := outputTraceSafe }
  · exact
      { left := by
          simpa [localGate, outputIndex, NatExpression.addOffset,
            NatExpression.counter] using
            (plannedGate_local (offset := 1) bounds (by omega))
        right := by
          simpa [localGate, outputIndex, NatExpression.addOffset,
            NatExpression.counter] using
            (plannedGate_local (offset := 1) bounds (by omega)) }
  · exact
      { left := plannedInput_finalLock bounds
        right := by
          simpa [localGate, outputIndex, NatExpression.addOffset,
            NatExpression.counter] using
            (plannedGate_local (offset := 2) bounds (by omega)) }
  · exact
      { left := by
          simpa [localGate, outputIndex, NatExpression.addOffset,
            NatExpression.counter] using
            (plannedGate_local (offset := 3) bounds (by omega))
        right := by
          simpa [localGate, outputIndex, NatExpression.addOffset,
            NatExpression.counter] using
            (plannedGate_local (offset := 3) bounds (by omega)) }

private theorem compiledFinal_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (gates : List PlannedGate) (gatesProgram : List Primitive)
    (compiled :
      compileGates .marked gates = some gatesProgram)
    (gatesSafe :
      ∀ gate, gate ∈ gates →
        PlannedGateSafe raw source runtime.registers
          runtime.captured gate) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      (gatesProgram ++ [.resetScratch]) runtime
      (finalResult runtime gates) := by
  have gateRun :=
    compileGates_safe (context := workspace.context)
      (ModeReady.marked workspace.cursor) gates gatesProgram
      runtime compiled scratchBound
      range.ledgerFits gatesSafe
  have afterGatesBound :=
    gatesResult_scratch_lt gates runtime scratchBound gatesSafe
  have resetRun :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.resetScratch] (gatesResult runtime gates)
        (finalResult runtime gates) := by
    simpa [finalResult, resetScratchResult] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.resetScratch
          (gatesResult runtime gates) afterGatesBound))
  exact gateRun.append resetRun

/-- The no-input finalizer is capacity-safe. -/
theorem finalZero_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (captured : CapturedReady raw source runtime.captured) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      TargetEmitterController.Plan.finalZero runtime
      (finalResult runtime finalZeroPlan) := by
  rcases finalZeroProgram_closed with ⟨program, compiled⟩
  have closed := compiled
  unfold finalZeroProgram at compiled
  cases gatesEq : compileGates .marked finalZeroPlan with
  | none =>
      simp [gatesEq] at compiled
  | some gatesProgram =>
      have programEq :
          program = gatesProgram ++ [.resetScratch] := by
        simpa [gatesEq] using compiled.symm
      subst program
      have bounds :=
        TargetEmitterCapacity.planBounds
          range capturedBound scratchBound
      have safe :=
        compiledFinal_safe workspace range scratchBound
          finalZeroPlan gatesProgram gatesEq
          (finalZeroPlan_safe bounds captured)
      simpa [TargetEmitterController.Plan.finalZero,
        TargetEmitterController.Plan.optionProgram, closed] using safe

/-- The finalizer that references the raw output gate is capacity-safe. -/
theorem finalRaw_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (captured : CapturedReady raw source runtime.captured) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      TargetEmitterController.Plan.finalRaw runtime
      (finalResult runtime (finalPositivePlan rawGateTrace)) := by
  rcases finalPositiveRawGateProgram_closed with
    ⟨program, compiled⟩
  have closed := compiled
  unfold finalPositiveProgram at compiled
  cases gatesEq :
      compileGates .marked (finalPositivePlan rawGateTrace) with
  | none =>
      simp [gatesEq] at compiled
  | some gatesProgram =>
      have programEq :
          program = gatesProgram ++ [.resetScratch] := by
        simpa [gatesEq] using compiled.symm
      subst program
      have bounds :=
        TargetEmitterCapacity.planBounds
          range capturedBound scratchBound
      have safe :=
        compiledFinal_safe workspace range scratchBound
          (finalPositivePlan rawGateTrace) gatesProgram gatesEq
          (finalPositivePlan_safe bounds rawGateTrace
            (plannedInput_rawGateTrace bounds captured))
      simpa [TargetEmitterController.Plan.finalRaw,
        TargetEmitterController.Plan.optionProgram, closed] using safe

/-- The finalizer that references the normalized trace is capacity-safe. -/
theorem finalNormalized_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      TargetEmitterController.Plan.finalNormalized runtime
      (finalResult runtime
        (finalPositivePlan traceCoordinate)) := by
  rcases finalPositiveNormalizedProgram_closed with
    ⟨program, compiled⟩
  have closed := compiled
  unfold finalPositiveProgram at compiled
  cases gatesEq :
      compileGates .marked
        (finalPositivePlan traceCoordinate) with
  | none =>
      simp [gatesEq] at compiled
  | some gatesProgram =>
      have programEq :
          program = gatesProgram ++ [.resetScratch] := by
        simpa [gatesEq] using compiled.symm
      subst program
      have bounds :=
        TargetEmitterCapacity.planBounds
          range capturedBound scratchBound
      have safe :=
        compiledFinal_safe workspace range scratchBound
          (finalPositivePlan traceCoordinate)
          gatesProgram gatesEq
          (finalPositivePlan_safe bounds traceCoordinate
            (plannedInput_traceCoordinate bounds))
      simpa [TargetEmitterController.Plan.finalNormalized,
        TargetEmitterController.Plan.optionProgram, closed] using safe

/-! ### Prefix-fold blocks -/

private theorem emitPoppedGateSource_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source} {mode : CursorMode}
    (ready : ModeReady source mode)
    (runtime : Runtime)
    (scratchBound : runtime.scratch ≤ capacity) :
    ProgramSafe capacity source context
      (emitPoppedGateSource mode) runtime
      (emittedPoppedSourceResult runtime) := by
  let afterTag : Runtime :=
    { runtime with
      targetTokens := runtime.targetTokens ++ [.gate] }
  have tagSafe :
      ProgramSafe capacity source context
        [.append mode .gate] runtime afterTag := by
    simpa [afterTag] using
      (ProgramSafe.singleton
        (ready.append (context := context) runtime .gate))
  have naturalSafe :
      ProgramSafe capacity source context
        [.emitScratchNat mode] afterTag
        (emittedPoppedSourceResult runtime) := by
    simpa [afterTag, emittedPoppedSourceResult,
      encodeSourceTokens, List.append_assoc] using
      (ProgramSafe.singleton
        (ready.emitScratch (context := context)
          afterTag (by simpa [afterTag] using scratchBound)))
  simpa [emitPoppedGateSource] using
    tagSafe.append naturalSafe

private theorem appendGateEnd_safe
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source} {mode : CursorMode}
    (ready : ModeReady source mode)
    (runtime : Runtime) :
    ProgramSafe capacity source context
      [.append mode .gateEnd] runtime
      (appendedGateEndResult runtime) := by
  simpa [appendedGateEndResult] using
    (ProgramSafe.singleton
      (ready.append (context := context) runtime .gateEnd))

private theorem prefixClose_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime) (count : Nat)
    (range : ControllerRange raw runtime.registers)
    (countBound : count ≤ 18)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      (prefixCloseProgram count) runtime
      (prefixCloseResult runtime count) := by
  let afterEnd := appendedGateEndResult runtime
  let afterIncrement := incrementOutputResult afterEnd count
  have endSafe :=
    appendGateEnd_safe
      (capacity := TargetEmitterLedger.slotCapacity raw)
      (context := workspace.context)
      (ModeReady.marked workspace.cursor) runtime
  have incrementBound :
      afterEnd.registers.outputIndex + count <
        TargetEmitterLedger.slotCapacity raw := by
    have envelope :=
      range.outputIndex_add_eighteen_lt_slotCapacity
    simp [afterEnd, appendedGateEndResult]
    omega
  have incrementSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        (repeatPrimitive count
          (.incrementRegister .outputIndex))
        afterEnd afterIncrement := by
    exact
      repeatIncrementOutputIndex_safe count afterEnd
        (by simpa [afterEnd, appendedGateEndResult] using
          range.ledgerFits)
        incrementBound
  have resetSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.resetScratch] afterIncrement
        (prefixCloseResult runtime count) := by
    simpa [afterIncrement, afterEnd, prefixCloseResult,
      incrementOutputResult, appendedGateEndResult,
      resetScratchResult] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.resetScratch
          afterIncrement (by
            simpa [afterIncrement, afterEnd,
              incrementOutputResult, appendedGateEndResult] using
              scratchBound)))
  simpa [prefixCloseProgram, List.append_assoc] using
    endSafe.append (incrementSafe.append resetSafe)

private theorem firstPrefixOpening_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime} {prior : List Nat} {newest : Nat}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (checksShape : runtime.checks = prior ++ [newest])
    (newestBound :
      newest < TargetEmitterLedger.slotCapacity raw) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      firstPrefixOpeningProgram runtime
      (firstPrefixOpeningResult runtime prior newest) := by
  let afterLeft := emittedPoppedSourceResult runtime
  let afterReset : Runtime := { afterLeft with scratch := 0 }
  let afterPop : Runtime :=
    { afterLeft with scratch := newest, checks := prior }
  let afterRight := emittedPoppedSourceResult afterPop
  have leftSafe :=
    emitPoppedGateSource_safe
      (capacity := TargetEmitterLedger.slotCapacity raw)
      (context := workspace.context)
      (ModeReady.marked workspace.cursor) runtime (by omega)
  have resetSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.resetScratch] afterLeft afterReset := by
    simpa [afterReset] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.resetScratch
          afterLeft (by
            simpa [afterLeft, emittedPoppedSourceResult] using
              scratchBound)))
  have popSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.popCheck] afterReset afterPop := by
    simpa [afterReset, afterPop, afterLeft,
      emittedPoppedSourceResult] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.popCheck
          afterReset prior newest
          (by simpa [afterReset, afterLeft,
            emittedPoppedSourceResult] using range.ledgerFits)
          (by simp [afterReset])
          (by simpa [afterReset, afterLeft,
            emittedPoppedSourceResult] using checksShape)
          (by omega)))
  have rightSafe :=
    emitPoppedGateSource_safe
      (capacity := TargetEmitterLedger.slotCapacity raw)
      (context := workspace.context)
      (ModeReady.marked workspace.cursor) afterPop (by
        simp [afterPop]
        omega)
  have endSafe :=
    appendGateEnd_safe
      (capacity := TargetEmitterLedger.slotCapacity raw)
      (context := workspace.context)
      (ModeReady.marked workspace.cursor) afterRight
  have allSafe :=
    leftSafe.append
      (resetSafe.append
        (popSafe.append (rightSafe.append endSafe)))
  simpa [firstPrefixOpeningProgram, afterLeft, afterReset,
    afterPop, afterRight, firstPrefixOpeningResult,
    emittedPoppedSourceResult, appendedGateEndResult,
    encodeGateTokens, encodeSourceTokens,
    List.append_assoc] using allSafe

/-- The first two-gate right-fold link is capacity-safe for a nonempty
check stack whose newest entry fits strictly in the unary workspace. -/
theorem firstPrefix_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime} {prior : List Nat} {newest : Nat}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (checksShape : runtime.checks = prior ++ [newest])
    (newestBound :
      newest < TargetEmitterLedger.slotCapacity raw) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      TargetEmitterController.Plan.firstPrefix runtime
      (firstPrefixResult runtime prior newest) := by
  rcases firstPrefixProgram_closed with ⟨program, compiled⟩
  have closed := compiled
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
      have bounds :=
        TargetEmitterCapacity.planBounds
          range capturedBound scratchBound
      have openingSafe :=
        firstPrefixOpening_safe workspace range scratchBound
          checksShape newestBound
      have localPlan :
          PlannedSourceSafe raw source
            afterOpening.registers afterOpening.captured
            (.gate outputIndex) := by
        simpa [afterOpening, firstPrefixOpeningResult] using
          (plannedGate_outputIndex (source := source) bounds)
      have localLeftSafe :
          ProgramSafe
            (TargetEmitterLedger.slotCapacity raw)
            source workspace.context localProgram
            afterOpening afterLocalLeft := by
        exact
          compileSource_safe
            (context := workspace.context)
            (ModeReady.marked workspace.cursor)
            (.gate outputIndex) localProgram afterOpening localEq
            (by
              simp [afterOpening, firstPrefixOpeningResult]
              exact newestBound)
            (by simpa [afterOpening, firstPrefixOpeningResult] using
              range.ledgerFits)
            localPlan
      have localPlanRight :
          PlannedSourceSafe raw source
            afterLocalLeft.registers afterLocalLeft.captured
            (.gate outputIndex) := by
        simpa [afterLocalLeft, sourceResult] using localPlan
      have afterLeftBound :
          afterLocalLeft.scratch <
            TargetEmitterLedger.slotCapacity raw :=
        plannedSourceSafe_scratch localPlan newestBound
      have localRightSafe :
          ProgramSafe
            (TargetEmitterLedger.slotCapacity raw)
            source workspace.context localProgram
            afterLocalLeft afterLocalRight := by
        exact
          compileSource_safe
            (context := workspace.context)
            (ModeReady.marked workspace.cursor)
            (.gate outputIndex) localProgram afterLocalLeft localEq
            afterLeftBound
            (by simpa [afterLocalLeft, afterOpening,
              sourceResult, firstPrefixOpeningResult] using
              range.ledgerFits)
            localPlanRight
      have afterRightBound :
          afterLocalRight.scratch <
            TargetEmitterLedger.slotCapacity raw :=
        plannedSourceSafe_scratch localPlanRight afterLeftBound
      have closeRange :
          ControllerRange raw afterLocalRight.registers := by
        simpa [afterLocalRight, afterLocalLeft, afterOpening,
          sourceResult, firstPrefixOpeningResult] using range
      have closeSafe :=
        prefixClose_safe workspace afterLocalRight 1 closeRange
          (by omega) afterRightBound
      have allSafe :=
        openingSafe.append
          (localLeftSafe.append
            (localRightSafe.append closeSafe))
      simpa [TargetEmitterController.Plan.firstPrefix,
        TargetEmitterController.Plan.optionProgram, closed,
        firstPrefixResult, afterOpening, afterLocalLeft,
        afterLocalRight, List.append_assoc] using allSafe

private theorem nextPrefixOpening_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime} {accumulatorProgram : List Primitive}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (compiled :
      compileSource .marked (.gate outputIndex) =
        some accumulatorProgram)
    (accumulatorPlan :
      PlannedSourceSafe raw source runtime.registers
        runtime.captured (.gate outputIndex)) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      (nextPrefixOpeningProgram accumulatorProgram) runtime
      (nextPrefixOpeningResult runtime) := by
  let afterPush : Runtime :=
    { runtime with
      checks := runtime.checks ++ [runtime.scratch] }
  let afterAccumulator :=
    sourceResult afterPush (.gate outputIndex)
  let afterReset : Runtime :=
    { afterAccumulator with scratch := 0 }
  let afterPop : Runtime :=
    { afterAccumulator with
      scratch := runtime.scratch
      checks := runtime.checks }
  let afterPoppedSource :=
    emittedPoppedSourceResult afterPop
  have pushSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.pushCheck] runtime afterPush := by
    simpa [afterPush] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.pushCheck
          runtime range.ledgerFits (by omega)))
  have accumulatorPlan' :
      PlannedSourceSafe raw source afterPush.registers
        afterPush.captured (.gate outputIndex) := by
    simpa [afterPush] using accumulatorPlan
  have accumulatorSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        accumulatorProgram afterPush afterAccumulator := by
    exact
      compileSource_safe
        (context := workspace.context)
        (ModeReady.marked workspace.cursor)
        (.gate outputIndex) accumulatorProgram afterPush compiled
        (by simpa [afterPush] using scratchBound)
        (by simpa [afterPush] using range.ledgerFits)
        accumulatorPlan'
  have accumulatorBound :
      afterAccumulator.scratch <
        TargetEmitterLedger.slotCapacity raw :=
    plannedSourceSafe_scratch accumulatorPlan' (by
      simpa [afterPush] using scratchBound)
  have resetSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.resetScratch] afterAccumulator afterReset := by
    simpa [afterReset] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.resetScratch
          afterAccumulator accumulatorBound))
  have popSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.popCheck] afterReset afterPop := by
    simpa [afterReset, afterPop, afterAccumulator,
      afterPush, sourceResult] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.popCheck
          afterReset runtime.checks runtime.scratch
          (by simpa [afterReset, afterAccumulator,
            afterPush, sourceResult] using range.ledgerFits)
          (by simp [afterReset])
          (by simp [afterReset, afterAccumulator,
            afterPush, sourceResult])
          (by omega)))
  have poppedSourceSafe :=
    emitPoppedGateSource_safe
      (capacity := TargetEmitterLedger.slotCapacity raw)
      (context := workspace.context)
      (ModeReady.marked workspace.cursor) afterPop (by
        simp [afterPop]
        omega)
  have endSafe :=
    appendGateEnd_safe
      (capacity := TargetEmitterLedger.slotCapacity raw)
      (context := workspace.context)
      (ModeReady.marked workspace.cursor) afterPoppedSource
  have allSafe :=
    pushSafe.append
      (accumulatorSafe.append
        (resetSafe.append
          (popSafe.append
            (poppedSourceSafe.append endSafe))))
  simpa [nextPrefixOpeningProgram, afterPush,
    afterAccumulator, afterReset, afterPop,
    afterPoppedSource, nextPrefixOpeningResult,
    sourceResult, sourceScratch, evaluatedSource,
    naturalValue, outputIndex, NatExpression.counter,
    NatExpression.evaluate, NatExpression.evaluateCounter,
    PlannedSource.evaluate, emittedPoppedSourceResult,
    appendedGateEndResult, encodeGateTokens,
    encodeSourceTokens, List.append_assoc] using allSafe

/-- Every later two-gate right-fold link is capacity-safe. -/
theorem nextPrefix_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      TargetEmitterController.Plan.nextPrefix runtime
      (nextPrefixResult runtime) := by
  rcases nextPrefixTailProgram_closed with
    ⟨program, compiled⟩
  have closed := compiled
  unfold nextPrefixTailProgram at compiled
  cases accumulatorEq :
      compileSource .marked (.gate outputIndex) with
  | none =>
      simp [accumulatorEq] at compiled
  | some accumulatorProgram =>
      cases localEq :
          compileSource .marked
            (.gate
              (NatExpression.addOffset outputIndex 1)) with
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
          have bounds :=
            TargetEmitterCapacity.planBounds
              range capturedBound scratchBound
          have accumulatorPlan :=
            plannedGate_outputIndex (source := source) bounds
          have openingSafe :=
            nextPrefixOpening_safe workspace range scratchBound
              accumulatorEq accumulatorPlan
          have localPlan :
              PlannedSourceSafe raw source
                afterOpening.registers afterOpening.captured
                localSource := by
            simpa [localSource, afterOpening,
              nextPrefixOpeningResult, localGate] using
              (plannedGate_local
                (source := source) (offset := 1)
                bounds (by omega))
          have localLeftSafe :
              ProgramSafe
                (TargetEmitterLedger.slotCapacity raw)
                source workspace.context localProgram
                afterOpening afterLocalLeft := by
            exact
              compileSource_safe
                (context := workspace.context)
                (ModeReady.marked workspace.cursor)
                localSource localProgram afterOpening
                (by simpa [localSource] using localEq)
                (by simpa [afterOpening,
                  nextPrefixOpeningResult] using scratchBound)
                (by simpa [afterOpening,
                  nextPrefixOpeningResult] using range.ledgerFits)
                localPlan
          have localPlanRight :
              PlannedSourceSafe raw source
                afterLocalLeft.registers afterLocalLeft.captured
                localSource := by
            simpa [afterLocalLeft, sourceResult] using localPlan
          have afterLeftBound :
              afterLocalLeft.scratch <
                TargetEmitterLedger.slotCapacity raw := by
            exact
              plannedSourceSafe_scratch localPlan
                (by simpa [afterOpening,
                  nextPrefixOpeningResult] using scratchBound)
          have localRightSafe :
              ProgramSafe
                (TargetEmitterLedger.slotCapacity raw)
                source workspace.context localProgram
                afterLocalLeft afterLocalRight := by
            exact
              compileSource_safe
                (context := workspace.context)
                (ModeReady.marked workspace.cursor)
                localSource localProgram afterLocalLeft
                (by simpa [localSource] using localEq)
                afterLeftBound
                (by simpa [afterLocalLeft, afterOpening,
                  sourceResult, nextPrefixOpeningResult] using
                  range.ledgerFits)
                localPlanRight
          have afterRightBound :
              afterLocalRight.scratch <
                TargetEmitterLedger.slotCapacity raw :=
            plannedSourceSafe_scratch
              localPlanRight afterLeftBound
          have closeRange :
              ControllerRange raw afterLocalRight.registers := by
            simpa [afterLocalRight, afterLocalLeft,
              afterOpening, sourceResult,
              nextPrefixOpeningResult] using range
          have closeSafe :=
            prefixClose_safe workspace afterLocalRight 2
              closeRange (by omega) afterRightBound
          have allSafe :=
            openingSafe.append
              (localLeftSafe.append
                (localRightSafe.append closeSafe))
          simpa [TargetEmitterController.Plan.nextPrefix,
            TargetEmitterController.Plan.optionProgram, closed,
            nextPrefixResult, afterOpening, localSource,
            afterLocalLeft, afterLocalRight,
            List.append_assoc] using allSafe

/-! ### Output blocks -/

/-- The controller's standalone gate-reset block is capacity-safe. -/
theorem outputGateReset_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (context : SourceContext source)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source context
      TargetEmitterController.Plan.outputGateReset runtime
      (resetScratchResult runtime) := by
  simpa [TargetEmitterController.Plan.outputGateReset,
    resetScratchResult] using
    (ProgramSafe.singleton
      (TargetEmitterRuntimeProgram.PrimitiveSafe.resetScratch
        runtime scratchBound))

/-- The output-section opener is safe at a marked source cursor. -/
theorem beginOutput_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (workspace : MarkedWorkspace source)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      TargetEmitterController.Plan.beginOutput runtime
      (beginOutputResult runtime) := by
  let afterEnd : Runtime :=
    { runtime with
      targetTokens := runtime.targetTokens ++ [.programEnd] }
  have appendSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.append .marked .programEnd] runtime afterEnd := by
    simpa [afterEnd] using
      (ProgramSafe.singleton
        ((ModeReady.marked workspace.cursor).append
          (capacity := TargetEmitterLedger.slotCapacity raw)
          (context := workspace.context) runtime .programEnd))
  have resetSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.resetScratch] afterEnd (beginOutputResult runtime) := by
    simpa [afterEnd, beginOutputResult] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.resetScratch
          afterEnd (by simpa [afterEnd] using scratchBound)))
  simpa [TargetEmitterController.Plan.beginOutput,
    beginOutputProgram] using appendSafe.append resetSafe

/-- One output-loop gate source is safe and advances the output cursor once. -/
theorem outputItem_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (workspace : MarkedWorkspace source)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      TargetEmitterController.Plan.outputItem runtime
      (outputLoopItemResult runtime) := by
  let afterTag : Runtime :=
    { runtime with
      targetTokens := runtime.targetTokens ++ [.gate] }
  let afterNatural : Runtime :=
    { afterTag with
      targetTokens :=
        afterTag.targetTokens ++ encodeNatTokens runtime.scratch }
  have tagSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.append .marked .gate] runtime afterTag := by
    simpa [afterTag] using
      (ProgramSafe.singleton
        ((ModeReady.marked workspace.cursor).append
          (capacity := TargetEmitterLedger.slotCapacity raw)
          (context := workspace.context) runtime .gate))
  have naturalSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.emitScratchNat .marked] afterTag afterNatural := by
    simpa [afterTag, afterNatural] using
      (ProgramSafe.singleton
        ((ModeReady.marked workspace.cursor).emitScratch
          (context := workspace.context) afterTag (by
            simp [afterTag]
            omega)))
  have incrementSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.incrementScratch] afterNatural
        (outputLoopItemResult runtime) := by
    simpa [afterTag, afterNatural, outputLoopItemResult,
      encodeSourceTokens, List.append_assoc] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.incrementScratch
          afterNatural (by simpa [afterNatural, afterTag] using scratchBound)))
  simpa [TargetEmitterController.Plan.outputItem,
    outputLoopItemProgram] using
    tagSafe.append (naturalSafe.append incrementSafe)

/-- The final output-loop item and threshold suffix are safe once the loop
cursor has reached the source-derived baseline. -/
theorem outputFinish_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (atBaseline :
      runtime.scratch = runtime.registers.baseline) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      TargetEmitterController.Plan.outputFinish runtime
      (outputLoopFinishResult runtime) := by
  let afterOne : Runtime :=
    { runtime with scratch := runtime.scratch + 1 }
  let afterTwo : Runtime :=
    { runtime with scratch := runtime.scratch + 2 }
  let afterThree : Runtime :=
    { runtime with scratch := runtime.scratch + 3 }
  let afterTag : Runtime :=
    { afterThree with
      targetTokens := afterThree.targetTokens ++ [.gate] }
  let afterNatural : Runtime :=
    { afterTag with
      targetTokens :=
        afterTag.targetTokens ++
          encodeNatTokens afterTag.scratch }
  let afterOutputsEnd : Runtime :=
    { afterNatural with
      targetTokens :=
        afterNatural.targetTokens ++ [.outputsEnd] }
  let afterReset : Runtime :=
    { afterOutputsEnd with scratch := 0 }
  let afterBaseline : Runtime :=
    { afterReset with
      scratch := runtime.registers.baseline }
  let afterThreshold : Runtime :=
    { afterBaseline with
      targetTokens :=
        afterBaseline.targetTokens ++ [.threshold] }
  let afterThresholdNatural : Runtime :=
    { afterThreshold with
      targetTokens :=
        afterThreshold.targetTokens ++
          encodeNatTokens afterThreshold.scratch }
  have block := TargetEmitterCapacity.blockBounds range
  have threeBound :
      runtime.scratch + 3 <
        TargetEmitterLedger.slotCapacity raw := by
    rw [atBaseline]
    exact block.outputLastBaseline
  have incrementOne :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.incrementScratch] runtime afterOne := by
    simpa [afterOne] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.incrementScratch
          runtime (by omega)))
  have incrementTwo :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.incrementScratch] afterOne afterTwo := by
    simpa [afterOne, afterTwo] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.incrementScratch
          afterOne (by simp [afterOne]; omega)))
  have incrementThree :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.incrementScratch] afterTwo afterThree := by
    simpa [afterTwo, afterThree] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.incrementScratch
          afterTwo (by simp [afterTwo]; omega)))
  have tagSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.append .marked .gate] afterThree afterTag := by
    simpa [afterTag] using
      (ProgramSafe.singleton
        ((ModeReady.marked workspace.cursor).append
          (capacity := TargetEmitterLedger.slotCapacity raw)
          (context := workspace.context) afterThree .gate))
  have naturalSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.emitScratchNat .marked] afterTag afterNatural := by
    simpa [afterNatural] using
      (ProgramSafe.singleton
        ((ModeReady.marked workspace.cursor).emitScratch
          (context := workspace.context) afterTag (by
            simp [afterTag, afterThree]
            omega)))
  have outputsEndSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.append .marked .outputsEnd] afterNatural
        afterOutputsEnd := by
    simpa [afterOutputsEnd] using
      (ProgramSafe.singleton
        ((ModeReady.marked workspace.cursor).append
          (capacity := TargetEmitterLedger.slotCapacity raw)
          (context := workspace.context) afterNatural .outputsEnd))
  have resetSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.resetScratch] afterOutputsEnd afterReset := by
    simpa [afterReset] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.resetScratch
          afterOutputsEnd (by
            simp [afterOutputsEnd, afterNatural, afterTag, afterThree]
            omega)))
  have addBaselineSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.addRegister .baseline] afterReset afterBaseline := by
    simpa [afterReset, afterBaseline,
      TargetEmitterLedger.slotValue] using
      (ProgramSafe.singleton
        (TargetEmitterRuntimeProgram.PrimitiveSafe.addRegister
          afterReset .baseline .baseline rfl range.ledgerFits
          (by
            simp [afterReset]
            exact range.ledgerFits.baseline)))
  have thresholdSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.append .marked .threshold] afterBaseline
        afterThreshold := by
    simpa [afterThreshold] using
      (ProgramSafe.singleton
        ((ModeReady.marked workspace.cursor).append
          (capacity := TargetEmitterLedger.slotCapacity raw)
          (context := workspace.context) afterBaseline .threshold))
  have thresholdNaturalSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.emitScratchNat .marked] afterThreshold
        afterThresholdNatural := by
    simpa [afterThresholdNatural] using
      (ProgramSafe.singleton
        ((ModeReady.marked workspace.cursor).emitScratch
          (context := workspace.context) afterThreshold (by
            simp [afterThreshold, afterBaseline]
            exact range.ledgerFits.baseline)))
  have instanceEndSafe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        [.append .marked .instanceEnd] afterThresholdNatural
        (outputLoopFinishResult runtime) := by
    simpa [afterThresholdNatural, afterThreshold, afterBaseline,
      afterReset, afterOutputsEnd, afterNatural, afterTag,
      afterThree, outputLoopFinishResult, encodeSourceTokens,
      atBaseline, List.append_assoc] using
      (ProgramSafe.singleton
        ((ModeReady.marked workspace.cursor).append
          (capacity := TargetEmitterLedger.slotCapacity raw)
          (context := workspace.context)
          afterThresholdNatural .instanceEnd))
  have allSafe :=
    incrementOne.append
      (incrementTwo.append
        (incrementThree.append
          (tagSafe.append
            (naturalSafe.append
              (outputsEndSafe.append
                (resetSafe.append
                  (addBaselineSafe.append
                    (thresholdSafe.append
                      (thresholdNaturalSafe.append
                        instanceEndSafe)))))))))
  simpa [TargetEmitterController.Plan.outputFinish,
    outputLoopFinishProgram, List.append_assoc] using allSafe

end PNP.Concrete.LockedNAND.TargetEmitterRuntimeProgramSafety
