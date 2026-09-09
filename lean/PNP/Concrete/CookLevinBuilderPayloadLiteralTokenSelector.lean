/-
Copyright (c) 2026 PNP Labs.

Read literal operands directly from actual local-constraint payloads and a
physical loop ordinal. The fixed schema, not the runtime data, determines the
finite machine. Implication premises are negated; their conclusion remains in
its original payload header and is selected last. No selected literal or token
is supplied to the machine.

This is the valid-ordinal primitive for the source-bound clause search. The
enclosing dispatcher must derive the kind and frame and guard the ordinal.
The complete formula builder and its global output invariant remain open.
-/
import PNP.Concrete.CookLevinBuilderIndexedLiteralTokenSelector
import PNP.Concrete.CookLevinBuilderRegisterExactlyOnePayload

namespace PNP.Concrete.CookLevin.BuilderPayloadLiteralTokenSelector

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (signValue literalValues literalListValues variableValues)
open PipelineStateNamespace (renameConfiguration)

/-- Fixed field schemas; these are not runtime literal values or list sizes. -/
inductive Kind where
  | required | premise | conclusion | positive
  deriving DecidableEq, Repr

def stride : Kind → Nat
  | .required | .conclusion => 17
  | .premise => 19
  | .positive => 18
def valueSlot : Kind → Nat
  | .required | .positive => 13
  | .premise => 16
  | .conclusion => 14
def signSlot : Kind → Nat
  | .required => 12
  | .premise => 15
  | .conclusion => 13
  | .positive => 0

/-- Proof-level source selection. The ordinal itself is an input register. -/
inductive Source (width : Nat) where
  | required (literal : BoundedLiteral width)
  | premise (premises : List (BoundedLiteral width)) (conclusion : BoundedLiteral width)
      (index : Fin premises.length)
  | conclusion (premises : List (BoundedLiteral width)) (literal : BoundedLiteral width)
  | positive (variables : List (Fin width)) (index : Fin variables.length)

namespace Source

def kind {width : Nat} : Source width → Kind
  | .required _ => .required
  | .premise _ _ _ => .premise
  | .conclusion _ _ => .conclusion
  | .positive _ _ => .positive

def ordinal {width : Nat} : Source width → Nat
  | .required _ => 0
  | .premise _ _ index => index.val
  | .conclusion premises _ => premises.length
  | .positive _ index => index.val

def slot {width : Nat} : Source width → BuilderLocalConstraintPayload.Slot width
  | .required literal => some (some (.require literal))
  | .premise premises resultLiteral _ => some (some (.implication premises resultLiteral))
  | .conclusion premises literal => some (some (.implication premises literal))
  | .positive variables _ => some (some (.exactlyOne variables))

def originalLiteral {width : Nat} : Source width → BoundedLiteral width
  | .required literal => literal
  | .premise premises _ index => premises[index.val]
  | .conclusion _ literal => literal
  | .positive variables index => ⟨true, variables[index.val]⟩

def selectedLiteral {width : Nat} (source : Source width) : BoundedLiteral width :=
  if source.kind = .premise then source.originalLiteral.negate else source.originalLiteral

end Source

/-- Retained source request and actual clause-search frame, not a token verdict. -/
structure Context (ordinal : Nat) where
  gap : List Nat
  gap_length : gap.length = 9
  clauseIndex : Nat
  originalPosition : Nat
  prior : List Nat
  prior_length : prior.length = 17 * ordinal
  remaining : Nat
  position : Nat

def readerPrefix {ordinal : Nat} (context : Context ordinal) : List Nat :=
  context.prior.reverse ++ [context.originalPosition, context.clauseIndex] ++ context.gap.reverse
def reader {width : Nat} (source : Source width) (context : Context source.ordinal) : List Nat :=
  readerPrefix context ++ BuilderLocalConstraintPayload.front source.slot
def initialValues {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) : List Nat :=
  older ++ (reader source context).reverse ++ [source.ordinal, context.remaining, context.position]

theorem readerPrefix_length {ordinal : Nat} (context : Context ordinal) :
    (readerPrefix context).length = 17 * ordinal + 11 := by
  simp only [readerPrefix, List.length_append, List.length_reverse, List.length_cons,
    List.length_nil, context.prior_length, context.gap_length]

theorem initial_values_layout {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) :
    initialValues source context older =
      older ++ BuilderLocalConstraintPayload.values source.slot ++ context.gap ++
        [context.clauseIndex, context.originalPosition] ++ context.prior ++
          [source.ordinal, context.remaining, context.position] := by
  simp only [initialValues, reader, readerPrefix, BuilderLocalConstraintPayload.values,
    List.reverse_append, List.reverse_reverse, List.reverse_cons, List.reverse_nil,
    List.append_assoc, List.cons_append, List.nil_append]

private def sourceValueOffset {width : Nat} : Source width → Nat
  | .required _ => 2
  | .premise _ _ index => 4 + (2 * index.val + 1)
  | .conclusion _ _ => 3
  | .positive _ index => 2 + index.val
private def sourceSignOffset {width : Nat} : Source width → Nat
  | .required _ => 1
  | .premise _ _ index => 4 + 2 * index.val
  | .conclusion _ _ => 2
  | .positive _ _ => 0

private theorem value_offset {width : Nat} (source : Source width) (context : Context source.ordinal) :
    stride source.kind * source.ordinal + valueSlot source.kind =
      (readerPrefix context).length + sourceValueOffset source := by
  rw [readerPrefix_length]
  cases source <;> simp only [Source.kind, Source.ordinal, stride, valueSlot, sourceValueOffset] <;> omega

private theorem sign_offset {width : Nat} (source : Source width) (context : Context source.ordinal)
    (hKind : source.kind ≠ .positive) :
    stride source.kind * source.ordinal + signSlot source.kind =
      (readerPrefix context).length + sourceSignOffset source := by
  rw [readerPrefix_length]
  cases source with
  | required literal => simp only [Source.kind, Source.ordinal, stride, signSlot, sourceSignOffset] <;> omega
  | premise premises literal index => simp only [Source.kind, Source.ordinal, stride, signSlot, sourceSignOffset] <;> omega
  | conclusion premises literal => simp only [Source.kind, Source.ordinal, stride, signSlot, sourceSignOffset] <;> omega
  | positive variables index => exact False.elim (hKind rfl)

private theorem source_value_lt {width : Nat} (source : Source width) :
    sourceValueOffset source < (BuilderLocalConstraintPayload.front source.slot).length := by
  cases source with
  | required literal => change (2 : Nat) < 3; decide
  | premise premises conclusion index =>
      have h := BuilderPayloadFieldCopy.literal_field_lt premises index.val index.isLt ⟨1, by decide⟩
      simpa only [sourceValueOffset, Source.slot, BuilderLocalConstraintPayload.front,
        literalValues, List.length_append, List.length_cons, List.length_nil] using Nat.add_lt_add_left h 4
  | conclusion premises literal =>
      simp only [sourceValueOffset, Source.slot, BuilderLocalConstraintPayload.front,
        literalValues, List.length_append, List.length_cons, List.length_nil]
      omega
  | positive variables index =>
      have h := index.isLt
      simp only [sourceValueOffset, Source.slot, BuilderLocalConstraintPayload.front,
        variableValues, List.length_append, List.length_cons, List.length_nil, List.length_map]
      omega

private theorem source_value {width : Nat} (source : Source width) :
    (BuilderLocalConstraintPayload.front source.slot)[sourceValueOffset source]'(source_value_lt source) =
      source.originalLiteral.index.val := by
  cases source with
  | required literal => rfl
  | premise premises conclusion index =>
      have h := BuilderPayloadFieldCopy.literal_field_value premises index.val index.isLt ⟨1, by decide⟩
      have hOffset : 4 + (2 * index.val + 1) = (2 * index.val + 1) + 1 + 1 + 1 + 1 := by omega
      simpa only [sourceValueOffset, Source.slot, Source.originalLiteral,
        BuilderLocalConstraintPayload.front, literalValues, List.cons_append, List.nil_append,
        hOffset, List.getElem_cons_succ, BuilderPayloadFieldCopy.literalField, Nat.one_ne_zero, ite_false] using h
  | conclusion premises literal => rfl
  | positive variables index =>
      simp only [sourceValueOffset, Source.slot, Source.originalLiteral,
        BuilderLocalConstraintPayload.front, variableValues, List.cons_append, List.nil_append,
        Nat.add_comm, List.getElem_cons_succ, List.getElem_map]

private theorem source_sign_lt {width : Nat} (source : Source width) (hKind : source.kind ≠ .positive) :
    sourceSignOffset source < (BuilderLocalConstraintPayload.front source.slot).length := by
  cases source with
  | required literal => change (1 : Nat) < 3; decide
  | premise premises conclusion index =>
      have h := BuilderPayloadFieldCopy.literal_field_lt premises index.val index.isLt ⟨0, by decide⟩
      simpa only [sourceSignOffset, Source.slot, BuilderLocalConstraintPayload.front,
        literalValues, List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using Nat.add_lt_add_left h 4
  | conclusion premises literal =>
      simp only [sourceSignOffset, Source.slot, BuilderLocalConstraintPayload.front,
        literalValues, List.length_append, List.length_cons, List.length_nil]
      omega
  | positive variables index => exact False.elim (hKind rfl)

private theorem source_sign {width : Nat} (source : Source width) (hKind : source.kind ≠ .positive) :
    (BuilderLocalConstraintPayload.front source.slot)[sourceSignOffset source]'(source_sign_lt source hKind) =
      signValue source.originalLiteral.positive := by
  cases source with
  | required literal => rfl
  | premise premises conclusion index =>
      have h := BuilderPayloadFieldCopy.literal_field_value premises index.val index.isLt ⟨0, by decide⟩
      have hOffset : 4 + 2 * index.val = 2 * index.val + 1 + 1 + 1 + 1 := by omega
      simpa only [sourceSignOffset, Source.slot, Source.originalLiteral,
        BuilderLocalConstraintPayload.front, literalValues, List.cons_append, List.nil_append,
        hOffset, List.getElem_cons_succ, BuilderPayloadFieldCopy.literalField, ite_true, Nat.add_zero] using h
  | conclusion premises literal => rfl
  | positive variables index => exact False.elim (hKind rfl)

theorem value_field_lt {width : Nat} (source : Source width) (context : Context source.ordinal) :
    stride source.kind * source.ordinal + valueSlot source.kind < (reader source context).length := by
  rw [value_offset, reader, List.length_append]
  exact Nat.add_lt_add_left (source_value_lt source) _
theorem value_field {width : Nat} (source : Source width) (context : Context source.ordinal) :
    (reader source context)[stride source.kind * source.ordinal + valueSlot source.kind]'
      (value_field_lt source context) = source.originalLiteral.index.val := by
  simp only [value_offset source context, reader, List.getElem_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, source_value]

theorem sign_field_lt {width : Nat} (source : Source width) (context : Context source.ordinal)
    (hKind : source.kind ≠ .positive) :
    stride source.kind * source.ordinal + signSlot source.kind < (reader source context).length := by
  rw [sign_offset source context hKind, reader, List.length_append]
  exact Nat.add_lt_add_left (source_sign_lt source hKind) _
theorem sign_field {width : Nat} (source : Source width) (context : Context source.ordinal)
    (hKind : source.kind ≠ .positive) :
    (reader source context)[stride source.kind * source.ordinal + signSlot source.kind]'
      (sign_field_lt source context hKind) = signValue source.originalLiteral.positive := by
  simp only [sign_offset source context hKind, reader,
    List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, source_sign source hKind]

/-- Four physical steps complement the final Boolean unary register in place. -/
def signFlipMachine : WorkMachine :=
  { rules :=
      [ {sourceState := 0, targetState := 1, readSymbol := scratchEndSymbol, writeSymbol := scratchEndSymbol, move := .right},
        {sourceState := 1, targetState := 2, readSymbol := separatorSymbol, writeSymbol := separatorSymbol, move := .left},
        {sourceState := 1, targetState := 4, readSymbol := unitSymbol, writeSymbol := unitSymbol, move := .left},
        {sourceState := 2, targetState := 3, readSymbol := scratchEndSymbol, writeSymbol := unitSymbol, move := .left},
        {sourceState := 4, targetState := 5, readSymbol := scratchEndSymbol, writeSymbol := WorkSymbol.blank, move := .right},
        {sourceState := 5, targetState := 6, readSymbol := unitSymbol, writeSymbol := scratchEndSymbol, move := .stay} ] ++
        PipelineMachineSimulation.allWorkSymbols.map (fun symbol =>
          {sourceState := 3, targetState := 6, readSymbol := symbol, writeSymbol := scratchEndSymbol, move := .stay})
    startState := 0, acceptState := 6, rejectState := 7 }

def flipOutside (positive : Bool) (outside : List WorkSymbol) : List WorkSymbol :=
  if positive then WorkSymbol.blank :: outside else outside.drop 1

theorem sign_flip_workRunExact (positive : Bool) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? signFlipMachine 4
      (workStartConfiguration signFlipMachine (endTape (older ++ [signValue positive]) inside outside)) =
      some {state := signFlipMachine.acceptState, tape := endTape (older ++ [signValue (!positive)]) inside (flipOutside positive outside)} := by
  simp only [endTape, registerWord_append, registerWord, List.append_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.reverse_replicate, List.append_assoc, List.cons_append]
  cases positive with
  | false =>
      cases outside with
      | nil => rfl
      | cons symbol rest =>
          rcases symbol with ⟨first, second⟩
          cases first <;> cases second <;> rfl
  | true => rfl

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem flip_good : Good signFlipMachine := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold WorkMachineChain.QueryDistinct; decide
  · intro rule h; decide +revert
  · intro rule h; decide +revert
  · decide

def valueHistory (kind : Kind) (ordinal value : Nat) : List Nat :=
  BuilderPayloadFieldCopy.scratch (stride kind) (valueSlot kind) 2 ordinal ++ [value]
def signPrefix (kind : Kind) (ordinal : Nat) : List Nat :=
  if kind = .positive then [0,0,0,0,0]
  else BuilderPayloadFieldCopy.scratch (stride kind) (signSlot kind) 8 ordinal
def signHistory (kind : Kind) (ordinal : Nat) (positive : Bool) : List Nat :=
  signPrefix kind ordinal ++ [signValue positive]
def afterValue (kind : Kind) (ordinal remaining position value : Nat) : List Nat :=
  [remaining, position] ++ valueHistory kind ordinal value
def history (kind : Kind) (ordinal remaining position value : Nat) (positive : Bool) : List Nat :=
  [ordinal] ++ afterValue kind ordinal remaining position value ++ signHistory kind ordinal positive

theorem valueHistory_length (kind : Kind) (ordinal value : Nat) : (valueHistory kind ordinal value).length = 6 := rfl
theorem signPrefix_length (kind : Kind) (ordinal : Nat) : (signPrefix kind ordinal).length = 5 := by
  cases kind <;> rfl
theorem history_length (kind : Kind) (ordinal remaining position value : Nat) (positive : Bool) :
    (history kind ordinal remaining position value positive).length = 15 := by
  simp only [history, afterValue, signHistory, List.length_append, List.length_cons, List.length_nil,
    valueHistory_length, signPrefix_length]

def argumentEnvironment (kind : Kind) (ordinal remaining position value : Nat) (positive : Bool) (index : Fin 15) : Nat :=
  (history kind ordinal remaining position value positive)[index.val]'(by rw [history_length]; exact index.isLt)
def argumentFields : List (BuilderRegisterPack.Field 15) :=
  [.argument ⟨14, by decide⟩, .argument ⟨8, by decide⟩, .argument ⟨2, by decide⟩]
theorem environment_values (kind : Kind) (ordinal remaining position value : Nat) (positive : Bool) :
    List.ofFn (argumentEnvironment kind ordinal remaining position value positive) =
      history kind ordinal remaining position value positive := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, history_length]
  · intro index hLeft hRight
    simp only [List.getElem_ofFn, argumentEnvironment]
theorem packed_values (kind : Kind) (ordinal remaining position value : Nat) (positive : Bool) :
    BuilderRegisterPack.values argumentFields (argumentEnvironment kind ordinal remaining position value positive) =
      BuilderLiteralTokenSelector.frame positive value position := by
  cases kind <;> rfl

def positiveFields : List (BuilderRegisterPack.Field 0) :=
  [.constant 0, .constant 0, .constant 0, .constant 0, .constant 0, .constant 1]
def emptyEnvironment : Fin 0 → Nat := Fin.elim0
def signReadMachine (kind : Kind) : WorkMachine :=
  if kind = .positive then BuilderRegisterPack.machine positiveFields 0
  else BuilderPayloadFieldCopy.machine (stride kind) (signSlot kind) 8
def signMachine (kind : Kind) : WorkMachine :=
  if kind = .premise then WorkMachineChain.machine (signReadMachine kind) signFlipMachine
  else signReadMachine kind
def prepareMachine (kind : Kind) : WorkMachine :=
  WorkMachineChain.machine (BuilderPayloadFieldCopy.machine (stride kind) (valueSlot kind) 2)
    (WorkMachineChain.machine (signMachine kind) (BuilderRegisterPack.machine argumentFields 0))
def machine (kind : Kind) : WorkMachine :=
  WorkMachineChain.machine (prepareMachine kind) BuilderLiteralTokenSelector.machine

def signReadSteps (kind : Kind) (ordinal remaining position value : Nat) (positive : Bool) (payload : List Nat) : Nat :=
  if kind = .positive then BuilderRegisterPack.workSteps positiveFields emptyEnvironment []
  else BuilderPayloadFieldCopy.workSteps (stride kind) (signSlot kind) 8 ordinal
    (afterValue kind ordinal remaining position value) payload (signValue positive)
def signSteps (kind : Kind) (ordinal remaining position value : Nat) (positive : Bool) (payload : List Nat) : Nat :=
  if kind = .premise then signReadSteps kind ordinal remaining position value positive payload + 1 + 4
  else signReadSteps kind ordinal remaining position value positive payload
def prepareSteps {width : Nat} (source : Source width) (context : Context source.ordinal) : Nat :=
  BuilderPayloadFieldCopy.workSteps (stride source.kind) (valueSlot source.kind) 2 source.ordinal
    [context.remaining, context.position] (reader source context) source.originalLiteral.index.val + 1 +
      (signSteps source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val
        source.originalLiteral.positive (reader source context) + 1 +
          BuilderRegisterPack.workSteps argumentFields
            (argumentEnvironment source.kind source.ordinal context.remaining context.position
              source.originalLiteral.index.val source.selectedLiteral.positive) [])
def workSteps {width : Nat} (source : Source width) (context : Context source.ordinal) : Nat :=
  prepareSteps source context + 1 +
    BuilderLiteralTokenSelector.workSteps source.selectedLiteral.positive source.originalLiteral.index.val context.position

def valueOutside {width : Nat} (source : Source width) (outside : List WorkSymbol) : List WorkSymbol :=
  outside.drop (BuilderPayloadFieldCopy.allocation (stride source.kind) (valueSlot source.kind) 2 source.ordinal source.originalLiteral.index.val)
def signReadOutside {width : Nat} (source : Source width) (outside : List WorkSymbol) : List WorkSymbol :=
  if source.kind = .positive then (valueOutside source outside).drop 7
  else (valueOutside source outside).drop
    (BuilderPayloadFieldCopy.allocation (stride source.kind) (signSlot source.kind) 8 source.ordinal
      (signValue source.originalLiteral.positive))
def signOutside {width : Nat} (source : Source width) (outside : List WorkSymbol) : List WorkSymbol :=
  if source.kind = .premise then flipOutside source.originalLiteral.positive (signReadOutside source outside)
  else signReadOutside source outside
def prepareOlder {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) : List Nat :=
  older ++ (reader source context).reverse ++
    history source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val source.selectedLiteral.positive
def prepareOutside {width : Nat} (source : Source width) (context : Context source.ordinal) (outside : List WorkSymbol) : List WorkSymbol :=
  (signOutside source outside).drop
    (registerWord (BuilderLiteralTokenSelector.frame source.selectedLiteral.positive source.originalLiteral.index.val context.position)).length
def prepareTape {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkTape :=
  endTape (prepareOlder source context older ++
    BuilderLiteralTokenSelector.frame source.selectedLiteral.positive source.originalLiteral.index.val context.position)
    inside (prepareOutside source context outside)
def initialConfiguration {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine source.kind) (endTape (initialValues source context older) inside outside)
def finalConfiguration {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderLiteralTokenSelector.finalConfiguration source.selectedLiteral.positive source.originalLiteral.index.val context.position
      (prepareOlder source context older) inside (prepareOutside source context outside))
def observe := BuilderIndexedLiteralTokenSelector.observe

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond


def readOlder {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) : List Nat :=
  older ++ (reader source context).reverse ++ [source.ordinal] ++
    afterValue source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val

private theorem sign_read_workRunExact {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (signReadMachine source.kind)
      (signReadSteps source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val
        source.originalLiteral.positive (reader source context))
      (workStartConfiguration (signReadMachine source.kind)
        (endTape (readOlder source context older) inside (valueOutside source outside))) =
      some {state := (signReadMachine source.kind).acceptState, tape := endTape (readOlder source context older ++
          signHistory source.kind source.ordinal source.originalLiteral.positive) inside (signReadOutside source outside)} := by
  by_cases hKind : source.kind = .positive
  · have hSign : source.originalLiteral.positive = true := by
      cases source <;> simp only [Source.kind] at hKind
      · cases hKind
      · cases hKind
      · cases hKind
      · rfl
    have h := BuilderRegisterPack.workRunExact positiveFields 0 (readOlder source context older)
      emptyEnvironment [] inside (valueOutside source outside) rfl
    have hFields : BuilderRegisterPack.values positiveFields emptyEnvironment = [0,0,0,0,0,1] := rfl
    have hHistory : signHistory source.kind source.ordinal source.originalLiteral.positive = [0,0,0,0,0,1] := by
      rw [hKind, hSign]
      rfl
    have hWord : (registerWord ([0,0,0,0,0,1] : List Nat)).length = 7 := rfl
    simpa only [signReadMachine, signReadSteps, if_pos hKind, BuilderRegisterPack.initialConfiguration,
      BuilderRegisterPack.finalConfiguration, hFields, hHistory, List.ofFn_zero, List.append_nil,
      hWord, signReadOutside] using h
  · have h := BuilderPayloadFieldCopy.workRunExact (stride source.kind) (signSlot source.kind) 8 source.ordinal
      (reader source context) older
      (afterValue source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val)
      inside (valueOutside source outside) rfl (sign_field_lt source context hKind)
    simpa only [sign_field source context hKind, signReadMachine, signReadSteps, if_neg hKind,
      BuilderPayloadFieldCopy.initialConfiguration, BuilderPayloadFieldCopy.finalConfiguration,
      BuilderPayloadFieldCopy.initialValues, BuilderPayloadFieldCopy.finalValues,
      readOlder, signHistory, signPrefix, signReadOutside, List.append_assoc] using h

private theorem sign_workRunExact {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (signMachine source.kind)
      (signSteps source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val
        source.originalLiteral.positive (reader source context))
      (workStartConfiguration (signMachine source.kind)
        (endTape (readOlder source context older) inside (valueOutside source outside))) =
      some {state := (signMachine source.kind).acceptState, tape := endTape (prepareOlder source context older) inside (signOutside source outside)} := by
  have hRead := sign_read_workRunExact source context older inside outside
  by_cases hKind : source.kind = .premise
  · have hFlip := sign_flip_workRunExact source.originalLiteral.positive
      (readOlder source context older ++ signPrefix source.kind source.ordinal) inside (signReadOutside source outside)
    have h := chain_run _ _ _ _ _ _ _ hRead (by simpa only [signHistory, List.append_assoc] using hFlip)
    simpa only [signMachine, signSteps, if_pos hKind, Source.selectedLiteral, BoundedLiteral.negate,
      prepareOlder, history, readOlder, signHistory, signOutside, List.append_assoc] using h
  · simpa only [signMachine, signSteps, if_neg hKind, Source.selectedLiteral,
      prepareOlder, history, readOlder, signHistory, signOutside, List.append_assoc] using hRead

/-- Both operands are read from the original source; the final frame uses its canonical sign. -/
theorem prepare_workRunExact {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (prepareMachine source.kind) (prepareSteps source context)
      (workStartConfiguration (prepareMachine source.kind) (endTape (initialValues source context older) inside outside)) =
      some {state := (prepareMachine source.kind).acceptState, tape := prepareTape source context older inside outside} := by
  have hValue := BuilderPayloadFieldCopy.workRunExact (stride source.kind) (valueSlot source.kind) 2 source.ordinal
    (reader source context) older [context.remaining, context.position] inside outside rfl (value_field_lt source context)
  have hFirst : workRunExact? (BuilderPayloadFieldCopy.machine (stride source.kind) (valueSlot source.kind) 2)
      (BuilderPayloadFieldCopy.workSteps (stride source.kind) (valueSlot source.kind) 2 source.ordinal
        [context.remaining, context.position] (reader source context) source.originalLiteral.index.val)
      (workStartConfiguration (BuilderPayloadFieldCopy.machine (stride source.kind) (valueSlot source.kind) 2)
        (endTape (initialValues source context older) inside outside)) =
      some {state := (BuilderPayloadFieldCopy.machine (stride source.kind) (valueSlot source.kind) 2).acceptState, tape := endTape (readOlder source context older) inside (valueOutside source outside)} := by
    simpa only [value_field, BuilderPayloadFieldCopy.initialConfiguration, BuilderPayloadFieldCopy.finalConfiguration,
      BuilderPayloadFieldCopy.initialValues, BuilderPayloadFieldCopy.finalValues, initialValues,
      readOlder, valueOutside, afterValue, valueHistory, List.append_assoc, List.cons_append, List.nil_append] using hValue
  have hSign := sign_workRunExact source context older inside outside
  have hPack := BuilderRegisterPack.workRunExact argumentFields 0 (older ++ (reader source context).reverse)
    (argumentEnvironment source.kind source.ordinal context.remaining context.position
      source.originalLiteral.index.val source.selectedLiteral.positive) [] inside (signOutside source outside) rfl
  have hLast : workRunExact? (BuilderRegisterPack.machine argumentFields 0)
      (BuilderRegisterPack.workSteps argumentFields
        (argumentEnvironment source.kind source.ordinal context.remaining context.position
          source.originalLiteral.index.val source.selectedLiteral.positive) [])
      (workStartConfiguration (BuilderRegisterPack.machine argumentFields 0)
        (endTape (prepareOlder source context older) inside (signOutside source outside))) =
      some {state := (BuilderRegisterPack.machine argumentFields 0).acceptState, tape := prepareTape source context older inside outside} := by
    simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
      environment_values, packed_values, List.append_nil, prepareOlder, prepareTape, prepareOutside] using hPack
  exact chain_run _ _ _ _ _ _ _ hFirst (chain_run _ _ _ _ _ _ _ hSign hLast)

theorem workRunExact {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine source.kind) (workSteps source context)
      (initialConfiguration source context older inside outside) =
      some (finalConfiguration source context older inside outside) := by
  have hPrepare := prepare_workRunExact source context older inside outside
  have hSelect := BuilderLiteralTokenSelector.workRunExact source.selectedLiteral.positive source.originalLiteral.index.val
    context.position (prepareOlder source context older) inside (prepareOutside source context outside)
  exact WorkMachineChain.workRunExact _ _ _ _ _ _ _ hPrepare rfl hSelect

theorem run_compile_exact {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine source.kind)) (6 * workSteps source context)
      (encodeWorkConfiguration (initialConfiguration source context older inside outside)) =
      encodeWorkConfiguration (finalConfiguration source context older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact source context older inside outside)

theorem selected_index {width : Nat} (source : Source width) :
    source.selectedLiteral.index = source.originalLiteral.index := by
  unfold Source.selectedLiteral
  split <;> rfl

theorem canonical_result {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration source context older inside outside) =
      DirectToken.literalSlot source.selectedLiteral.emit context.position := by
  rw [finalConfiguration, observe, BuilderIndexedLiteralTokenSelector.observe_renamed,
    BuilderLiteralTokenSelector.canonical_result]
  simp only [BoundedLiteral.emit, selected_index, BuilderLiteralTokenSelector.literal]

theorem workRun_observes_literal {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    observe (workRun (machine source.kind) (workSteps source context)
      (initialConfiguration source context older inside outside)) =
      DirectToken.literalSlot source.selectedLiteral.emit context.position := by
  rw [workRun_eq_of_workRunExact _ _ _ _ (workRunExact source context older inside outside)]
  exact canonical_result source context older inside outside

theorem final_tape {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration source context older inside outside).tape =
      endTape (BuilderLiteralTokenSelector.finalValues source.selectedLiteral.positive source.originalLiteral.index.val
        context.position (prepareOlder source context older)) inside
          (BuilderLiteralTokenSelector.finalOutside source.selectedLiteral.positive source.originalLiteral.index.val
            context.position (prepareOutside source context outside)) := rfl

theorem original_frame_preserved {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) :
    ∃ scratch, BuilderLiteralTokenSelector.finalValues source.selectedLiteral.positive source.originalLiteral.index.val
      context.position (prepareOlder source context older) = initialValues source context older ++ scratch := by
  refine ⟨valueHistory source.kind source.ordinal source.originalLiteral.index.val ++
    signHistory source.kind source.ordinal source.selectedLiteral.positive ++
    BuilderLiteralTokenSelector.frame source.selectedLiteral.positive source.originalLiteral.index.val context.position ++
      (if context.position = 0 then [] else BuilderRegisterCompareResidual.outputValues
        (BuilderLiteralTokenSelector.comparisonResult source.originalLiteral.index.val context.position)), ?_⟩
  simp only [BuilderLiteralTokenSelector.finalValues, prepareOlder, initialValues, history, afterValue,
    List.append_assoc, List.cons_append, List.nil_append]

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
   WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
   WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
   WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩
private theorem field_good (stride slot count : Nat) : Good (BuilderPayloadFieldCopy.machine stride slot count) :=
  ⟨BuilderPayloadFieldCopy.rules_pairwise_query_distinct _ _ _, BuilderPayloadFieldCopy.noRuleAtAccept _ _ _,
   BuilderPayloadFieldCopy.noRuleAtReject _ _ _, BuilderPayloadFieldCopy.acceptState_ne_rejectState _ _ _⟩
private theorem pack_good {arity : Nat} (fields : List (BuilderRegisterPack.Field arity)) :
    Good (BuilderRegisterPack.machine fields 0) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct _ _, BuilderRegisterPack.noRuleAtAccept _ _,
   BuilderRegisterPack.noRuleAtReject _ _, BuilderRegisterPack.acceptState_ne_rejectState _ _⟩
private theorem signRead_good (kind : Kind) : Good (signReadMachine kind) := by
  unfold signReadMachine
  split
  · exact pack_good positiveFields
  · exact field_good _ _ _
private theorem sign_good (kind : Kind) : Good (signMachine kind) := by
  unfold signMachine
  split
  · exact chain_good _ _ (signRead_good kind) flip_good
  · exact signRead_good kind
private theorem prepare_good (kind : Kind) : Good (prepareMachine kind) :=
  chain_good _ _ (field_good _ _ _) (chain_good _ _ (sign_good kind) (pack_good argumentFields))
private theorem selector_good : Good BuilderLiteralTokenSelector.machine :=
  ⟨BuilderLiteralTokenSelector.rules_pairwise_query_distinct, BuilderLiteralTokenSelector.noRuleAtAccept,
   BuilderLiteralTokenSelector.noRuleAtReject, BuilderLiteralTokenSelector.acceptState_ne_rejectState⟩
private theorem good (kind : Kind) : Good (machine kind) := chain_good _ _ (prepare_good kind) selector_good

theorem rules_pairwise_query_distinct (kind : Kind) : (machine kind).rules.Pairwise WorkMachineChain.QueryDistinct := (good kind).1
theorem noRuleAtAccept (kind : Kind) : WorkMachineChain.NoRuleAtAccept (machine kind) := (good kind).2.1
theorem noRuleAtReject (kind : Kind) : WorkMachineProgramGraph.NoRuleAt (machine kind) (machine kind).rejectState := (good kind).2.2.1
theorem acceptState_ne_rejectState (kind : Kind) : (machine kind).acceptState ≠ (machine kind).rejectState := (good kind).2.2.2
theorem noRuleAtPadding (kind : Kind) : WorkMachineProgramGraph.NoRuleAt (machine kind) (WorkMachineChain.secondState 2) :=
  WorkMachineChain.noRuleAtAccept (prepareMachine kind) {BuilderLiteralTokenSelector.machine with acceptState := 2}
    (WorkMachineProgramGraph.noRuleAt_globalDead BuilderLiteralTokenSelector.graph)


theorem premise_canonical_order {width : Nat} (premises : List (BoundedLiteral width))
    (conclusion : BoundedLiteral width) (index : Fin premises.length) :
    (Source.premise premises conclusion index).selectedLiteral =
      (BoundedClause.negated premises ++ [conclusion])[index.val]'(by
        simp only [BoundedClause.negated, List.length_append, List.length_map, List.length_cons, List.length_nil]
        have h := index.isLt
        omega) := by
  simp only [Source.selectedLiteral, Source.kind, ite_true, Source.originalLiteral, BoundedClause.negated]
  rw [List.getElem_append_left]
  · rw [List.getElem_map]
  · simpa only [List.length_map] using index.isLt

theorem conclusion_canonical_order {width : Nat} (premises : List (BoundedLiteral width))
    (conclusion : BoundedLiteral width) :
    (Source.conclusion premises conclusion).selectedLiteral =
      (BoundedClause.negated premises ++ [conclusion])[premises.length]'(by
        simp only [BoundedClause.negated, List.length_append, List.length_map, List.length_cons, List.length_nil]
        omega) := by
  simp only [Source.selectedLiteral, Source.kind, reduceCtorEq, ite_false, Source.originalLiteral, BoundedClause.negated]
  rw [List.getElem_append_right]
  · simp only [List.length_map, Nat.sub_self, List.getElem_cons_zero]
  · simp only [List.length_map]
    exact Nat.le_refl _

def valueSpanPolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  BuilderPayloadFieldCopy.spanPolynomial (stride kind) (valueSlot kind) 2 bound
def signReadSpanPolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  if kind = .positive then .add (BuilderRegisterPack.spanPolynomial positiveFields bound) bound
  else BuilderPayloadFieldCopy.spanPolynomial (stride kind) (signSlot kind) 8 bound
def signSpanPolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  .add (signReadSpanPolynomial kind bound) (.constant 1)
def prepareSpanPolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  let middle := signSpanPolynomial kind (valueSpanPolynomial kind bound)
  .add (BuilderRegisterPack.spanPolynomial argumentFields middle) middle
def spanPolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  BuilderLiteralTokenSelector.spanPolynomial (prepareSpanPolynomial kind bound)
def signReadTimePolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  if kind = .positive then BuilderRegisterPack.rawTimePolynomial positiveFields bound
  else BuilderPayloadFieldCopy.rawTimePolynomial (stride kind) (signSlot kind) 8 bound
def signTimePolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  .add (signReadTimePolynomial kind bound) (.constant 30)
def prepareRawTimePolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderPayloadFieldCopy.rawTimePolynomial (stride kind) (valueSlot kind) 2 bound) (.constant 6))
    (.add (.add (signTimePolynomial kind (valueSpanPolynomial kind bound)) (.constant 6))
      (BuilderRegisterPack.rawTimePolynomial argumentFields (signSpanPolynomial kind (valueSpanPolynomial kind bound))))
def rawTimePolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (prepareRawTimePolynomial kind bound) (.constant 6))
    (BuilderLiteralTokenSelector.rawTimePolynomial (prepareSpanPolynomial kind bound))

private theorem flip_span (positive : Bool) (older : List Nat) (outside : List WorkSymbol) :
    (registerWord (older ++ [signValue (!positive)])).length + (flipOutside positive outside).length ≤
      (registerWord (older ++ [signValue positive])).length + outside.length + 1 := by
  cases positive <;>
    simp only [signValue, flipOutside, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
      registerWord_append, registerWord, List.length_append, List.length_reverse, List.length_cons,
      List.length_nil, List.length_replicate, List.length_drop] <;> omega

private theorem sign_read_bounds {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (readOlder source context older)).length + (valueOutside source outside).length ≤ bound.eval input) :
    (registerWord (readOlder source context older ++ signHistory source.kind source.ordinal source.originalLiteral.positive)).length +
      (signReadOutside source outside).length ≤ (signReadSpanPolynomial source.kind bound).eval input ∧
    6 * signReadSteps source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val
      source.originalLiteral.positive (reader source context) ≤ (signReadTimePolynomial source.kind bound).eval input := by
  by_cases hKind : source.kind = .positive
  · have hSign : source.originalLiteral.positive = true := by
      cases source <;> simp only [Source.kind] at hKind
      · cases hKind
      · cases hKind
      · cases hKind
      · rfl
    have hInput : (registerWord (readOlder source context older ++ List.ofFn emptyEnvironment ++ [])).length ≤ bound.eval input := by
      simpa only [List.ofFn_zero, List.append_nil] using Nat.le_trans (Nat.le_add_right _ _) hSpan
    have h := BuilderRegisterPack.source_polynomial_bounds positiveFields bound input
      (readOlder source context older) emptyEnvironment [] hInput
    have hFields : BuilderRegisterPack.values positiveFields emptyEnvironment =
        signHistory source.kind source.ordinal source.originalLiteral.positive := by
      rw [hKind, hSign]
      rfl
    simp only [List.ofFn_zero, List.append_nil, hFields, hKind] at h
    constructor
    · simp only [signReadSpanPolynomial, hKind, ite_true, NatPolynomial.eval_add, signReadOutside, List.length_drop]
      have hOutside : (valueOutside source outside).length ≤ bound.eval input := by omega
      omega
    · simpa only [signReadTimePolynomial, signReadSteps, hKind, ite_true] using h.2
  · have hInput : (registerWord (BuilderPayloadFieldCopy.initialValues (reader source context) older source.ordinal
        (afterValue source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val))).length +
        (valueOutside source outside).length ≤ bound.eval input := by
      simpa only [BuilderPayloadFieldCopy.initialValues, readOlder, List.append_assoc] using hSpan
    have h := BuilderPayloadFieldCopy.source_polynomial_bounds (stride source.kind) (signSlot source.kind) 8 source.ordinal
      (reader source context) older
      (afterValue source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val)
      (valueOutside source outside) bound input rfl (sign_field_lt source context hKind) hInput
    simpa only [sign_field source context hKind, BuilderPayloadFieldCopy.finalValues, BuilderPayloadFieldCopy.initialValues,
      signReadSpanPolynomial, signReadTimePolynomial, signReadSteps, signReadOutside, if_neg hKind,
      readOlder, signHistory, signPrefix, List.append_assoc] using h

private theorem sign_bounds {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (readOlder source context older)).length + (valueOutside source outside).length ≤ bound.eval input) :
    (registerWord (prepareOlder source context older)).length + (signOutside source outside).length ≤
      (signSpanPolynomial source.kind bound).eval input ∧
    6 * signSteps source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val
      source.originalLiteral.positive (reader source context) ≤ (signTimePolynomial source.kind bound).eval input := by
  have h := sign_read_bounds source context older outside bound input hSpan
  by_cases hKind : source.kind = .premise
  · have hFlip := flip_span source.originalLiteral.positive
      (readOlder source context older ++ signPrefix source.kind source.ordinal) (signReadOutside source outside)
    simp only [List.append_assoc] at hFlip
    simp only [signHistory] at h
    constructor
    · simp only [prepareOlder, history, Source.selectedLiteral, if_pos hKind, BoundedLiteral.negate,
        signHistory, signOutside, signSpanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant,
        readOlder, List.append_assoc] at h hFlip ⊢
      omega
    · simp only [signSteps, if_pos hKind, signTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega
  · constructor
    · simpa only [prepareOlder, history, Source.selectedLiteral, if_neg hKind, signOutside,
        signSpanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant, readOlder, List.append_assoc]
        using Nat.le_trans h.1 (Nat.le_add_right _ 1)
    · simp only [signSteps, if_neg hKind, signTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega

theorem prepare_source_polynomial_bounds {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues source context older)).length + outside.length ≤ bound.eval input) :
    (registerWord (prepareOlder source context older ++
      BuilderLiteralTokenSelector.frame source.selectedLiteral.positive source.originalLiteral.index.val context.position)).length +
        (prepareOutside source context outside).length ≤ (prepareSpanPolynomial source.kind bound).eval input ∧
    6 * prepareSteps source context ≤ (prepareRawTimePolynomial source.kind bound).eval input := by
  have hInput : (registerWord (BuilderPayloadFieldCopy.initialValues (reader source context) older source.ordinal
      [context.remaining, context.position])).length + outside.length ≤ bound.eval input := by
    simpa only [BuilderPayloadFieldCopy.initialValues, initialValues, List.append_assoc, List.cons_append, List.nil_append] using hSpan
  have hValue := BuilderPayloadFieldCopy.source_polynomial_bounds (stride source.kind) (valueSlot source.kind) 2 source.ordinal
    (reader source context) older [context.remaining, context.position] outside bound input rfl
    (value_field_lt source context) hInput
  simp only [value_field] at hValue
  have hMiddle : (registerWord (readOlder source context older)).length + (valueOutside source outside).length ≤
      (valueSpanPolynomial source.kind bound).eval input := by
    simpa only [BuilderPayloadFieldCopy.finalValues, BuilderPayloadFieldCopy.initialValues, valueSpanPolynomial,
      valueOutside, readOlder, afterValue, valueHistory, List.append_assoc, List.cons_append, List.nil_append] using hValue.1
  have hSign := sign_bounds source context older outside (valueSpanPolynomial source.kind bound) input hMiddle
  have hPackInput : (registerWord ((older ++ (reader source context).reverse) ++
      List.ofFn (argumentEnvironment source.kind source.ordinal context.remaining context.position
        source.originalLiteral.index.val source.selectedLiteral.positive) ++ [])).length ≤
        (signSpanPolynomial source.kind (valueSpanPolynomial source.kind bound)).eval input := by
    simpa only [environment_values, List.append_nil, prepareOlder] using Nat.le_trans (Nat.le_add_right _ _) hSign.1
  have hPack := BuilderRegisterPack.source_polynomial_bounds argumentFields
    (signSpanPolynomial source.kind (valueSpanPolynomial source.kind bound)) input
    (older ++ (reader source context).reverse)
    (argumentEnvironment source.kind source.ordinal context.remaining context.position
      source.originalLiteral.index.val source.selectedLiteral.positive) [] hPackInput
  simp only [environment_values, packed_values, List.append_nil] at hPack
  constructor
  · simp only [prepareSpanPolynomial, NatPolynomial.eval_add, prepareOutside, List.length_drop, prepareOlder]
    have hExterior : (signOutside source outside).length ≤
        (signSpanPolynomial source.kind (valueSpanPolynomial source.kind bound)).eval input := by omega
    omega
  · simp only [prepareSteps, prepareRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem source_polynomial_bounds {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues source context older)).length + outside.length ≤ bound.eval input) :
    (registerWord (BuilderLiteralTokenSelector.finalValues source.selectedLiteral.positive source.originalLiteral.index.val
      context.position (prepareOlder source context older))).length +
        (BuilderLiteralTokenSelector.finalOutside source.selectedLiteral.positive source.originalLiteral.index.val
          context.position (prepareOutside source context outside)).length ≤ (spanPolynomial source.kind bound).eval input ∧
    6 * workSteps source context ≤ (rawTimePolynomial source.kind bound).eval input := by
  have hPrepare := prepare_source_polynomial_bounds source context older outside bound input hSpan
  have hSelect := BuilderLiteralTokenSelector.source_polynomial_bounds source.selectedLiteral.positive
    source.originalLiteral.index.val context.position (prepareOlder source context older) (prepareOutside source context outside)
    (prepareSpanPolynomial source.kind bound) input hPrepare.1
  constructor
  · exact hSelect.1
  · simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderPayloadLiteralTokenSelector
