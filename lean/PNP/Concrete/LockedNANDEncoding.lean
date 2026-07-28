/-
Copyright (c) 2026 PNP Labs.

Canonical, fail-closed encodings for finite topological NAND circuits and
locked-NAND threshold instances.  The codec is deliberately separate from the
builder machine: it fixes the bytes that the machine must emit and gives the
later reduction a concrete language boundary.
-/

import PNP.Concrete.BitString
import PNP.LockedNANDGlobalSemanticThreshold

namespace PNP
namespace Concrete
namespace LockedNAND

open DirectWire
open DirectWire.LockedNANDTrace

/-! ## Untyped finite syntax at the bitstring boundary -/

inductive RawSource where
  | input (index : Nat)
  | constant (value : Bool)
  | gate (index : Nat)
deriving BEq, DecidableEq, Repr

structure RawGate where
  left : RawSource
  right : RawSource
deriving BEq, DecidableEq, Repr

structure RawCircuit where
  inputCount : Nat
  gates : List RawGate
  output : RawSource
deriving BEq, DecidableEq, Repr

structure RawCandidate where
  inputCount : Nat
  gates : List RawGate
  outputs : List RawSource
deriving BEq, DecidableEq, Repr

structure RawLockedInstance where
  candidate : RawCandidate
  baseline : Nat
deriving BEq, DecidableEq, Repr

def RawSource.wellFormed (inputs priorGates : Nat) : RawSource → Bool
  | .input index => index < inputs
  | .constant _ => true
  | .gate index => index < priorGates

def RawGate.wellFormed (inputs priorGates : Nat) (gate : RawGate) : Bool :=
  gate.left.wellFormed inputs priorGates &&
    gate.right.wellFormed inputs priorGates

def rawGatesWellFormed (inputs : Nat) : Nat → List RawGate → Bool
  | _, [] => true
  | priorGates, gate :: rest =>
      gate.wellFormed inputs priorGates &&
        rawGatesWellFormed inputs (priorGates + 1) rest

def RawCircuit.wellFormed (circuit : RawCircuit) : Bool :=
  rawGatesWellFormed circuit.inputCount 0 circuit.gates &&
    circuit.output.wellFormed circuit.inputCount circuit.gates.length

def rawOutputsWellFormed (inputs gates : Nat) : List RawSource → Bool
  | [] => true
  | output :: rest =>
      output.wellFormed inputs gates &&
        rawOutputsWellFormed inputs gates rest

def RawCandidate.wellFormed (candidate : RawCandidate) : Bool :=
  rawGatesWellFormed candidate.inputCount 0 candidate.gates &&
    rawOutputsWellFormed candidate.inputCount candidate.gates.length
      candidate.outputs

/-! ## Direct semantics of the untyped boundary syntax -/

def RawSource.eval (input : Nat → Bool) (gateValues : List Bool) :
    RawSource → Bool
  | .input index => input index
  | .constant value => value
  | .gate index => gateValues.getD index false

def RawGate.eval (input : Nat → Bool) (gateValues : List Bool)
    (gate : RawGate) : Bool :=
  boolNand (gate.left.eval input gateValues)
    (gate.right.eval input gateValues)

def evalRawGatesAux (input : Nat → Bool) :
    List Bool → List RawGate → List Bool
  | values, [] => values
  | values, gate :: rest =>
      evalRawGatesAux input
        (values ++ [gate.eval input values]) rest

def RawCircuit.eval (circuit : RawCircuit) (input : Nat → Bool) : Bool :=
  let gateValues := evalRawGatesAux input [] circuit.gates
  circuit.output.eval input gateValues

theorem evalRawGatesAux_append (input : Nat → Bool)
    (values : List Bool) (first second : List RawGate) :
    evalRawGatesAux input values (first ++ second) =
      evalRawGatesAux input (evalRawGatesAux input values first) second := by
  induction first generalizing values with
  | nil => rfl
  | cons gate rest ih =>
      simp only [List.cons_append, evalRawGatesAux]
      exact ih (values ++ [gate.eval input values])

theorem evalRawGatesAux_length (input : Nat → Bool)
    (values : List Bool) (gates : List RawGate) :
    (evalRawGatesAux input values gates).length =
      values.length + gates.length := by
  induction gates generalizing values with
  | nil => simp [evalRawGatesAux]
  | cons gate rest ih =>
      rw [evalRawGatesAux, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-! ## Legacy output normalization -/

/-- Normalize a boundary output to an actual gate output.  This is the
versioned reconstruction of the historical UFS-002 normalization rule. -/
def RawCircuit.normalize (circuit : RawCircuit) : RawCircuit :=
  match circuit.output with
  | .gate _ => circuit
  | .input index =>
      let first := circuit.gates.length
      { inputCount := circuit.inputCount
        gates := circuit.gates ++
          [ { left := .input index, right := .constant true }
          , { left := .gate first, right := .gate first } ]
        output := .gate (first + 1) }
  | .constant false =>
      let first := circuit.gates.length
      { inputCount := circuit.inputCount
        gates := circuit.gates ++
          [{ left := .constant true, right := .constant true }]
        output := .gate first }
  | .constant true =>
      let first := circuit.gates.length
      { inputCount := circuit.inputCount
        gates := circuit.gates ++
          [{ left := .constant false, right := .constant false }]
        output := .gate first }

def RawCircuit.normalizationAddedGates (circuit : RawCircuit) : Nat :=
  match circuit.output with
  | .gate _ => 0
  | .input _ => 2
  | .constant _ => 1

theorem RawCircuit.normalize_gate (circuit : RawCircuit) (index : Nat)
    (h : circuit.output = .gate index) :
    circuit.normalize = circuit := by
  simp [RawCircuit.normalize, h]

theorem RawCircuit.normalize_idempotent (circuit : RawCircuit) :
    circuit.normalize.normalize = circuit.normalize := by
  cases circuit with
  | mk inputs gates output =>
      cases output with
      | input index => simp [RawCircuit.normalize]
      | gate index => rfl
      | constant value =>
          cases value <;> simp [RawCircuit.normalize]

theorem RawCircuit.normalize_eval (circuit : RawCircuit)
    (input : Nat → Bool) :
    circuit.normalize.eval input = circuit.eval input := by
  cases circuit with
  | mk inputs gates output =>
      cases output with
      | gate index => rfl
      | input index =>
          let values := evalRawGatesAux input [] gates
          have valuesLength : values.length = gates.length := by
            simp [values, evalRawGatesAux_length]
          cases inputValue : input index with
          | false =>
              simp only [RawCircuit.normalize, RawCircuit.eval,
                evalRawGatesAux_append, RawSource.eval]
              rw [inputValue]
              change
                (evalRawGatesAux input values
                    [{ left := .input index, right := .constant true },
                     { left := .gate gates.length,
                       right := .gate gates.length }]).getD
                    (gates.length + 1) false =
                  false
              simp only [evalRawGatesAux]
              rw [← valuesLength]
              simp [RawGate.eval, RawSource.eval,
                inputValue, boolNand]
          | true =>
              simp only [RawCircuit.normalize, RawCircuit.eval,
                evalRawGatesAux_append, RawSource.eval]
              rw [inputValue]
              change
                (evalRawGatesAux input values
                    [{ left := .input index, right := .constant true },
                     { left := .gate gates.length,
                       right := .gate gates.length }]).getD
                    (gates.length + 1) false =
                  true
              simp only [evalRawGatesAux]
              rw [← valuesLength]
              simp [RawGate.eval, RawSource.eval,
                inputValue, boolNand]
      | constant value =>
          let values := evalRawGatesAux input [] gates
          have valuesLength : values.length = gates.length := by
            simp [values, evalRawGatesAux_length]
          cases value with
          | false =>
              simp only [RawCircuit.normalize, RawCircuit.eval,
                evalRawGatesAux_append]
              change
                (evalRawGatesAux input values
                    [{ left := .constant true,
                       right := .constant true }]).getD
                    gates.length false =
                  false
              simp only [evalRawGatesAux]
              rw [← valuesLength]
              simp [RawGate.eval, RawSource.eval, boolNand]
          | true =>
              simp only [RawCircuit.normalize, RawCircuit.eval,
                evalRawGatesAux_append]
              change
                (evalRawGatesAux input values
                    [{ left := .constant false,
                       right := .constant false }]).getD
                    gates.length false =
                  true
              simp only [evalRawGatesAux]
              rw [← valuesLength]
              simp [RawGate.eval, RawSource.eval, boolNand]

/-! ## Constructive elaboration into the intrinsic syntax -/

def RawSource.elaborate (inputs gates : Nat) :
    RawSource → Option (Source inputs gates)
  | .input index =>
      if valid : index < inputs then
        some (.input ⟨index, valid⟩)
      else
        none
  | .constant value => some (.constant value)
  | .gate index =>
      if valid : index < gates then
        some (.gate ⟨index, valid⟩)
      else
        none

def RawGate.elaborate (inputs gates : Nat) (gate : RawGate) :
    Option (Gate inputs gates) :=
  match gate.left.elaborate inputs gates,
      gate.right.elaborate inputs gates with
  | some left, some right => some { left := left, right := right }
  | _, _ => none

structure PackedProgram (inputs : Nat) where
  gateCount : Nat
  program : Program inputs gateCount

def elaborateGatesAux {inputs gates : Nat}
    (program : Program inputs gates) :
    List RawGate → Option (PackedProgram inputs)
  | [] => some { gateCount := gates, program := program }
  | gate :: rest =>
      match gate.elaborate inputs gates with
      | none => none
      | some elaborated =>
          elaborateGatesAux (.snoc program elaborated) rest

def elaborateGates (inputs : Nat) (gates : List RawGate) :
    Option (PackedProgram inputs) :=
  elaborateGatesAux (Program.empty : Program inputs 0) gates

structure PackedCircuit where
  inputCount : Nat
  circuit : Circuit inputCount

structure PackedOutputWord (inputs gates : Nat) where
  outputCount : Nat
  outputs : OutputWord inputs gates outputCount

def elaborateSources (inputs gates : Nat) :
    List RawSource → Option (PackedOutputWord inputs gates)
  | [] =>
      some
        { outputCount := 0
          outputs := .nil }
  | source :: rest =>
      match source.elaborate inputs gates,
          elaborateSources inputs gates rest with
      | some elaborated, some packed =>
          some
            { outputCount := packed.outputCount + 1
              outputs := .cons elaborated packed.outputs }
      | _, _ => none

structure PackedCandidate where
  inputCount : Nat
  gateCount : Nat
  outputCount : Nat
  candidate : Candidate inputCount gateCount outputCount

def RawCandidate.elaborate (raw : RawCandidate) : Option PackedCandidate :=
  match elaborateGates raw.inputCount raw.gates with
  | none => none
  | some packedProgram =>
      match elaborateSources raw.inputCount packedProgram.gateCount
          raw.outputs with
      | none => none
      | some packedOutputs =>
          some
            { inputCount := raw.inputCount
              gateCount := packedProgram.gateCount
              outputCount := packedOutputs.outputCount
              candidate :=
                { program := packedProgram.program
                  outputs := packedOutputs.outputs } }

structure PackedLockedInstance where
  inputCount : Nat
  gateCount : Nat
  outputCount : Nat
  candidate : Candidate inputCount gateCount outputCount
  baseline : Nat

def RawLockedInstance.elaborate
    (raw : RawLockedInstance) : Option PackedLockedInstance :=
  match raw.candidate.elaborate with
  | none => none
  | some packed =>
      some
        { inputCount := packed.inputCount
          gateCount := packed.gateCount
          outputCount := packed.outputCount
          candidate := packed.candidate
          baseline := raw.baseline }

/-- Elaborate after the legacy output normalization.  Every successful result
has an actual final gate, so it can inhabit the intrinsic `Circuit` type. -/
def RawCircuit.elaborate (raw : RawCircuit) : Option PackedCircuit :=
  let normalized := raw.normalize
  match elaborateGates normalized.inputCount normalized.gates with
  | none => none
  | some packed =>
      match normalized.output.elaborate normalized.inputCount
          packed.gateCount with
      | some (.gate outputGate) =>
          some
            { inputCount := normalized.inputCount
              circuit :=
                { gateCount := packed.gateCount
                  program := packed.program
                  outputGate := outputGate } }
      | _ => none

theorem RawCircuit.elaborate_normalize (raw : RawCircuit) :
    raw.normalize.elaborate = raw.elaborate := by
  unfold RawCircuit.elaborate
  rw [RawCircuit.normalize_idempotent]

/-- Satisfaction at the external boundary is the satisfaction of the
constructively elaborated normalized circuit.  Failed elaboration is
fail-closed. -/
def RawCircuit.Satisfiable (raw : RawCircuit) : Prop :=
  match raw.elaborate with
  | some packed => packed.circuit.Satisfiable
  | none => False

theorem RawCircuit.normalize_satisfiable (raw : RawCircuit) :
    raw.normalize.Satisfiable ↔ raw.Satisfiable := by
  unfold RawCircuit.Satisfiable
  rw [RawCircuit.elaborate_normalize]

def fallbackCircuit : Circuit 0 :=
  { gateCount := 1
    program :=
      .snoc .empty
        { left := .constant true
          right := .constant true }
    outputGate := ⟨0, by decide⟩ }

theorem fallbackCircuit_not_satisfiable :
    ¬ fallbackCircuit.Satisfiable := by
  rintro ⟨input, outputTrue⟩
  change false = true at outputTrue
  exact Bool.noConfusion outputTrue

/-! ## Reification of the existing intrinsically typed construction -/

def RawSource.ofSource {inputs gates : Nat} :
    Source inputs gates → RawSource
  | .input index => .input index.val
  | .constant value => .constant value
  | .gate index => .gate index.val

def RawGate.ofGate {inputs gates : Nat} (gate : Gate inputs gates) : RawGate :=
  { left := RawSource.ofSource gate.left
    right := RawSource.ofSource gate.right }

theorem RawSource.elaborate_ofSource {inputs gates : Nat}
    (source : Source inputs gates) :
    (RawSource.ofSource source).elaborate inputs gates =
      some source := by
  cases source with
  | input index =>
      simp [RawSource.ofSource, RawSource.elaborate, index.isLt]
  | constant value =>
      rfl
  | gate index =>
      simp [RawSource.ofSource, RawSource.elaborate, index.isLt]

theorem RawGate.elaborate_ofGate {inputs gates : Nat}
    (gate : Gate inputs gates) :
    (RawGate.ofGate gate).elaborate inputs gates =
      some gate := by
  cases gate with
  | mk left right =>
      simp [RawGate.ofGate, RawGate.elaborate,
        RawSource.elaborate_ofSource]

def rawProgramGates {inputs : Nat} :
    {gates : Nat} → Program inputs gates → List RawGate
  | 0, .empty => []
  | _ + 1, .snoc initial gate =>
      rawProgramGates initial ++ [RawGate.ofGate gate]

def rawOutputSources {inputs gates : Nat} :
    {outputs : Nat} → OutputWord inputs gates outputs → List RawSource
  | 0, .nil => []
  | _ + 1, .cons head tail =>
      RawSource.ofSource head :: rawOutputSources tail

theorem elaborateGatesAux_append {inputs gates : Nat}
    (program : Program inputs gates) (first second : List RawGate) :
    elaborateGatesAux program (first ++ second) =
      match elaborateGatesAux program first with
      | none => none
      | some packed => elaborateGatesAux packed.program second := by
  induction first generalizing gates with
  | nil => rfl
  | cons gate rest ih =>
      simp only [List.cons_append, elaborateGatesAux]
      cases elaborated : gate.elaborate inputs gates with
      | none => rfl
      | some typedGate =>
          exact ih (.snoc program typedGate)

theorem elaborateGates_rawProgramGates {inputs gates : Nat}
    (program : Program inputs gates) :
    elaborateGates inputs (rawProgramGates program) =
      some { gateCount := gates, program := program } := by
  induction program with
  | empty => rfl
  | @snoc gates initial gate ih =>
      unfold elaborateGates at ih ⊢
      rw [rawProgramGates, elaborateGatesAux_append, ih]
      simp [elaborateGatesAux, RawGate.elaborate_ofGate]

theorem elaborateSources_rawOutputSources
    {inputs gates outputs : Nat}
    (word : OutputWord inputs gates outputs) :
    elaborateSources inputs gates (rawOutputSources word) =
      some { outputCount := outputs, outputs := word } := by
  induction word with
  | nil => rfl
  | @cons outputs head tail ih =>
      simp [rawOutputSources, elaborateSources,
        RawSource.elaborate_ofSource, ih]

def RawCircuit.ofCircuit {inputs : Nat} (circuit : Circuit inputs) : RawCircuit :=
  { inputCount := inputs
    gates := rawProgramGates circuit.program
    output := .gate circuit.outputGate.val }

theorem RawCircuit.elaborate_ofCircuit {inputs : Nat}
    (circuit : Circuit inputs) :
    (RawCircuit.ofCircuit circuit).elaborate =
      some { inputCount := inputs, circuit := circuit } := by
  cases circuit with
  | mk gates program outputGate =>
      simp [RawCircuit.ofCircuit, RawCircuit.elaborate,
        RawCircuit.normalize, elaborateGates_rawProgramGates,
        RawSource.elaborate, outputGate.isLt]

def RawCandidate.ofCandidate {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) : RawCandidate :=
  { inputCount := inputs
    gates := rawProgramGates candidate.program
    outputs := rawOutputSources candidate.outputs }

def RawLockedInstance.ofCandidate {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (baseline : Nat) :
    RawLockedInstance :=
  { candidate := RawCandidate.ofCandidate candidate
    baseline := baseline }

theorem RawCandidate.elaborate_ofCandidate
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    (RawCandidate.ofCandidate candidate).elaborate =
      some
        { inputCount := inputs
          gateCount := gates
          outputCount := outputs
          candidate := candidate } := by
  cases candidate with
  | mk program word =>
      simp [RawCandidate.ofCandidate, RawCandidate.elaborate,
        elaborateGates_rawProgramGates,
        elaborateSources_rawOutputSources]

theorem RawLockedInstance.elaborate_ofCandidate
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (baseline : Nat) :
    (RawLockedInstance.ofCandidate candidate baseline).elaborate =
      some
        { inputCount := inputs
          gateCount := gates
          outputCount := outputs
          candidate := candidate
          baseline := baseline } := by
  simp [RawLockedInstance.ofCandidate, RawLockedInstance.elaborate,
    RawCandidate.elaborate_ofCandidate]

def lockedInstanceOfCircuit {inputs : Nat} (circuit : Circuit inputs) :
    RawLockedInstance :=
  RawLockedInstance.ofCandidate
    (DirectWire.LockedNANDGlobalCandidates.fullCandidate circuit)
    (DirectWire.lockedBaselineCount circuit.program)

/-! ## Fixed four-bit token alphabet -/

inductive Token where
  | version0
  | unit
  | natEnd
  | input
  | constantFalse
  | constantTrue
  | gate
  | gateEnd
  | programEnd
  | outputsEnd
  | threshold
  | instanceEnd
deriving BEq, DecidableEq, Repr

namespace Token

def bits : Token → BitString
  | .version0 => [false, false, false, false]
  | .unit => [false, false, false, true]
  | .natEnd => [false, false, true, false]
  | .input => [false, false, true, true]
  | .constantFalse => [false, true, false, false]
  | .constantTrue => [false, true, false, true]
  | .gate => [false, true, true, false]
  | .gateEnd => [false, true, true, true]
  | .programEnd => [true, false, false, false]
  | .outputsEnd => [true, false, false, true]
  | .threshold => [true, false, true, false]
  | .instanceEnd => [true, false, true, true]

/-- The four unused code points are rejected rather than treated as aliases. -/
def ofBits : Bool → Bool → Bool → Bool → Option Token
  | false, false, false, false => some .version0
  | false, false, false, true => some .unit
  | false, false, true, false => some .natEnd
  | false, false, true, true => some .input
  | false, true, false, false => some .constantFalse
  | false, true, false, true => some .constantTrue
  | false, true, true, false => some .gate
  | false, true, true, true => some .gateEnd
  | true, false, false, false => some .programEnd
  | true, false, false, true => some .outputsEnd
  | true, false, true, false => some .threshold
  | true, false, true, true => some .instanceEnd
  | true, true, _, _ => none

theorem ofBits_bits (token : Token) :
    match token.bits with
    | [a, b, c, d] => ofBits a b c d = some token
    | _ => False := by
  cases token <;> rfl

end Token

def encodeTokens : List Token → BitString
  | [] => []
  | token :: rest => token.bits ++ encodeTokens rest

def decodeTokens : BitString → Option (List Token)
  | [] => some []
  | a :: b :: c :: d :: rest =>
      match Token.ofBits a b c d, decodeTokens rest with
      | some token, some tokens => some (token :: tokens)
      | _, _ => none
  | _ => none

theorem decodeTokens_encodeTokens (tokens : List Token) :
    decodeTokens (encodeTokens tokens) = some tokens := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      cases token <;> simp [encodeTokens, Token.bits, decodeTokens, Token.ofBits, ih]

/-! ## Canonical token grammar -/

def encodeNatTokens : Nat → List Token
  | 0 => [.natEnd]
  | value + 1 => .unit :: encodeNatTokens value

def decodeNatTokens : List Token → Option (Nat × List Token)
  | [] => none
  | .unit :: rest =>
      match decodeNatTokens rest with
      | none => none
      | some (value, suffix) => some (value + 1, suffix)
  | .natEnd :: rest => some (0, rest)
  | _ :: _ => none

theorem decodeNatTokens_encodeNatTokens_append
    (value : Nat) (suffix : List Token) :
    decodeNatTokens (encodeNatTokens value ++ suffix) =
      some (value, suffix) := by
  induction value with
  | zero => rfl
  | succ value ih =>
      change
        (match decodeNatTokens (encodeNatTokens value ++ suffix) with
          | none => none
          | some (decoded, rest) => some (decoded + 1, rest)) =
            some (value + 1, suffix)
      rw [ih]

def encodeSourceTokens : RawSource → List Token
  | .input index => .input :: encodeNatTokens index
  | .constant false => [.constantFalse]
  | .constant true => [.constantTrue]
  | .gate index => .gate :: encodeNatTokens index

def decodeSourceTokens : List Token → Option (RawSource × List Token)
  | [] => none
  | .input :: rest =>
      match decodeNatTokens rest with
      | some (index, suffix) => some (.input index, suffix)
      | none => none
  | .constantFalse :: rest => some (.constant false, rest)
  | .constantTrue :: rest => some (.constant true, rest)
  | .gate :: rest =>
      match decodeNatTokens rest with
      | some (index, suffix) => some (.gate index, suffix)
      | none => none
  | _ :: _ => none

theorem decodeSourceTokens_encodeSourceTokens_append
    (source : RawSource) (suffix : List Token) :
    decodeSourceTokens (encodeSourceTokens source ++ suffix) =
      some (source, suffix) := by
  cases source with
  | input index =>
      simp only [encodeSourceTokens, List.cons_append, decodeSourceTokens]
      rw [decodeNatTokens_encodeNatTokens_append]
  | constant value =>
      cases value <;> rfl
  | gate index =>
      simp only [encodeSourceTokens, List.cons_append, decodeSourceTokens]
      rw [decodeNatTokens_encodeNatTokens_append]

def encodeGateTokens (gate : RawGate) : List Token :=
  encodeSourceTokens gate.left ++
    encodeSourceTokens gate.right ++ [.gateEnd]

def encodeGateListTokens : List RawGate → List Token
  | [] => []
  | gate :: rest => encodeGateTokens gate ++ encodeGateListTokens rest

def decodeNGatesTokens : Nat → List Token →
    Option (List RawGate × List Token)
  | 0, tokens => some ([], tokens)
  | count + 1, tokens =>
      match decodeSourceTokens tokens with
      | none => none
      | some (left, afterLeft) =>
          match decodeSourceTokens afterLeft with
          | none => none
          | some (right, afterRight) =>
              match afterRight with
              | .gateEnd :: afterGate =>
                  match decodeNGatesTokens count afterGate with
                  | none => none
                  | some (gates, suffix) =>
                      some ({ left := left, right := right } :: gates, suffix)
              | _ => none

theorem decodeNGatesTokens_encodeGateListTokens_append
    (gates : List RawGate) (suffix : List Token) :
    decodeNGatesTokens gates.length
        (encodeGateListTokens gates ++ suffix) =
      some (gates, suffix) := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      cases gate with
      | mk left right =>
          simp only [encodeGateListTokens, encodeGateTokens,
            List.append_assoc, List.cons_append, List.nil_append,
            List.length_cons, decodeNGatesTokens,
            decodeSourceTokens_encodeSourceTokens_append]
          rw [ih]

def encodeSourceListTokens : List RawSource → List Token
  | [] => []
  | source :: rest =>
      encodeSourceTokens source ++ encodeSourceListTokens rest

def decodeNSourcesTokens : Nat → List Token →
    Option (List RawSource × List Token)
  | 0, tokens => some ([], tokens)
  | count + 1, tokens =>
      match decodeSourceTokens tokens with
      | none => none
      | some (source, afterSource) =>
          match decodeNSourcesTokens count afterSource with
          | none => none
          | some (sources, suffix) => some (source :: sources, suffix)

theorem decodeNSourcesTokens_encodeSourceListTokens_append
    (sources : List RawSource) (suffix : List Token) :
    decodeNSourcesTokens sources.length
        (encodeSourceListTokens sources ++ suffix) =
      some (sources, suffix) := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
      simp only [encodeSourceListTokens, List.append_assoc,
        List.length_cons, decodeNSourcesTokens,
        decodeSourceTokens_encodeSourceTokens_append]
      rw [ih]

def encodeCircuitTokens (circuit : RawCircuit) : List Token :=
  .version0 ::
    (encodeNatTokens circuit.inputCount ++
      encodeNatTokens circuit.gates.length ++
      encodeGateListTokens circuit.gates ++
      [.programEnd] ++
      encodeSourceTokens circuit.output ++
      [.outputsEnd, .instanceEnd])

def decodeCircuitTokens (tokens : List Token) : Option RawCircuit :=
  match tokens with
  | .version0 :: afterVersion =>
      match decodeNatTokens afterVersion with
      | some (inputs, afterInputs) =>
          match decodeNatTokens afterInputs with
          | some (gateCount, afterGateCount) =>
              match decodeNGatesTokens gateCount afterGateCount with
              | some (gates, .programEnd :: afterProgram) =>
                  match decodeSourceTokens afterProgram with
                  | some (output, [.outputsEnd, .instanceEnd]) =>
                      some
                        { inputCount := inputs
                          gates := gates
                          output := output }
                  | _ => none
              | _ => none
          | none => none
      | none => none
  | _ => none

def encodeCircuit (circuit : RawCircuit) : BitString :=
  encodeTokens (encodeCircuitTokens circuit)

def decodeCircuit (bits : BitString) : Option RawCircuit :=
  match decodeTokens bits with
  | none => none
  | some tokens => decodeCircuitTokens tokens

def decodeValidCircuit (bits : BitString) : Option RawCircuit :=
  match decodeCircuit bits with
  | some circuit =>
      if circuit.wellFormed then some circuit else none
  | none => none

theorem decodeCircuitTokens_encodeCircuitTokens (circuit : RawCircuit) :
    decodeCircuitTokens (encodeCircuitTokens circuit) = some circuit := by
  cases circuit with
  | mk inputs gates output =>
      simp [encodeCircuitTokens, decodeCircuitTokens, List.append_assoc,
        decodeNatTokens_encodeNatTokens_append,
        decodeNGatesTokens_encodeGateListTokens_append,
        decodeSourceTokens_encodeSourceTokens_append]

theorem decodeCircuit_encodeCircuit (circuit : RawCircuit) :
    decodeCircuit (encodeCircuit circuit) = some circuit := by
  unfold decodeCircuit encodeCircuit
  rw [decodeTokens_encodeTokens]
  exact decodeCircuitTokens_encodeCircuitTokens circuit

theorem decodeValidCircuit_encodeCircuit
    (circuit : RawCircuit) (valid : circuit.wellFormed = true) :
    decodeValidCircuit (encodeCircuit circuit) = some circuit := by
  simp [decodeValidCircuit, decodeCircuit_encodeCircuit, valid]

def encodeCandidateTokens (candidate : RawCandidate) : List Token :=
  .version0 ::
    (encodeNatTokens candidate.inputCount ++
      encodeNatTokens candidate.gates.length ++
      encodeNatTokens candidate.outputs.length ++
      encodeGateListTokens candidate.gates ++
      [.programEnd] ++
      encodeSourceListTokens candidate.outputs ++
      [.outputsEnd, .instanceEnd])

def decodeCandidateTokens (tokens : List Token) : Option RawCandidate :=
  match tokens with
  | .version0 :: afterVersion =>
      match decodeNatTokens afterVersion with
      | some (inputs, afterInputs) =>
          match decodeNatTokens afterInputs with
          | some (gateCount, afterGateCount) =>
              match decodeNatTokens afterGateCount with
              | some (outputCount, afterOutputCount) =>
                  match decodeNGatesTokens gateCount afterOutputCount with
                  | some (gates, .programEnd :: afterProgram) =>
                      match decodeNSourcesTokens outputCount afterProgram with
                      | some (outputs, [.outputsEnd, .instanceEnd]) =>
                          some
                            { inputCount := inputs
                              gates := gates
                              outputs := outputs }
                      | _ => none
                  | _ => none
              | none => none
          | none => none
      | none => none
  | _ => none

def encodeCandidate (candidate : RawCandidate) : BitString :=
  encodeTokens (encodeCandidateTokens candidate)

def decodeCandidate (bits : BitString) : Option RawCandidate :=
  match decodeTokens bits with
  | none => none
  | some tokens => decodeCandidateTokens tokens

theorem decodeCandidateTokens_encodeCandidateTokens
    (candidate : RawCandidate) :
    decodeCandidateTokens (encodeCandidateTokens candidate) =
      some candidate := by
  cases candidate with
  | mk inputs gates outputs =>
      simp [encodeCandidateTokens, decodeCandidateTokens,
        List.append_assoc, decodeNatTokens_encodeNatTokens_append,
        decodeNGatesTokens_encodeGateListTokens_append,
        decodeNSourcesTokens_encodeSourceListTokens_append]

theorem decodeCandidate_encodeCandidate (candidate : RawCandidate) :
    decodeCandidate (encodeCandidate candidate) = some candidate := by
  unfold decodeCandidate encodeCandidate
  rw [decodeTokens_encodeTokens]
  exact decodeCandidateTokens_encodeCandidateTokens candidate

def encodeLockedInstanceTokens
    (rawInstance : RawLockedInstance) : List Token :=
  .version0 ::
    (encodeNatTokens rawInstance.candidate.inputCount ++
      encodeNatTokens rawInstance.candidate.gates.length ++
      encodeNatTokens rawInstance.candidate.outputs.length ++
      encodeGateListTokens rawInstance.candidate.gates ++
      [.programEnd] ++
      encodeSourceListTokens rawInstance.candidate.outputs ++
      [.outputsEnd, .threshold] ++
      encodeNatTokens rawInstance.baseline ++
      [.instanceEnd])

def decodeLockedInstanceTokens
    (tokens : List Token) : Option RawLockedInstance :=
  match tokens with
  | .version0 :: afterVersion =>
      match decodeNatTokens afterVersion with
      | some (inputs, afterInputs) =>
          match decodeNatTokens afterInputs with
          | some (gateCount, afterGateCount) =>
              match decodeNatTokens afterGateCount with
              | some (outputCount, afterOutputCount) =>
                  match decodeNGatesTokens gateCount afterOutputCount with
                  | some (gates, .programEnd :: afterProgram) =>
                      match decodeNSourcesTokens outputCount afterProgram with
                      | some (outputs, .outputsEnd :: .threshold :: afterThreshold) =>
                          match decodeNatTokens afterThreshold with
                          | some (baseline, [.instanceEnd]) =>
                              some
                                { candidate :=
                                    { inputCount := inputs
                                      gates := gates
                                      outputs := outputs }
                                  baseline := baseline }
                          | _ => none
                      | _ => none
                  | _ => none
              | none => none
          | none => none
      | none => none
  | _ => none

def encodeLockedInstance (rawInstance : RawLockedInstance) : BitString :=
  encodeTokens (encodeLockedInstanceTokens rawInstance)

def decodeLockedInstance (bits : BitString) : Option RawLockedInstance :=
  match decodeTokens bits with
  | none => none
  | some tokens => decodeLockedInstanceTokens tokens

theorem decodeLockedInstanceTokens_encodeLockedInstanceTokens
    (rawInstance : RawLockedInstance) :
    decodeLockedInstanceTokens (encodeLockedInstanceTokens rawInstance) =
      some rawInstance := by
  cases rawInstance with
  | mk candidate baseline =>
      cases candidate with
      | mk inputs gates outputs =>
          simp [encodeLockedInstanceTokens,
            decodeLockedInstanceTokens, List.append_assoc,
            decodeNatTokens_encodeNatTokens_append,
            decodeNGatesTokens_encodeGateListTokens_append,
            decodeNSourcesTokens_encodeSourceListTokens_append]

theorem decodeLockedInstance_encodeLockedInstance
    (rawInstance : RawLockedInstance) :
    decodeLockedInstance (encodeLockedInstance rawInstance) =
      some rawInstance := by
  unfold decodeLockedInstance encodeLockedInstance
  rw [decodeTokens_encodeTokens]
  exact decodeLockedInstanceTokens_encodeLockedInstanceTokens rawInstance

theorem encodeTokens_length (tokens : List Token) :
    (encodeTokens tokens).length = 4 * tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      cases token <;>
        simp [encodeTokens, Token.bits, ih, Nat.mul_add, Nat.add_assoc]

end LockedNAND
end Concrete
end PNP
