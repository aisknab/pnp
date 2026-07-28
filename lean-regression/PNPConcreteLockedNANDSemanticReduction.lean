import PNP.Concrete.LockedNANDReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace PNP.Concrete.LockedNANDSemanticReductionRegression

open DirectWire
open DirectWire.LockedNANDTrace
open DirectWire.LockedNANDGlobalCandidates
open LockedNAND

def zeroInput : Valuation 0 := fun index => Fin.elim0 index

def constantTrueProgram : Program 0 1 :=
  .snoc .empty
    { left := .constant false
      right := .constant false }

def constantTrueCircuit : Circuit 0 :=
  { gateCount := 1
    program := constantTrueProgram
    outputGate := fin1Zero }

theorem constantTrueCircuit_satisfiable :
    constantTrueCircuit.Satisfiable :=
  ⟨zeroInput, rfl⟩

def constantFalseProgram : Program 0 1 :=
  .snoc .empty
    { left := .constant true
      right := .constant true }

def constantFalseCircuit : Circuit 0 :=
  { gateCount := 1
    program := constantFalseProgram
    outputGate := fin1Zero }

theorem constantFalseCircuit_not_satisfiable :
    ¬ constantFalseCircuit.Satisfiable := by
  rintro ⟨input, outputTrue⟩
  change false = true at outputTrue
  exact Bool.noConfusion outputTrue

def inputOutputCircuit : RawCircuit :=
  { inputCount := 1
    gates := []
    output := .input 0 }

def constantZeroOutputCircuit : RawCircuit :=
  { inputCount := 0
    gates := []
    output := .constant false }

def canonicalRawCircuit : RawCircuit :=
  RawCircuit.ofCircuit constantTrueCircuit

example : Token.version0.bits = [false, false, false, false] := rfl
example : Token.instanceEnd.bits = [true, false, true, true] := rfl
example : Token.ofBits true true false false = none := rfl
example : Token.ofBits true true true true = none := rfl

example :
    decodeTokens (encodeTokens
      [.version0, .input, .unit, .natEnd, .instanceEnd]) =
      some [.version0, .input, .unit, .natEnd, .instanceEnd] :=
  decodeTokens_encodeTokens _

example : decodeTokens [false] = none := rfl
example : decodeTokens [true, true, false, false] = none := rfl

example :
    inputOutputCircuit.normalizationAddedGates = 2 := rfl

example :
    inputOutputCircuit.normalize =
      { inputCount := 1
        gates :=
          [ { left := .input 0, right := .constant true }
          , { left := .gate 0, right := .gate 0 } ]
        output := .gate 1 } := rfl

example :
    constantZeroOutputCircuit.normalizationAddedGates = 1 := rfl

example (input : Nat → Bool) :
    inputOutputCircuit.normalize.eval input =
      inputOutputCircuit.eval input :=
  RawCircuit.normalize_eval inputOutputCircuit input

example (input : Nat → Bool) :
    constantZeroOutputCircuit.normalize.eval input =
      constantZeroOutputCircuit.eval input :=
  RawCircuit.normalize_eval constantZeroOutputCircuit input

example :
    decodeCircuit (encodeCircuit canonicalRawCircuit) =
      some canonicalRawCircuit :=
  decodeCircuit_encodeCircuit canonicalRawCircuit

example :
    decodeElaboratedCircuit
        (encodeCircuit canonicalRawCircuit) =
      some { inputCount := 0, circuit := constantTrueCircuit } :=
  decodeElaboratedCircuit_encodeCircuit_ofCircuit constantTrueCircuit

example :
    decodeCandidate
        (encodeCandidate
          (RawCandidate.ofCandidate
            (fullCandidate constantTrueCircuit))) =
      some
        (RawCandidate.ofCandidate
          (fullCandidate constantTrueCircuit)) :=
  decodeCandidate_encodeCandidate _

example :
    decodeLockedInstance
        (encodeLockedInstance
          (lockedInstanceOfCircuit constantTrueCircuit)) =
      some (lockedInstanceOfCircuit constantTrueCircuit) :=
  decodeLockedInstance_encodeLockedInstance _

example :
    EncodedNANDSAT
      (encodeCircuit
        (RawCircuit.ofCircuit constantTrueCircuit)) := by
  simp [EncodedNANDSAT,
    decodeElaboratedCircuit_encodeCircuit_ofCircuit,
    constantTrueCircuit_satisfiable]

example :
    ¬ EncodedNANDSAT
      (encodeCircuit
        (RawCircuit.ofCircuit constantFalseCircuit)) := by
  simp [EncodedNANDSAT,
    decodeElaboratedCircuit_encodeCircuit_ofCircuit,
    constantFalseCircuit_not_satisfiable]

example :
    EncodedLockedNANDThreshold
      (encodeLockedInstance
        (lockedInstanceOfCircuit constantTrueCircuit)) :=
  (encoded_fullCandidate_threshold_iff_satisfiable
    constantTrueCircuit).2 constantTrueCircuit_satisfiable

example :
    ¬ EncodedLockedNANDThreshold
      (encodeLockedInstance
        (lockedInstanceOfCircuit constantFalseCircuit)) :=
  mt (encoded_fullCandidate_threshold_iff_satisfiable
    constantFalseCircuit).1 constantFalseCircuit_not_satisfiable

example (bits : BitString) (packed : PackedCircuit)
    (decoded : decodeElaboratedCircuit bits = some packed) :
    buildLockedNANDInstance bits =
      encodeLockedInstance
        (lockedInstanceOfCircuit packed.circuit) :=
  buildLockedNANDInstance_of_decoded bits packed decoded

example {inputs : Nat} (circuit : Circuit inputs) :
    decodeLockedInstance
        (encodeLockedInstance
          (lockedInstanceOfCircuit circuit)) =
      some (lockedInstanceOfCircuit circuit) :=
  decodeLockedInstance_encodeLockedInstance _

example : buildLockedNANDInstance [] = [] := rfl

example : ¬ EncodedLockedNANDThreshold [] :=
  empty_not_encodedLockedNANDThreshold

example (bits : BitString) :
    EncodedNANDSAT bits ↔
      EncodedLockedNANDThreshold
        (buildLockedNANDInstance bits) :=
  buildLockedNANDInstance_correct bits

end PNP.Concrete.LockedNANDSemanticReductionRegression
