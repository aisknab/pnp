/-
Copyright (c) 2026 PNP Labs.

Concrete, finite syntax for polynomially charged function and decision
pipelines, together with certificate-based NP and polynomial many-one
reductions.

This layer deliberately makes a modest claim.  A pipeline is a finite syntax
tree whose leaves are `Machine` programs, and every leaf is charged an
explicit natural-polynomial transition budget.  Composition is interpreted by
this file; no compiler from a composite pipeline to one raw `Machine` is
claimed here.
-/

import PNP.Concrete.TapeHandoff

namespace PNP.Concrete

namespace TapeSymbol

/-- Totalize one represented cell to a bit for compatibility lemmas.  The
observable output decoder does not use this function on blanks; it stops at
the first blank delimiter. -/
def toBool : TapeSymbol → Bool
  | .blank => false
  | .zero => false
  | .one => true

theorem toBool_ofBool (bit : Bool) : toBool (ofBool bit) = bit := by
  cases bit <;> rfl

end TapeSymbol

namespace Tape

theorem map_toBool_ofBool (bits : BitString) :
    (bits.map TapeSymbol.ofBool).map TapeSymbol.toBool = bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit with
      | false => exact congrArg (List.cons false) ih
      | true => exact congrArg (List.cons true) ih

end Tape

/-- Output produced after giving one concrete machine a fixed transition
budget, under the output convention above. -/
def machineOutput (machine : Machine) (steps : Nat) (input : BitString) :
    BitString :=
  (run machine steps (startConfig machine input)).tape.outputBits

theorem machineOutput_immediateAccept_zero (input : BitString) :
    machineOutput immediateAcceptMachine 0 input = input := by
  unfold machineOutput
  change Tape.outputBits (Tape.ofInput input) = input
  exact Tape.outputBits_ofInput input

namespace NatPolynomial

/-- Substitute `inner` for the variable of `outer`. -/
def substitute : NatPolynomial → NatPolynomial → NatPolynomial
  | .constant value, _ => .constant value
  | .variable, inner => inner
  | .add left right, inner => .add (substitute left inner) (substitute right inner)
  | .mul left right, inner => .mul (substitute left inner) (substitute right inner)

theorem eval_substitute (outer inner : NatPolynomial) (input : Nat) :
    eval (substitute outer inner) input = eval outer (eval inner input) := by
  induction outer with
  | constant value => rfl
  | «variable» => rfl
  | add left right leftIH rightIH =>
      change eval (substitute left inner) input +
        eval (substitute right inner) input =
        eval left (eval inner input) + eval right (eval inner input)
      rw [leftIH, rightIH]
  | mul left right leftIH rightIH =>
      change eval (substitute left inner) input *
        eval (substitute right inner) input =
        eval left (eval inner input) * eval right (eval inner input)
      rw [leftIH, rightIH]

end NatPolynomial

/-- Closed finite syntax for bitstring-producing pipelines.

Every leaf is a concrete machine together with the polynomial budget at which
it is run.  A composite first evaluates its left child and then supplies that
bitstring to its right child. -/
inductive FunctionProgram where
  | machine (program : Machine) (stepBound : NatPolynomial)
  | compose (first second : FunctionProgram)
deriving DecidableEq, Repr

namespace FunctionProgram

/-- Interpret a closed function pipeline. -/
def eval : FunctionProgram → BitString → BitString
  | .machine program stepBound, input =>
      machineOutput program (stepBound.eval (BitString.size input)) input
  | .compose first second, input => eval second (eval first input)

/-- Total transition budget charged by a pipeline evaluation. -/
def chargedSteps : FunctionProgram → BitString → Nat
  | (.machine _ stepBound), input => stepBound.eval (BitString.size input)
  | .compose first second, input =>
      chargedSteps first input + BitString.size (eval first input) +
        chargedSteps second (eval first input)

/-- Every machine leaf reaches one of its designated halting states at its
charged budget. -/
def Halts : FunctionProgram → BitString → Prop
  | .machine program stepBound, input =>
      boundedDecide program (stepBound.eval (BitString.size input)) input ≠
        .timeout
  | .compose first second, input =>
      Halts first input ∧ Halts second (eval first input)

end FunctionProgram

/-- A finite function pipeline with proved polynomial transition and output
size bounds.  There is no function-valued executable field. -/
structure PolynomialTimeFunction where
  program : FunctionProgram
  runtimeBound : NatPolynomial
  outputSizeBound : NatPolynomial
  haltsWithin : ∀ input, program.Halts input
  runtime_le : ∀ input,
    program.chargedSteps input ≤ runtimeBound.eval (BitString.size input)
  output_size_le : ∀ input,
    BitString.size (program.eval input) ≤
      outputSizeBound.eval (BitString.size input)

namespace PolynomialTimeFunction

/-- Evaluate the finite program stored in a proof-bearing function witness. -/
def output (function : PolynomialTimeFunction) (input : BitString) : BitString :=
  function.program.eval input

/-- The identity transformation, implemented by a concrete zero-step machine
whose initial tape already contains the input. -/
def identity : PolynomialTimeFunction :=
  { program := .machine immediateAcceptMachine (.constant 0)
    runtimeBound := .constant 0
    outputSizeBound := .variable
    haltsWithin := by
      intro input
      exact Verdict.noConfusion
    runtime_le := by
      intro input
      exact Nat.le_refl 0
    output_size_le := by
      intro input
      change BitString.size (machineOutput immediateAcceptMachine 0 input) ≤
        BitString.size input
      rw [machineOutput_immediateAccept_zero]
      exact Nat.le_refl (BitString.size input) }

theorem identity_output (input : BitString) : identity.output input = input := by
  unfold output identity FunctionProgram.eval
  exact machineOutput_immediateAccept_zero input

/-- Sequential composition of two proof-bearing finite pipelines. -/
def compose (first second : PolynomialTimeFunction) : PolynomialTimeFunction :=
  { program := .compose first.program second.program
    runtimeBound := .add (.add first.runtimeBound first.outputSizeBound)
      (NatPolynomial.substitute second.runtimeBound first.outputSizeBound)
    outputSizeBound :=
      NatPolynomial.substitute second.outputSizeBound first.outputSizeBound
    haltsWithin := by
      intro input
      exact ⟨first.haltsWithin input, second.haltsWithin (first.output input)⟩
    runtime_le := by
      intro input
      rw [NatPolynomial.eval_add, NatPolynomial.eval_add,
        NatPolynomial.eval_substitute]
      exact Nat.add_le_add
        (Nat.add_le_add (first.runtime_le input) (first.output_size_le input))
        (Nat.le_trans (second.runtime_le (first.output input))
          (NatPolynomial.eval_mono second.runtimeBound
            (first.output_size_le input)))
    output_size_le := by
      intro input
      rw [NatPolynomial.eval_substitute]
      exact Nat.le_trans (second.output_size_le (first.output input))
        (NatPolynomial.eval_mono second.outputSizeBound
          (first.output_size_le input)) }

theorem compose_output (first second : PolynomialTimeFunction)
    (input : BitString) :
    (compose first second).output input = second.output (first.output input) := rfl

end PolynomialTimeFunction

/-- Closed finite syntax for decision pipelines.  A terminal leaf is a raw
machine; preprocessing is an explicit finite `FunctionProgram` tree. -/
inductive DecisionProgram where
  | machine (program : Machine) (stepBound : NatPolynomial)
  | precompose (preprocessor : FunctionProgram) (decision : DecisionProgram)
deriving DecidableEq, Repr

namespace DecisionProgram

/-- Verdict produced by a finite decision pipeline. -/
def verdict : DecisionProgram → BitString → Verdict
  | .machine program stepBound, input =>
      boundedDecide program (stepBound.eval (BitString.size input)) input
  | .precompose preprocessor decision, input =>
      verdict decision (preprocessor.eval input)

/-- Total transition budget charged by a decision pipeline. -/
def chargedSteps : DecisionProgram → BitString → Nat
  | (.machine _ stepBound), input => stepBound.eval (BitString.size input)
  | .precompose preprocessor decision, input =>
      preprocessor.chargedSteps input +
        BitString.size (preprocessor.eval input) +
        chargedSteps decision (preprocessor.eval input)

/-- Every preprocessing leaf and the terminal decision leaf halt at their
charged budgets. -/
def Halts : DecisionProgram → BitString → Prop
  | .machine program stepBound, input =>
      boundedDecide program (stepBound.eval (BitString.size input)) input ≠
        .timeout
  | .precompose preprocessor decision, input =>
      preprocessor.Halts input ∧ Halts decision (preprocessor.eval input)

end DecisionProgram

/-- A concrete language is a predicate on finite bitstrings. -/
abbrev Language := BitString → Prop

/-- A finite decision pipeline with a proved polynomial transition bound and
exact acceptance semantics. -/
structure PolynomialTimeDecider (language : Language) where
  program : DecisionProgram
  runtimeBound : NatPolynomial
  haltsWithin : ∀ input, program.Halts input
  runtime_le : ∀ input,
    program.chargedSteps input ≤ runtimeBound.eval (BitString.size input)
  accepts_iff : ∀ input, program.verdict input = .accept ↔ language input

namespace PolynomialTimeDecider

/-- Embed the earlier single-machine witness in the finite decision-pipeline
interface. -/
def ofMachine {language : Language}
    (witness : PolynomialTimeMachine language) :
    PolynomialTimeDecider language :=
  { program := .machine witness.machine witness.timeBound
    runtimeBound := witness.timeBound
    haltsWithin := witness.haltsWithin
    runtime_le := by
      intro input
      exact Nat.le_refl (witness.timeBound.eval (BitString.size input))
    accepts_iff := witness.accepts_iff }

/-- Reuse one decision program for an extensionally equivalent language. -/
def relabel {oldLanguage newLanguage : Language}
    (decision : PolynomialTimeDecider oldLanguage)
    (equivalence : ∀ input, oldLanguage input ↔ newLanguage input) :
    PolynomialTimeDecider newLanguage :=
  { program := decision.program
    runtimeBound := decision.runtimeBound
    haltsWithin := decision.haltsWithin
    runtime_le := decision.runtime_le
    accepts_iff := by
      intro input
      exact Iff.trans (decision.accepts_iff input) (equivalence input) }

/-- Precompose a decider with a polynomially charged finite function
pipeline. -/
def precompose {language : Language}
    (function : PolynomialTimeFunction)
    (decision : PolynomialTimeDecider language) :
    PolynomialTimeDecider (fun input => language (function.output input)) :=
  { program := .precompose function.program decision.program
    runtimeBound := .add (.add function.runtimeBound function.outputSizeBound)
      (NatPolynomial.substitute decision.runtimeBound function.outputSizeBound)
    haltsWithin := by
      intro input
      exact ⟨function.haltsWithin input,
        decision.haltsWithin (function.output input)⟩
    runtime_le := by
      intro input
      rw [NatPolynomial.eval_add, NatPolynomial.eval_add,
        NatPolynomial.eval_substitute]
      exact Nat.add_le_add
        (Nat.add_le_add (function.runtime_le input)
          (function.output_size_le input))
        (Nat.le_trans (decision.runtime_le (function.output input))
          (NatPolynomial.eval_mono decision.runtimeBound
            (function.output_size_le input)))
    accepts_iff := by
      intro input
      exact decision.accepts_iff (function.output input) }

end PolynomialTimeDecider

/-- Finite choice of how a verifier supplies an instance and certificate to
its decision pipeline.  The paired mode uses the canonical self-delimiting
codec from `BitString`; input-only mode is the standard embedding of a
deterministic decider that ignores its certificate. -/
inductive VerifierInputMode where
  | inputOnly
  | paired
deriving DecidableEq, Repr

namespace VerifierInputMode

/-- Encode verifier data according to the finite mode. -/
def encode : VerifierInputMode → BitString → BitString → BitString
  | .inputOnly, input, _ => input
  | .paired, input, certificate => BitString.pair input certificate

theorem encode_paired (input certificate : BitString) :
    encode .paired input certificate = BitString.pair input certificate := rfl

end VerifierInputMode

/-- Finite verifier syntax: an input convention plus a closed decision
pipeline. -/
structure VerifierProgram where
  inputMode : VerifierInputMode
  decision : DecisionProgram
deriving DecidableEq, Repr

namespace VerifierProgram

/-- Execute a verifier on an instance and certificate. -/
def verdict (program : VerifierProgram) (input certificate : BitString) : Verdict :=
  program.decision.verdict (program.inputMode.encode input certificate)

/-- Charge the decision pipeline on its encoded verifier input. -/
def chargedSteps (program : VerifierProgram)
    (input certificate : BitString) : Nat :=
  program.decision.chargedSteps (program.inputMode.encode input certificate)

/-- All leaves in the verifier's decision pipeline halt on the encoded input. -/
def Halts (program : VerifierProgram)
    (input certificate : BitString) : Prop :=
  program.decision.Halts (program.inputMode.encode input certificate)

end VerifierProgram

/-- Standard bounded-certificate NP semantics over a finite verifier program.

Both certificate length and charged runtime are bounded by explicit natural
polynomials in the instance length. -/
structure PolynomialTimeVerifier (language : Language) where
  program : VerifierProgram
  certificateBound : NatPolynomial
  runtimeBound : NatPolynomial
  haltsWithin : ∀ input certificate,
    BitString.size certificate ≤ certificateBound.eval (BitString.size input) →
      program.Halts input certificate
  runtime_le : ∀ input certificate,
    BitString.size certificate ≤ certificateBound.eval (BitString.size input) →
      program.chargedSteps input certificate ≤
        runtimeBound.eval (BitString.size input)
  accepts_iff : ∀ input, language input ↔
    ∃ certificate,
      BitString.size certificate ≤ certificateBound.eval (BitString.size input) ∧
      program.verdict input certificate = .accept

/-- Membership in the concrete finite-pipeline class P. -/
def InP (language : Language) : Prop :=
  Nonempty (PolynomialTimeDecider language)

/-- Membership in the concrete bounded-certificate finite-pipeline class NP. -/
def InNP (language : Language) : Prop :=
  Nonempty (PolynomialTimeVerifier language)

/-- Mutual inclusion of the two concrete classes.  This formulation avoids
using function or proposition extensionality in the theorem kernel. -/
def PEqualsNP : Prop :=
  (∀ language : Language, InP language → InNP language) ∧
  (∀ language : Language, InNP language → InP language)

/-- Embed a deterministic finite decision pipeline as a verifier which ignores
its certificate. -/
def verifierFromDecider {language : Language}
    (decision : PolynomialTimeDecider language) :
    PolynomialTimeVerifier language :=
  { program := { inputMode := .inputOnly, decision := decision.program }
    certificateBound := .constant 0
    runtimeBound := decision.runtimeBound
    haltsWithin := by
      intro input certificate certificateSize
      exact decision.haltsWithin input
    runtime_le := by
      intro input certificate certificateSize
      exact decision.runtime_le input
    accepts_iff := by
      intro input
      constructor
      · intro member
        exact ⟨[], Nat.le_refl 0, (decision.accepts_iff input).mpr member⟩
      · intro certificateExists
        rcases certificateExists with ⟨certificate, certificateSize, accepted⟩
        exact (decision.accepts_iff input).mp accepted }

/-- The concrete finite-pipeline class P is contained in its bounded-
certificate NP class. -/
theorem p_subset_np {language : Language} : InP language → InNP language := by
  intro inP
  rcases inP with ⟨decision⟩
  exact ⟨verifierFromDecider decision⟩

/-- A polynomial many-one reduction has a closed finite function pipeline and
an extensional membership proof. -/
structure PolynomialReduction (source target : Language) where
  function : PolynomialTimeFunction
  correctness : ∀ input,
    source input ↔ target (function.output input)

/-- Existence of a concrete polynomial many-one reduction. -/
def ReducesTo (source target : Language) : Prop :=
  Nonempty (PolynomialReduction source target)

namespace PolynomialReduction

/-- Identity is a concrete polynomial many-one reduction. -/
def identity (language : Language) : PolynomialReduction language language :=
  { function := PolynomialTimeFunction.identity
    correctness := by
      intro input
      rw [PolynomialTimeFunction.identity_output] }

/-- Compose concrete polynomial many-one reductions by composing their finite
function programs and their proved polynomial bounds. -/
def compose {first middle last : Language}
    (left : PolynomialReduction first middle)
    (right : PolynomialReduction middle last) :
    PolynomialReduction first last :=
  { function := PolynomialTimeFunction.compose left.function right.function
    correctness := by
      intro input
      change first input ↔
        last (right.function.output (left.function.output input))
      exact Iff.trans (left.correctness input)
        (right.correctness (left.function.output input)) }

end PolynomialReduction

/-- Polynomial reducibility is reflexive. -/
theorem reduction_refl (language : Language) : ReducesTo language language :=
  ⟨PolynomialReduction.identity language⟩

/-- Polynomial reducibility is transitive. -/
theorem reduction_comp {first middle last : Language} :
    ReducesTo first middle → ReducesTo middle last → ReducesTo first last := by
  intro leftExists rightExists
  rcases leftExists with ⟨left⟩
  rcases rightExists with ⟨right⟩
  exact ⟨PolynomialReduction.compose left right⟩

/-- A concrete polynomial reduction to a language in P constructs a finite
decision pipeline for the source language. -/
theorem reduction_transports_p {source target : Language} :
    ReducesTo source target → InP target → InP source := by
  intro reductionExists targetInP
  rcases reductionExists with ⟨reduction⟩
  rcases targetInP with ⟨targetDecision⟩
  let precomposed :=
    PolynomialTimeDecider.precompose reduction.function targetDecision
  exact ⟨PolynomialTimeDecider.relabel precomposed (by
    intro input
    exact (reduction.correctness input).symm)⟩

/-- NP-completeness relative to the concrete reduction and verifier notions. -/
structure NPComplete (language : Language) : Prop where
  inNP : InNP language
  hard : ∀ source : Language, InNP source → ReducesTo source language

/-- If an NP-complete language has a concrete P decider, the concrete P and NP
classes mutually include one another. -/
theorem np_complete_in_p_implies_p_eq_np
    {completeLanguage : Language}
    (complete : NPComplete completeLanguage)
    (completeInP : InP completeLanguage) : PEqualsNP := by
  constructor
  · intro language languageInP
    exact p_subset_np languageInP
  · intro language languageInNP
    exact reduction_transports_p (complete.hard language languageInNP) completeInP

end PNP.Concrete
