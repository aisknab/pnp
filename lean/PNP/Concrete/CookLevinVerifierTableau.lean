/-
Copyright (c) 2026 PNP Labs.

Uniform bounded tableaux for an arbitrary verifier in the concrete NP model.

The verifier's finite decision pipeline is compiled to one raw machine by the
already proved recursive pipeline compiler.  For one source input, every
certificate inside the advertised certificate polynomial is run at one
answer-independent fuel budget obtained from the maximum encoded input size.

This file proves semantic tableau equivalence only.  It does not emit CNF,
construct a reduction, or claim NP-hardness.
-/

import PNP.Concrete.CookLevinTableau
import PNP.Concrete.PipelineRefinement

namespace PNP.Concrete

namespace CookLevin

/-! ### Verifier input size and one uniform raw budget -/

/-- Translate the concrete verifier input convention to the tableau layout
convention. -/
def inputModeOfVerifier : VerifierInputMode → InputMode
  | .inputOnly => .inputOnly
  | .paired => .paired

theorem verifierPair_add_one_same_normalize (value : Nat) :
    value + 1 + value = value + value + 1 := by
  rw [Nat.add_assoc]
  rw [Nat.add_comm 1 value]
  rw [← Nat.add_assoc]

theorem verifierPair_merge_unit_offsets (left right : Nat) :
    (left + 1) + (right + 1) = left + right + 2 := by
  rw [Nat.add_assoc]
  rw [← Nat.add_assoc 1 right 1]
  rw [Nat.add_comm 1 right]
  rw [Nat.add_assoc right 1 1]
  rw [← Nat.add_assoc left right 2]

theorem verifierPair_size_arithmetic (left right : Nat) :
    (left + 1 + left) + (right + 1 + right) =
      2 * left + 2 * right + 2 := by
  rw [verifierPair_add_one_same_normalize,
    verifierPair_add_one_same_normalize]
  rw [Nat.two_mul, Nat.two_mul]
  exact verifierPair_merge_unit_offsets (left + left) (right + right)

/-- Closed arithmetic form of the canonical verifier pair length, proved
without importing a specialized CNF verifier. -/
theorem verifierPair_size (input certificate : BitString) :
    BitString.size (BitString.pair input certificate) =
      2 * BitString.size input + 2 * BitString.size certificate + 2 := by
  rw [BitString.size_pair]
  exact verifierPair_size_arithmetic input.length certificate.length

/-- Every bounded verifier input fits the answer-independent encoded-input
polynomial used by the tableau dimensions. -/
theorem verifierEncodedInput_size_le
    (mode : VerifierInputMode) (certificateBound : NatPolynomial)
    (input certificate : BitString)
    (hCertificate : BitString.size certificate ≤
      certificateBound.eval (BitString.size input)) :
    BitString.size (mode.encode input certificate) ≤
      (encodedInputPolynomial (inputModeOfVerifier mode) certificateBound).eval
        (BitString.size input) := by
  cases mode with
  | inputOnly =>
      exact Nat.le_refl (BitString.size input)
  | paired =>
      rw [VerifierInputMode.encode_paired, verifierPair_size]
      change
        2 * BitString.size input + 2 * BitString.size certificate + 2 ≤
          2 * BitString.size input +
            2 * certificateBound.eval (BitString.size input) + 2
      have doubled : 2 * BitString.size certificate ≤
          2 * certificateBound.eval (BitString.size input) :=
        Nat.mul_le_mul_left 2 hCertificate
      exact Nat.add_le_add_right
        (Nat.add_le_add_left doubled (2 * BitString.size input)) 2

/-! ### One input of one concrete NP verifier -/

/-- The proof-bearing verifier and source input whose bounded certificates
will share one compiled raw-machine tableau budget. -/
structure VerifierTableauProblem (language : Language) where
  verifier : PolynomialTimeVerifier language
  input : BitString

namespace VerifierTableauProblem

/-- Compile the complete finite decision pipeline once, independently of the
certificate and of its answer. -/
def refinement {language : Language}
    (problem : VerifierTableauProblem language) :
    DecisionProgram.RawRefinement problem.verifier.program.decision :=
  DecisionProgram.RawRefinement.compile problem.verifier.program.decision

def rawMachine {language : Language}
    (problem : VerifierTableauProblem language) : Machine :=
  problem.refinement.machine

def rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) : NatPolynomial :=
  problem.refinement.timeBound

def tableauInputMode {language : Language}
    (problem : VerifierTableauProblem language) : InputMode :=
  inputModeOfVerifier problem.verifier.program.inputMode

def certificateLimit {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  problem.verifier.certificateBound.eval (BitString.size problem.input)

def rawInput {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString) : BitString :=
  problem.verifier.program.inputMode.encode problem.input certificate

/-- Per-certificate compiled fuel before uniform padding. -/
def actualFuel {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString) : Nat :=
  problem.rawTimeBound.eval (BitString.size (problem.rawInput certificate))

/-- Maximum encoded verifier-input size for this source input. -/
def encodedInputLimit {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (encodedInputPolynomial problem.tableauInputMode
    problem.verifier.certificateBound).eval (BitString.size problem.input)

/-- One answer-independent fuel budget shared by every bounded certificate. -/
def uniformFuel {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  problem.rawTimeBound.eval problem.encodedInputLimit

/-- The numeric layout that later formula emitters must use. -/
def dimensions {language : Language}
    (problem : VerifierTableauProblem language) : Dimensions :=
  dimensionsAt problem.rawMachine problem.tableauInputMode
    problem.verifier.certificateBound problem.rawTimeBound
    (BitString.size problem.input)

def layout {language : Language}
    (problem : VerifierTableauProblem language) : VariableLayout :=
  { dimensions := problem.dimensions, mode := problem.tableauInputMode }

theorem dimensions_inputLength {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.dimensions.inputLength = BitString.size problem.input := rfl

theorem dimensions_certificateBound {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.dimensions.certificateBound = problem.certificateLimit := rfl

theorem dimensions_timeBound {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.dimensions.timeBound = problem.uniformFuel := rfl

theorem layout_mode {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.layout.mode = problem.tableauInputMode := rfl

theorem rawInput_size_le {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString)
    (hCertificate : BitString.size certificate ≤ problem.certificateLimit) :
    BitString.size (problem.rawInput certificate) ≤
      problem.encodedInputLimit := by
  exact verifierEncodedInput_size_le
    problem.verifier.program.inputMode problem.verifier.certificateBound
    problem.input certificate hCertificate

theorem actualFuel_le_uniformFuel {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString)
    (hCertificate : BitString.size certificate ≤ problem.certificateLimit) :
    problem.actualFuel certificate ≤ problem.uniformFuel := by
  exact NatPolynomial.eval_mono problem.rawTimeBound
    (problem.rawInput_size_le certificate hCertificate)

/-! ### Compiled verifier correctness at the uniform budget -/

theorem source_halts {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString)
    (hCertificate : BitString.size certificate ≤ problem.certificateLimit) :
    problem.verifier.program.decision.Halts
      (problem.rawInput certificate) := by
  exact problem.verifier.haltsWithin problem.input certificate hCertificate

theorem actualFuel_ne_timeout {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString)
    (hCertificate : BitString.size certificate ≤ problem.certificateLimit) :
    boundedDecide problem.rawMachine (problem.actualFuel certificate)
      (problem.rawInput certificate) ≠ .timeout := by
  exact problem.refinement.haltsWithin (problem.rawInput certificate)
    (problem.source_halts certificate hCertificate)

theorem actualFuel_final_isHalted {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString)
    (hCertificate : BitString.size certificate ≤ problem.certificateLimit) :
    problem.rawMachine.isHalted
        (run problem.rawMachine (problem.actualFuel certificate)
          (startConfig problem.rawMachine (problem.rawInput certificate))) =
      true := by
  exact (boundedDecide_ne_timeout_iff_final_isHalted
    problem.rawMachine (problem.actualFuel certificate)
    (problem.rawInput certificate)).mp
      (problem.actualFuel_ne_timeout certificate hCertificate)

/-- Padding every bounded certificate to the shared fuel preserves the exact
accept/reject verdict of the source verifier program. -/
theorem uniformFuel_verdict_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString)
    (hCertificate : BitString.size certificate ≤ problem.certificateLimit) :
    boundedDecide problem.rawMachine problem.uniformFuel
        (problem.rawInput certificate) =
      problem.verifier.program.verdict problem.input certificate := by
  calc
    boundedDecide problem.rawMachine problem.uniformFuel
        (problem.rawInput certificate) =
        boundedDecide problem.rawMachine (problem.actualFuel certificate)
          (problem.rawInput certificate) :=
      boundedDecide_pad_of_halted problem.rawMachine
        (problem.rawInput certificate)
        (problem.actualFuel_le_uniformFuel certificate hCertificate)
        (problem.actualFuel_final_isHalted certificate hCertificate)
    _ = problem.verifier.program.decision.verdict
        (problem.rawInput certificate) :=
      problem.refinement.verdict_eq (problem.rawInput certificate)
        (problem.source_halts certificate hCertificate)
    _ = problem.verifier.program.verdict problem.input certificate := rfl

/-! ### Variable-certificate accepting tableaux -/

def initial {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString) : Configuration :=
  startConfig problem.rawMachine (problem.rawInput certificate)

def canonicalTableau {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString) : List Configuration :=
  trace problem.rawMachine problem.uniformFuel (problem.initial certificate)

def Valid {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString) (tableau : List Configuration) : Prop :=
  ValidTableau problem.rawMachine (problem.initial certificate)
    problem.uniformFuel tableau

def tableauVerdict {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString) (tableau : List Configuration) : Verdict :=
  configurationVerdict problem.rawMachine
    (tableauEndpoint (problem.initial certificate) tableau)

def Accepting {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString) (tableau : List Configuration) : Prop :=
  problem.Valid certificate tableau ∧
    problem.tableauVerdict certificate tableau = .accept

/-- A complete witness includes the bounded certificate itself and the exact
semantic tableau. -/
def AcceptingWitness {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString) (tableau : List Configuration) : Prop :=
  BitString.size certificate ≤ problem.certificateLimit ∧
    problem.Accepting certificate tableau

theorem canonicalTableau_valid {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString) :
    problem.Valid certificate (problem.canonicalTableau certificate) :=
  CookLevin.canonicalTableau_valid problem.rawMachine problem.uniformFuel
    (problem.initial certificate)

theorem valid_iff_eq_canonical {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString) (tableau : List Configuration) :
    problem.Valid certificate tableau ↔
      tableau = problem.canonicalTableau certificate :=
  validTableau_iff_eq_trace problem.rawMachine
    (problem.initial certificate) problem.uniformFuel tableau

theorem tableauEndpoint_of_valid {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString) (tableau : List Configuration)
    (hValid : problem.Valid certificate tableau) :
    tableauEndpoint (problem.initial certificate) tableau =
      run problem.rawMachine problem.uniformFuel
        (problem.initial certificate) :=
  CookLevin.tableauEndpoint_of_valid problem.rawMachine
    (problem.initial certificate) problem.uniformFuel tableau hValid

theorem tableauVerdict_of_valid {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString) (tableau : List Configuration)
    (hValid : problem.Valid certificate tableau) :
    problem.tableauVerdict certificate tableau =
      boundedDecide problem.rawMachine problem.uniformFuel
        (problem.rawInput certificate) := by
  unfold tableauVerdict configurationVerdict
  rw [problem.tableauEndpoint_of_valid certificate tableau hValid]
  rfl

theorem tableauVerdict_eq_program_of_valid {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString) (tableau : List Configuration)
    (hCertificate : BitString.size certificate ≤ problem.certificateLimit)
    (hValid : problem.Valid certificate tableau) :
    problem.tableauVerdict certificate tableau =
      problem.verifier.program.verdict problem.input certificate := by
  rw [problem.tableauVerdict_of_valid certificate tableau hValid]
  exact problem.uniformFuel_verdict_eq certificate hCertificate

theorem exists_accepting_iff_program_accept {language : Language}
    (problem : VerifierTableauProblem language)
    (certificate : BitString)
    (hCertificate : BitString.size certificate ≤ problem.certificateLimit) :
    (∃ tableau, problem.Accepting certificate tableau) ↔
      problem.verifier.program.verdict problem.input certificate =
        .accept := by
  constructor
  · intro existsTableau
    rcases existsTableau with ⟨tableau, hValid, hAccept⟩
    rw [problem.tableauVerdict_eq_program_of_valid certificate tableau
      hCertificate hValid] at hAccept
    exact hAccept
  · intro hAccept
    refine ⟨problem.canonicalTableau certificate,
      problem.canonicalTableau_valid certificate, ?_⟩
    rw [problem.tableauVerdict_eq_program_of_valid certificate
      (problem.canonicalTableau certificate) hCertificate
      (problem.canonicalTableau_valid certificate)]
    exact hAccept

/-- The concrete NP verifier semantics are exactly existential bounded
acceptance of the uniform compiled raw-machine tableau. -/
theorem language_iff_exists_acceptingTableau {language : Language}
    (problem : VerifierTableauProblem language) :
    language problem.input ↔
      ∃ certificate tableau,
        problem.AcceptingWitness certificate tableau := by
  constructor
  · intro member
    rcases (problem.verifier.accepts_iff problem.input).mp member with
      ⟨certificate, hCertificate, hAccept⟩
    rcases (problem.exists_accepting_iff_program_accept certificate
      hCertificate).mpr hAccept with ⟨tableau, hTableau⟩
    exact ⟨certificate, tableau, hCertificate, hTableau⟩
  · intro witness
    rcases witness with
      ⟨certificate, tableau, hCertificate, hTableau⟩
    apply (problem.verifier.accepts_iff problem.input).mpr
    refine ⟨certificate, hCertificate, ?_⟩
    exact (problem.exists_accepting_iff_program_accept certificate
      hCertificate).mp ⟨tableau, hTableau⟩

end VerifierTableauProblem

end CookLevin

end PNP.Concrete
