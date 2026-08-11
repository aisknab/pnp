/-
Copyright (c) 2026 PNP Labs.

Finite activation-exact BN4 cancellation above the candidate-derived BN3
request envelope.  A singleton minimal consumer is used as the canonical
activation code, and code equality is proved equivalent to equality of the
induced activation predicates without enumerating cuts.  Signed finite cells
are grouped only by a complete typed key containing that activation code's
atom, an explicit semantic signature, and an explicit transport type.

For each exact key, an executable classifier totals positive and negative
natural-number masses and returns either balance or one strictly positive
residual sign.  The residual contribution is proved equal to the original
integer ledger, preserves the complete key, and cannot contain opposite signs
at one key.  A total wrapper preserves every upstream BN3 failure and rejects
cell ledgers that mention atoms outside the successful nucleus.

This is a finite cancellation kernel over an explicit typed cell ledger.  It
does not derive the cells or their semantic/transport labels from the
four-corner bases, prove a polynomial construction, construct BN5 or BN6,
complete residual routing, prove ZeroSlack, PCCMin, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalBN3RequestEnvelope

namespace PNP
namespace DirectWire

/-! ## Canonical active-antichain codes -/

/-- In the current candidate-derived BN3 envelope every request has exactly
    one singleton minimal consumer.  Its singleton family is the canonical
    active-antichain code used by this finite BN4 kernel. -/
def terminalBN4ActivationCode {alpha : Type} (atom : alpha) :
    List (List alpha) :=
  [terminalBN3MinimalConsumer atom]

/-- A finite antichain code is active when one of its consumers is contained
    in the cut. -/
def TerminalBN4CodeActive {alpha : Type}
    (code : List (List alpha)) (cut : List alpha) : Prop :=
  ∃ consumer, consumer ∈ code ∧
    ∀ atom, atom ∈ consumer -> atom ∈ cut

/-- The singleton code activates exactly the BN3 request predicate. -/
theorem terminalBN4ActivationCode_active_iff
    {alpha : Type} (atom : alpha) (cut : List alpha) :
    TerminalBN4CodeActive (terminalBN4ActivationCode atom) cut ↔
      TerminalBN3RequestPredicate atom cut := by
  simp [TerminalBN4CodeActive, terminalBN4ActivationCode,
    terminalBN3MinimalConsumer, TerminalBN3RequestPredicate]

/-- Equality of canonical singleton codes is exactly equality of request
    atoms. -/
theorem terminalBN4ActivationCode_eq_iff
    {alpha : Type} (left right : alpha) :
    terminalBN4ActivationCode left = terminalBN4ActivationCode right ↔
      left = right := by
  simp [terminalBN4ActivationCode, terminalBN3MinimalConsumer]

/-- Canonical code equality is equivalent to equality of the activation
    functions on every cut.  The reverse direction evaluates only the
    singleton witness cut; it does not enumerate the cut universe. -/
theorem terminalBN4ActivationCode_eq_iff_activation
    {alpha : Type} (left right : alpha) :
    terminalBN4ActivationCode left = terminalBN4ActivationCode right ↔
      ∀ cut,
        (TerminalBN4CodeActive (terminalBN4ActivationCode left) cut ↔
          TerminalBN4CodeActive (terminalBN4ActivationCode right) cut) := by
  constructor
  · intro equal cut
    rw [equal]
  · intro activationEqual
    apply (terminalBN4ActivationCode_eq_iff left right).2
    have leftActive :
        TerminalBN4CodeActive (terminalBN4ActivationCode left) [left] := by
      exact (terminalBN4ActivationCode_active_iff left [left]).2 (by simp
        [TerminalBN3RequestPredicate])
    have rightActive := (activationEqual [left]).1 leftActive
    have rightMember : right ∈ [left] :=
      (terminalBN4ActivationCode_active_iff right [left]).1 rightActive
    have rightEqual : right = left := by
      simpa using rightMember
    exact rightEqual.symm

/-! ## Complete typed cancellation keys -/

/-- Cancellation keys retain the activation atom, the complete semantic
    signature supplied by the finite cell producer, and the complete
    transport type.  No field is erased before comparison. -/
structure TerminalBN4ActivationKey
    (Atom SemanticSignature TransportType : Type) where
  atom : Atom
  semanticSignature : SemanticSignature
  transportType : TransportType
deriving DecidableEq

/-- Equality of complete typed keys is exactly activation-function equality,
    semantic-signature equality, and transport-type equality. -/
theorem terminalBN4ActivationKey_eq_iff
    {Atom SemanticSignature TransportType : Type}
    (left right :
      TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    left = right ↔
      (∀ cut,
        (TerminalBN4CodeActive (terminalBN4ActivationCode left.atom) cut ↔
          TerminalBN4CodeActive
            (terminalBN4ActivationCode right.atom) cut)) ∧
      left.semanticSignature = right.semanticSignature ∧
      left.transportType = right.transportType := by
  constructor
  · intro equal
    subst right
    exact ⟨fun _ => Iff.rfl, rfl, rfl⟩
  · rintro ⟨activationEqual, semanticEqual, transportEqual⟩
    have atomEqual : left.atom = right.atom :=
      (terminalBN4ActivationCode_eq_iff left.atom right.atom).1
        ((terminalBN4ActivationCode_eq_iff_activation left.atom right.atom).2
          activationEqual)
    cases left
    cases right
    cases atomEqual
    cases semanticEqual
    cases transportEqual
    rfl

/-- Positive and negative are the only input and residual polarities. -/
inductive TerminalBN4CellSign where
  | positive
  | negative
deriving DecidableEq, Repr

/-- One finite signed mass cell.  A zero input mass is harmless and disappears
    from the canonical residual; every emitted residual mass is strictly
    positive. -/
structure TerminalBN4ActivationCell
    (Atom SemanticSignature TransportType : Type) where
  key : TerminalBN4ActivationKey Atom SemanticSignature TransportType
  sign : TerminalBN4CellSign
  mass : Nat
deriving DecidableEq

/-- Integer interpretation of one signed cell. -/
def TerminalBN4ActivationCell.signedContribution
    {Atom SemanticSignature TransportType : Type}
    (cell : TerminalBN4ActivationCell Atom SemanticSignature TransportType) :
    Int :=
  match cell.sign with
  | .positive => Int.ofNat cell.mass
  | .negative => -Int.ofNat cell.mass

/-! ## Executable per-key mass totals -/

/-- Total positive mass at one complete typed key. -/
def terminalBN4PositiveMass
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (cells : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType))
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    Nat :=
  (cells.map fun cell =>
    if cell.key = key then
      match cell.sign with
      | .positive => cell.mass
      | .negative => 0
    else 0).sum

/-- Total negative mass at one complete typed key. -/
def terminalBN4NegativeMass
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (cells : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType))
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    Nat :=
  (cells.map fun cell =>
    if cell.key = key then
      match cell.sign with
      | .positive => 0
      | .negative => cell.mass
    else 0).sum

/-- Exact signed input ledger at one complete typed key. -/
def terminalBN4InputSignedMass
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (cells : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType))
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    Int :=
  Int.ofNat (terminalBN4PositiveMass cells key) -
    Int.ofNat (terminalBN4NegativeMass cells key)

/-- The integer input ledger is exactly positive mass less negative mass. -/
theorem terminalBN4IntegerMassLedger_exact
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (cells : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType))
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    terminalBN4InputSignedMass cells key +
        Int.ofNat (terminalBN4NegativeMass cells key) =
      Int.ofNat (terminalBN4PositiveMass cells key) := by
  unfold terminalBN4InputSignedMass
  omega

/-! ## Exact cancellation and canonical residual sign -/

/-- Proof-bearing trichotomy after cancelling one complete typed key. -/
inductive TerminalBN4KeyCancellation
    (positiveMass negativeMass : Nat) where
  | balanced (exact : positiveMass = negativeMass)
  | positive (mass : Nat) (massPositive : 0 < mass)
      (exact : positiveMass = negativeMass + mass)
  | negative (mass : Nat) (massPositive : 0 < mass)
      (exact : negativeMass = positiveMass + mass)

/-- Executable exact natural-mass cancellation. -/
def classifyTerminalBN4KeyCancellation
    (positiveMass negativeMass : Nat) :
    TerminalBN4KeyCancellation positiveMass negativeMass :=
  if equal : positiveMass = negativeMass then
    .balanced equal
  else if positive : negativeMass < positiveMass then
    .positive (positiveMass - negativeMass) (by omega) (by omega)
  else
    .negative (negativeMass - positiveMass) (by omega) (by omega)

/-- Cancel all cells at one exact key. -/
def terminalBN4CancelAtKey
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (cells : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType))
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    TerminalBN4KeyCancellation
      (terminalBN4PositiveMass cells key)
      (terminalBN4NegativeMass cells key) :=
  classifyTerminalBN4KeyCancellation
    (terminalBN4PositiveMass cells key)
    (terminalBN4NegativeMass cells key)

/-- Canonical residual list at one key: empty on exact balance and otherwise a
    singleton of the unique surviving sign. -/
def TerminalBN4KeyCancellation.residualCells
    {Atom SemanticSignature TransportType : Type}
    {positiveMass negativeMass : Nat}
    (outcome : TerminalBN4KeyCancellation positiveMass negativeMass)
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    List (TerminalBN4ActivationCell Atom SemanticSignature TransportType) :=
  match outcome with
  | .balanced _ => []
  | .positive mass _ _ => [{ key := key, sign := .positive, mass := mass }]
  | .negative mass _ _ => [{ key := key, sign := .negative, mass := mass }]

/-- Every emitted residual keeps the complete activation/semantic/transport
    key. -/
theorem TerminalBN4KeyCancellation.residual_key_eq
    {Atom SemanticSignature TransportType : Type}
    {positiveMass negativeMass : Nat}
    (outcome : TerminalBN4KeyCancellation positiveMass negativeMass)
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType)
    (cell : TerminalBN4ActivationCell
      Atom SemanticSignature TransportType)
    (member : cell ∈ outcome.residualCells key) :
    cell.key = key := by
  cases outcome with
  | balanced exact => simp [TerminalBN4KeyCancellation.residualCells] at member
  | positive mass massPositive exact =>
      simp [TerminalBN4KeyCancellation.residualCells] at member
      subst cell
      rfl
  | negative mass massPositive exact =>
      simp [TerminalBN4KeyCancellation.residualCells] at member
      subst cell
      rfl

/-- Every emitted residual has strictly positive natural mass. -/
theorem TerminalBN4KeyCancellation.residual_mass_positive
    {Atom SemanticSignature TransportType : Type}
    {positiveMass negativeMass : Nat}
    (outcome : TerminalBN4KeyCancellation positiveMass negativeMass)
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType)
    (cell : TerminalBN4ActivationCell
      Atom SemanticSignature TransportType)
    (member : cell ∈ outcome.residualCells key) :
    0 < cell.mass := by
  cases outcome with
  | balanced exact => simp [TerminalBN4KeyCancellation.residualCells] at member
  | positive mass massPositive exact =>
      simp [TerminalBN4KeyCancellation.residualCells] at member
      subst cell
      exact massPositive
  | negative mass massPositive exact =>
      simp [TerminalBN4KeyCancellation.residualCells] at member
      subst cell
      exact massPositive

/-- No opposite-sign pair can survive at one key because the canonical
    residual is empty or a singleton. -/
theorem TerminalBN4KeyCancellation.no_opposite_sign_residual
    {Atom SemanticSignature TransportType : Type}
    {positiveMass negativeMass : Nat}
    (outcome : TerminalBN4KeyCancellation positiveMass negativeMass)
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType)
    (left right : TerminalBN4ActivationCell
      Atom SemanticSignature TransportType)
    (leftMember : left ∈ outcome.residualCells key)
    (rightMember : right ∈ outcome.residualCells key) :
    left.sign = right.sign := by
  cases outcome with
  | balanced exact =>
      simp [TerminalBN4KeyCancellation.residualCells] at leftMember
  | positive mass massPositive exact =>
      simp [TerminalBN4KeyCancellation.residualCells] at leftMember rightMember
      subst left
      subst right
      rfl
  | negative mass massPositive exact =>
      simp [TerminalBN4KeyCancellation.residualCells] at leftMember rightMember
      subst left
      subst right
      rfl

/-- Same-key cancellation preserves the exact signed integer contribution. -/
theorem TerminalBN4KeyCancellation.residual_signedContribution_exact
    {Atom SemanticSignature TransportType : Type}
    {positiveMass negativeMass : Nat}
    (outcome : TerminalBN4KeyCancellation positiveMass negativeMass)
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    ((outcome.residualCells key).map
      TerminalBN4ActivationCell.signedContribution).sum =
        Int.ofNat positiveMass - Int.ofNat negativeMass := by
  cases outcome with
  | balanced exact =>
      simp [TerminalBN4KeyCancellation.residualCells]
      omega
  | positive mass massPositive exact =>
      simp [TerminalBN4KeyCancellation.residualCells,
        TerminalBN4ActivationCell.signedContribution]
      omega
  | negative mass massPositive exact =>
      simp [TerminalBN4KeyCancellation.residualCells,
        TerminalBN4ActivationCell.signedContribution]
      omega

/-- The executable cell-list classifier has exactly the original signed mass
    at every complete key. -/
theorem terminalBN4CancelAtKey_signedContribution_exact
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (cells : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType))
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    (((terminalBN4CancelAtKey cells key).residualCells key).map
      TerminalBN4ActivationCell.signedContribution).sum =
        terminalBN4InputSignedMass cells key := by
  unfold terminalBN4InputSignedMass
  exact (terminalBN4CancelAtKey cells key).residual_signedContribution_exact key

/-! ## Canonical finite key universe -/

/-- Duplicate-free first-occurrence key order from the explicit finite cell
    ledger. -/
def terminalBN4CanonicalKeys
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (cells : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType)) :
    List (TerminalBN4ActivationKey Atom SemanticSignature TransportType) :=
  match cells with
  | [] => []
  | cell :: tail =>
      let tailKeys := terminalBN4CanonicalKeys tail
      if cell.key ∈ tailKeys then tailKeys else cell.key :: tailKeys

/-- Canonical keys contain no duplicate cancellation class. -/
theorem terminalBN4CanonicalKeys_nodup
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (cells : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType)) :
    (terminalBN4CanonicalKeys cells).Nodup := by
  induction cells with
  | nil => simp [terminalBN4CanonicalKeys]
  | cons cell tail ih =>
      simp only [terminalBN4CanonicalKeys]
      split
      · exact ih
      · exact List.nodup_cons.2 ⟨by assumption, ih⟩

/-- The canonical key universe contains exactly the keys occurring in the
    input ledger. -/
theorem mem_terminalBN4CanonicalKeys_iff
    {Atom SemanticSignature TransportType : Type}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType]
    (cells : List
      (TerminalBN4ActivationCell Atom SemanticSignature TransportType))
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    key ∈ terminalBN4CanonicalKeys cells ↔
      ∃ cell, cell ∈ cells ∧ cell.key = key := by
  induction cells with
  | nil => simp [terminalBN4CanonicalKeys]
  | cons cell tail ih =>
      simp only [terminalBN4CanonicalKeys]
      split
      · rename_i headAlreadyPresent
        constructor
        · intro keyMember
          obtain ⟨found, foundMember, foundKey⟩ := ih.1 keyMember
          exact ⟨found, by simp [foundMember], foundKey⟩
        · rintro ⟨found, foundMember, foundKey⟩
          simp only [List.mem_cons] at foundMember
          cases foundMember with
          | inl foundHead =>
              subst found
              rw [foundKey] at headAlreadyPresent
              exact headAlreadyPresent
          | inr foundTail =>
              exact ih.2 ⟨found, foundTail, foundKey⟩
      · rename_i headFresh
        constructor
        · intro keyMember
          simp only [List.mem_cons] at keyMember
          cases keyMember with
          | inl keyHead =>
              exact ⟨cell, by simp, keyHead.symm⟩
          | inr keyTail =>
              obtain ⟨found, foundMember, foundKey⟩ := ih.1 keyTail
              exact ⟨found, by simp [foundMember], foundKey⟩
        · rintro ⟨found, foundMember, foundKey⟩
          simp only [List.mem_cons] at foundMember
          simp only [List.mem_cons]
          cases foundMember with
          | inl foundHead =>
              subst found
              exact Or.inl foundKey.symm
          | inr foundTail =>
              exact Or.inr (ih.2 ⟨found, foundTail, foundKey⟩)

/-! ## BN3-consuming proof-bearing package -/

/-- Every explicit cell must use an atom in the successful nucleus's canonical
    BN3 identity space. -/
def TerminalBN4CellsUseCanonicalAtoms
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    {SemanticSignature TransportType : Type}
    (result : TerminalComputedBCELAnchorNucleus problem)
    (cells : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType)) : Prop :=
  (cells.all fun cell =>
    terminalBN3RequestPredicateBool cell.key.atom result.requestAtoms) = true

/-- The executable atom check accepts exactly ledgers whose every cell uses a
    canonical BN3 request atom. -/
theorem terminalBN4CellsUseCanonicalAtoms_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    {SemanticSignature TransportType : Type}
    (result : TerminalComputedBCELAnchorNucleus problem)
    (cells : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType)) :
    TerminalBN4CellsUseCanonicalAtoms result cells ↔
      ∀ cell, cell ∈ cells -> cell.key.atom ∈ result.requestAtoms := by
  simp [TerminalBN4CellsUseCanonicalAtoms,
    terminalBN3RequestPredicateBool_eq_true_iff,
    TerminalBN3RequestPredicate]

/-- Finite BN4 kernel constructed over one successful BN3 identity space and
    one explicit typed cell ledger. -/
structure TerminalComputedBN4ActivationCancellation
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    {SemanticSignature TransportType : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    (result : TerminalComputedBCELAnchorNucleus problem)
    (cells : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType)) : Prop where
  cellsUseCanonicalAtoms : TerminalBN4CellsUseCanonicalAtoms result cells
  activationByActiveAntichain : ∀
    (atom : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)),
    TerminalBN4CodeActive (terminalBN4ActivationCode atom) cut ↔
      TerminalBN3RequestPredicate atom cut
  activationEqualityWithoutCutEnumeration : ∀
    (left right :
      TerminalPrimitiveRecord inputs gates outputs profileWidth),
    terminalBN4ActivationCode left = terminalBN4ActivationCode right ↔
      ∀ cut,
        (TerminalBN4CodeActive (terminalBN4ActivationCode left) cut ↔
          TerminalBN4CodeActive (terminalBN4ActivationCode right) cut)
  completeTypedKeyEquality : ∀ left right : TerminalBN4ActivationKey
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType,
    left = right ↔
      (∀ cut,
        (TerminalBN4CodeActive (terminalBN4ActivationCode left.atom) cut ↔
          TerminalBN4CodeActive
            (terminalBN4ActivationCode right.atom) cut)) ∧
      left.semanticSignature = right.semanticSignature ∧
      left.transportType = right.transportType
  canonicalKeysNodup : (terminalBN4CanonicalKeys cells).Nodup
  sameKeyCancellationExact : ∀ key,
    ((((terminalBN4CancelAtKey cells key).residualCells key).map
      TerminalBN4ActivationCell.signedContribution).sum =
        terminalBN4InputSignedMass cells key)
  completeKeyPreserved : ∀ key cell,
    cell ∈ (terminalBN4CancelAtKey cells key).residualCells key ->
      cell.key = key
  noOppositeSignSameKeyResidual : ∀ key left right,
    left ∈ (terminalBN4CancelAtKey cells key).residualCells key ->
      right ∈ (terminalBN4CancelAtKey cells key).residualCells key ->
        left.sign = right.sign
  residualMassPositive : ∀ key cell,
    cell ∈ (terminalBN4CancelAtKey cells key).residualCells key ->
      0 < cell.mass
  integerMassLedgerExact : ∀ key,
    terminalBN4InputSignedMass cells key +
        Int.ofNat (terminalBN4NegativeMass cells key) =
      Int.ofNat (terminalBN4PositiveMass cells key)

/-- Assemble every finite BN4 kernel obligation after canonical-atom checking;
    no cancellation result or arithmetic certificate is supplied by callers. -/
theorem TerminalComputedBCELAnchorNucleus.computedBN4ActivationCancellation
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    {SemanticSignature TransportType : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    (result : TerminalComputedBCELAnchorNucleus problem)
    (cells : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType))
    (canonicalAtoms : TerminalBN4CellsUseCanonicalAtoms result cells) :
    TerminalComputedBN4ActivationCancellation result cells := by
  exact
    { cellsUseCanonicalAtoms := canonicalAtoms
      activationByActiveAntichain := terminalBN4ActivationCode_active_iff
      activationEqualityWithoutCutEnumeration :=
        terminalBN4ActivationCode_eq_iff_activation
      completeTypedKeyEquality := terminalBN4ActivationKey_eq_iff
      canonicalKeysNodup := terminalBN4CanonicalKeys_nodup cells
      sameKeyCancellationExact :=
        terminalBN4CancelAtKey_signedContribution_exact cells
      completeKeyPreserved := fun key cell member =>
        (terminalBN4CancelAtKey cells key).residual_key_eq key cell member
      noOppositeSignSameKeyResidual := fun key left right leftMember rightMember =>
        (terminalBN4CancelAtKey cells key).no_opposite_sign_residual
          key left right leftMember rightMember
      residualMassPositive := fun key cell member =>
        (terminalBN4CancelAtKey cells key).residual_mass_positive key cell member
      integerMassLedgerExact := terminalBN4IntegerMassLedger_exact cells }

/-! ## Total fail-closed pipeline wrapper -/

/-- Total outcome preserving all upstream BN3 failures, rejecting a typed cell
    ledger with a noncanonical atom, or returning the proved finite BN4 kernel. -/
inductive TerminalBN4ActivationCancellationOutcome
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {SemanticSignature TransportType : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    (problem : TerminalBCELAnchorProblem candidate system)
    (cells : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType)) where
  | insufficient (failure : TerminalBCELInsufficientNucleusFailure problem)
  | algebraFailure
      (nucleus : TerminalMinimalPositiveAnchorNucleus problem)
      (first : findTerminalPositiveAnchorNucleus problem = some nucleus)
      (failure : TerminalBCELAnchorAlgebraFailure problem nucleus.anchors)
  | cutDefectFailure
      (nucleus : TerminalMinimalPositiveAnchorNucleus problem)
      (first : findTerminalPositiveAnchorNucleus problem = some nucleus)
      (failure : TerminalBCELCutDefectFailure problem nucleus.anchors
        (problem.familyDefect nucleus.anchors))
  | cutRouteFailure
      (nucleus : TerminalMinimalPositiveAnchorNucleus problem)
      (first : findTerminalPositiveAnchorNucleus problem = some nucleus)
      (failure : TerminalBCELCutRouteFailure problem nucleus.anchors)
  | invalidAtomLedger
      (result : TerminalComputedBCELAnchorNucleus problem)
      (envelope : TerminalComputedBN3RequestEnvelope result)
      (failure : ¬ TerminalBN4CellsUseCanonicalAtoms result cells)
  | ready
      (result : TerminalComputedBCELAnchorNucleus problem)
      (envelope : TerminalComputedBN3RequestEnvelope result)
      (cancellation : TerminalComputedBN4ActivationCancellation result cells)

private def terminalBN4CellsUseCanonicalAtomsDecidable
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    {SemanticSignature TransportType : Type}
    (result : TerminalComputedBCELAnchorNucleus problem)
    (cells : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType)) :
    Decidable (TerminalBN4CellsUseCanonicalAtoms result cells) := by
  unfold TerminalBN4CellsUseCanonicalAtoms
  infer_instance

/-- Run the existing total BN3 classifier, then deterministically validate and
    cancel the explicit finite typed cell ledger. -/
def classifyTerminalBN4ActivationCancellation
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {SemanticSignature TransportType : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    (problem : TerminalBCELAnchorProblem candidate system)
    (wholePositive : 0 < problem.familyDefect problem.anchorRecords)
    (cells : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType)) :
    TerminalBN4ActivationCancellationOutcome problem cells :=
  match classifyTerminalBN3RequestEnvelope problem wholePositive with
  | .insufficient failure => .insufficient failure
  | .algebraFailure nucleus first failure =>
      .algebraFailure nucleus first failure
  | .cutDefectFailure nucleus first failure =>
      .cutDefectFailure nucleus first failure
  | .cutRouteFailure nucleus first failure =>
      .cutRouteFailure nucleus first failure
  | .ready result envelope =>
      letI : Decidable (TerminalBN4CellsUseCanonicalAtoms result cells) :=
        terminalBN4CellsUseCanonicalAtomsDecidable result cells
      if canonicalAtoms : TerminalBN4CellsUseCanonicalAtoms result cells then
        .ready result envelope
          (result.computedBN4ActivationCancellation cells canonicalAtoms)
      else
        .invalidAtomLedger result envelope canonicalAtoms

/-- No seventh unclassified finite BN4 pipeline case exists. -/
theorem classifyTerminalBN4ActivationCancellation_exhaustive
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {SemanticSignature TransportType : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    (problem : TerminalBCELAnchorProblem candidate system)
    (wholePositive : 0 < problem.familyDefect problem.anchorRecords)
    (cells : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType)) :
    Nonempty (TerminalBN4ActivationCancellationOutcome problem cells) :=
  ⟨classifyTerminalBN4ActivationCancellation problem wholePositive cells⟩

end DirectWire
end PNP
