/-
Copyright (c) 2026 PNP Labs.

Executable activation-coherence obstruction between the checked finite
BCEL-ready nucleus and the exactly mapped grouped BN6 Packet family.  M183
computes one terminal defect for every proper nucleus cut, while M184 proves
that constant activation on the same Packet family is impossible.  This module
checks the missing numerical bridge and returns either a cut-value mismatch or
a concrete nonempty proper cut whose activation weight differs from the
terminal defect.

The terminal problem, positive starting premise, Packet family, anchor map,
activation cells and masses, payloads, budget, realizer table, dependency
table, and rank maps remain supplied finite inputs.  The obstruction does not
derive activation coherence from positive residual slack, construct BN3--BN6
data, prove unconditional SaturatePositive, BCELReady, ZeroSlack or PCCMin,
establish polynomial runtime, put SAT in P, remove a project assumption, or
prove P = NP.
-/

import PNP.ResidualTerminalFiniteBCELPacketCarrierCoherence

namespace PNP

/-- The exact M183 nucleus defect against which the mapped Packet quantities
    must be compared. -/
def TerminalFiniteBCELPacketCarrierCoherenceCertificate.terminalDefect
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) : Nat :=
  certificate.problem.anchorProblem.toProblem.familyDefect
    certificate.terminalReady.result.nucleus.anchors

/-- The missing numerical BCEL/Packet bridge: both the declared Packet cut
    value and every governed nonempty proper activation weight equal the exact
    terminal defect. -/
def TerminalFiniteBCELPacketActivationCoherent
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) : Prop :=
  packetBudgetNoLower.family.cutValue = certificate.terminalDefect ∧
    ∀ cut, cut.Sublist packetBudgetNoLower.family.carrier → cut ≠ [] →
      cut ≠ packetBudgetNoLower.family.carrier →
        packetBudgetNoLower.family.activationWeight cut =
          certificate.terminalDefect

/-- Proof-bearing result of the deterministic failed-coherence classifier. -/
inductive TerminalFiniteBCELPacketActivationObstruction
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) where
  | cutValueMismatch
      (mismatch : packetBudgetNoLower.family.cutValue ≠
        certificate.terminalDefect)
  | activationMismatch
      (cut : List packetBudgetNoLower.Anchor)
      (included : cut.Sublist packetBudgetNoLower.family.carrier)
      (nonempty : cut ≠ [])
      (proper : cut ≠ packetBudgetNoLower.family.carrier)
      (mismatch : packetBudgetNoLower.family.activationWeight cut ≠
        certificate.terminalDefect)

private def terminalFiniteBCELPacketProperCuts
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (_certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) :
    List (List packetBudgetNoLower.Anchor) :=
  (DirectWire.terminalListSubsets
    packetBudgetNoLower.family.carrier).filter fun cut =>
      decide (cut ≠ [] ∧ cut ≠ packetBudgetNoLower.family.carrier)

private theorem mem_terminalFiniteBCELPacketProperCuts_iff
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower)
    (cut : List packetBudgetNoLower.Anchor) :
    cut ∈ terminalFiniteBCELPacketProperCuts certificate ↔
      cut.Sublist packetBudgetNoLower.family.carrier ∧ cut ≠ [] ∧
        cut ≠ packetBudgetNoLower.family.carrier := by
  unfold terminalFiniteBCELPacketProperCuts
  constructor
  · intro member
    have parts := List.mem_filter.mp member
    have proper : cut ≠ [] ∧ cut ≠ packetBudgetNoLower.family.carrier :=
      of_decide_eq_true parts.2
    exact ⟨DirectWire.terminalListSubsets_sublist
      packetBudgetNoLower.family.carrier cut parts.1,
      proper.1, proper.2⟩
  · intro proper
    exact List.mem_filter.mpr
      ⟨DirectWire.terminalV53_sublist_mem_terminalListSubsets proper.1,
        decide_eq_true ⟨proper.2.1, proper.2.2⟩⟩

/-- Recompute the cut-value comparison and every canonical nonempty proper
    Packet-cut activation comparison. -/
def checkTerminalFiniteBCELPacketActivationCoherence
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) : Bool :=
  decide (packetBudgetNoLower.family.cutValue =
    certificate.terminalDefect) &&
  (terminalFiniteBCELPacketProperCuts certificate).all fun cut =>
    decide (packetBudgetNoLower.family.activationWeight cut =
      certificate.terminalDefect)

/-- The executable check accepts exactly the complete finite activation-
    coherence proposition; no caller flag or sampled-cut certificate is used. -/
theorem checkTerminalFiniteBCELPacketActivationCoherence_eq_true_iff
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) :
    checkTerminalFiniteBCELPacketActivationCoherence certificate = true ↔
      TerminalFiniteBCELPacketActivationCoherent certificate := by
  constructor
  · intro accepted
    have checks :
        decide (packetBudgetNoLower.family.cutValue =
          certificate.terminalDefect) = true ∧
        (terminalFiniteBCELPacketProperCuts certificate).all (fun cut =>
          decide (packetBudgetNoLower.family.activationWeight cut =
            certificate.terminalDefect)) = true := by
      simpa only [checkTerminalFiniteBCELPacketActivationCoherence,
        Bool.and_eq_true] using accepted
    refine ⟨of_decide_eq_true checks.1, ?_⟩
    intro cut included nonempty proper
    have checked := (List.all_eq_true.mp checks.2) cut
      ((mem_terminalFiniteBCELPacketProperCuts_iff certificate cut).2
        ⟨included, nonempty, proper⟩)
    exact of_decide_eq_true checked
  · rintro ⟨cutValue, allCuts⟩
    simp only [checkTerminalFiniteBCELPacketActivationCoherence,
      Bool.and_eq_true]
    refine ⟨decide_eq_true cutValue, ?_⟩
    apply List.all_eq_true.mpr
    intro cut member
    have proper :=
      (mem_terminalFiniteBCELPacketProperCuts_iff certificate cut).1 member
    exact decide_eq_true (allCuts cut proper.1 proper.2.1 proper.2.2)

/-- Hypothetical checker acceptance supplies the exact missing numerical link:
    the activation weight of every mapped terminal proper cut equals that
    cut's M183 projection excess. -/
theorem TerminalFiniteBCELPacketCarrierCoherenceCertificate.activation_coherent_mapped_cut_equation
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower)
    (coherent : TerminalFiniteBCELPacketActivationCoherent certificate)
    (cut : List (DirectWire.TerminalPrimitiveRecord
      packetBudgetNoLower.inputs packetBudgetNoLower.gates
      packetBudgetNoLower.outputs packetBudgetNoLower.profileWidth))
    (proper : DirectWire.TerminalBCELProperCutSeed
      certificate.terminalReady.result.nucleus.anchors cut) :
    Int.ofNat (packetBudgetNoLower.family.activationWeight
      (cut.map certificate.anchorMap)) =
      ((certificate.problem.anchorProblem.toProblem.cutCarrier
        certificate.terminalReady.result.nucleus.anchors cut).optimizationCorners
          certificate.problem.anchorProblem.toProblem.observe).projectionExcess := by
  have included : cut.Sublist
      certificate.terminalReady.result.nucleus.anchors :=
    DirectWire.terminalListSubsets_sublist
      certificate.terminalReady.result.nucleus.anchors cut proper.1
  have mappedIncluded : (cut.map certificate.anchorMap).Sublist
      packetBudgetNoLower.family.carrier := by
    rw [certificate.family_carrier_eq]
    exact included.map certificate.anchorMap
  have mappedNonempty : cut.map certificate.anchorMap ≠ [] := by
    intro mappedNil
    have lengthZero : cut.length = 0 := by
      have lengths := congrArg List.length mappedNil
      simpa only [List.length_map, List.length_nil] using lengths
    exact proper.2.1 (List.eq_nil_of_length_eq_zero lengthZero)
  have mappedProper : cut.map certificate.anchorMap ≠
      packetBudgetNoLower.family.carrier := by
    intro mappedFull
    have lengths := congrArg List.length mappedFull
    have equalLengths : cut.length =
        certificate.terminalReady.result.nucleus.anchors.length := by
      simpa only [certificate.family_carrier_eq, List.length_map] using lengths
    exact (Nat.ne_of_lt proper.2.2) equalLengths
  have activation := coherent.2 (cut.map certificate.anchorMap)
    mappedIncluded mappedNonempty mappedProper
  calc
    Int.ofNat (packetBudgetNoLower.family.activationWeight
        (cut.map certificate.anchorMap)) =
        Int.ofNat certificate.terminalDefect :=
      congrArg Int.ofNat activation
    _ = ((certificate.problem.anchorProblem.toProblem.cutCarrier
          certificate.terminalReady.result.nucleus.anchors cut).optimizationCorners
            certificate.problem.anchorProblem.toProblem.observe).projectionExcess := by
      simpa only [
        TerminalFiniteBCELPacketCarrierCoherenceCertificate.terminalDefect]
        using (certificate.terminalReady.properCutConstantEquation
          cut proper).symm

/-- M184's same-family Packet exclusion makes complete activation coherence
    impossible. -/
theorem TerminalFiniteBCELPacketCarrierCoherenceCertificate.not_activation_coherent
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) :
    ¬TerminalFiniteBCELPacketActivationCoherent certificate := by
  intro coherent
  apply certificate.not_constant_activation
  intro cut included nonempty proper
  exact (coherent.2 cut included nonempty proper).trans coherent.1.symm

private def firstTerminalFiniteBCELPacketActivationMismatch?
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) :
    Option (List packetBudgetNoLower.Anchor) :=
  (terminalFiniteBCELPacketProperCuts certificate).find? fun cut =>
    decide (packetBudgetNoLower.family.activationWeight cut ≠
      certificate.terminalDefect)

private theorem firstTerminalFiniteBCELPacketActivationMismatch?_sound
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower)
    (cut : List packetBudgetNoLower.Anchor)
    (found : firstTerminalFiniteBCELPacketActivationMismatch? certificate =
      some cut) :
    (cut.Sublist packetBudgetNoLower.family.carrier ∧ cut ≠ [] ∧
      cut ≠ packetBudgetNoLower.family.carrier) ∧
    packetBudgetNoLower.family.activationWeight cut ≠
      certificate.terminalDefect := by
  have member : cut ∈ terminalFiniteBCELPacketProperCuts certificate :=
    List.mem_of_find?_eq_some found
  have expanded :
      (terminalFiniteBCELPacketProperCuts certificate).find? (fun candidate =>
        decide (packetBudgetNoLower.family.activationWeight candidate ≠
          certificate.terminalDefect)) = some cut := by
    simpa only [firstTerminalFiniteBCELPacketActivationMismatch?] using found
  have mismatchChecked : decide
      (packetBudgetNoLower.family.activationWeight cut ≠
        certificate.terminalDefect) = true :=
    @List.find?_some (List packetBudgetNoLower.Anchor)
      (fun candidate => decide
        (packetBudgetNoLower.family.activationWeight candidate ≠
          certificate.terminalDefect)) cut
      (terminalFiniteBCELPacketProperCuts certificate) expanded
  exact ⟨
    (mem_terminalFiniteBCELPacketProperCuts_iff certificate cut).1 member,
    of_decide_eq_true mismatchChecked⟩

private theorem firstTerminalFiniteBCELPacketActivationMismatch?_eq_none_all
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower)
    (noneFound : firstTerminalFiniteBCELPacketActivationMismatch? certificate =
      none) :
    ∀ cut, cut.Sublist packetBudgetNoLower.family.carrier → cut ≠ [] →
      cut ≠ packetBudgetNoLower.family.carrier →
        packetBudgetNoLower.family.activationWeight cut =
          certificate.terminalDefect := by
  intro cut included nonempty proper
  by_cases activationMatches : packetBudgetNoLower.family.activationWeight cut =
      certificate.terminalDefect
  · exact activationMatches
  · have member : cut ∈ terminalFiniteBCELPacketProperCuts certificate :=
      (mem_terminalFiniteBCELPacketProperCuts_iff certificate cut).2
        ⟨included, nonempty, proper⟩
    have mismatchChecked : decide
        (packetBudgetNoLower.family.activationWeight cut ≠
          certificate.terminalDefect) = true :=
      decide_eq_true activationMatches
    have someMismatch :
        (firstTerminalFiniteBCELPacketActivationMismatch?
          certificate).isSome = true :=
      (List.find?_isSome).mpr ⟨cut, member, mismatchChecked⟩
    rw [noneFound] at someMismatch
    exact Bool.noConfusion someMismatch

/-- Deterministically return the declared-value mismatch first, otherwise the
    first canonical proper cut whose activation weight misses the terminal
    defect. The impossible all-match branch is discharged by M184. -/
def classifyTerminalFiniteBCELPacketActivationObstruction
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) :
    TerminalFiniteBCELPacketActivationObstruction certificate := by
  by_cases cutValueMatches : packetBudgetNoLower.family.cutValue =
      certificate.terminalDefect
  · match found : firstTerminalFiniteBCELPacketActivationMismatch?
      certificate with
    | none =>
        have coherent : TerminalFiniteBCELPacketActivationCoherent
            certificate :=
          ⟨cutValueMatches,
            firstTerminalFiniteBCELPacketActivationMismatch?_eq_none_all
              certificate found⟩
        exact False.elim (certificate.not_activation_coherent coherent)
    | some cut =>
        have sound :=
          firstTerminalFiniteBCELPacketActivationMismatch?_sound
            certificate cut found
        exact .activationMismatch cut sound.1.1 sound.1.2.1
          sound.1.2.2 sound.2
  · exact .cutValueMismatch cutValueMatches

/-- The exact complete finite coherence checker must reject on the accepted
    M184 family. -/
theorem TerminalFiniteBCELPacketCarrierCoherenceCertificate.activation_coherence_check_eq_false
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) :
    checkTerminalFiniteBCELPacketActivationCoherence certificate = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact certificate.not_activation_coherent
    ((checkTerminalFiniteBCELPacketActivationCoherence_eq_true_iff
      certificate).1 accepted)

/-- Named M185 endpoint: the missing numerical bridge is checked completely
    and fails with either the exact declared cut value or a proof-bearing
    governed proper-cut activation mismatch. -/
theorem terminal_finite_bcel_packet_activation_obstruction_checked_complete
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) :
    checkTerminalFiniteBCELPacketActivationCoherence certificate = false ∧
    (packetBudgetNoLower.family.cutValue ≠ certificate.terminalDefect ∨
      ∃ cut, cut.Sublist packetBudgetNoLower.family.carrier ∧ cut ≠ [] ∧
        cut ≠ packetBudgetNoLower.family.carrier ∧
        packetBudgetNoLower.family.activationWeight cut ≠
          certificate.terminalDefect) := by
  refine ⟨certificate.activation_coherence_check_eq_false, ?_⟩
  exact match
      classifyTerminalFiniteBCELPacketActivationObstruction certificate with
    | .cutValueMismatch mismatch => Or.inl mismatch
    | .activationMismatch cut included nonempty proper mismatch =>
        Or.inr ⟨cut, included, nonempty, proper, mismatch⟩

end PNP
