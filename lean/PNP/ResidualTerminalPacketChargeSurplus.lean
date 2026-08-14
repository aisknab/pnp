/-
Copyright (c) 2026 PNP Labs.

Finite charge-surplus arithmetic for the Packet selector realizer route.  An
exact occurrence ledger pairs every replacement charge with one support
charge, preserves the weight of each pair, partitions the complete support
ledger into paired and unmatched occurrences, and identifies an unmatched
support charge of positive weight.  These structural facts, rather than an
assumed inequality, imply that the replacement has strictly smaller total
weight.

When the two totals are exact NAND gate counts and semantic equivalence is
proved independently, the strict surplus constructs a genuine
`StrictEquivalentGain` and hence strict residual descent.  The finite ledgers,
pairing, gate accounting, and equivalence remain explicit inputs.  This module
does not construct selector replacements, derive charge ledgers from terminal
data, prove realizer faithfulness or typed failure routes, close HB/rank
routing, establish polynomial bounds, prove unconditional ZeroSlack or
PCCMin, put SAT in P, remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPacketSelectorGainCoverage

namespace PNP
namespace DirectWire

/-! ## Exact finite occurrence matching -/

/-- A finite occurrence-level charge injection with strict surplus.  The two
    `Perm` fields account for multiplicity exactly: every replacement
    occurrence appears in one match, while every support occurrence appears
    either in one match or in the unmatched remainder.  Thus duplicated charge
    values cannot reuse one support occurrence. -/
structure TerminalPacketChargeSurplus
    {SupportCharge ReplacementCharge : Type}
    (support : List SupportCharge)
    (replacement : List ReplacementCharge)
    (supportWeight : SupportCharge -> Nat)
    (replacementWeight : ReplacementCharge -> Nat) : Type where
  pairing : List (SupportCharge × ReplacementCharge)
  unmatched : List SupportCharge
  supportExact : support.Perm (pairing.map Prod.fst ++ unmatched)
  replacementExact : replacement.Perm (pairing.map Prod.snd)
  weightPreserved : ∀ entry, entry ∈ pairing ->
    replacementWeight entry.2 = supportWeight entry.1
  positiveUnmatched : ∃ charge, charge ∈ unmatched ∧ 0 < supportWeight charge

/-- Every paired replacement charge has exactly the weight of its distinct
    matched support occurrence, so the two paired totals agree. -/
theorem TerminalPacketChargeSurplus.matchedWeight_eq
    {SupportCharge ReplacementCharge : Type}
    {support : List SupportCharge}
    {replacement : List ReplacementCharge}
    {supportWeight : SupportCharge -> Nat}
    {replacementWeight : ReplacementCharge -> Nat}
    (surplus : TerminalPacketChargeSurplus support replacement
      supportWeight replacementWeight) :
    (surplus.pairing.map fun entry => replacementWeight entry.2).sum =
      (surplus.pairing.map fun entry => supportWeight entry.1).sum :=
  terminalV53_sum_congr surplus.pairing
    (fun entry => replacementWeight entry.2)
    (fun entry => supportWeight entry.1)
    surplus.weightPreserved

/-- Exact support occurrence accounting splits total support weight into the
    matched total and the unmatched remainder total. -/
theorem TerminalPacketChargeSurplus.supportWeight_eq_matched_add_unmatched
    {SupportCharge ReplacementCharge : Type}
    {support : List SupportCharge}
    {replacement : List ReplacementCharge}
    {supportWeight : SupportCharge -> Nat}
    {replacementWeight : ReplacementCharge -> Nat}
    (surplus : TerminalPacketChargeSurplus support replacement
      supportWeight replacementWeight) :
    (support.map supportWeight).sum =
      (surplus.pairing.map fun entry => supportWeight entry.1).sum +
        (surplus.unmatched.map supportWeight).sum := by
  have permuted := (surplus.supportExact.map supportWeight).sum_nat
  simpa only [List.map_append, List.sum_append, List.map_map,
    Function.comp_def] using permuted

/-- Exact replacement occurrence accounting identifies its total with the
    paired replacement total. -/
theorem TerminalPacketChargeSurplus.replacementWeight_eq_matched
    {SupportCharge ReplacementCharge : Type}
    {support : List SupportCharge}
    {replacement : List ReplacementCharge}
    {supportWeight : SupportCharge -> Nat}
    {replacementWeight : ReplacementCharge -> Nat}
    (surplus : TerminalPacketChargeSurplus support replacement
      supportWeight replacementWeight) :
    (replacement.map replacementWeight).sum =
      (surplus.pairing.map fun entry => replacementWeight entry.2).sum := by
  have permuted := (surplus.replacementExact.map replacementWeight).sum_nat
  simpa only [List.map_map, Function.comp_def] using permuted

/-- The unmatched remainder has positive total weight because it contains a
    disclosed positive support occurrence. -/
theorem TerminalPacketChargeSurplus.unmatchedWeight_pos
    {SupportCharge ReplacementCharge : Type}
    {support : List SupportCharge}
    {replacement : List ReplacementCharge}
    {supportWeight : SupportCharge -> Nat}
    {replacementWeight : ReplacementCharge -> Nat}
    (surplus : TerminalPacketChargeSurplus support replacement
      supportWeight replacementWeight) :
    0 < (surplus.unmatched.map supportWeight).sum := by
  obtain ⟨charge, member, positive⟩ := surplus.positiveUnmatched
  exact Nat.lt_of_lt_of_le positive
    (terminalV53_term_le_sum surplus.unmatched supportWeight charge member)

/-- Exact occurrence accounting and a nonempty unmatched remainder also make
    the replacement ledger strictly shorter than the support ledger.  This is
    the occurrence-level injectivity check; the weighted theorem below is the
    gate-cost conclusion. -/
theorem TerminalPacketChargeSurplus.replacementLength_lt_supportLength
    {SupportCharge ReplacementCharge : Type}
    {support : List SupportCharge}
    {replacement : List ReplacementCharge}
    {supportWeight : SupportCharge -> Nat}
    {replacementWeight : ReplacementCharge -> Nat}
    (surplus : TerminalPacketChargeSurplus support replacement
      supportWeight replacementWeight) :
    replacement.length < support.length := by
  have replacementLength : replacement.length = surplus.pairing.length := by
    simpa only [List.length_map] using surplus.replacementExact.length_eq
  have supportLength : support.length =
      surplus.pairing.length + surplus.unmatched.length := by
    simpa only [List.length_append, List.length_map] using
      surplus.supportExact.length_eq
  have unmatchedLengthPositive : 0 < surplus.unmatched.length := by
    obtain ⟨charge, member, _positive⟩ := surplus.positiveUnmatched
    cases equation : surplus.unmatched with
    | nil => simp [equation] at member
    | cons head tail => simp
  calc
    replacement.length = surplus.pairing.length := replacementLength
    _ < surplus.pairing.length + surplus.unmatched.length :=
      Nat.lt_add_of_pos_right unmatchedLengthPositive
    _ = support.length := supportLength.symm

/-- The manuscript's unmatched-positive-charge argument: exact injective
    matching and weight preservation force strict total charge surplus. -/
theorem TerminalPacketChargeSurplus.replacementWeight_lt_supportWeight
    {SupportCharge ReplacementCharge : Type}
    {support : List SupportCharge}
    {replacement : List ReplacementCharge}
    {supportWeight : SupportCharge -> Nat}
    {replacementWeight : ReplacementCharge -> Nat}
    (surplus : TerminalPacketChargeSurplus support replacement
      supportWeight replacementWeight) :
    (replacement.map replacementWeight).sum <
      (support.map supportWeight).sum := by
  calc
    (replacement.map replacementWeight).sum =
        (surplus.pairing.map fun entry => replacementWeight entry.2).sum :=
      surplus.replacementWeight_eq_matched
    _ = (surplus.pairing.map fun entry => supportWeight entry.1).sum :=
      surplus.matchedWeight_eq
    _ < (surplus.pairing.map fun entry => supportWeight entry.1).sum +
        (surplus.unmatched.map supportWeight).sum :=
      Nat.lt_add_of_pos_right surplus.unmatchedWeight_pos
    _ = (support.map supportWeight).sum :=
      surplus.supportWeight_eq_matched_add_unmatched.symm

/-! ## Gate-count and semantic realization -/

/-- A Packet replacement whose complete support and replacement charge totals
    account exactly for the two NAND gate counts.  Semantic equivalence is kept
    independent of charge arithmetic; strict gate decrease is deliberately not
    a field. -/
structure TerminalPacketChargeSurplusRealization
    {SupportCharge ReplacementCharge : Type}
    {inputs outputs : Nat}
    (current next : Implementation inputs outputs)
    (support : List SupportCharge)
    (replacement : List ReplacementCharge)
    (supportWeight : SupportCharge -> Nat)
    (replacementWeight : ReplacementCharge -> Nat) : Type where
  surplus : TerminalPacketChargeSurplus support replacement
    supportWeight replacementWeight
  supportAccountsCurrent :
    (support.map supportWeight).sum = current.gateCount
  replacementAccountsNext :
    (replacement.map replacementWeight).sum = next.gateCount
  semanticsPreserved : Equivalent next.candidate.program
    next.candidate.directWireWord current.candidate.program
    current.candidate.directWireWord

/-- Exact charge surplus plus independent semantic preservation constructs a
    genuine strict equivalent gain; no strict inequality is accepted from the
    caller. -/
theorem TerminalPacketChargeSurplusRealization.strictEquivalentGain
    {SupportCharge ReplacementCharge : Type}
    {inputs outputs : Nat}
    {current next : Implementation inputs outputs}
    {support : List SupportCharge}
    {replacement : List ReplacementCharge}
    {supportWeight : SupportCharge -> Nat}
    {replacementWeight : ReplacementCharge -> Nat}
    (realization : TerminalPacketChargeSurplusRealization current next support
      replacement supportWeight replacementWeight) :
    StrictEquivalentGain current next := by
  refine ⟨?_, realization.semanticsPreserved⟩
  rw [← realization.supportAccountsCurrent,
    ← realization.replacementAccountsNext]
  exact realization.surplus.replacementWeight_lt_supportWeight

/-- The charge-derived gain strictly decreases the established reference
    residual slack. -/
theorem TerminalPacketChargeSurplusRealization.strictResidualDescent
    {SupportCharge ReplacementCharge : Type}
    {inputs outputs : Nat}
    {current next : Implementation inputs outputs}
    {support : List SupportCharge}
    {replacement : List ReplacementCharge}
    {supportWeight : SupportCharge -> Nat}
    {replacementWeight : ReplacementCharge -> Nat}
    (realization : TerminalPacketChargeSurplusRealization current next support
      replacement supportWeight replacementWeight) :
    residualSlack next < residualSlack current :=
  realization.strictEquivalentGain.strictResidualDescent

end DirectWire
end PNP
