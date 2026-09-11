# Computed full-profile gain acceptance and exact slack descent

M239 checks the complete profile of the actual M238 physical-gain result.
It closes the acceptance boundary between a smaller Boolean-equivalent
implementation and use of that implementation in the existing full carrier.
The algorithm does not accept a caller-supplied replacement, seed, profile
equality proof or correctness certificate.

## Exact theorem boundary

The [gain-profile module](../lean/PNP/ResidualTerminalGainProfileFirewall.lean)
quantifies over arbitrary finite input, gate, output and profile widths and
the existing executable terminal model.

- `firstTerminalGainProfileMismatch_eq_none_iff` reflects agreement at every
  full-profile coordinate.
- `firstTerminalGainProfileMismatch_spec` identifies the first mismatch
  in canonical coordinate order, with a complete agreeing prefix.
- `terminalFullProfileMinimum_eq_of_fullRealization` proves invariance of
  the attained full-profile minimum under full-carrier realization. It
  transports realizations in both directions and uses their universal lower
  bounds; it does not identify this minimum with the unconstrained Boolean
  reference minimum.
- `classifyTerminalCandidateGainProfile_accepted_iff` characterizes acceptance
  as an actual successful physical search whose result agrees at every
  profile coordinate.
- `classifyTerminalCandidateGainProfile_noGain_iff` characterizes the no-gain
  branch as exactly the existing physical search failure.
- `classifyTerminalCandidateGainProfile_mismatch_iff` characterizes rejection
  through the actual returned implementation and its actual first mismatch.
- `TerminalCandidateFullProfileGain.fullSlack_gain` recovers the actual
  selected proper-positive seed and proves that the accepted replacement's
  full-profile slack plus its local physical gain equals the original
  full-profile slack. The decrease is strict.

The classifier checks all full-profile coordinates, including obligation
coordinates. A quotient projection cannot erase a mismatch from acceptance.
It reuses M238's proved Boolean equivalence rather than rerunning an exhaustive
equivalence check. Existing obligation discharge transports through the full
realization; an open obligation is not thereby discharged.

## Manuscript linkage and limits

The [plan](plans/2026-09-12-computed-full-profile-gain-firewall.md) anchors the
step in the pinned manuscript's section 2 carrier and compatible replacement,
Global slack law, full/quotient mode distinction and section 10
RW-SaturatePositive verified-gain boundary.

The [computed physical gain](lean_residual_terminal_physical_gain.md),
support context, saturation executor and exhaustive reference minima are
unchanged. These are accepted-result laws for a supplied executable profile
model, not a theorem that every physical gain is full-profile compatible.
A first mismatch is not a completed named global route. The classifier
does not search alternative physical gains after a mismatch.

The observer and profile model remain supplied data. Influence, canonical
seed search and semantic minima remain exhaustive finite reference constructions.
Finite termination and a smaller output do not prove a polynomial encoded-size
or runtime bound for the complete construction.

Faithful input-derived manuscript carrier data, complete materializer charges,
fixed global ownership, full-minimum growth during saturation, quotient bounds,
terminal-family derivation and global rank-decreasing route coverage remain
open. Ambient observations are not silently identified with differently typed
global profile observations.

## Regression and assumption evidence

The [permanent regressions](../lean-regression/PNPResidualTerminalGainProfileFirewall.lean)
apply all seven general interfaces at arbitrary dimensions. A minimal genuine
physical gain is accepted by a nonconstant semantic observer. A gate-count
observer rejects the same smaller Boolean-equivalent result at a later
coordinate despite a quotient projection forgetting that coordinate.
Zero profile width and the zero-dimensional no-gain branch are covered.
Obligation tests preserve existing discharge without inventing new discharge.

A bounded diagnostic isolated expensive kernel reduction in the semantic-observer
acceptance fixture. That same input and expected result are exercised by a
guarded Lean runtime assertion that fails on mismatch. Runtime execution is
test evidence, not theorem authority. The seven general theorem applications
and remaining finite branch checks remain kernel checked; no proof statement
or algorithm was weakened to accommodate the fixture.

The [explicit-root audit](../lean-audit/PNPResidualTerminalGainProfileFirewallAxiomAudit.lean)
checks all seven interfaces. Full-profile-minimum invariance uses only
`propext`; the other six use only `propext` and `Quot.sound`.
No project-specific axiom, classical choice or native-execution proof
authority is introduced.
The [source and compiled contracts](../audits/lean-residual-terminal-gain-profile-firewall0.test.mjs)
reject skipped or reordered coordinates, supplied results or profile checks,
weakened descent, finite-only substitutes and compiled type drift.

## Remaining proof burden and progress

No unconditional SaturatePositive, BCELReady or ZeroSlack, complete polynomial
PCCMin, deterministic CNFSAT in P or eligible root theorem follows.
The publication gate remains false. No fixed checkpoint or global gate closes.

Formal artefact coverage: 215 of 217 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

The two measures come from the [canonical progress ledger](../status/PROOF_PROGRESS.json).
Neither expresses confidence that `P = NP` is true, probability of success
or time remaining.

Publication decision: defer. Preserve the coherent M231 PNPLabs source pin.
This is a checked acceptance boundary for an existing physical gain, not a
complete global or polynomial route. Meaningful verified core submilestone
and release notifications continue independently.
