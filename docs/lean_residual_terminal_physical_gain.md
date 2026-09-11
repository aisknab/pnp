# Computed proper-support physical gain and exact slack descent

M238 turns the actual production proper-positive support search into a
constructed whole-circuit physical gain. It connects the existing search,
reference-minimum witness and computed replacement context without adding
a caller-supplied seed, replacement or correctness certificate.

## Exact theorem boundary

The [physical-gain module](../lean/PNP/ResidualTerminalPhysicalGain.lean)
defines `terminalCandidateSaturatePhysicalMinimumReplacement` for every
candidate, executable terminal model and seed. The unchanged extractor and
M237 context surround the existing exhaustive reference-minimum support witness.

Three universal interfaces hold without properness or positivity premises:

- `terminalCandidateSaturatePhysicalMinimumReplacement_equivalent` preserves
  the complete original ordered Boolean output word.
- `terminalCandidateSaturatePhysicalMinimumReplacement_size_gain` proves
  that replacement gate count plus computed local gain equals original size.
- `terminalCandidateSaturatePhysicalMinimumReplacement_slack_gain` proves
  that replacement physical residual slack plus that same gain equals
  original physical residual slack.

The optional `findTerminalCandidatePhysicalGain` maps this construction over
`findTerminalCandidateProperPositiveSupport`. It does not run a new enumerator
or accept a search result as input.

- `findTerminalCandidatePhysicalGain_sound` recovers the actual selected
  canonical seed, properness and positive local gain from every successful
  result. It proves whole Boolean equivalence, both exact equations, and
  strict decrease of physical gate count and physical residual slack.
- `findTerminalCandidatePhysicalGain_eq_none_iff` characterizes failure as
  absence of every canonical proper positive seed for the actual
  candidate-derived system. It does not conclude global minimality.

All interfaces quantify over arbitrary finite input, gate, output and profile
widths. The algorithm uses computed saturation and its computed context; no
external dependency relation, frame or whole-replacement certificate is supplied.

## Manuscript linkage and limits

The [plan](plans/2026-09-12-computed-proper-support-physical-gain.md) anchors
the step in the pinned manuscript's section 2 Compatible replacement and
Global slack law, section 3 saturated support calculus, and section 10
RW-SaturatePositive's verified-gain outcomes.

The [computed support context](lean_residual_terminal_saturated_support_context.md),
[physical charge ledger](lean_residual_terminal_physical_charge_ledger.md),
saturation executor, support extractor, observer, classifier and reference
minimum are unchanged.

These are physical Boolean reference gain-realization laws, not full-profile
replacement compatibility or a complete named global route. The complete
profile/materializer charge universe, fixed global ownership, obligation
transport, full-minimum growth, quotient bounds and full-profile
rank-decreasing route coverage remain open.

The observer and profile model remain supplied data. Influence, canonical seed
search and semantic minima remain exhaustive finite reference constructions.
Finite termination and a smaller output do not prove a polynomial encoded-size
or runtime bound for the complete construction.

## Regression and assumption evidence

The [permanent regressions](../lean-regression/PNPResidualTerminalPhysicalGain.lean)
apply all five theorem interfaces at arbitrary dimensions. Fixed-seed execution
checks a genuine two-gate local gain, exact replacement size and slack, repeated
outputs, input bypasses, repeated seeds and empty support. A smaller circuit
executes the complete search/minimum/context pipeline with a real proper
positive result. Zero-dimensional and wire-only candidates exercise failure.

A double-negation circuit has positive whole-circuit slack but no proper
positive saturated support. Its checked search failure protects the crucial
distinction between absence of a proper local witness and global minimality.
It is not a claim that the manuscript's other named routes fail.

An oversized rich complete-search regression was discarded as failed
verification. Bounded prefix diagnosis isolated that exhaustive computation.
The final regression retains the rich fixed-seed checks and the smaller
complete-search case; no theorem statement or claim was weakened.

The [explicit-root audit](../lean-audit/PNPResidualTerminalPhysicalGainAxiomAudit.lean)
checks all five interfaces. Their axiom closures contain only `propext` and
`Quot.sound`, with no project-specific axiom or classical choice.
The [source and compiled contracts](../audits/lean-residual-terminal-physical-gain0.test.mjs)
reject supplied results, finite-only substitutes, weakened size/slack descent,
omitted canonical seeds, overstated failure and compiled type drift.

## Remaining proof burden and progress

No input-derived complete terminal family, global named route completeness,
unconditional SaturatePositive, BCELReady or ZeroSlack, complete polynomial
PCCMin, deterministic CNFSAT in P or eligible root theorem follows.
The publication gate remains false. No fixed checkpoint or global gate closes.

Formal artefact coverage: 214 of 216 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

The two measures come from the [canonical progress ledger](../status/PROOF_PROGRESS.json).
Neither expresses confidence that `P = NP` is true, probability of success
or time remaining.

Publication decision: defer. Preserve the coherent M231 PNPLabs source pin
until a major full-profile, global or polynomial capability warrants publication.
Meaningful verified core submilestone and release notifications continue independently.
