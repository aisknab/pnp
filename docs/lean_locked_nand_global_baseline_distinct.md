# Lean locked-NAND global baseline distinctness

`lean/PNP/LockedNANDGlobalCandidates.lean` now discharges the next bounded
Section 17 obligation from the pinned legacy manuscript. For every nonempty,
finite, topologically typed NAND circuit, the exact square baseline candidate
satisfies all three semantic conditions required by the direct-wire output
lower bound.

## Plain-language result

The baseline exposes one Boolean output for every gate it contains. Merely
having the same number of outputs and gates is not enough to prove that all
those gates are necessary: two outputs could secretly compute the same
function, an output could be constant, or it could simply copy an input.

Lean now rules out all three shortcuts for every circuit in the family:

- each exposed output changes on some input;
- no exposed output is just a positive copy of one carrier bit; and
- every pair of different exposed coordinates computes different Boolean
  functions.

Because the baseline has exactly `B` outputs and `B` gates, the exhaustive
reference minimum is therefore exactly `B`.

## Constructive separation argument

Each local source or trace macro was already proved to satisfy the baseline
conditions using its own fresh lock coordinate. The new proof lifts those
finite local witnesses through the complete topological macro assembly.

The prefix conjunction is more subtle because every prefix gate combines
several checks. The proof constructs explicit valuations showing that every
prefix gate depends on both of the final two distinguished checks: the final
right-source lock and final trace lock. Arbitrary check vectors are realized
by coherent carrier valuations, so those local prefix witnesses lift to the
actual circuit carrier.

For a cross pair consisting of one macro gate and one prefix gate, the macro
gate is independent of at least one of those two anchors:

- every gate before the final trace block is independent of the final trace
  lock; and
- every gate inside the final trace block is independent of the final
  right-source lock.

The prefix output necessarily changes at both anchors. Essential dependence
on one side and independence on the other gives a concrete valuation that
separates the two functions. This closes every macro/macro, prefix/prefix, and
macro/prefix case without a caller certificate or host-side search.

## Public theorem boundary

The five new declarations are:

- `baselineCandidate_outputNonconstant`;
- `baselineCandidate_outputNotPositiveProjection`;
- `baselineCandidate_outputPairwiseDistinct`;
- `baselineCandidate_outputConditions`; and
- `baselineCandidate_referenceMinimum`.

The dedicated axiom transcript reports exactly `propext` and `Quot.sound` for
each theorem. It reaches neither `Classical.choice` nor any of the four
project assumptions. A constructive impossible-case proof is retained
explicitly so the closure cannot silently widen through tactic-generated
choice.

The regression instantiates both an input-source circuit and a constant-source
circuit. It checks all three semantic interfaces and exact exhaustive minima
`42` and `28`, respectively. The hostile mutation audit rejects missing or
weakened theorem shapes, extra declarations, assumptions, `Classical.choice`,
`sorry`, `admit`, native evaluation, host lookup, caller certificates, and
threshold overclaims.

## What this does not prove

This milestone instantiates `baselineConditions` in the six-field conditional
threshold package. At this boundary, two semantic fields remained:

1. `unsatisfiableFinalZero`; and
2. `satisfiableFinalConditions`.

The following unsatisfiable-final-zero milestone now discharges the first
field on the whole carrier. `satisfiableFinalConditions` remains open.
Baseline distinctness alone does not prove either whole-carrier final-output
law. The later unsatisfiable and
[`global semantic threshold`](./lean_locked_nand_global_semantic_threshold.md)
milestones now prove both branches, the typed threshold, and residual slack
at most four. The answer-independent encoded polynomial builder from input
bitstrings, report-level language link, deterministic polynomial-time CNF-SAT
decider, NP-completeness theorem, and `P = NP` remain absent.

The legacy manuscript remains the reconstruction specification. An
alternative construction is appropriate only if a precise Lean obligation
shows that route to be inconsistent or incomplete; no new assumption is
introduced to force the result.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-27-86`: 12,245 declarations, 7,158
theorems, 3,676 assumption-free theorems, 4,997 excluded private
declarations, 105 source-closure modules, and 1,968 reviewed milestone
candidates. Its 11,181,437 canonical bytes have SHA-256
`33ceee3aa55116581d0c6b9790a35c046832076b168e77116e71bb8573ec3ea1`;
the Lean source-closure SHA-256 is
`01b522a560680c69c52c988a0c08c25483d12f5e53de72ff1d8106ae4313a738`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-27-86` has
66 milestones, of which 63 are earned and the same three global milestones
remain unearned, plus 1,968 exact kernel-type fingerprints. Its canonical
reviewed-object fingerprint is
`4f8e3bfd7f028ae17d2d84eef1876ad2e3fc68faf9ca383940c35bd6f0a0a529`.
Its 645,075 file bytes have SHA-256
`abf11a2bfcc536c0ba5a509575bed8f6d0cc7ecb1df01f9a079d37e3dc7d8200`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-27-86` has
1,578,871 bytes and SHA-256
`06d77025ac41dda41d748f43080ffcf9ebd56b606e0d1a1d0a0c4d7c32df9569`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-27-86`; its 151,526-byte
TeX has SHA-256
`a8b59bfbcd67a2c50127ba77e7d659564623c8e9844f8bf3f1f741c2b03299c7`,
and its 63-page, 402,808-byte PDF has SHA-256
`9991dd5fcc9fc8da5ba1161434af216b23735b6f379fee9fa6cdd28c2227d4f3`.

All five activation fingerprints remain unset, all four project assumptions
and six blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete
publication gate remains false.
