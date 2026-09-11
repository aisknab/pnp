# M239 plan: computed full-profile acceptance of physical gain

This is a pre-implementation specification, not an earned release claim.
Preparation is based on the verified M238 source at `7ad33c7920884ed2efd8b215cadd4965f09fec13`, tree
`e974fa8e0fdfd3e43c3833c24a3f5056bf68fe48`. Reanchor to its actual merge before release and require all
predecessor release checks. Do not publish a dependent result over an
unverified predecessor.

## Manuscript anchor and missing dependency

The manuscript pinned by [the archive manifest](../../archive/legacy-v0/ARCHIVE.json)
defines the carrier, compatible replacement and Global slack law in section 2.
The full/quotient mode firewall and section 10 RW-SaturatePositive require a
verified gain to respect the complete active carrier, not only Boolean outputs.

M238 computes a smaller Boolean-equivalent whole implementation from the actual
production proper-positive support search. Its deliberately physical contract
does not say that every computed profile coordinate agrees. The next edge is
to evaluate those coordinates on that actual returned implementation and accept
full-carrier use only when they all agree, retaining an explicit first mismatch
otherwise.

Use the existing M238 algorithm, candidate-derived saturation and profile
system. Do not add a replacement, search result, seed, profile-equality proof,
route certificate or alternative minimizer as an algorithm input. Do not
repeat exhaustive Boolean equivalence checking: M238 already proves it for the
actual result. The additional computation scans the finite profile coordinates.

## Unbounded construction

Quantify over arbitrary input, gate, output and profile widths, a finite
direct-wire candidate, and its existing executable terminal model.

Define a total classification with three mutually exclusive outcomes:

1. No physical gain: the unchanged production search returned none. Preserve
   M238's exact absence of canonical proper-positive supports; this does not
   mean global minimality.
2. Profile mismatch: the actual physical result is accompanied by the first
   coordinate, in canonical coordinate order, whose full profile differs.
   Every earlier coordinate agrees. Report its actual role and values; do not
   interpret this local mismatch as an already completed named global route.
3. Full-profile gain: the exact actual result carries complete full-carrier
   realization evidence. Recover its selected seed, physical gain, complete
   Boolean equivalence and strict size/slack decrease from M238, not a supplied
   certificate.

The projection cannot erase a mismatching coordinate from this check. It is a
full-mode acceptance boundary, including all obligation-role coordinates.
Transport existing obligation discharge through full profile equality; do not
claim that equality discharges an obligation that was already open.

## Main theorem interfaces

Prove exact branch reflection at arbitrary dimensions: no gain precisely when
the production search fails; full-profile acceptance precisely when an actual
physical result agrees at every profile coordinate; mismatch precisely when
that result disagrees, with the deterministic first failure and complete
earlier-coordinate agreement.

For every computed accepted result, prove equality of the exhaustive full-profile
minimum with the original implementation. Derive the exact full-profile slack
equation: replacement size minus its full-profile minimum, plus the computed
local physical gain, equals original size minus its full-profile minimum.
Hence the accepted result strictly decreases that full-profile slack.

Use the existing attained full-profile minimum and universal lower bound.
Transport complete realizations in both directions; do not identify the full
minimum with the unconstrained Boolean minimum or assume extensionality of the
supplied observer. Do not change M238 or its preceding extractor/context to
make these claims easier.

## Verification and regressions

Before implementation, reconcile the exact declaration and algorithm contracts.
Compile small bounded proof prefixes and inspect their axiom closures before
the permanent root build and complete inventory.

Use arbitrary-dimension theorem applications plus minimal executable success,
no-gain and mismatch fixtures. Include a genuinely smaller Boolean-equivalent
result rejected by a gate-count-sensitive profile observer, a nonconstant
semantic observer accepted because outputs agree, a later mismatch preceded
by equal coordinates, a projection that forgets the mismatching coordinate,
and zero profile width. Cover preservation of already discharged obligations,
without asserting discharge of an open obligation.

Probe each new exhaustive-search fixture with a short timeout and modest
memory ceiling. Use one smallest complete search per meaningful branch;
derive richer layout properties through general interfaces or targeted
construction checks rather than larger exponential searches.

The seven general results now compile with their reviewed standard axiom
closures. Bounded independent regression probes isolated one expensive kernel
reduction in the nonconstant semantic-observer acceptance fixture. The same
input and expected result are retained as a guarded Lean runtime assertion;
the general theorem applications and the remaining finite branch checks stay
kernel checked. Runtime execution is test evidence, not theorem authority.
The permanent regression then passed within the original bounded limit.

Update the permanent source/hostile contracts, explicit-root audit, compiled
inventory producers, publication row and fingerprints, status producers and
all expectation consumers together. Include the publication-map coordinate
literal in the coordinate preflight before status generation. Derive all counts,
hashes and report metadata from successful authoritative generation.

Run targeted checks first, then the existing report reproduction and one
deduplicated union of required test files. Preserve successful evidence for
unchanged source, inputs, toolchain and trust boundary. Normal PR/post-merge
checks and independent exact-object reproduction remain required; no proof
build is repeated for PNPLabs.

## Remaining obligations and progress

The model and observer remain supplied; the existing influence, support search
and reference minima remain exhaustive. The classifier does not prove that
every physical gain passes full-profile checks, search all alternative gains
after a mismatch, identify ambient observations with differently typed global
observations, or derive faithful manuscript carrier data from every valid input.

Complete materializer charges, fixed global ownership, full-minimum growth
during saturation, quotient bounds, routing of a rejected result, complete
terminal families and global rank-decreasing route coverage remain open.
No unconditional SaturatePositive, BCELReady, ZeroSlack, complete polynomial
PCCMin, runtime/certificate bound, deterministic CNFSAT in P or eligible root
theorem is claimed.

M238's canonical baseline is formal artefact coverage 214 of 216, risk-weighted
proof completion estimate 40%, uncertainty 20% to 40%, global gates closed
0 of 5, no project-specific axioms, absent eligible root and false publication
gate. No fixed weighted checkpoint or global gate is expected to change.

Publication decision: defer. This is the computed full-mode acceptance boundary
for the existing physical gain, not a complete full-profile/global or polynomial
route. Preserve the coherent published PNPLabs source pin; continue meaningful
verified core submilestone and release notifications independently.
