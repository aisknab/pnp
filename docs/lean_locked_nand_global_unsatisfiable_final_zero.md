# Lean locked-NAND global unsatisfiable final-zero branch

`lean/PNP/LockedNANDGlobalUnsatisfiableFinalZero.lean` discharges the next
bounded Section 17 obligation from the pinned legacy manuscript. For every
finite topologically ordered NAND circuit, it proves the whole carrier
unsatisfiable branch and its exact exhaustive reference minimum.

## Plain-language result

The locked-NAND construction adds one final output that can become true only
when all of the following agree:

- the fresh final lock is on;
- every encoded trace check is correct; and
- the source circuit's declared output is true.

If the source circuit is unsatisfiable, there is no source input for which a
correct trace can end in true. Lean now proves that the new final output is
therefore false for every possible assignment to the entire carrier,
including malformed trace coordinates and a hostile assignment that turns
the final lock on.

That pointwise result also fixes the exact unsatisfiable reference minimum.
Writing the square baseline size as `B`, the complete candidate has `B + 4`
gates and `B + 1` outputs, but in the unsatisfiable branch its last output is
identically zero. It is therefore equivalent to the baseline with one free
zero output appended, giving an upper bound of `B`. Projecting away the final
output recovers the baseline and gives the matching lower bound. The minimum
is exactly `B`.

## Public theorem boundary

The two public declarations are:

- `fullCandidate_final_eq_false_of_unsatisfiable`; and
- `fullCandidate_referenceMinimum_eq_baseline_of_unsatisfiable`.

The first theorem quantifies over every flattened carrier valuation; it does
not assume a coherent trace. The second uses the already formalized baseline
conditions and the direct-wire zero-output convention to prove exact
reference-minimum equality.

The dedicated axiom transcript reports exactly `propext` and `Quot.sound` for
both theorems. It reaches neither `Classical.choice` nor any project axiom.
The implementation does not inspect a satisfiability answer while constructing
the candidate, use host-side lookup, or accept a caller-supplied certificate.

The regression covers two different unsatisfiable circuits, arbitrary,
all-false, all-true, and final-lock-forced carrier valuations, and exact
reference minima for both examples. A satisfiable constant-true circuit is
also retained as a separation case: its coherent final output can be true.

## What this does not prove

This milestone instantiates `unsatisfiableFinalZero` in the six-field
conditional threshold package. By itself it does not prove satisfiable
`FinalLockSeparation`.

The following
[`global semantic threshold`](./lean_locked_nand_global_semantic_threshold.md)
milestone now supplies `satisfiableFinalConditions`, packages all six fields,
and derives the typed threshold and residual-slack bound. The encoded
answer-independent polynomial bitstring builder, report-level language link,
deterministic polynomial-time CNF-SAT decider, NP-completeness theorem, and
`P = NP` remain absent.

The pinned legacy manuscript remains the reconstruction specification.
An alternative construction is appropriate only if a precise Lean obligation
shows that route to be inconsistent or incomplete; no new assumption is
introduced to force the result.

## Generated publication artifacts

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-27-87`: 12,247 declarations, 7,160
theorems, 3,676 assumption-free theorems, 5,000 excluded private
declarations, 106 source-closure modules, and 1,970 reviewed milestone
candidates. Its 11,197,669 canonical bytes have SHA-256
`6c77607a6c03fd4136c31d62517d7773ec3989dbfd95188f28995c10f32f44fd`;
the Lean source-closure SHA-256 is
`d6be2beffdfaa94f5a53139fa1a4272bbb7b1cd1b0f7dfe764d1934ba86aed9c`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-27-87` has
67 milestones, of which 64 are earned and the same three global milestones
remain unearned, plus 1,970 exact kernel-type fingerprints. Its canonical
reviewed-object fingerprint is
`c86ea14da8f100850605ab7ad3b9b9c9dc8bf19d5a1f923cdb4ea4989c369985`.
Its 646,335 file bytes have SHA-256
`9d588fb56eb496806bbacf9021fd2fa84a74e91dbe462756bf5eee1d3dc63abe`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-27-87` has
1,582,057 bytes and SHA-256
`c0bb68c8c353d034294e7377cc43d5146a1c84723c11029b909ba6cbb22192bd`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-27-87`; its 152,171-byte
TeX has SHA-256
`f0dd87b5b3799b7651eb0a3a321d9054c7acce1f815e86f473bac25467006a71`.
Its 63-page, 402,956-byte PDF has SHA-256
`9d0743f86dd9da269d6244a543a1c4a21a2ede2b7cfdc5508875b17c7ae8f4ad`.

All five activation fingerprints remain unset, all four project assumptions
and five blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete
publication gate remains false.

The current successor evidence is recorded at inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-08-11-125` and status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-126`; see
[Lean locked-NAND global semantic threshold](./lean_locked_nand_global_semantic_threshold.md).
