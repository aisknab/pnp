# Lean locked-NAND carrier layout and trace equivalence

`lean/PNP/LockedNANDCarrierTrace.lean` formalizes one unbounded part of the
legacy locked-NAND argument: the global carrier geometry and the
`TraceEquivalence` induction for arbitrary finite, topologically ordered NAND
circuits. This is a direct reconstruction of the trace layer identified in
legacy report Section 17, Theorem 17.2 and Lemmas 17.5–17.7. It is not the
complete locked-NAND builder or threshold theorem.

## Exact carrier

For a circuit with `n` inputs and `m` NAND gates, Lean defines the disjoint
carrier

```text
X ⊔ T ⊔ O ⊔ R ⊔ L ⊔ {z}
```

with these exact widths:

| Family | Meaning | Width |
| --- | --- | ---: |
| `X` / `primary` | primary-input values | `n` |
| `T` / `trace` | one claimed value for each NAND gate | `m` |
| `O` / `occurrence` | ordered left/right source occurrences | `2m` |
| `R` / `sourceLock` | one active lock per source occurrence | `2m` |
| `L` / `traceLock` | one active lock per NAND equation | `m` |
| `z` / `finalLock` | globally fresh final-lock coordinate | `1` |

Thus `carrierWidth n m = n + 6m + 1`. `CarrierSlot.encode` maps every tagged
family into one contiguous `Fin` interval, while `decodeCarrierSlot` is total
on that interval. Lean proves both inverse laws and injectivity. The theorem
`finalLock_fresh` then proves that no non-final tagged slot encodes to `z`.
These facts are derived from the layout; callers do not supply a separation or
freshness certificate.

## Exact trace predicate

The source program is intrinsically topological: a gate can read a primary
input, a Boolean carrier constant, or an earlier gate, but never a later gate.
For each actual gate, `distinguishedChecks` generates exactly three checks:

1. the left occurrence equals the value of the gate's typed left source;
2. the right occurrence equals the value of its typed right source; and
3. the claimed trace value equals NAND of those two occurrences.

The existing report macros supply the distinguished Boolean outputs. Source
constructors select equality, constant-zero, or constant-one checks directly;
there is no caller-provided occurrence table or host-side lookup. Lean proves
that the generated list has exactly `3m` entries.

## Both proof directions

The forward direction constructs `coherentExtension program input`: genuine
topological gate values, genuine ordered source occurrences, and active source
and trace locks. Every generated distinguished check reduces to true.

The reverse direction is a topological induction over the typed program. From
an accepted prefix conjunction, it extracts the two current source equations
and current NAND equation, applies the induction hypothesis to every earlier
trace coordinate, and proves the current trace coordinate equals genuine
program evaluation. Consequently:

```text
∃ carrier extension with the chosen primary input,
  all trace checks true, and declared trace output true
↔
the source circuit evaluates to true on that input
```

The global existential form is
`satisfiable_iff_trace_extension`. The constructive coherence form
`exists_coherent_trace` is independent of the declared output value.

## What this closes—and what it does not

This closes the trace-equivalence item in the hostile-review inventory at the
semantic carrier level for arbitrary finite NAND circuits. It replaces an
infinitely repeatable fixed-slot construction tactic with one induction over
the entire gate list.

This carrier/trace module by itself does not:

- prove cross-instance `BaselineDistinct`/`MacroDistinct` on the whole
  carrier;
- prove the whole-carrier unsatisfiable-zero and satisfiable separation laws;
- construct the answer-independent bitstring-level builder or prove its
  polynomial runtime; or
- prove the locked-NAND threshold, CNF-SAT in P, or `P = NP`.

The following
[`LockedNANDGlobalCandidates`](./lean_locked_nand_global_candidates.md)
milestone now assembles the complete baseline and four-gate extension and
constructs three of the six conditional-boundary fields. In particular, this
carrier theorem alone does not establish `FinalLockSeparation` merely because
`z` is syntactically fresh; the remaining semantic branch laws are separate
proof obligations.

## Audit and regression boundary

The dedicated transcript covers all 71 public source declarations exactly
once. The compiled closures use only the approved Lean-standard set: 18
declarations have empty closure, 13 use only `propext`, and 40 use only
`propext` plus `Quot.sound`. No declaration depends on `Classical.choice` or a
project axiom.

The regression module checks all six carrier families, the exact carrier
width, zero-, one-, and two-gate check counts, accepting and rejecting truth
branches, constant-source satisfiability, an incorrect trace value, an
inactive source lock, and the general reverse soundness theorem.

## Generated publication artifacts at this milestone

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-25-84`: 12,138 declarations, 7,074
theorems, 3,654 assumption-free theorems, 4,532 excluded private
declarations, 104 source-closure modules, and 1,952 reviewed milestone
candidates. Its 11,074,060 canonical bytes have SHA-256
`da77e1663fdbb70c0796ef006e66e68636dd45e3c33c350262bd9d0b2a0a0524`;
the Lean source-closure SHA-256 is
`3830caf4570da74521ede477a38aa7c6ba815c9b9ecea0d2cefcf5be28155e40`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-25-84` has
64 milestones, of which 61 are earned and the same three global milestones
remain unearned, plus 1,952 exact kernel-type fingerprints. Its canonical
reviewed-object fingerprint is
`d66d2b6962c1b100952b606974076a7e19e7e11518910cf051f07ccdd72df234`.
Its 639,925 file bytes have SHA-256
`f910d7ace254717eea3827fb3a454741c82d43f6f6a132c55c58ad6ede623dd8`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-25-84` has
1,565,360 bytes and SHA-256
`8d345785cb4bfeb200779eace1c787aa9885123123b5572b3f61dd9e7c6c1bce`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-25-84`; its 150,465-byte
TeX has SHA-256
`e5678e9f60ff781dfaf2b8b5d6c192e0132c012e9cebc98d9e5ff0eb4188c332`,
and its 62-page, 402,257-byte PDF has SHA-256
`c1a1d5367c8c0760a09cd5ad2a124d920e8739bc33c8f146eed626bc1a4fbdaa`.

All five activation fingerprints remain unset, all four project assumptions
and six blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete
publication gate remains false.
