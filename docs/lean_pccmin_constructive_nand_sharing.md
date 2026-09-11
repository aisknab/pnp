# Constructive whole-program NAND sharing

M242 reconstructs the physical structural-congruence and latent-sharing subcase
of Package E (R1/R4) and the semantics/size input to Traceable normalization in
the pinned manuscript. The existing normalization/oracle composition previously
accepted both stages as supplied constructions. This milestone supplies one
actual all-program sharing stage; the oracle and the other normalization
operations remain open.

M242 constructs a whole-program NAND-sharing stage: it computes aliases for every original gate, reuses actual retained gates with equal or commuted inputs, translates every ordered output, and proves exact physical gate savings and residual-slack descent. The concrete normalizer surfaces every computed fold as a checked gain. A no-fold branch does not establish semantic minimality or ZeroSlack.

Formal artefact coverage: 218 of 220 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

## Computed construction

The pass traverses an arbitrary intrinsically topological finite NAND program.
Before handling each gate it translates both sources through the aliases already
computed for the prefix. It searches actual retained gates for the same two
sources, allowing the NAND input pair to commute. A successful lookup reuses its
gate; an unsuccessful lookup appends exactly one translated gate. The complete
ordered output word is then translated through the final alias map.

No optimizer or correctness certificate is supplied by the caller. Proof fields
in the result are constructed by the recursive pass. The implementation does not
enumerate input valuations, equivalent circuits or reference minima.

## Nine general interfaces

All names below are in `PNP.DirectWire` and are quantified over arbitrary
compatible finite dimensions.

| Interface | Checked obligation |
| --- | --- |
| `compileNANDSharing_alias_semantics` | Every original gate and every input valuation have the same value at the computed alias. |
| `compileNANDSharing_exact_accounting` | Retained gates plus actual successful reuse branches equal the original gate count. |
| `sharingImplementation_equivalent` | The complete ordered multi-output semantics is preserved. |
| `sharingImplementation_gateCount_le` | The pass cannot increase physical gate count. |
| `sharingImplementation_referenceMinimum` | The semantic reference minimum is invariant. |
| `sharingImplementation_residualSlack` | Original slack equals result slack plus the computed fold count. |
| `sharingImplementation_strictGain_iff` | A strict gain occurs exactly when at least one gate was reused. |
| `sharingImplementation_strictResidualDescent` | A computed fold strictly decreases the loop's residual measure. |
| `nandSharingNormalizer_checked` | The existing normalizer interface returns the computed result and distinguishes gain from no fold correctly. |

The explicit root builds all nine interfaces. Their exact audited dependencies
are only `propext` and `Quot.sound`; no project-specific axiom or
`Classical.choice` is used.

## No-fold is not a stopping theorem

The regression contains a cascading six-gate program whose commuted and
alias-induced duplicates reduce to three gates. The resulting program has no
further structural fold, but a two-gate circuit has the same complete outputs.
A kernel-checked strict-gain witness therefore proves positive residual slack
after this no-fold result.

A no-fold branch does not imply semantic minimality, absence of other gains or
ZeroSlack. It means only that this pass's computed structural lookup found no
reuse at that execution. The next PCCOracle stage remains an explicit
construction boundary.

## Limits and downstream work

This is a computed physical R1/R4 structural-sharing stage, not complete
manuscript N1-N10 normalization. It does not find every semantic or latent-sharing
opportunity or construct the proper-support Package E ledger, arbitrary
replacement pullback, full-profile carrier and obligation transport,
terminal-derived families or global rank-decreasing route coverage.

Reference minima appear only in the specification theorems; the pass does not
execute the exhaustive reference minimizer. A finite structural traversal is
not a uniformly encoded-size polynomial theorem for the complete PCCMin
construction. No runtime checkpoint is earned here.

Unconditional SaturatePositive, BCELReady and ZeroSlack, the complete PCCMin
oracle and polynomial bounds, deterministic CNFSAT in P and the eligible root
remain open. No fixed checkpoint or global gate closes. P = NP is not proved.

## Verification and publication

The permanent regressions cover arbitrary-dimension theorem applications,
composition with the still-supplied oracle, empty programs and interfaces,
constant and primary-input outputs, repeated outputs, input commutation,
cascading aliases, unequal pairs and the nonminimal no-fold example.
Runtime execution is test evidence, not theorem authority.

Hostile contracts reject weakened or finite-only types, supplied optimizer
authority, fake lookups, missing output rewiring, invented fold counts,
assumption injection and widened publication claims. Exact kernel fingerprints
bind the publication row to the root-built theorem types.

Publication decision: **defer PNPLabs**. This internal normalization stage does
not close a fixed checkpoint or global gate and does not change the published
M231 bottom line.

See the [milestone plan](plans/2026-09-12-constructive-nand-sharing.md),
[physical ownership boundary](lean_residual_terminal_physical_ownership.md),
[formal reconstruction status](FORMAL_RECONSTRUCTION.md) and
[fixed progress model](proof_progress.md).
