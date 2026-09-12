# M247: computed NAND constant propagation

M247 computes literal constant propagation through every gate of an arbitrary finite NAND program and rewrites its complete ordered output tuple. Computed source aliases propagate earlier constants, and ten general interfaces prove primitive recognition, all-input semantics, exact retained/eliminated gate accounting and residual-slack descent. No-elimination is not semantic minimality. This physical structural-congruence component does not derive the manuscript carrier, full-profile transport, obligation lifecycle ledger, complete normalization or global PCCMin route.

## Legacy anchor and computed construction

The pinned manuscript's section 2 direct-wire language includes constant sources,
earlier gate outputs and ordered output tuples. Section 5 lists R1 structural
congruence among the rewrite families. M247 implements the physical
literal-constant structural-congruence component of that dependency.

The pass starts with the empty program and traverses every original gate in
topological order. Before inspecting a gate it replaces each earlier-gate
reference with the source alias already computed for that gate. A false source
on either side of NAND yields true; two true sources yield false. Those cases
record a constant alias and remove one gate. Every other case appends the
translated gate and records its retained-gate source.

Consequently one elimination can propagate into arbitrarily later gates. After
the traversal, every original ordered output is rewritten through the same
alias map. Primary-input, constant and repeated outputs remain represented.
No optimizer, result or correctness assertion is supplied by the caller.

## Reviewed general interfaces

- `PNP.DirectWire.constantGateValue_sound`: The recognized constant is the NAND value for every input and gate valuation; this primitive theorem is axiom-free.
- `PNP.DirectWire.compileNANDConstantPropagation_alias_semantics`: Every original gate has a computed retained-source alias with exactly the same value for every input.
- `PNP.DirectWire.compileNANDConstantPropagation_exact_accounting`: Retained gates plus actual elimination branches equal the original gate count.
- `PNP.DirectWire.constantPropagationImplementation_equivalent`: The complete ordered output word has unchanged Boolean semantics, for arbitrary input and output dimensions.
- `PNP.DirectWire.constantPropagationImplementation_gateCount_le`: The computed physical implementation never has more gates.
- `PNP.DirectWire.constantPropagationImplementation_referenceMinimum`: Complete equivalence preserves the semantic reference minimum as a specification theorem.
- `PNP.DirectWire.constantPropagationImplementation_residualSlack`: The original residual slack equals remaining slack plus the exact elimination count.
- `PNP.DirectWire.constantPropagationImplementation_strictGain_iff`: Strict equivalent gain occurs exactly when an actual constant elimination occurred.
- `PNP.DirectWire.constantPropagationImplementation_strictResidualDescent`: A positive elimination count strictly decreases the loop's residual measure.
- `PNP.DirectWire.nandConstantPropagationNormalizer_checked`: Both normalizer branches return the actual computed implementation; the gain branch records positive elimination and the no-elimination branch preserves gate count.

All ten interfaces are built through the explicit PNP root with exact reviewed
kernel-type fingerprints. Apart from the axiom-free primitive constant rule,
the other nine use only the standard propext and Quot.sound axioms. The compiled
inventory and publication ledger are the authoritative fingerprint records.

## Stopping boundary and remaining obligations

No-elimination does not imply semantic minimality or ZeroSlack.
The regression program NAND(x, NAND(x,x)) has no literal constant source, so
the pass retains both gates. Nevertheless a zero-gate constant-true output word
is equivalent. This is checked as a strict equivalent gain, not dismissed as
a failed simplification test.

This component does not derive full-profile preservation, the complete
manuscript carrier, arbitrary-support pullback/expansion, the R5/R6-R8 obligation
lifecycle ledger, complete Package E, complete N1-N10 normalization or a total
PCCMin oracle. Its physical normalizer branch is not a proof of manuscript
normal form or of the absence of other routes.

The reference minimum occurs only in specification theorems. The pass does not
execute an exhaustive search over supports, implementations or input valuations.
No uniformly encoded-size polynomial runtime, output-size or certificate-size
theorem is established here. Unconditional SaturatePositive, BCELReady and
ZeroSlack, deterministic CNFSAT in P and the eligible root theorem remain open.
No fixed checkpoint or global gate closes.

## Regression and publication evidence

General type regressions cover all ten statements. Bounded fixtures check the
four constant truth cases, left/right false sources, retained nonconstant NAND,
cascading eliminations, input/constant/repeated ordered outputs and empty
dimensions. The nonminimum stopping example protects the global claim boundary.
Runtime execution is test evidence, not theorem authority.

Source and compiled hostile contracts reject incorrect NAND constants,
fabricated aliases, invented elimination counts, omitted output rewriting,
finite-only or weakened types, caller-supplied correctness, changed fingerprints,
extra axioms and widened normalization or global claims. The permanent workflow
executes the exact audited interfaces and regressions.

## Current metrics and publication decision

Formal artefact coverage: 223 of 225 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

Formal artefact coverage measures only the current evidence ledger; its
denominator can grow and it is not proof completion. The fixed-weight estimate
is not confidence that P=NP is true, a probability of success or a time estimate.

Publication decision: defer PNPLabs. This physical R1 component does not change
the coherent published M231 bottom line. Verified submilestone notifications
remain independent of website publication cadence.

See the [recorded plan](plans/2026-09-12-computed-nand-constant-propagation.md),
[computed NAND sharing](lean_pccmin_constructive_nand_sharing.md),
[computed dead-support acceptance](lean_pccmin_dead_support_full_mode.md) and
[canonical progress policy](proof_progress.md).
