# M242: constructive whole-program NAND sharing

## Legacy anchor and dependency edge

Reconstruct the physical structural-congruence and latent-sharing subcase of
Package E (R1/R4), and its semantics/size input to Traceable normalization in the
canonical manuscript pinned by
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`.
The active `PCCMinNormalizeOracleComposition` already composes a supplied
proof-bearing normalizer with a supplied oracle. This milestone constructs one
actual all-program sharing stage for that interface; it does not claim that this
stage implements every manuscript normalization operation.

## Unbounded abstraction and construction

Process an arbitrary intrinsically topological finite NAND program in order.
Translate each gate's sources through the computed aliases of earlier gates.
Search the actual retained program for the same NAND input pair (including
commuted inputs). Reuse the matching gate, or append the translated gate.
Translate the complete ordered output word through the final alias map.
Count precisely the reuse branches. Do not use truth-table enumeration,
reference minimization, a caller-supplied optimizer, or a correctness certificate.

The source dimensions, gate count, graph shape and output width are arbitrary.
Empty programs, constants, primary-input outputs, repeated outputs, cascading
sharing and unequal source pairs are regression cases, not separate milestones.

## Required theorem boundary

For every `program : Program inputs gates`, construct a result with a concrete
retained program, a total alias `Fin gates -> Fin result.gateCount`, and a
computed `foldCount`. Prove:

- For every input valuation and original gate, evaluation at its computed alias
  equals evaluation of that original gate.
- `result.gateCount + result.foldCount = gates`.
- The implementation with translated ordered outputs is `Equivalent` to the
  original implementation and has no greater gate count.
- Its reference minimum is unchanged, and original residual slack is exactly
  normalized residual slack plus the computed fold count.
- A positive computed fold count gives `StrictEquivalentGain` and strict
  residual descent.
- The concrete `PCCMinTotalNormalizer` emits that checked gain when any fold
  occurred, and otherwise emits the checked non-increasing equivalent result.

This is a total structural-sharing pass, not a claim of semantic minimality,
complete N1-N10 normal form, or completeness for every R1/R4 opportunity.

## Remaining obligations and progress policy

No complete full-profile ownership/transport or obligation ledger is derived.
No proper-support Package E acceptance, arbitrary replacement pullback,
terminal-derived family, global route completeness, unconditional
SaturatePositive/BCELReady/ZeroSlack, complete PCCMin oracle, encoded-size
polynomial runtime, deterministic SAT algorithm or eligible root is claimed.
Do not alter existing proof statements, production rejection rules or checkpoint
weights to earn this milestone.

Keep the fixed proof estimate unchanged unless a fixed checkpoint is actually
closed. Update formal artefact coverage independently after compiled evidence.

Publication decision: **defer PNPLabs**. This concrete internal normalization
stage does not by itself close a weighted checkpoint/global gate or change the
published M231 bottom line.

## Verification and release plan

1. Implement the computed pass and universal proofs in one new Lean module.
2. Build the leaf under bounded resources; inspect exact axiom closures before
   integration. Add arbitrary-dimension and finite edge-case regressions.
3. Update root imports, inventory producer/consumer, fingerprints, publication
   row, status fields, focused hostile contracts and exact workflow assertions
   together before broader verification.
4. Rebuild the modified dependency chain and explicit root; seal the inventory,
   status, progress and current documentation only after source stabilizes.
5. Run focused changed-boundary checks, then one deduplicated standard suite.
   Build/reproduce/render the canonical report once through its existing command.
6. Preserve the verified tree while reanchoring to the actual verified M241
   merge. Run independent exact-head and exact-merge identity/publication checks
   without repeating unchanged Lean, report or hostile-suite evidence.
7. Use the normal draft PR, all normal PR checks, manual ready/merge, all
   post-merge checks, and independent exact-merge reproduction. Notify meaningful
   verified substeps and completion; then remove the named temporary artifacts.
