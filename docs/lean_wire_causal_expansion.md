# Source-ordered physical support expansion

As of PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-14-262.

Formal artefact coverage: 238 of 240 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

The module [NANDWireCausalExpansion.lean](../lean/PNP/NANDWireCausalExpansion.lean)
constructs an actual compiled NAND implementation for an arbitrary finite
computational support and a well-typed local replacement. Its namespace is
`PNP.DirectWire.WireCausalExpansion`. The
[M262 plan](plans/2026-09-14-wire-causal-expansion.md) records the manuscript
anchor, intended dependency edge and remaining obligations.

## Construction and semantics are separate

`graph`, `compile`, `compiled`, `expanded` and `expandedCarrier` derive their
physical data from the original candidate, selected records and replacement.
No caller supplies an acyclicity witness, rank, schedule, compiler-success
certificate or final semantic witness. `graph_rank_decreases`,
`graph_wellFounded`, `compile_success` and `compiled_spec` prove that the actual
executable compiler succeeds at arbitrary finite widths.

Correctness requires the ordinary **complete local open-function equality**
between the replacement and extracted support. `masked_replacement_output`
covers every open boundary valuation, not just whole-circuit-induced inputs.
It uses the existing prefix noninterference theorem: only later gate-valued
boundary ports may be masked. Primary inputs and required earlier ports retain
their actual values.

`values_solution` proves the actual NAND equations. `expanded_semantics`
transports that solution through the compiler to all original ordered outputs.
`expandedCarrier` first exposes the entire computational field word, then
unpacks the same compiled implementation. `expandedCarrier_output` and
`expandedCarrier_field` preserve ordinary outputs and every field's full value.
Quotient-only or ordinary-output-only agreement is insufficient.

`expandedR5Creation` rebinds an existing lost-field creation to the same field
coordinate. Its coordinate and full-witness theorems preserve the original
full source value. This is literal R5 binding transport, not the full R5–R8
obligation calculus or an arbitrary semantic dependency DAG.

## Every physical copy is paid for

Let `G` be the original gate count, `S` the selected count, `E` the exterior
count, `K` the computed number of distinct retained physical producers and `R`
the replacement gate count. Then `G = S + E` and

```text
expanded gate count = E + K * R
strict original-size saving iff K * R < S
proper support separately requires S < G
```

Every exterior gate is retained once. Each retained producer owns a whole
replacement copy. A repeated output or field reference does not allocate another
copy, while two physically different producers are not merged merely because
they have equal values. Exterior and copy-position injections are disjoint;
`expanded_gate_ownership` covers every emitted gate. Literal source-equality
theorems preserve sharing through the actual compiled positions.

The construction does **not** infer global saving from `R < S`. A locally smaller
replacement can lose its apparent saving after copies are charged. The
single-interface corollary has one paid copy and works at arbitrary incoming
boundary width. It does not replace the general theorem with a unary fixture.

## Independent evidence and unchanged limitations

The [permanent axiom audit](../lean-audit/PNPWireCausalExpansionAxiomAudit.lean)
imports the explicit root and checks the reviewed theorem closures. The
[source and hostile contracts](../audits/lean-wire-causal-expansion0.test.mjs)
freeze the intended interfaces and reject weakened cost, causality, ownership
and semantic premises. The
[Lean regression](../lean-regression/PNPWireCausalExpansion.lean) independently
exercises the cyclic-literal-splice distinction, paid and unpaid local savings,
empty dimensions, full and empty supports, distinct equal-valued producers,
reordered repeated fields, fields-only carriers and original R5 source values.
These executable fixtures are regression evidence, not proof authority.

The old literal compiler still rejects its cyclic fixture. This new expansion
pays for extra physical structure; it does not repeal that obstruction or claim
free duplication. Existing cone and unary constructions are unchanged.

Matched-kappa Pull/Expand and global CompatibleReplacement/SlackLaw remain open.
So do arbitrary implementation-dependent observers and profiles, the complete
obligation calculus and Package E, global routes, unconditional ZeroSlack, exact
PCCMin and complete encoded-input-size polynomial runtime/output/certificate
bounds. No fixed weighted checkpoint or global proof gate closes, and P = NP
is not proved. Current coverage, risk-weighted estimate, uncertainty and gate
states are separately maintained in the
[canonical progress ledger](../status/PROOF_PROGRESS.json).

Publication decision: publish one batched PNPLabs update after the M262 core release gates pass. The source-derived physical constructor now covers arbitrary supports and incoming-boundary widths, materially extending the previous scoped construction boundary. The public account must retain the paid-copy condition and all global non-claims; this is not a score increase or a publication triggered merely by another evidence row.
