# PkgC ambient BN4 residual reduction plan

## Legacy anchor

Pinned manuscript Section 11.3, `BN4-ActivationExact`, states that exact
same-key cancellation leaves a canonical residual ledger with no surviving
opposite-sign pair. Section 11.5, `PkgC: separating consumers`, then uses a
typed full restoration of a nonsingleton separating pair to produce a
same-key cancellation or a named localization route.

## Unbounded abstraction

Work over arbitrary finite ambient BN4 cell ledgers and arbitrary carrier
types. Do not fix a candidate size, cut, key, atom type, or ledger length.
Represent the generated restoration cells by the exact permutation embedding
already proved in `ResidualTerminalPkgCAmbientBN4Ledger`.

## Exact theorem boundary

Define the complete canonical residual ledger by cancelling every canonical
key of the ambient ledger. Prove that exact removal of the generated balanced
PkgC subledger leaves the same per-key cancellation classification and hence
the same complete residual ledger as the explicit remainder. Package this as
a proof-bearing reduction object for a computed ambient BN4 cancellation, and
prove that an empty remainder forces the complete residual ledger to be empty.

Add a total classifier that constructs both the exact embedding and reduction
from the existing fail-closed canonical ledger binding. It may reject a
proposed canonical serialization, but it must accept no caller-provided
success bit, embedding proof, or residual equality.

## Remaining downstream blockers

This milestone does not derive the ambient ledger, restorer, or remainder from
an arbitrary terminal candidate. It does not prove restoration semantic
adequacy, show that the relevant remainder is empty or route-producing,
embed every local obstruction in the complete decreasing global outcome
system, construct the BN6 survivor grouping, complete Packet selectors or
realizers, prove polynomial runtime or certificate bounds, establish
ZeroSlack or PCCMin, put CNF-SAT in P, remove a project assumption, or prove
`P = NP`.

## Required evidence

- Lean theorem module over arbitrary finite types and ledgers.
- Axiom audit with an exact declaration list.
- Regression covering reordered embeddings, duplicate keys, nonempty
  remainders, empty remainders, and rejected serializations.
- Hostile JavaScript audit pinning the theorem surface and non-claims.
- Synchronized theorem inventory, publication map, status payloads, report,
  documentation, and durable read-only workflow checks.
