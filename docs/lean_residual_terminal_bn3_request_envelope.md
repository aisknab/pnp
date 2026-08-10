# Candidate-derived finite BN3 request envelope

`PNP.ResidualTerminalBN3RequestEnvelope` closes a finite, explicitly bounded
version of the BN3 request-envelope obligation after the existing computed
BCEL anchor-nucleus classifier succeeds. It does not assume the legacy
`jointSideTightRealizability` Boolean or accept a request system, basis family,
or incidence certificate from its caller.

The successful nucleus's canonically ordered primitive records form one
duplicate-free request-atom identity space for every proper cut. An atom's
request predicate is exact list membership. Lean proves that this predicate is
executable, monotone under inclusion, stable under every extensional transport
preserving membership, and represented exactly by the singleton minimal
consumer `[atom]`.

For each cut, the active-incidence ledger filters that one identity space by
the exact request predicate. It is duplicate-free and, on every canonical
proper cut, contains exactly the cut's atoms. This prevents a record from being
counted twice and makes omission or addition visible in the theorem statement.

The same definition selects the existing canonical full or quotient BN2 basis
for every proper cut. The computed BCEL local conclusion proves that each
selected basis is side-tight and coherent in its mode. The resulting
`TerminalComputedBN3RequestEnvelope` packages:

- duplicate-free canonical request identities;
- complete finite proper-cut enumeration;
- monotone and stable predicates;
- exact singleton minimal consumers;
- exact, duplicate-free active incidence; and
- one canonical jointly side-tight full/quotient basis selection function.

`classifyTerminalBN3RequestEnvelope` is total. It preserves the existing
insufficient-nucleus, algebra-failure, cut-defect, and cut-route evidence
unchanged, and constructs the envelope only on the proof-bearing ready branch.
The regression reaches that branch on the concrete two-anchor fixture and
checks that exactly two proper cuts are present.

## Deliberate boundary

The construction enumerates all subsets of the finite nucleus. It is therefore
exponential reference computation, not a polynomial algorithm. It also starts
after a successful computed BCEL nucleus; it does not derive the terminal
dependency system or map every residual route into a complete decreasing
global outcome system.

This milestone does not construct BN4-BN6, prove selector or realizer
completeness, establish global ZeroSlack or PCCMin, put SAT in P, remove any of
the four disclosed project assumptions, or prove `P = NP`. Those claims remain
mechanically fail-closed.

## Reproduction

```bash
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalBN3RequestEnvelopeAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalBN3RequestEnvelope.lean
node --test audits/lean-residual-terminal-bn3-request-envelope0.test.mjs
```
