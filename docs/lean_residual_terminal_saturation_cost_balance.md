# Candidate-derived terminal saturation cost balance

## Result

`PNP.ResidualTerminalCandidateSaturation` removes the arbitrary dependency
relation from the production terminal path. Physical dependencies are computed
from the candidate's actual gate sources and output interface. Profile
dependencies are computed by toggling each gate across every finite subset of
the other gates and comparing the executable ambient observer coordinate. The
caller supplies an observer and forgetful projection, but no `requires`
relation, extraction certificate, cost certificate, or branch selector.

`PNP.ResidualTerminalSaturationCostBalance` then audits the exact deterministic
saturation trace. Every generated record retains its first rule tag and the
support immediately before and after processing. Gate records have unit cost;
boundary, interface, and profile records have zero physical cost.

## Transparent and fail-closed branches

One event is transparent only when all of the following computed facts hold:

1. a saturation rule generated the record;
2. a materialized gate has exactly one active rule/dependent owner;
3. support gate count increases by the event cost;
4. the exhaustive full-profile minimum increases by the same cost; and
5. the exhaustive quotient-profile minimum increases by no more than that
   cost.

Equal support and full charges preserve full slack exactly. The quotient bound
makes projection defect nondecreasing. The trace-link theorem proves that these
facts telescope from the normalized seed through the replayed final support,
so positive initial full slack survives every fully transparent trace.

The total classifier returns either proof that every deterministic event is
transparent or the exact first nontransparent event. A failure contains the
complete transparent prefix, remaining suffix, rejected event, negated
transparency proposition, and one of five typed reasons: missing rule,
nonunique materializer owner, support-cost mismatch, full-cost mismatch, or
quotient-cost excess.

## Exact milestone boundary

This closes the finite terminal forms of
`transparentSaturationCostBalanced` and
`firstNontransparentStepRecorded`. Together with the preceding positivity
firewall, three of the five named `RW-SaturatePositive` sub-obligations now
have finite terminal realizations.

The following remain open:

- `interfaceExposureRoutesToE`; and
- `originKernelObligationClosureRouted`.

Accordingly, `leanSaturatePositiveFormalized` and
`leanBCELReadyFormalized` remain false. The observer and projection remain
explicit executable model inputs. A nontransparent event is recorded, not yet
routed into Package E. No full `SaturatePositive`, Package E, global routing,
ZeroSlack, PCCMin, polynomial-runtime, SAT-in-P, or P = NP theorem follows.

## Trust and verification

The axiom transcript covers the rule-labelled trace, candidate-derived
dependency system, production wrappers, exact cost snapshots, pointwise and
aggregate preservation theorems, and both total classifiers. The regression
checks derived physical/profile edges, deterministic trace order, unit-cost and
metadata events, a genuine multiple-owner rejection, a balanced full trace,
and its exact first failure after a hostile extra seed.

The durable checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalSaturationCostBalanceAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalSaturationCostBalance.lean
node --test audits/lean-residual-terminal-saturation-cost-balance0.test.mjs
npm run formal:inventory:check
npm run formal:publication:check
npm run report:check
```

The root import, workflow, theorem inventory, publication map,
reconstruction status, canonical report, and public mirrors are released as
one fail-closed surface.
