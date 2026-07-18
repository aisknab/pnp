# Concrete Cook–Levin dynamic token-cursor step

`lean/PNP/Concrete/CookLevinBuilderDynamicTokenCursorStep.lean` adds one
literal cursor transition after the complete first-clause prefix. The
predecessor leaves token coordinate `formulaVariableSlotBound + 12` as the
root of its newest unary scratch register. The new table advances that root
to `formulaVariableSlotBound + 13`, restores the represented raw-input focus,
and leaves the formula output unchanged.

This coordinate has a precise schedule meaning. The first canonical shape
clause occupies offsets zero through ten of its fixed token rectangle. Offset
eleven is therefore the first in-range padding opportunity. The theorem
`nextTokenSlot_direct_eq_padding` proves the direct structural lookup is
`some none`: it is neither a populated token nor an out-of-range result.
`specification_step` then proves that the token-level specification cursor
returns padding and advances by exactly one.

## Literal cursor table

The standalone `CursorAdvance.machine` has five nonhalting control states and
45 rules:

```text
5 states × 9 work symbols = 45 rules
```

Its successful path performs the following finite operations:

1. move from the represented input to the left boundary;
2. scan durable unary units and register separators to the active scratch-end
   marker;
3. overwrite that marker with one new unary unit and relocate the marker one
   cell outward;
4. rewind across the same scratch word; and
5. cross the left boundary to restore the original input focus.

For a scratch word of length `L`, this takes exactly `2*L + 7` work
transitions. Relocating the marker consumes the first exterior garbage cell
when present and materializes an implicit blank cell when it is absent. The
all-input trace proves both cases without a cleanliness assumption beyond the
active scratch word itself.

The rules are generated only from the five fixed state specifications and the
nine-symbol work alphabet. They do not call the formula, encoded formula,
token schedule, direct coordinate decoder, SAT, or a caller-provided outcome.
The direct decoder appears only in the semantic theorem identifying this
particular retained coordinate.

## Composition and exact endpoint

One total nine-symbol bridge joins the complete first-clause machine to the
45-rule cursor table. The composed symbolic rule count is

```text
1192
+ width-evaluator ruleCount
+ body-start-coordinate evaluator ruleCount
+ first-literal-coordinate evaluator ruleCount
+ first-clause-coordinate evaluator ruleCount.
```

Only the cursor table’s accept and reject images are global halts. The source
images are injective and disjoint, the bridge precedes both renamed component
tables, and `rules_pairwise_query_distinct` proves deterministic first-match
dispatch. `launch_workStep`, `cursor_workRunExact`, and `workRunExact` expose
the exact bridge, standalone cursor, and complete raw-input traces.

`finalOutside_contains_finalTokenSlot` audits the resulting unary root at
`formulaVariableSlotBound + 13`. `finalTape_represents` proves that the raw
input remains represented. Because the decoded opportunity is padding, no
token is appended; `finalTokenBits_eq_encodedFormula_firstClause` preserves
the exact canonical formula prefix through the first clause.

## External compiled bound

Let `L` be the length of the structurally compiled first-clause cursor scratch
word. The external polynomial evaluates to

```text
BuilderFirstClausePrefix.rawTimeBound(n) + 48 + 12*L.
```

The constant covers six compiled transitions for the bridge and six times the
seven fixed cursor transitions; the remaining `12*L` covers the outward and
return scans. `rawTimeBound_le` proves this polynomial bounds six times the
exact composed work trace. The compiled theorems establish exact execution,
execution at polynomial fuel, ordinary blank-equivalent start transport, and
acceptance.

## Fail-closed boundaries and audits

The module proves timeout at three new boundaries:

- the complete first-clause endpoint before the launch bridge;
- a malformed cursor scratch symbol, which enters an explicit nonhalting dead
  state for every fuel budget; and
- exactly one work transition less than the successful trace.

The regression covers empty input, one-bit zero and one, odd and even lengths,
all-zero and all-one inputs, input-only and paired verifiers, exact rule and
step counts, the bridge, direct padding semantics, the advanced unary root,
final tape and token bits, compiled acceptance, and polynomial evaluation.

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderDynamicTokenCursorStepAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderDynamicTokenCursorStep.lean
node --test \
  audits/lean-concrete-cook-levin-builder-dynamic-token-cursor-step0.test.mjs
```

All 47 public declarations close over only the approved Lean-standard axioms
`propext` and `Quot.sound`. The two additional reviewed dispatch facts expose
the malformed-scratch transition into the dead state and its total self-loop
for collision-free downstream composition. The hostile audit rejects state collision, removal
of a cursor phase or the launch bridge, an altered padding result or increment,
host-side lookup in the rule table, and any new assumption.

## Remaining boundary

This is one proved padding transition, not a complete dynamic cursor loop.
It does not decode arbitrary header, clause, literal, input-bit, final-token,
or out-of-range coordinates; branch to all four token appenders; iterate over
the remaining schedule; construct the complete formula; supply builder
`RawRefinement` or a `PolynomialReduction`; prove CNF-SAT NP-complete or in P;
or establish `PNP.Main.p_eq_np`. The four project assumptions, six blockers,
unset activation fingerprints, and false publication gate remain unchanged.
