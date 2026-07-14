# Concrete fixed-certificate execution tableaux

`PNP.Concrete.CookLevinTableau` defines the semantic bounded tableau that the
later Cook–Levin formula must encode.  It runs the repository's literal
finite-rule `step?` interpreter from an ordinary `startConfig` on the
canonical pair of one fixed source input and one fixed certificate.

The layer proves:

- `traceTail_length` and `trace_length`, fixing one configuration per time;
- `run_succ_eq_run_advance`, connecting the totalized tableau step to `run`;
- `validTableau_iff_eq_trace`, proving soundness, completeness, and uniqueness
  of the transition tableau;
- `tableauEndpoint_of_valid`, identifying every valid endpoint with the raw
  machine endpoint at the exact fuel budget;
- `FixedTableauInstance.tableauVerdict_of_valid`, preserving accept, reject,
  and timeout exactly; and
- `FixedTableauInstance.exists_accepting_iff_boundedDecide_accept`, relating
  existential valid-tableau acceptance to the concrete bounded machine.

A halted or stuck endpoint repeats.  It is not silently turned into rejection:
the final verdict still comes from the ordinary `boundedDecide` classifier, so
a stuck nonhalting endpoint remains timeout.

The complete 30-declaration kernel audit has empty axiom closure.  This layer
does not allocate a variable-length certificate, emit CNF, prove an output or
runtime polynomial, define a reduction, prove CNFSAT NP-complete or in P, or
establish P = NP.  The concrete publication gate remains false.
