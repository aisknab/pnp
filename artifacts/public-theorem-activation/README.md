# Public theorem activation withdrawal artifacts

The historical checker path now validates withdrawal rather than activation.

Run:

```bash
npm run proof:public-theorem-withdrawal
```

The generated verdict is written to:

```text
artifacts/public-theorem-activation/latest-verdict.json
```

An accepted verdict means the old activation is superseded and current theorem emission remains disabled. It does not establish `P = NP`.
