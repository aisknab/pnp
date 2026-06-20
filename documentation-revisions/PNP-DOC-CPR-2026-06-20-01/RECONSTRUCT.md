# Exact reconstruction

The revised payload is derived from the unmodified canonical report at documentation base commit `8c408dbe2056ae3d9f3eb0c3e2662d4d4291306e`.

Required base-file hashes:

```text
d5559b4d0ca59b9c08d180cd802652159da75e58291aa293e539776207865b21  canonical_proof_report.tex
e134c92d74eb4fdbe4e86814d8c0a86fa49768f2036cb98b5fc9f8da906c44c2  canonical_proof_report.pdf
```

From a clean checkout of that commit, with this revision directory copied into the checkout:

```bash
REV=documentation-revisions/PNP-DOC-CPR-2026-06-20-01

printf '%s  %s\n' \
  d5559b4d0ca59b9c08d180cd802652159da75e58291aa293e539776207865b21 \
  canonical_proof_report.tex | sha256sum -c -
printf '%s  %s\n' \
  e134c92d74eb4fdbe4e86814d8c0a86fa49768f2036cb98b5fc9f8da906c44c2 \
  canonical_proof_report.pdf | sha256sum -c -

patch -o "$REV/canonical_proof_report.tex" \
  canonical_proof_report.tex \
  "$REV/canonical_proof_report.tex.patch"

cat "$REV"/canonical_proof_report.pdf.zstpatch.b64.part* \
  | base64 -d > "$REV/canonical_proof_report.pdf.zstpatch"
zstd -d --patch-from=canonical_proof_report.pdf \
  "$REV/canonical_proof_report.pdf.zstpatch" \
  -o "$REV/canonical_proof_report.pdf" -f

(cd "$REV" && sha256sum -c SHA256SUMS)
(cd "$REV" && sha256sum -c PATCH_SHA256SUMS)
```

The PDF delta is an exact binary patch, not a source-level approximation. Successful verification produces the payload hashes recorded in `SHA256SUMS`.
