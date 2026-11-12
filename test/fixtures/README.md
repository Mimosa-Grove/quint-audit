# Test fixtures

Synthetic Quint specifications (generated, no real user specs) and the IR and
source map recorded from `quint parse` 0.33.1. Each `specs/<name>.qnt` pairs
with `ir/<name>.json` (parse IR) and `ir/<name>-map.json` (source map).

Generation, from the repository root:

```sh
quint parse --out test/fixtures/ir/<name>.json \
  --source-map test/fixtures/ir/<name>-map.json \
  test/fixtures/specs/<name>.qnt
```

After parsing, rewrite the map's `sourceIndex.0` value to the stable relative
path `fixtures/specs/<name>.qnt`. Quint records the absolute path it was
given; the rewrite keeps the committed fixture free of machine paths. The
tests read the recorded `sourceIndex.0` value and pass it to the decoder, so
the relative value is exercised, not special-cased.

`bad_parse.qnt` and `bad_nonascii.qnt` are input-contract fixtures and have
no recorded IR.

`imported_ok.qnt`, `imported_short.qnt`, `unit_helper.qnt`, `unit_entry.qnt`,
`unit_leaf.qnt`, `unit_mid.qnt` and `unit_chain_entry.qnt` are pipeline
fixtures for the decode, import-attribution and entry-scope cells. They
resolve each other by relative import, so they are parsed live by the
pipeline tests and carry no recorded IR.

`full_clean.qnt`, `full_init_false.qnt`, `full_no_init.qnt`,
`full_violation.qnt` and `full_witness_initonly.qnt` are `full`-mode
pipeline fixtures, parsed live and carrying no recorded IR.
