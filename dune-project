(lang dune 3.17)
(name quint-audit)
(version 0.1.0)
(generate_opam_files true)

(package
 (name quint-audit)
 (synopsis "Deterministic linter for Quint specifications")
 (description
  "Decodes quint's parse IR into typed OCaml structures and reports the
   Quint LLM kit review checklist plus production-pitfall checks.")
 (authors "Phill Clarke <phill@mimosadev.org>")
 (maintainers "Phill Clarke <phill@mimosadev.org>")
 (license AGPL-3.0-or-later)
 (homepage "https://github.com/Mimosa-Grove/quint-audit")
 (bug_reports "https://github.com/Mimosa-Grove/quint-audit/issues")
 (depends
  (ocaml (>= 5.3))
  dune
  yojson
  cmdliner
  (alcotest :with-test)
  (qcheck :with-test)
  (qcheck-alcotest :with-test)))
