(** quint-audit core library entry point.

    Submodule aliases make the library usable as [Quint_audit.<module>] while
    keeping this file the single external interface. See README.md.
    Licence: AGPLv3 - see LICENSE. *)

module Analysis = Analysis
module Checks = Checks
module Finding = Finding
module Ir = Ir
module Ir_decode = Ir_decode
module Ir_facts = Ir_facts
module Lint = Lint
module Qcalc = Qcalc
module Quint_parse = Quint_parse
module Report = Report
module Run_checks = Run_checks
module Run_disc = Run_disc
module Runner = Runner
module Sha256 = Sha256
module Symbols = Symbols
module Version = Version

let version = Version.version
