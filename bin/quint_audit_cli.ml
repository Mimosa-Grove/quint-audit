(** The quint-audit command line: the lint and full subcommands over one
    report shape. Licence: AGPLv3 - see LICENSE. See README.md (Usage). *)

open Quint_audit

let version = Version.version

open Cmdliner

(* The integration contract, stated once and printed in every help page. The
   cmdliner default exits (123, 124, 125) are overridden: every path that the
   audit could not complete is exit 2. README (Exit codes). *)
let exit_contract =
  [
    Cmd.Exit.info 0 ~doc:"on success.";
    Cmd.Exit.info 1 ~doc:"when findings meet the threshold.";
    Cmd.Exit.info 2
      ~doc:
        "when the audit could not run (usage error, missing quint, non-ASCII \
         input, parse failure, typed decode failure, a run that did not \
         execute, internal error).";
  ]

let contract_exit code =
  match code with 123 | 124 | 125 -> 2 | code -> code

let spec_arg =
  Arg.(
    required & pos 0 (some string) None
    & info [] ~docv:"SPEC" ~doc:"Path to the .qnt specification to lint.")

let format_arg =
  Arg.(
    value
    & opt (enum [ ("human", `Human); ("json", `Json) ]) `Human
    & info [ "format" ] ~docv:"FORMAT"
        ~doc:"Report format: $(b,human) (default) or $(b,json).")

let fail_on_arg =
  Arg.(
    value
    & opt (enum [ ("fail", `Fail); ("warn", `Warn) ]) `Fail
    & info [ "fail-on" ] ~docv:"SEVERITY"
        ~doc:"Lowest severity that makes the exit code 1: $(b,fail) (default) or $(b,warn).")

let quint_arg =
  Arg.(
    value & opt (some string) None
    & info [ "quint" ] ~docv:"PATH"
        ~doc:"Path to the quint binary (default: search PATH).")

let quint_name = function Some p -> p | None -> "quint"

let run_int_arg names default doc =
  Arg.(
    value & opt int default
    & info [ names ] ~docv:"N" ~doc)

let max_samples_arg =
  run_int_arg "max-samples" 10
    "Number of sampled traces per run-driving check (default: 10)."

let max_steps_arg =
  run_int_arg "max-steps" 20
    "Maximum steps per sampled trace (default: 20)."

let seed_arg =
  Arg.(
    value & opt (some string) None
    & info [ "seed" ] ~docv:"SEED"
        ~doc:
          "Random seed for the run-driving checks. When supplied, --max-samples is still passed explicitly (the quint default drops to 1 with a seed).")

let run_timeout_arg =
  Arg.(
    value & opt float 120.0
    & info [ "run-timeout" ] ~docv:"SECONDS"
        ~doc:"Timeout for one quint run invocation (default: 120).")

let invariant_arg =
  Arg.(
    value & opt_all string []
    & info [ "invariant" ] ~docv:"NAME"
        ~doc:
          "Name of a `val` to evaluate as an invariant (repeatable). Nothing is evaluated when no name is supplied, so QL010/QL011 are never passed by default.")

let lint spec format fail_on quint =
  match Lint.run { quint; threshold = fail_on } spec with
  | Ok result ->
      (match format with
      | `Human -> print_string result.Lint.human
      | `Json -> print_string result.Lint.json; print_newline ());
      result.Lint.report.Report.exit_code
  | Error error ->
      Printf.eprintf "quint-audit: %s\n"
        (Analysis.describe ~quint_path:(quint_name quint) error);
      2

let lint_cmd =
  let doc = "Run the deterministic IR checks on a Quint specification." in
  Cmd.v (Cmd.info "lint" ~doc ~exits:exit_contract)
    Term.(const lint $ spec_arg $ format_arg $ fail_on_arg $ quint_arg)

let full spec format fail_on quint max_samples max_steps seed run_timeout
    invariants =
  let config =
    Lint.{ max_samples; max_steps; seed; run_timeout_s = run_timeout; invariants }
  in
  match Lint.run_full { quint; threshold = fail_on } config spec with
  | Ok result ->
      (match format with
      | `Human -> print_string result.Lint.human
      | `Json -> print_string result.Lint.json; print_newline ());
      result.Lint.report.Report.exit_code
  | Error error ->
      Printf.eprintf "quint-audit: %s\n"
        (Analysis.describe ~quint_path:(quint_name quint) error);
      2

let full_cmd =
  let doc =
    "Run the IR checks plus the run-driving checks (witnesses, init,\n\
     invariants at init and after actions). Every quint run is pinned; see\n\
     the README (Usage)."
  in
  Cmd.v (Cmd.info "full" ~doc ~exits:exit_contract)
    Term.(
      const full $ spec_arg $ format_arg $ fail_on_arg $ quint_arg
      $ max_samples_arg $ max_steps_arg $ seed_arg $ run_timeout_arg
      $ invariant_arg)

let () =
  let doc = "deterministic linter for Quint specifications" in
  let info = Cmd.info "quint-audit" ~version ~doc ~exits:exit_contract in
  let code = Cmd.eval' ~term_err:2 (Cmd.group info [ lint_cmd; full_cmd ]) in
  exit (contract_exit code)
