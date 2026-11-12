(** The lint pipeline: source -> quint parse -> typed IR -> checks -> report.

    Parse and decode failures are exit 2 and never
    produce a report. Licence: AGPLv3 - see LICENSE. See README.md (How it
    works). *)

type threshold = [ `Fail | `Warn ]

type options = {
  quint : string option;
  threshold : threshold;
}

type run_config = {
  max_samples : int;
  max_steps : int;
  seed : string option;
  run_timeout_s : float;
  invariants : string list;
}

type result = { report : Report.t; human : string; json : string }

let resolve_spec_path path =
  let absolute =
    if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path
    else path
  in
  try Unix.realpath absolute with Unix.Unix_error _ -> absolute

let run (options : options) spec_path =
  let spec_path = resolve_spec_path spec_path in
  if not (Sys.file_exists spec_path) then
    Error (Analysis.Io { path = spec_path; reason = "no such file" })
  else
    match Quint_parse.resolve ~quint:options.quint with
    | Error reason -> Error (Analysis.Internal { path = spec_path; reason })
    | Ok quint -> (
        match Ir_facts.get ~quint ~spec_path ~flags:"lint-v1" with
        | Error err -> Error err
        | Ok payload ->
            let findings =
              List.concat_map
                (fun (m : Ir.module_) ->
                  let symbols =
                    Symbols.build ~resolution:payload.Ir_facts.program.Ir.resolution m
                  in
                  let ctx = Checks.{ program = payload.Ir_facts.program; module_ = m; symbols } in
                  Checks.run_ir_checks ctx)
                payload.Ir_facts.program.Ir.modules
            in
            let report =
              Report.make ~spec_path ~quint_version:payload.Ir_facts.quint_version
                ~ir_sha256:payload.Ir_facts.ir_sha256
                ~parse_ms:payload.Ir_facts.parse_ms ~mode:"ir"
                ~threshold:options.threshold payload.Ir_facts.program findings
            in
            Ok
              {
                report;
                human = Report.human report;
                json = Report.json_string report;
              })

let run_full (options : options) (config : run_config) spec_path =
  let spec_path = resolve_spec_path spec_path in
  if not (Sys.file_exists spec_path) then
    Error (Analysis.Io { path = spec_path; reason = "no such file" })
  else
    match Quint_parse.resolve ~quint:options.quint with
    | Error reason -> Error (Analysis.Internal { path = spec_path; reason })
    | Ok quint -> (
        match Ir_facts.get ~quint ~spec_path ~flags:"full-v1" with
        | Error err -> Error err
        | Ok payload ->
            let pins =
              Runner.
                {
                  backend = "rust";
                  max_samples = config.max_samples;
                  max_steps = config.max_steps;
                  seed = config.seed;
                  timeout_s = config.run_timeout_s;
                }
            in
            let run_options =
              Run_checks.{ quint; pins; invariants = config.invariants }
            in
            let step acc (m : Ir.module_) =
              match acc with
              | Error _ as error -> error
              | Ok findings ->
                  let symbols =
                    Symbols.build
                      ~resolution:payload.Ir_facts.program.Ir.resolution m
                  in
                  let ctx =
                    Checks.
                      { program = payload.Ir_facts.program; module_ = m; symbols }
                  in
                  let ir = Checks.run_ir_checks ctx in
                  (match Run_checks.run run_options ctx with
                  | Error error -> Error error
                  | Ok run_findings ->
                      Ok (List.rev_append (ir @ run_findings) findings))
            in
            (match List.fold_left step (Ok []) payload.Ir_facts.program.Ir.modules with
            | Error error -> Error error
            | Ok findings ->
                let run_pins =
                  Report.
                    {
                      backend = pins.Runner.backend;
                      samples = pins.Runner.max_samples;
                      steps = pins.Runner.max_steps;
                      seed = pins.Runner.seed;
                    }
                in
                let report =
                  Report.make ~run_mode:true ~run_pins ~spec_path
                    ~quint_version:payload.Ir_facts.quint_version
                    ~ir_sha256:payload.Ir_facts.ir_sha256
                    ~parse_ms:payload.Ir_facts.parse_ms ~mode:"ir+run"
                    ~threshold:options.threshold payload.Ir_facts.program
                    findings
                in
                Ok
                  {
                    report;
                    human = Report.human report;
                    json = Report.json_string report;
                  }))
