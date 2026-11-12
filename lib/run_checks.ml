(** The run-driving checks: the QL004 RUN half, both QL007 halves, QL010 and
    QL011.

    Every invocation is pinned: an explicit
    backend, verbosity, sample count and step bound. The classification is the
    three-state discipline in [Run_disc]: a run that did not execute is an
    analysis error (exit 2), never a pass and never a lint finding. A run's
    invariant and action names are carried from the invocation, never read
    from default-verbosity output. See README.md (Usage).
    Licence: AGPLv3 - see LICENSE. *)

type options = { quint : string; pins : Runner.pins; invariants : string list }

let ( let* ) result f =
  match result with Ok value -> f value | Error _ as error -> error

let spec_path ctx = ctx.Checks.program.Ir.source_path
let module_name ctx = ctx.Checks.module_.Ir.module_name

let decl_of ctx name =
  List.find_opt
    (fun (d : Ir.declaration) -> d.Ir.name = name)
    ctx.Checks.module_.Ir.declarations

let witness_candidates ctx =
  Checks.vals ctx
  (* QL004's census is state-reading plain vals; pure declarations are
     reporting subjects for QL006/QP001 but not witnesses.
     A witness is a nullary value quint can evaluate by name, so a
     parameterised val is not a
     candidate. *)
  |> List.filter (fun (d : Ir.declaration) ->
      d.Ir.qualifier = Some Ir.Val && d.Ir.params = [])
  |> List.filter (fun (d : Ir.declaration) ->
      match d.Ir.body with
      | None -> false
      | Some body ->
          let refs = Symbols.referenced_names ctx.Checks.symbols body in
          let reads_var =
            List.exists
              (fun (name, _) ->
                Symbols.mem ctx.Checks.symbols.Symbols.vars name)
              refs.Symbols.refs
          in
          reads_var
          &&
          match Qcalc.classify body with Qcalc.Refused _ -> false | _ -> true)

(* The declaration shape, for a usage diagnostic. *)
let declaration_shape (d : Ir.declaration) =
  let shape =
    match (d.Ir.kind, d.Ir.qualifier) with
    | Ir.NonSubject (Ir.Import _), _ -> "import"
    | Ir.NonSubject (Ir.Instance _), _ -> "instance"
    | Ir.NonSubject (Ir.Assume _), _ -> "assume"
    | Ir.NonSubject (Ir.Unmodelled { kind }), _ -> kind
    | Ir.Const, _ -> "const"
    | Ir.Var, _ -> "var"
    | Ir.TypeDef, _ -> "type"
    | Ir.Def, Some Ir.Val -> "val"
    | Ir.Def, Some Ir.PureVal -> "pure val"
    | Ir.Def, Some Ir.PureDef -> "pure def"
    | Ir.Def, Some Ir.Action -> "action"
    | Ir.Def, Some Ir.Temporal -> "temporal"
    | Ir.Def, Some Ir.Run -> "run"
    | Ir.Def, Some Ir.PlainDef -> "def"
    | Ir.Def, Some (Ir.OtherQualifier other) -> other
    | Ir.Def, None -> "declaration"
  in
  if d.Ir.params <> [] then shape ^ " with parameters" else shape

(* The QL010/QL011 object: only the vals the caller declared with
   --invariant. Quint 0.33.1 has no invariant keyword (quint#1772), so the
   invocation is the declaration. Witness candidates are a different role
   and never feed these checks.

   A supplied name is never dropped: a name that resolves to
   no declaration, or to a declaration whose shape is not evaluable as an
   invariant, is a usage error naming what was found. *)
let invariant_decl ctx name =
  match decl_of ctx name with
  | None ->
      Error
        (Printf.sprintf "`--invariant=%s` names no declaration in module `%s`"
           name (module_name ctx))
  | Some d ->
      if
        d.Ir.kind = Ir.Def && d.Ir.qualifier = Some Ir.Val
        && d.Ir.params = [] && Option.is_some d.Ir.body
      then Ok d
      else
        Error
          (Printf.sprintf
             "`--invariant=%s` names declaration `%s` (%s); only a nullary `val` with a body can be evaluated as an invariant"
             name d.Ir.name (declaration_shape d))

let invariant_decls ctx names =
  let rec go acc = function
    | [] -> Ok (List.rev acc)
    | name :: rest -> (
        match invariant_decl ctx name with
        | Ok d -> go (d :: acc) rest
        | Error reason ->
            Error
              (Analysis.Run_failed { stage = "invariant declaration"; reason }))
  in
  go [] names

let run_failed stage reason = Error (Analysis.Run_failed { stage; reason })

(* ---- QL007 RUN half ------------------------------------------------------ *)

type init_state = Init_true | Init_false of string | Init_error of string

let first_line_with text prefix =
  String.split_on_char '\n' text
  |> List.find_opt (fun line ->
         String.starts_with ~prefix (String.trim line))
  |> Option.map String.trim

(* A run that quint refused to execute (a QNT-coded refusal or a runtime
   [error] line) produced no verdict: analysis-incomplete, never a violation. *)
let run_error_line text =
  match Runner.first_qnt_error_line text with
  | Some line -> Some line
  | None -> first_line_with text "[error]"

let init_detail text =
  match Runner.first_qnt_error_line text with
  | Some line -> line
  | None -> (
      match first_line_with text "error: Runtime error" with
      | Some _ -> "init raised a runtime error"
      | None -> "init returns false")

let classify_init_text text =
  if Runner.contains text "Runtime error" || Runner.has_qnt_error text then
    Init_error (init_detail text)
  else if Runner.contains text "Invariant violated" then
    Init_false "init returns false"
  else Init_false "init returns false (counterexample print crashed)"

let init_evidence options ctx =
  let spec = spec_path ctx and main = module_name ctx in
  let run verbosity =
    Runner.run_init ~quint:options.quint ~spec_path:spec ~module_name:main
      ~pins:options.pins ~verbosity
  in
  let probe_zero () =
    let v0 = run 0 in
    match v0.Runner.verdict with
    | Run_disc.Failed -> Ok (classify_init_text (Runner.output_text v0))
    | Run_disc.Passed ->
        run_failed "QL007 init"
          "the level-1 run crashed but the level-0 run reports success; the init verdict is ambiguous"
    | Run_disc.Did_not_run ->
        run_failed "QL007 init"
          (Printf.sprintf
             "the init run did not complete (timed_out=%b, output=%d bytes)"
             v0.facts.Run_disc.timed_out
             (String.length (String.trim (Runner.output_text v0))))
  in
  let v1 = run 1 in
  match v1.Runner.verdict with
  | Run_disc.Passed -> Ok Init_true
  | Run_disc.Failed ->
      let text = Runner.output_text v1 in
      if Runner.contains text "Runtime error" || Runner.has_qnt_error text
      then Ok (Init_error (init_detail text))
      else if Runner.contains text "Invariant violated" then
        Ok (Init_false "init returns false")
      else probe_zero ()
  | Run_disc.Did_not_run -> probe_zero ()

(* ---- QL004 --------------------------------------------------------------- *)

let tmp_prefix () =
  let base = Filename.temp_file "quint-audit-itf-" ".json" in
  Sys.remove base;
  base

let itf_paths prefix n =
  List.filter_map
    (fun i ->
      let path = prefix ^ string_of_int i ^ ".itf.json" in
      if Sys.file_exists path then Some (i, path) else None)
    (List.init n (fun i -> i))

let cleanup paths = List.iter (fun p -> try Sys.remove p with Sys_error _ -> ()) paths

let check_witnesses options ctx ~init_ok candidates =
  match candidates with
  | [] ->
      Ok
        [
          Checks.module_finding ctx Finding.QL004 Finding.Fail
            "no state-reading val declaration can serve as a witness"
            (Some
               "add a `val` over the model state; a witness counts how many sampled traces reach it");
        ]
  | _ when not init_ok ->
      Ok
        [
          Checks.module_finding ctx Finding.QL004 Finding.Warn
            "init did not establish a state; witness trace counts were not sampled"
            None;
        ]
  | _ ->
      let names = List.map (fun (d : Ir.declaration) -> d.Ir.name) candidates in
      let inv =
        Runner.run_witnesses ~quint:options.quint ~spec_path:(spec_path ctx)
          ~module_name:(module_name ctx) ~pins:options.pins ~witnesses:names
      in
      (match inv.Runner.verdict with
      | Run_disc.Did_not_run ->
          run_failed "QL004 witnesses"
            "the witness run did not complete (timeout, crash or empty output)"
      | Run_disc.Failed ->
          Ok
            [
              Checks.module_finding ctx Finding.QL004 Finding.Fail
                (Printf.sprintf "the witness run failed: %s"
                   (match
                      first_line_with (Runner.output_text inv) "[violation]"
                    with
                   | Some line -> line
                   | None -> "no failure summary"))
                None;
            ]
      | Run_disc.Passed -> (
          let counts = Runner.parse_witness_counts (Runner.output_text inv) in
          let count_of name =
            List.find_opt (fun (candidate, _, _) -> candidate = name) counts
            |> Option.map (fun (_, witnessed, explored) -> (witnessed, explored))
          in
          let witness_findings =
            List.filter_map
              (fun (d : Ir.declaration) ->
                match count_of d.Ir.name with
                | None ->
                    Some
                      (Checks.decl_finding ctx Finding.QL004 Finding.Fail d
                         (Printf.sprintf
                            "no witness count reported for `%s`" d.Ir.name)
                         None)
                | Some (0, explored) ->
                    Some
                      (Checks.decl_finding ctx Finding.QL004 Finding.Fail d
                         (Printf.sprintf
                            "witness `%s` was reached in 0 of %d sampled traces (dead or not evaluated)"
                            d.Ir.name explored)
                         (Some
                            "zero also covers a false init, no executed step and a deadlock; check the init run first"))
                | Some (_n, _explored) -> None)
              candidates
          in
          let prefix = tmp_prefix () in
          let coverage =
            Runner.run_coverage ~quint:options.quint ~spec_path:(spec_path ctx)
              ~module_name:(module_name ctx) ~pins:options.pins ~out_prefix:prefix
          in
          match coverage.Runner.verdict with
          | Run_disc.Did_not_run ->
              run_failed "QL004 action coverage"
                "the sampled coverage run did not complete"
          | Run_disc.Failed ->
              Ok
                (witness_findings
                @ [
                    Checks.module_finding ctx Finding.QL004 Finding.Warn
                      "the sampled coverage run failed; action coverage is unknown"
                      None;
                  ])
          | Run_disc.Passed ->
              let paths = itf_paths prefix options.pins.Runner.max_samples in
              if paths = [] then
                (* Quint exited 0 but wrote no ITF files: the coverage
                   analysis has no evidence and did not complete:
                   exit 2, never a warn-only report. *)
                run_failed "QL004 action coverage"
                  "the coverage run wrote no ITF evidence; action coverage was not analysed"
              else
              let decoded =
                List.map
                  (fun (index, path) -> (index, Runner.itf_trace path))
                  paths
              in
              cleanup (List.map snd paths);
              (match List.find_opt (function _, Error _ -> true | _ -> false) decoded with
              | Some (index, Error reason) ->
                  (* ITF files that exist but cannot be decoded are
                     incomplete evidence. Treating them as zero observed
                     actions would report every leaf action as unexercised
                     (analysis-incomplete, exit 2). Name the evidence by its
                     {seq} role, never by the absolute path - the path carries
                     the per-run random temp name, so two identical runs would
                     differ. *)
                  run_failed "QL004 action coverage"
                    (Printf.sprintf
                       "the coverage ITF evidence for trace %d could not be decoded (%s); action coverage was not analysed"
                       index reason)
              | _ ->
              let traces =
                List.filter_map
                  (function _, Ok (trace : Runner.itf_trace) -> Some trace | _ -> None)
                  decoded
              in
              let observed =
                List.sort_uniq String.compare
                  (List.concat_map
                     (fun (trace : Runner.itf_trace) -> trace.Runner.actions)
                     traces)
              in
              let analysed_files = List.length traces in
              let analysed_states =
                List.fold_left
                  (fun n (trace : Runner.itf_trace) -> n + trace.Runner.states)
                  0 traces
              in
              (* The coverage verdict is about OBSERVED
                 STATES. A decodable trace whose states carry no state object
                 is not evidence: five such files must never read as complete
                 coverage (analysis-incomplete, exit 2). *)
              if analysed_states = 0 then
                run_failed "QL004 action coverage"
                  (Printf.sprintf
                     "the coverage ITF evidence carried no observed states (read %d ITF trace files, 0 states); action coverage was not analysed"
                     analysed_files)
              else
              (* Only a trace that contributed states is analysed evidence; an
                 empty trace must not satisfy the partial-evidence gate. *)
              let evidence_files =
                List.length
                  (List.filter
                     (fun (trace : Runner.itf_trace) -> trace.Runner.states > 0)
                     traces)
              in
              let evidence_note =
                (* A partial ITF set is analysed, and the report says how
                   much evidence was read. *)
                if evidence_files < options.pins.Runner.max_samples then
                  [
                    Checks.module_finding ctx Finding.QL004 Finding.Info
                      (Printf.sprintf
                         "partial ITF evidence: analysed %d of %d sampled trace files (%d states)"
                         evidence_files options.pins.Runner.max_samples
                         analysed_states)
                      None;
                  ]
                else []
              in
              (* A file mixing accepted and refused states discloses the
                 refused count. File-level counts alone would hide it. *)
              let refused_states =
                List.fold_left
                  (fun n (trace : Runner.itf_trace) -> n + trace.Runner.refused)
                  0 traces
              in
              let refused_note =
                if refused_states > 0 then
                  [
                    Checks.module_finding ctx Finding.QL004 Finding.Info
                      (Printf.sprintf
                         "refused %d ITF state entries as shells (not state reads); the accepted states were analysed"
                         refused_states)
                      None;
                  ]
                else []
              in
              let leaf =
                Checks.actions ctx
                |> List.filter (fun (d : Ir.declaration) ->
                       d.Ir.name <> "init" && d.Ir.name <> "step"
                       && not (Checks.is_composer ctx d))
              in
              let uncovered =
                List.filter_map
                  (fun (d : Ir.declaration) ->
                    if List.mem d.Ir.name observed then None
                    else
                      Some
                        (Checks.decl_finding ctx Finding.QL004 Finding.Warn d
                           (Printf.sprintf
                              "action `%s` was not exercised in %d sampled traces (analysed %d of %d ITF trace files, %d states; sampled coverage, not proof of unreachability)"
                              d.Ir.name options.pins.Runner.max_samples
                              evidence_files options.pins.Runner.max_samples
                              analysed_states)
                           (Some "raise --max-samples/--max-steps or gate the action")))
                  leaf
              in
              Ok (witness_findings @ evidence_note @ refused_note @ uncovered))))

(* ---- QL010 and QL011 ----------------------------------------------------- *)

let state_text text =
  match List.rev (Runner.parse_states text) with
  | (_, state) :: _ when state <> "" -> state
  | _ -> "(state not printed)"

let check_hold_at_init options ctx invariants =
  if invariants = [] then
    Ok
      [
        Checks.module_finding ctx Finding.QL010 Finding.Warn
          "no `--invariant` declaration was supplied; QL010 was not evaluated"
          None;
      ]
  else
  let rec go acc = function
    | [] -> Ok (List.rev acc)
    | (d : Ir.declaration) :: rest -> (
        let inv =
          Runner.run_invariant ~quint:options.quint
            ~spec_path:(spec_path ctx) ~module_name:(module_name ctx)
            ~pins:options.pins ~invariant:d.Ir.name ~verbosity:2 ~max_steps:0
            ~max_samples:1 ~mbt:false
        in
        match inv.Runner.verdict with
        | Run_disc.Passed -> go acc rest
        | Run_disc.Failed -> (
            match run_error_line (Runner.output_text inv) with
            | Some line ->
                run_failed "QL010"
                  (Printf.sprintf
                     "the invariant run for `%s` did not execute: %s"
                     d.Ir.name line)
            | None ->
                let finding =
                  Checks.decl_finding ctx Finding.QL010 Finding.Fail d
                    (Printf.sprintf
                       "invariant `%s` is false at the initial state: %s"
                       d.Ir.name (state_text (Runner.output_text inv)))
                    (Some "fix the init action or the invariant")
                in
                go (finding :: acc) rest)
        | Run_disc.Did_not_run ->
            run_failed "QL010" "an invariant run at init did not complete")
  in
  go [] invariants

let check_after_actions options ctx invariants =
  if invariants = [] then
    Ok
      [
        Checks.module_finding ctx Finding.QL011 Finding.Warn
          "no `--invariant` declaration was supplied; QL011 was not evaluated"
          None;
      ]
  else
  let rec go acc = function
    | [] -> Ok (List.rev acc)
    | (d : Ir.declaration) :: rest -> (
        let inv =
          Runner.run_invariant ~quint:options.quint
            ~spec_path:(spec_path ctx) ~module_name:(module_name ctx)
            ~pins:options.pins ~invariant:d.Ir.name ~verbosity:3
            ~max_steps:options.pins.Runner.max_steps
            ~max_samples:options.pins.Runner.max_samples ~mbt:true
        in
        match inv.Runner.verdict with
        | Run_disc.Passed -> go acc rest
        | Run_disc.Failed -> (
            match run_error_line (Runner.output_text inv) with
            | Some line ->
                run_failed "QL011"
                  (Printf.sprintf
                     "the invariant run for `%s` did not execute: %s"
                     d.Ir.name line)
            | None -> (
                match List.rev (Runner.parse_states (Runner.output_text inv)) with
                | (index, state) :: _ when index > 0 ->
                    let action =
                      match Runner.action_of_state state with
                      | Some name -> Printf.sprintf "after action `%s`" name
                      | None -> "after an action (name not attributed)"
                    in
                    let finding =
                      Checks.decl_finding ctx Finding.QL011 Finding.Fail d
                        (Printf.sprintf "invariant `%s` is violated %s: %s"
                           d.Ir.name action state)
                        (Some "this is a sampled counterexample, not a proof")
                    in
                    go (finding :: acc) rest
                | _ -> go acc rest))
        | Run_disc.Did_not_run ->
            run_failed "QL011" "an invariant run did not complete")
  in
  go [] invariants

let sample_note options ctx =
  let seed =
    match options.pins.Runner.seed with
    | Some s -> Printf.sprintf ", seed %s" s
    | None -> ""
  in
  Checks.module_finding ctx Finding.QL011 Finding.Info
    (Printf.sprintf
       "run-driving sample: backend %s, max-samples %d, max-steps %d%s (sampled, not a proof)"
       options.pins.Runner.backend options.pins.Runner.max_samples
       options.pins.Runner.max_steps seed)
    None

let run options ctx =
  let candidates = witness_candidates ctx in
  let* invariants = invariant_decls ctx options.invariants in
  let ir_init = Checks.check_init_assignments ctx in
  let* init = init_evidence options ctx in
  let init_finding decl detail =
    match decl with
    | Some d ->
        [
          Checks.decl_finding ctx Finding.QL007 Finding.Fail d detail
            (Some "make the init action return true and assign every var");
        ]
    | None ->
        [ Checks.module_finding ctx Finding.QL007 Finding.Fail detail None ]
  in
  let init_finding =
    match init with
    | Init_true -> []
    | Init_false detail ->
        init_finding (decl_of ctx "init")
          (Printf.sprintf "init does not establish a state: %s" detail)
    | Init_error detail ->
        init_finding (decl_of ctx "init")
          (Printf.sprintf "init raises an error: %s" detail)
  in
  let init_ok = init = Init_true in
  let* witnesses = check_witnesses options ctx ~init_ok candidates in
  let skipped_notes check =
    if init_ok then []
    else
      [
        Checks.module_finding ctx check Finding.Warn
          "init did not establish a state; this run-driving check was not evaluated"
          None;
      ]
  in
  let* at_init =
    if init_ok then check_hold_at_init options ctx invariants
    else Ok (skipped_notes Finding.QL010)
  in
  let* after_actions =
    if init_ok then check_after_actions options ctx invariants
    else Ok (skipped_notes Finding.QL011)
  in
  let note = if init_ok then [ sample_note options ctx ] else [] in
  Ok (List.concat [ ir_init; init_finding; witnesses; at_init; after_actions; note ])
