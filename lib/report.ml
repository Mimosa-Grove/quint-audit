(** The report: human table and JSON.

    Both formats carry the same findings. Statuses are derived from findings:
    any fail is fail, else any warn is warn, else pass; an info-only check
    prints as a coverage note rather than a pass claim. A check that was
    not asked of the module is skipped: the deferred and requires-run checks,
    and QL009 on a module whose defining file is not the analysed spec
    (README, Reading the report). Licence: AGPLv3 - see LICENSE. *)

type pins = {
  backend : string;
  samples : int;
  steps : int;
  seed : string option;
}

type module_report = {
  module_ : Ir.module_;
  own : Finding.finding list;
  entry : bool;  (* the module's defining file is the analysed spec *)
}

type t = {
  spec_path : string;
  quint_version : string;
  ir_sha256 : string;
  parse_ms : int;
  mode : string;
  modules : module_report list;
  findings : Finding.finding list;
  emitted : int;  (* findings as all checks ran, before report dedup *)
  threshold : [ `Fail | `Warn ];
  exit_code : int;
  run_mode : bool;
  run_pins : pins option;
}

type status = Pass | Warn | Fail | Skipped

let string_of_status = function
  | Pass -> "pass"
  | Warn -> "warn"
  | Fail -> "fail"
  | Skipped -> "skipped"

let skipped_checks ?(run_mode = false) () =
  if run_mode then [ Finding.QL005 ]
  else [ Finding.QL004; Finding.QL005; Finding.QL007; Finding.QL010; Finding.QL011 ]

let skip_reason = function
  | Finding.QL005 -> "deferred"
  | Finding.QL004 | Finding.QL007 | Finding.QL010 | Finding.QL011 ->
      "skipped (requires run)"
  | Finding.QL009 ->
      "skipped (out of scope: module defined outside the analysed spec)"
  | _ -> "skipped"

(* A check that was not asked of the module is `skipped`,
   never `pass`. QL009 asks its runnable-unit question of the entry module
   only, so a non-entry module's QL009 row is scope-skipped. The entry test is
   [Ir.is_entry_module], the same predicate the check uses. *)
let scoped_skip check entry = check = Finding.QL009 && not entry

let status_of_findings findings check =
  let own = List.filter (fun f -> f.Finding.check = check) findings in
  if List.exists (fun f -> f.Finding.severity = Finding.Fail) own then Fail
  else if List.exists (fun f -> f.Finding.severity = Finding.Warn) own then Warn
  else Pass

let status_for ~skipped_list ~entry own check =
  if List.mem check skipped_list then Skipped
  else if scoped_skip check entry then Skipped
  else status_of_findings own check

let count_severity severity findings =
  List.length (List.filter (fun f -> f.Finding.severity = severity) findings)

let make ?(run_mode = false) ?run_pins ~spec_path ~quint_version ~ir_sha256
    ~parse_ms ~mode ~threshold (program : Ir.program) findings =
  let emitted = List.length findings in
  let findings = Finding.normalise findings in
  let modules =
    List.map
      (fun (m : Ir.module_) ->
        let own =
          List.filter (fun f -> f.Finding.module_name = m.Ir.module_name) findings
        in
        { module_ = m; own; entry = Ir.is_entry_module program m })
      program.Ir.modules
  in
  let exceeds =
    match threshold with
    | `Fail -> List.exists (fun f -> f.Finding.severity = Finding.Fail) findings
    | `Warn ->
        List.exists
          (fun f ->
            f.Finding.severity = Finding.Fail || f.Finding.severity = Finding.Warn)
          findings
  in
  {
    spec_path;
    quint_version;
    ir_sha256;
    parse_ms;
    mode;
    modules;
    findings;
    emitted;
    threshold;
    exit_code = if exceeds then 1 else 0;
    run_mode;
    run_pins;
  }

let position_json (p : Ir.position) =
  `Assoc
    [
      ("line", `Int (p.Ir.line + 1));
      ("col", `Int (p.Ir.column + 1));
      ("index", `Int p.Ir.index);
    ]

let span_json (s : Ir.span) =
  `Assoc
    [
      ("start", position_json s.Ir.start_pos);
      ("end", position_json s.Ir.end_pos);
    ]

let finding_json (f : Finding.finding) =
  `Assoc
    [
      ("check", `String (Finding.string_of_check f.Finding.check));
      ("severity", `String (Finding.string_of_severity f.Finding.severity));
      ("module", `String f.Finding.module_name);
      ("source", `String f.Finding.source);
      ("start", position_json f.Finding.location.Ir.start_pos);
      ("end", position_json f.Finding.location.Ir.end_pos);
      ("message", `String f.Finding.message);
      ( "suggestion",
        match f.Finding.suggestion with None -> `Null | Some s -> `String s );
    ]

let source_groups findings =
  (* findings arrive sorted by source, so equal sources are adjacent. *)
  let rec go acc current group = function
    | [] -> (
        match current with
        | None -> List.rev acc
        | Some source -> List.rev (`Assoc [ ("source", `String source); ("findings", `List (List.rev group)) ] :: acc))
    | (f : Finding.finding) :: rest -> (
        match current with
        | Some source when source = f.Finding.source -> go acc current (finding_json f :: group) rest
        | _ ->
            let acc =
              match current with
              | None -> acc
              | Some source ->
                  `Assoc [ ("source", `String source); ("findings", `List (List.rev group)) ] :: acc
            in
            go acc (Some f.Finding.source) [ finding_json f ] rest)
  in
  go [] None [] findings

let json (r : t) =
  let skipped_list = skipped_checks ~run_mode:r.run_mode () in
  let skipped_global =
    List.length
      (List.filter (fun c -> List.mem c skipped_list) Finding.all_checks)
  in
  let skipped =
    List.fold_left
      (fun acc (m : module_report) ->
        acc + skipped_global + if scoped_skip Finding.QL009 m.entry then 1 else 0)
      0 r.modules
  in
  let check_entries =
    List.concat_map
      (fun (m : module_report) ->
        List.map
          (fun check ->
            let status = status_for ~skipped_list ~entry:m.entry m.own check in
            let own_findings =
              List.filter (fun f -> f.Finding.check = check) m.own
            in
            `Assoc
              [
                ("id", `String (Finding.string_of_check check));
                ("name", `String (Finding.check_name check));
                ("mode", `String (Finding.string_of_mode (Finding.check_mode check)));
                ("module", `String m.module_.Ir.module_name);
                ("status", `String (string_of_status status));
                ("findings", `List (List.map finding_json own_findings));
              ])
          Finding.all_checks)
      r.modules
  in
  `Assoc
    [
      ( "tool",
        `Assoc
          [ ("name", `String "quint-audit"); ("version", `String Version.version) ] );
      ("spec", `String r.spec_path);
      ( "quint",
        `Assoc
          [
            ("version", `String r.quint_version);
            ("ir_sha256", `String r.ir_sha256);
            ("parse_ms", `Int r.parse_ms);
          ] );
      ("modules", `List (List.map (fun (m : module_report) -> `String m.module_.Ir.module_name) r.modules));
      ("checks", `List check_entries);
      ("findings", `List (List.map finding_json r.findings));
      ("sources", `List (source_groups r.findings));
      ( "dedup",
        `Assoc
          [
            ("emitted", `Int r.emitted);
            ("reported", `Int (List.length r.findings));
            ("removed", `Int (r.emitted - List.length r.findings));
          ] );
      ( "summary",
        `Assoc
          [
            ("fail", `Int (count_severity Finding.Fail r.findings));
            ("warn", `Int (count_severity Finding.Warn r.findings));
            ("info", `Int (count_severity Finding.Info r.findings));
            ("skipped", `Int skipped);
          ] );
      ("exit", `Int r.exit_code);
    ]

let json_string (r : t) = Yojson.Safe.pretty_to_string (json r)

(* Use the llm-kit glyphs: check, warning sign, cross. *)
let pass_glyph = "\xe2\x9c\x93"
let warn_glyph = "\xe2\x9a\xa0"
let fail_glyph = "\xe2\x9c\x97"

let own_for check findings =
  List.filter (fun f -> f.Finding.check = check) findings

let info_text own =
  let infos = List.filter (fun f -> f.Finding.severity = Finding.Info) own in
  if infos = [] then ""
  else
    Printf.sprintf "i %d: %s" (List.length infos)
      (String.concat "; "
         (List.map (fun (f : Finding.finding) -> f.Finding.message) infos))

let detail_for check status own =
  let scoped = own_for check own in
  let count severity = count_severity severity scoped in
  let with_info base =
    match info_text scoped with "" -> base | text -> base ^ "; " ^ text
  in
  match status with
  | Skipped -> skip_reason check
  | Pass ->
      (* Parity with the JSON: an Info finding's text is
         rendered here, not only its count, so the terminal says what the
         JSON says, and the same text rides on a Warn or Fail
         row too - every row that has an Info finding states it. *)
      (match info_text scoped with "" -> pass_glyph | text -> text)
  | Warn ->
      let n = count Finding.Warn + count Finding.Fail in
      with_info (Printf.sprintf "%s %d issue(s)" warn_glyph n)
  | Fail ->
      with_info (Printf.sprintf "%s %d issue(s)" fail_glyph (count Finding.Fail))

let render_rows skipped entry buffer module_findings =
  let render_section title checks =
    Buffer.add_string buffer (title ^ "\n");
    List.iter
      (fun check ->
        let status = status_for ~skipped_list:skipped ~entry module_findings check in
        Buffer.add_string buffer
          (Printf.sprintf "  %-31s %-5s  [%s]\n"
             (Finding.check_name check)
             (Finding.string_of_check check)
             (detail_for check status module_findings)))
      checks;
    Buffer.add_string buffer "\n"
  in
  render_section "Structural (vs the build discipline)"
    [ Finding.QL001; Finding.QL002; Finding.QL003; Finding.QL004; Finding.QL005; Finding.QL006 ];
  render_section "Runtime"
    [ Finding.QL007; Finding.QL008; Finding.QL009; Finding.QL010; Finding.QL011 ];
  render_section "Differentiator checks" [ Finding.QP001; Finding.QP002 ]

let position_text (p : Ir.position) =
  Printf.sprintf "%d:%d" (p.Ir.line + 1) (p.Ir.column + 1)

let top_issues r =
  let ranked =
    List.sort
      (fun a b ->
        match
          compare (Finding.severity_rank a.Finding.severity)
            (Finding.severity_rank b.Finding.severity)
        with
        | 0 -> Finding.compare_findings a b
        | c -> c)
      (List.filter
         (fun f -> f.Finding.severity <> Finding.Info)
         r.findings)
  in
  let rec take n = function [] -> [] | _ when n <= 0 -> [] | x :: xs -> x :: take (n - 1) xs in
  take 10 ranked

let human (r : t) =
  let buffer = Buffer.create 4096 in
  let base = Filename.basename r.spec_path in
  let skipped = skipped_checks ~run_mode:r.run_mode () in
  List.iter
    (fun (m : module_report) ->
      Buffer.add_string buffer
        (Printf.sprintf "-- Spec review: %s (module %s) --\n" base m.module_.Ir.module_name);
      Buffer.add_string buffer
        (Printf.sprintf "quint %s | ir sha256 %s | parse %d ms | mode %s\n"
           r.quint_version r.ir_sha256 r.parse_ms r.mode);
      (match r.run_pins with
      | Some p ->
          Buffer.add_string buffer
            (Printf.sprintf "run: backend %s, samples %d, steps %d%s\n"
               p.backend p.samples p.steps
               (match p.seed with Some s -> ", seed " ^ s | None -> ""))
      | None -> ());
      Buffer.add_string buffer "\n";
      render_rows skipped m.entry buffer m.own;
      Buffer.add_string buffer "\n")
    r.modules;
  let issues = top_issues r in
  if issues <> [] then begin
    Buffer.add_string buffer "-- Top issues --\n";
    List.iteri
      (fun i f ->
        let loc =
          Printf.sprintf "%s:%s" f.Finding.source
            (position_text f.Finding.location.Ir.start_pos)
        in
        let suggestion =
          match f.Finding.suggestion with
          | Some s -> Printf.sprintf " (%s)" s
          | None -> ""
        in
        Buffer.add_string buffer
          (Printf.sprintf "  %d. %s %s %s%s\n" (i + 1)
             (Finding.string_of_check f.Finding.check)
             loc f.Finding.message suggestion))
      issues;
    Buffer.add_string buffer "\n"
  end;
  let fails = count_severity Finding.Fail r.findings in
  let warns = count_severity Finding.Warn r.findings in
  (* The next-step list states what the report found. A clean report never
     suggests fixing fails that are not there. *)
  let steps =
    if fails > 0 then
      [
        "Fix the fails above";
        "Stress-test flagged scenarios with `quint run`";
        "Re-run `quint-audit lint` after fixes";
      ]
    else if warns > 0 then
      [
        "Review the warnings above";
        "Stress-test flagged scenarios with `quint run`";
        "Re-run `quint-audit lint` after fixes";
      ]
    else if r.run_mode then [ "No action required" ]
    else
      [
        "Run `quint-audit full` to sample the runtime checks";
        "Re-run `quint-audit lint` after changes";
      ]
  in
  Buffer.add_string buffer "-- Suggested next steps --\n";
  List.iteri
    (fun i step ->
      Buffer.add_string buffer (Printf.sprintf "  %d. %s\n" (i + 1) step))
    steps;
  Buffer.contents buffer
