(** One [quint run] invocation, as an argv vector through [Quint_parse.run].

    Every invocation pins [--backend], [--verbosity], [--max-samples] and
    [--max-steps]; [--seed] is optional. The observable facts are fed to the
    three-state classifier in [Run_disc]. See README.md (Usage).
    No shell is involved: argv only. Licence: AGPLv3 - see LICENSE. *)

type pins = {
  backend : string;
  max_samples : int;
  max_steps : int;
  seed : string option;
  timeout_s : float;
}

let default_pins =
  { backend = "rust"; max_samples = 10; max_steps = 20; seed = None;
    timeout_s = 120.0 }

type invocation = {
  argv : string list;
  outcome : Quint_parse.outcome;
  facts : Run_disc.facts;
  verdict : Run_disc.outcome;
}

let find_sub haystack needle =
  let n = String.length needle and h = String.length haystack in
  if n = 0 then Some 0
  else
    let rec go i =
      if i + n > h then None
      else if String.sub haystack i n = needle then Some i
      else go (i + 1)
    in
    go 0

let contains haystack needle = Option.is_some (find_sub haystack needle)

(* ---- quint error lines --------------------------------------------------- *)

(* Grammar of a quint error line (0.33.1 observed spellings): an error line
   starts at column 0 after leading whitespace with one of

     [QNT404] Name 'init' not found
     error: [QNT500] Expected boolean
     Error [QNT503]: Division by zero
     Error: [QNT...]

   i.e. the bracket tag itself, or the tag after an error lead. The tag is
   "[QNT" digits "]". A tag after any other lead (for example
   "warning: [QNT000] note") is NOT an error line: the run classification
   must not treat it as one. The match is case-sensitive and requires the
   bracket by design. *)
let qnt_error_tag line =
  let text = String.trim line in
  let starts prefix = String.starts_with ~prefix text in
  let drop n =
    if String.length text <= n then ""
    else String.trim (String.sub text n (String.length text - n))
  in
  let rest =
    if starts "[QNT" then Some text
    else if starts "error:" then Some (drop 6)
    else if starts "Error:" then Some (drop 6)
    else if starts "Error " then Some (drop 6)
    else None
  in
  match rest with
  | Some candidate when String.starts_with ~prefix:"[QNT" candidate ->
      let after = String.sub candidate 4 (String.length candidate - 4) in
      let digits = ref 0 in
      while
        !digits < String.length after
        && after.[!digits] >= '0'
        && after.[!digits] <= '9'
      do
        incr digits
      done;
      if
        !digits > 0
        && String.length after > !digits
        && after.[!digits] = ']'
      then Some (String.sub candidate 0 (5 + !digits))
      else None
  | _ -> None

let first_qnt_error_line text =
  String.split_on_char '\n' text
  |> List.find_map (fun line ->
         match qnt_error_tag line with
         | Some _ -> Some (String.trim line)
         | None -> None)

let has_qnt_error text = Option.is_some (first_qnt_error_line text)

let success_marker = "[ok] No violation found"

let failure_markers =
  [
    "[violation] Found an issue";
    "error: Invariant violated";
    "[error] Runtime error";
    "error: Runtime error";
  ]

let output_text (inv : invocation) =
  inv.outcome.Quint_parse.stdout ^ inv.outcome.Quint_parse.stderr

let facts_of_outcome (o : Quint_parse.outcome) =
  let combined = o.Quint_parse.stdout ^ o.Quint_parse.stderr in
  let rc =
    match o.Quint_parse.rc with
    | Some 0 -> Run_disc.Zero
    | Some _ -> Run_disc.Nonzero
    | None -> Run_disc.No_rc
  in
  {
    Run_disc.rc;
    timed_out = o.Quint_parse.timed_out;
    success_summary = contains combined success_marker;
    failure_summary =
      List.exists (contains combined) failure_markers
      || has_qnt_error combined;
    empty_output = String.trim combined = "";
  }

let run_invocation ~quint ~args ~pins =
  let outcome = Quint_parse.run ~quint ~args ~timeout_s:pins.timeout_s in
  let facts = facts_of_outcome outcome in
  { argv = quint :: args; outcome; facts; verdict = Run_disc.classify facts }

let base_args ~spec_path ~module_name ~pins ~verbosity ~max_steps ~max_samples
    =
  let seed =
    match pins.seed with Some s -> [ "--seed=" ^ s ] | None -> []
  in
  [
    "run";
    spec_path;
    "--main=" ^ module_name;
    "--backend=" ^ pins.backend;
    Printf.sprintf "--verbosity=%d" verbosity;
    Printf.sprintf "--max-samples=%d" max_samples;
    Printf.sprintf "--max-steps=%d" max_steps;
  ]
  @ seed

let run_witnesses ~quint ~spec_path ~module_name ~pins ~witnesses =
  let witness_args = List.map (fun w -> "--witnesses=" ^ w) witnesses in
  let args =
    base_args ~spec_path ~module_name ~pins ~verbosity:1
      ~max_steps:pins.max_steps ~max_samples:pins.max_samples
    @ witness_args
  in
  run_invocation ~quint ~args ~pins

let run_init ~quint ~spec_path ~module_name ~pins ~verbosity =
  let args =
    base_args ~spec_path ~module_name ~pins ~verbosity ~max_steps:0
      ~max_samples:1
  in
  run_invocation ~quint ~args ~pins

let run_invariant ~quint ~spec_path ~module_name ~pins ~invariant ~verbosity
    ~max_steps ~max_samples ~mbt =
  let args =
    base_args ~spec_path ~module_name ~pins ~verbosity ~max_steps ~max_samples
    @ [ "--invariant=" ^ invariant ]
    @ (if mbt then [ "--mbt" ] else [])
  in
  run_invocation ~quint ~args ~pins

let run_coverage ~quint ~spec_path ~module_name ~pins ~out_prefix =
  let args =
    base_args ~spec_path ~module_name ~pins ~verbosity:1
      ~max_steps:pins.max_steps ~max_samples:pins.max_samples
    @ [
        "--mbt";
        Printf.sprintf "--n-traces=%d" pins.max_samples;
        "--out-itf=" ^ out_prefix ^ "{seq}.itf.json";
      ]
  in
  run_invocation ~quint ~args ~pins

(* ---- pure output parsers ------------------------------------------------- *)

let split_ws s =
  String.split_on_char ' ' s |> List.filter (fun x -> x <> "")

(* "<name> was witnessed in <n> trace(s) out of <m> explored (p%)" *)
let parse_witness_line line =
  match find_sub line " was witnessed in " with
  | None -> None
  | Some i ->
      let name = String.sub line 0 i in
      let rest =
        String.sub line (i + String.length " was witnessed in ")
          (String.length line - i - String.length " was witnessed in ")
      in
      (match split_ws rest with
      | n :: _trace :: _out :: _of :: m :: _ -> (
          match (int_of_string_opt n, int_of_string_opt m) with
          | Some n, Some m -> Some (name, n, m)
          | _ -> None)
      | _ -> None)

let parse_witness_counts text =
  String.split_on_char '\n' text |> List.filter_map parse_witness_line

(* A state header is a line starting with "[State <n>]"; the state body may be
   on the same line or on following lines (a record is printed multi-line). *)
let state_header line =
  if String.starts_with ~prefix:"[State " line then
    let rest = String.sub line 7 (String.length line - 7) in
    match String.index_opt rest ']' with
    | Some j -> (
        match int_of_string_opt (String.trim (String.sub rest 0 j)) with
        | Some index ->
            Some
              ( index,
                String.sub rest (j + 1) (String.length rest - j - 1) )
        | None -> None)
    | None -> None
  else None

let ends_state_block line =
  List.exists
    (fun prefix -> String.starts_with ~prefix line)
    [ "[violation]"; "[ok]"; "[error]"; "error:"; "Use "; "Trace length"; "Witnesses:"; "You may" ]

let parse_states text =
  let lines = String.split_on_char '\n' text in
  let finish acc current =
    match current with
    | None -> acc
    | Some (index, body) -> (index, String.trim body) :: acc
  in
  let rec go acc current = function
    | [] -> List.rev (finish acc current)
    | line :: rest -> (
        match state_header line with
        | Some (index, first) ->
            go (finish acc current) (Some (index, first)) rest
        | None ->
            if ends_state_block line then List.rev (finish acc current)
            else
              match current with
              | None -> go acc None rest
              | Some (index, body) ->
                  go acc (Some (index, body ^ "\n" ^ line)) rest)
  in
  go [] None lines

let action_of_state state =
  let marker = "mbt::actionTaken: \"" in
  match find_sub state marker with
  | None -> None
  | Some i ->
      let start = i + String.length marker in
      let rest = String.sub state start (String.length state - start) in
      (match String.index_opt rest '"' with
      | Some j -> Some (String.sub rest 0 j)
      | None -> None)

(* ---- ITF trace evidence --------------------------------------------------- *)

(* One decoded ITF trace file: the action names recorded in its states, the
   number of sampled states that are state reads, and the number of state
   entries refused as shells. Decoding FAILURE is an [Error]: the coverage
   check classifies it as incomplete evidence, never as zero observed actions.
   A state entry that is not an object is not a state read, so it does not
   count as evidence. *)
type itf_trace = { actions : string list; states : int; refused : int }

(* A state object is an observation only
   when it binds at least one variable carrying a real value. `#meta` and
   `mbt::*` fields are protocol metadata, an action marker alone is not a
   binding, and an optional `vars` container counts only when one of its
   entries carries a real value. `null` and `{}` name no state, so they are
   refused as junk, not counted. Accepted as a state: any object with one
   other real-valued field. Refused as a shell: `{}`, `{"#meta": {...}}`,
   `{"mbt::actionTaken": ...}`, `{"vars": {}}`, `{"x": null}` and
   `{"vars": {"x": {}}}`. A trace whose states are all shells observes no
   state (analysis-incomplete, exit 2). *)
let real_binding_value = function
  | `Null -> false
  | `Assoc [] -> false
  | _ -> true

let state_binds_var (key, value) =
  key <> "#meta"
  && (not (String.starts_with ~prefix:"mbt::" key))
  &&
  if key = "vars" then
    match value with
    | `Assoc fields ->
        List.exists
          (fun (k, v) ->
            k <> "#meta"
            && (not (String.starts_with ~prefix:"mbt::" k))
            && real_binding_value v)
          fields
    | _ -> false
  else real_binding_value value

let is_state_observation = function
  | `Assoc fields -> List.exists state_binds_var fields
  | _ -> false

(* OCaml's Sys_error text is `<path>: <errno text>`, and
   the coverage evidence paths carry a per-run temp name. Keep the errno text,
   drop the path: the caller names the evidence by its role (trace index). *)
let sys_error_detail path message =
  let prefix = path ^ ": " in
  if String.starts_with ~prefix message then
    String.sub message (String.length prefix)
      (String.length message - String.length prefix)
  else "the file could not be read"

let itf_trace path =
  match Yojson.Safe.from_file path with
  | exception Sys_error message -> Error (sys_error_detail path message)
  | exception Yojson.Json_error message -> Error message
  | `Assoc fields -> (
      match List.assoc_opt "states" fields with
      | Some (`List states) ->
          let state_objects = List.filter is_state_observation states in
          let actions =
            List.filter_map
              (function
                | `Assoc state -> (
                    match List.assoc_opt "mbt::actionTaken" state with
                    | Some (`String action) -> Some action
                    | _ -> None)
                | _ -> None)
              state_objects
          in
          Ok
            {
              actions = List.sort_uniq String.compare actions;
              states = List.length state_objects;
              refused = List.length states - List.length state_objects;
            }
      | Some _ -> Error "the `states` field is not an array"
      | None -> Error "no `states` array (not an ITF trace)")
  | _ -> Error "not a JSON object (not an ITF trace)"
