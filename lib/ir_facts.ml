(** Parse-once-per-process IR facts, keyed by source sha and flags.

    A process-lifetime cache, no cross-run
    persistence and no cache directory in v1. See README.md (How it works).
    Licence: AGPLv3 - see LICENSE. *)

type payload = {
  program : Ir.program;
  ir_sha256 : string;
  ir_bytes : int;
  parse_ms : int;
  quint_version : string;
  source_sha256 : string;
}

let cache : (string, payload) Hashtbl.t = Hashtbl.create 8
let parse_count = ref 0
let parse_timeout_s = 60.0
let version_timeout_s = 10.0
let cached_version : string option ref = ref None

let reset () =
  Hashtbl.reset cache;
  parse_count := 0;
  cached_version := None

let read_text path =
  try Ok (Quint_parse.read_file path)
  with Sys_error reason -> Error (Analysis.Io { path; reason })

let quint_version ~quint =
  match !cached_version with
  | Some v -> v
  | None ->
      let v =
        match Quint_parse.version ~quint ~timeout_s:version_timeout_s with
        | Some v -> v
        | None -> "unknown"
      in
      cached_version := Some v;
      v

let parse_once ~quint ~spec_path ~source_text ~source_sha256 ~flags =
  let ir_path = Filename.temp_file "quint-audit-ir-" ".json" in
  let map_path = Filename.temp_file "quint-audit-map-" ".json" in
  let cleanup () =
    (try Sys.remove ir_path with Sys_error _ -> ());
    try Sys.remove map_path with Sys_error _ -> ()
  in
  Fun.protect ~finally:cleanup (fun () ->
      let started = Unix.gettimeofday () in
      let outcome =
        Quint_parse.run ~quint
          ~args:(Quint_parse.parse_args ~spec_path ~ir_path ~map_path)
          ~timeout_s:parse_timeout_s
      in
      parse_count := !parse_count + 1;
      let parse_ms =
        int_of_float ((Unix.gettimeofday () -. started) *. 1000.0)
      in
      if outcome.Quint_parse.timed_out then
        Error (Analysis.Parse_timeout { path = spec_path; seconds = parse_timeout_s })
      else
        match outcome.Quint_parse.rc with
        | Some 0 -> (
            match read_text ir_path with
            | Error (Analysis.Io { reason; _ }) ->
                Error (Analysis.Io { path = ir_path; reason })
            | Error err -> Error err
            | Ok ir_text -> (
                match read_text map_path with
                | Error (Analysis.Io { reason; _ }) ->
                    Error (Analysis.Io { path = map_path; reason })
                | Error err -> Error err
                | Ok map_text -> (
                    let decode_error path reason =
                      Analysis.Decode
                        {
                          path = spec_path;
                          error = Ir_decode.Invalid_value { path; reason };
                        }
                    in
                    match Yojson.Safe.from_string ir_text with
                    | exception Yojson.Json_error msg ->
                        Error (decode_error ir_path msg)
                    | ir -> (
                        match Yojson.Safe.from_string map_text with
                        | exception Yojson.Json_error msg ->
                            Error (decode_error map_path msg)
                        | map -> (
                            match
                              Ir_decode.decode_program ~ir ~map
                                ~source_path:spec_path ~source_text
                            with
                            | Error error -> Error (Analysis.Decode { path = spec_path; error })
                            | Ok program ->
                                Ok
                                  {
                                    program;
                                    ir_sha256 = Sha256.digest_bytes ir_text;
                                    ir_bytes = String.length ir_text;
                                    parse_ms;
                                    quint_version = quint_version ~quint;
                                    source_sha256;
                                  })))))
        | rc ->
            let first_ir_error =
              match read_text ir_path with
              | Error _ -> None
              | Ok text -> (
                  match Yojson.Safe.from_string text with
                  | exception Yojson.Json_error _ -> None
                  | `Assoc fs -> (
                      match List.assoc_opt "errors" fs with
                      | Some (`List (e :: _)) -> (
                          match e with
                          | `Assoc efs -> (
                              match List.assoc_opt "explanation" efs with
                              | Some (`String s) -> Some s
                              | _ -> None)
                          | _ -> None)
                      | _ -> None)
                  | _ -> None)
            in
            let detail =
              let stderr = String.trim outcome.Quint_parse.stderr in
              let stdout = String.trim outcome.Quint_parse.stdout in
              match (stderr, stdout, first_ir_error) with
              | "", "", Some s -> s
              | "", "", None -> "no diagnostic output"
              | "", s, _ -> s
              | s, _, _ -> s
            in
            Error
              (Analysis.Parse_failed
                 { path = spec_path; rc; detail = flags ^ ": " ^ detail }))

let get ~quint ~spec_path ~flags =
  match read_text spec_path with
  | Error err -> Error err
  | Ok source_text -> (
      match Ir_decode.non_ascii_offset source_text with
      | Some offset -> Error (Analysis.Non_ascii { path = spec_path; offset })
      | None ->
          let source_sha256 = Sha256.digest_bytes source_text in
          let key = source_sha256 ^ "|" ^ spec_path ^ "|" ^ flags in
          match Hashtbl.find_opt cache key with
          | Some payload -> Ok payload
          | None -> (
              match
                parse_once ~quint ~spec_path ~source_text ~source_sha256 ~flags
              with
              | Error err -> Error err
              | Ok payload ->
                  Hashtbl.replace cache key payload;
                  Ok payload))
