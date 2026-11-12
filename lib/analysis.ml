(** Analysis failures: everything that is exit code 2, never a lint finding.

    Exit 2 is "the analysis did not complete" and is never conflated with
    a lint failure (README, Exit codes). Licence: AGPLv3 - see LICENSE. *)

type error =
  | Io of { path : string; reason : string }
  | Non_ascii of { path : string; offset : int }
  | Parse_timeout of { path : string; seconds : float }
  | Parse_failed of { path : string; rc : int option; detail : string }
  | Decode of { path : string; error : Ir_decode.decode_error }
  | Run_failed of { stage : string; reason : string }
  | Internal of { path : string; reason : string }

let describe ~quint_path = function
  | Io { path; reason } ->
      Printf.sprintf "read: %s: %s" path reason
  | Non_ascii { path; offset } ->
      Printf.sprintf "ascii: %s: non-ASCII byte at offset %d" path offset
  | Parse_timeout { path; seconds } ->
      Printf.sprintf "parse: %s: timed out after %.0f s (quint: %s)" path seconds
        quint_path
  | Parse_failed { path; rc; detail } ->
      let rc =
        match rc with None -> "no exit code" | Some rc -> string_of_int rc
      in
      Printf.sprintf "parse: %s: quint parse failed (rc %s, quint: %s): %s" path rc
        quint_path detail
  | Decode { path; error } ->
      Printf.sprintf "decode: %s (quint: %s)"
        (Ir_decode.describe_error ~source:path error)
        quint_path
  | Run_failed { stage; reason } ->
      Printf.sprintf "run: %s: %s (quint: %s)" stage reason quint_path
  | Internal { path; reason } ->
      Printf.sprintf "internal: %s: %s" path reason

let exit_code _ = 2
