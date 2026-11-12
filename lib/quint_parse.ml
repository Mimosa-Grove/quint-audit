(** Running quint as an argv vector, never through a shell.

    An argv vector, never a shell string; [quint parse] is bounded at 60 s,
    and a timeout is a did-not-run, never a pass.
    Licence: AGPLv3 - see LICENSE. See README.md (How it works). *)

type outcome = {
  rc : int option;
  timed_out : bool;
  stdout : string;
  stderr : string;
}

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let n = in_channel_length ic in
      really_input_string ic n)

let path_binary name =
  match Sys.getenv_opt "PATH" with
  | None -> None
  | Some path ->
      let dirs = String.split_on_char ':' path in
      List.find_map
        (fun dir ->
          let candidate = Filename.concat dir name in
          if Sys.file_exists candidate && not (Sys.is_directory candidate) then
            match Unix.access candidate [ Unix.X_OK ] with
            | () -> Some candidate
            | exception Unix.Unix_error _ -> None
          else None)
        dirs

let resolve ~quint =
  match quint with
  | Some p -> Ok p
  | None -> (
      match path_binary "quint" with
      | Some p -> Ok p
      | None -> Error "quint not found on PATH and --quint not given")

let run ~quint ~args ~timeout_s =
  let out_path = Filename.temp_file "quint-audit-out-" ".log" in
  let err_path = Filename.temp_file "quint-audit-err-" ".log" in
  let argv = Array.of_list (quint :: args) in
  let devnull = Unix.openfile "/dev/null" [ Unix.O_RDONLY ] 0 in
  let out_fd =
    Unix.openfile out_path [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o600
  in
  let err_fd =
    Unix.openfile err_path [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o600
  in
  let finish rc timed_out =
    Unix.close devnull;
    Unix.close out_fd;
    Unix.close err_fd;
    let stdout = try read_file out_path with Sys_error _ -> "" in
    let stderr = try read_file err_path with Sys_error _ -> "" in
    Sys.remove out_path;
    Sys.remove err_path;
    { rc; timed_out; stdout; stderr }
  in
  match Unix.create_process argv.(0) argv devnull out_fd err_fd with
  | exception Unix.Unix_error (err, fn, _) ->
      finish None false
      |> fun o ->
      { o with stderr = Printf.sprintf "%s: %s" fn (Unix.error_message err) }
  | pid ->
      let deadline = Unix.gettimeofday () +. timeout_s in
      let rec wait () =
        match Unix.waitpid [ Unix.WNOHANG ] pid with
        | 0, _ ->
            if Unix.gettimeofday () > deadline then begin
              (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ());
              ignore (Unix.waitpid [] pid);
              finish None true
            end
            else begin
              Unix.sleepf 0.02;
              wait ()
            end
        | _, Unix.WEXITED code -> finish (Some code) false
        | _, (Unix.WSIGNALED _ | Unix.WSTOPPED _) -> finish None false
      in
      wait ()

let parse_args ~spec_path ~ir_path ~map_path =
  [ "parse"; "--out"; ir_path; "--source-map"; map_path; spec_path ]

let version ~quint ~timeout_s =
  match run ~quint ~args:[ "--version" ] ~timeout_s with
  | { rc = Some 0; stdout; _ } ->
      let first = match String.split_on_char '\n' stdout with [] -> "" | x :: _ -> x in
      Some (String.trim first)
  | _ -> None
