(** The three-state run discipline, mirroring spec/rundisc.qnt.

    [classify] is the OCaml mirror of the spec's [classifyRun]: passed needs
    rc 0 and the run's own success summary on non-empty output; failed needs
    rc nonzero and the run's own failure summary; everything else, including
    the masked-crash shape (rc 0 with empty output) and a timeout, is
    did-not-run. See spec/rundisc.qnt and README.md (How it works).
    Licence: AGPLv3 - see LICENSE. *)

type rc_class = Zero | Nonzero | No_rc

type facts = {
  rc : rc_class;
  timed_out : bool;
  success_summary : bool;
  failure_summary : bool;
  empty_output : bool;
}

type outcome = Passed | Failed | Did_not_run

let classify f =
  if f.timed_out then Did_not_run
  else if f.rc = Zero && f.success_summary && not f.empty_output then Passed
  else if f.rc = Nonzero && f.failure_summary && not f.empty_output then Failed
  else Did_not_run

let verdict f = match classify f with Failed -> true | Passed | Did_not_run -> false

let string_of_outcome = function
  | Passed -> "passed"
  | Failed -> "failed"
  | Did_not_run -> "did-not-run"

(* The backend-provenance layer (spec/rundisc.qnt).
   A TypeScript `passed` is not evidence: a false init reports the same shape
   there. An unpinned backend is never evidence. A TypeScript failure (an
   init error) stays evidence. *)
type evidence = Evidence of outcome | Not_evidence

let init_verdict backend f =
  match backend with
  | "rust" -> Evidence (classify f)
  | "typescript" -> (
      match classify f with Passed -> Not_evidence | outcome -> Evidence outcome)
  | _ -> Not_evidence

let string_of_evidence = function
  | Evidence outcome -> string_of_outcome outcome
  | Not_evidence -> "not-evidence"

let all_facts () =
  let rcs = [ Zero; Nonzero; No_rc ] in
  let bools = [ true; false ] in
  List.concat_map
    (fun rc ->
      List.concat_map
        (fun timed_out ->
          List.concat_map
            (fun success_summary ->
              List.concat_map
                (fun failure_summary ->
                  List.map
                    (fun empty_output ->
                      { rc; timed_out; success_summary; failure_summary; empty_output })
                    bools)
                bools)
            bools)
        bools)
    rcs
