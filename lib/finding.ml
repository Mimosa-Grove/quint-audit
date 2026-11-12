(** The finding model and catalogue rows.

    A finding is
    {check, severity, module, source, span, message, suggestion}. Info findings
    are coverage notes and never affect the exit code.
    Licence: AGPLv3 - see LICENSE. *)

type severity = Fail | Warn | Info

type check_id =
  | QL001
  | QL002
  | QL003
  | QL004
  | QL005
  | QL006
  | QL007
  | QL008
  | QL009
  | QL010
  | QL011
  | QP001
  | QP002
  | QP003
  | QP004

type mode = Ir | Ir_run | Run | Heur | Not

type finding = {
  check : check_id;
  severity : severity;
  module_name : string;
  source : string;  (* the file the span belongs to; an imported file is named *)
  location : Ir.span;
  message : string;
  suggestion : string option;
}

let all_checks =
  [
    QL001; QL002; QL003; QL004; QL005; QL006; QL007; QL008; QL009; QL010;
    QL011; QP001; QP002;
  ]

let string_of_check = function
  | QL001 -> "QL001"
  | QL002 -> "QL002"
  | QL003 -> "QL003"
  | QL004 -> "QL004"
  | QL005 -> "QL005"
  | QL006 -> "QL006"
  | QL007 -> "QL007"
  | QL008 -> "QL008"
  | QL009 -> "QL009"
  | QL010 -> "QL010"
  | QL011 -> "QL011"
  | QP001 -> "QP001"
  | QP002 -> "QP002"
  | QP003 -> "QP003"
  | QP004 -> "QP004"

let check_name = function
  | QL001 -> "thin actions"
  | QL002 -> "enums over strings"
  | QL003 -> "record grouping"
  | QL004 -> "witnesses present & per-action"
  | QL005 -> "right abstraction"
  | QL006 -> "non-trivial invariants"
  | QL007 -> "init assigns all vars"
  | QL008 -> "var assignment per action"
  | QL009 -> "step exists & complete"
  | QL010 -> "invariants hold at init"
  | QL011 -> "no counterexample after acts"
  | QP001 -> "literal-false property"
  | QP002 -> "state-reading pure def"
  | QP003 -> "forward reference"
  | QP004 -> "out-of-module declaration"

let check_mode = function
  | QL001 | QL002 | QL003 | QL006 | QL008 | QL009 | QP001 | QP002 | QP003 -> Ir
  | QL004 | QL007 -> Ir_run
  | QL010 | QL011 -> Run
  | QL005 -> Heur
  | QP004 -> Not

let string_of_mode = function
  | Ir -> "ir"
  | Ir_run -> "ir+run"
  | Run -> "run"
  | Heur -> "heur"
  | Not -> "not"

let string_of_severity = function
  | Fail -> "fail"
  | Warn -> "warn"
  | Info -> "info"

let severity_rank = function Fail -> 0 | Warn -> 1 | Info -> 2

let compare_findings a b =
  match compare a.location.Ir.start_pos.Ir.index b.location.Ir.start_pos.Ir.index with
  | 0 -> (
      match String.compare (string_of_check a.check) (string_of_check b.check) with
      | 0 -> String.compare a.message b.message
      | c -> c)
  | c -> c

let sort findings = List.sort compare_findings findings

(* The report dedup key. A finding is the same finding when
   the check, severity, owning file, span start and message all agree; the
   module is not part of the key because one definition can be reached
   through more than one import path. *)
(* Every serialised finding carries a start and an end.
   The location is total, so the report has no branch that can emit null. *)
let span_start (f : finding) = f.location.Ir.start_pos.Ir.index

let compare_report_order a b =
  let c = String.compare a.source b.source in
  if c <> 0 then c
  else
    let c = compare (span_start a) (span_start b) in
    if c <> 0 then c
    else
      let c = String.compare (string_of_check a.check) (string_of_check b.check) in
      if c <> 0 then c
      else
        let c = String.compare a.message b.message in
        if c <> 0 then c
        else
          let c = String.compare a.module_name b.module_name in
          if c <> 0 then c
          else String.compare (string_of_severity a.severity) (string_of_severity b.severity)

let same_finding a b =
  a.check = b.check && a.severity = b.severity && a.source = b.source
  && span_start a = span_start b && a.message = b.message

(* Sorted by source, span and check, so the report does not depend on module
   iteration order; adjacent equal keys collapse. *)
let normalise findings =
  let sorted = List.sort compare_report_order findings in
  let rec go acc = function
    | [] -> List.rev acc
    | [ x ] -> List.rev (x :: acc)
    | x :: (y :: _ as rest) ->
        if same_finding x y then go acc rest else go (x :: acc) rest
  in
  go [] sorted

let check_status ?(skipped = false) findings check =
  if skipped then `Skipped
  else
    let own = List.filter (fun f -> f.check = check) findings in
    if List.exists (fun f -> f.severity = Fail) own then `Fail
    else if List.exists (fun f -> f.severity = Warn) own then `Warn
    else `Pass
