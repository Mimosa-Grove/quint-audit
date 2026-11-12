(** QP001's truth-table calculus, mirroring spec/qcalc.qnt.

    The classifier decides a boolean property body over the connectives
    [and or not implies iff] (with [actionAll]/[actionAny] as and/or),
    [eq]/[neq] by canonical subtree identity, and Boolean literals. Every
    other subtree is an opaque free leaf. An unmodelled node kind, a
    malformed connective or more than [max_leaves] free leaves is a refusal,
    never a pass. See spec/qcalc.qnt and README.md (QP001).
    Licence: AGPLv3 - see LICENSE. *)

type result = Const_true | Const_false | Varies | Refused of string

let string_of_result = function
  | Const_true -> "const-true"
  | Const_false -> "const-false"
  | Varies -> "varies"
  | Refused reason -> "unknown (" ^ reason ^ ")"

let max_leaves = 16

(* Canonical form: ids stripped, structure kept. Length-prefixed so distinct
   trees cannot collide by concatenation. *)
let rec canonical_string e =
  let len s = Printf.sprintf "%d:%s" (String.length s) s in
  match e with
  | Ir.Name n -> "n" ^ len n.name
  | Ir.Str n -> "s" ^ len n.value
  | Ir.Int n -> "i" ^ len (string_of_int n.value)
  | Ir.Bool n -> "b" ^ len (string_of_bool n.value)
  | Ir.App n ->
      "a" ^ len (Ir.string_of_opcode n.opcode)
      ^ "(" ^ String.concat "" (List.map canonical_string n.args) ^ ")"
  | Ir.Lambda n ->
      "l("
      ^ String.concat ","
          (List.map
             (fun p ->
               len p.Ir.param_name
               ^
               match p.Ir.param_type with
               | None -> "?"
               | Some t -> canonical_string t)
             n.params)
      ^ ")" ^ canonical_string n.body
  | Ir.Let n ->
      "t" ^ len n.binder ^ "(" ^ canonical_string n.binder_body ^ ")"
      ^ canonical_string n.body
  | Ir.Unknown n -> "u" ^ len n.kind

let canonical_equal a b = String.equal (canonical_string a) (canonical_string b)

let rec refusal e =
  match e with
  | Ir.Unknown n -> Some (Printf.sprintf "unmodelled node kind %S" n.kind)
  | Ir.App { opcode = Ir.And | Ir.Or | Ir.ActionAll | Ir.ActionAny; args; _ } ->
      List.find_map refusal args
  | Ir.App { opcode = Ir.Not; args; _ } -> (
      match args with
      | [ a ] -> refusal a
      | _ -> Some "not is not unary")
  | Ir.App { opcode = Ir.Implies | Ir.Iff; args; _ } -> (
      match args with
      | [ a; b ] -> ( match refusal a with Some r -> Some r | None -> refusal b)
      | _ -> Some "implies/iff is not binary")
  | Ir.App { opcode = Ir.Eq | Ir.Neq; args; _ } -> List.find_map refusal args
  | Ir.App { args; _ } -> List.find_map refusal args
  | Ir.Lambda { params; body; _ } -> (
      match
        List.find_map
          (fun p -> Option.bind p.Ir.param_type refusal)
          params
      with
      | Some r -> Some r
      | None -> refusal body)
  | Ir.Let { binder_body; body; _ } -> (
      match refusal binder_body with Some r -> Some r | None -> refusal body)
  | Ir.Name _ | Ir.Str _ | Ir.Int _ | Ir.Bool _ -> None

(* Free-leaf keys, in first-seen order, plus the number of leaves. *)
let collect_leaves e =
  let order = ref [] in
  let seen = Hashtbl.create 8 in
  let add key =
    if not (Hashtbl.mem seen key) then begin
      Hashtbl.add seen key (List.length !order);
      order := key :: !order
    end
  in
  let rec go e =
    match e with
    | Ir.App { opcode = Ir.And | Ir.Or | Ir.ActionAll | Ir.ActionAny; args; _ } ->
        List.iter go args
    | Ir.App { opcode = Ir.Not; args; _ } -> List.iter go args
    | Ir.App { opcode = Ir.Implies | Ir.Iff; args; _ } -> List.iter go args
    | Ir.App { opcode = (Ir.Eq | Ir.Neq) as op; args; _ } -> (
        match args with
        | [ a; b ] when canonical_equal a b -> ignore op
        | _ -> add (canonical_string e))
    | Ir.Bool _ -> ()
    | other -> add (canonical_string other)
  in
  go e;
  (List.rev !order, List.length !order)

let eval_leaf key index assignment =
  let bit = (assignment lsr index) land 1 = 1 in
  ignore key;
  bit

let rec eval e keys assignment =
  match e with
  | Ir.Bool { value; _ } -> value
  | Ir.App { opcode = Ir.And | Ir.ActionAll; args; _ } ->
      List.for_all (eval_arg keys assignment) args
  | Ir.App { opcode = Ir.Or | Ir.ActionAny; args; _ } ->
      List.exists (eval_arg keys assignment) args
  | Ir.App { opcode = Ir.Not; args; _ } -> (
      match args with
      | [ a ] -> not (eval a keys assignment)
      | _ -> false)
  | Ir.App { opcode = Ir.Implies; args; _ } -> (
      match args with
      | [ a; b ] -> (not (eval a keys assignment)) || eval b keys assignment
      | _ -> false)
  | Ir.App { opcode = Ir.Iff; args; _ } -> (
      match args with
      | [ a; b ] -> eval a keys assignment = eval b keys assignment
      | _ -> false)
  | Ir.App { opcode = (Ir.Eq | Ir.Neq) as op; args; _ } -> (
      match args with
      | [ a; b ] when canonical_equal a b -> op = Ir.Eq
      | _ -> (
          match Hashtbl.find_opt keys (canonical_string e) with
          | Some index -> eval_leaf (canonical_string e) index assignment
          | None -> false))
  | other -> (
      match Hashtbl.find_opt keys (canonical_string other) with
      | Some index -> eval_leaf (canonical_string other) index assignment
      | None -> false)

and eval_arg keys assignment e = eval e keys assignment

let classify e =
  match refusal e with
  | Some reason -> Refused reason
  | None ->
      let keys, n = collect_leaves e in
      if n > max_leaves then
        Refused
          (Printf.sprintf "%d free leaves exceeds the bound of %d" n max_leaves)
      else
        let index = Hashtbl.create (max 1 n) in
        List.iteri (fun i key -> Hashtbl.add index key i) keys;
        let total = 1 lsl n in
        let all_true = ref true and all_false = ref true in
        for assignment = 0 to total - 1 do
          let v = eval e index assignment in
          if v then all_false := false else all_true := false
        done;
        if !all_true then Const_true
        else if !all_false then Const_false
        else Varies

(* The downstream decision: only [Varies] passes. Refusals and constants are
   findings, never a pass (qcalc [decision]). *)
let passes e = match classify e with Varies -> true | _ -> false
