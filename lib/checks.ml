(** The v1 IR-only checks: QL001, QL002, QL003, QL006, QL008, QL009 and
    QP001-QP002. Each reads typed IR only. See README.md (The check
    catalogue). Licence: AGPLv3 - see LICENSE. *)

type context = {
  program : Ir.program;
  module_ : Ir.module_;
  symbols : Symbols.t;
}

let module_name ctx = ctx.module_.Ir.module_name

let span_of ctx node =
  match Ir.IntMap.find_opt node ctx.program.Ir.spans with
  | Some span -> Some span
  | None -> None

(* Every finding carries a span. A node without a
   source-map entry falls back to the module span, the same attribution a
   module-level finding carries; the decoder refuses such a node in production. *)
let span_or_module ctx node =
  match span_of ctx node with
  | Some span -> span
  | None -> ctx.module_.Ir.module_span

(* A span can sit in an imported file, so the finding names the
   file the map attributes the span to, not only the module. *)
let source_of ctx node =
  match Ir.IntMap.find_opt node ctx.program.Ir.sources with
  | Some path -> path
  | None -> ctx.program.Ir.source_path

(* The entry module is the module whose defining file is the
   analysed spec. QL009 asks a runnable-unit question, so it classifies the
   entry module only; imported modules still receive every other check. The
   test lives in [Ir] so the report's scoped status uses the same predicate. *)
let is_entry_module ctx = Ir.is_entry_module ctx.program ctx.module_

let decl_finding ctx check severity (d : Ir.declaration) message suggestion =
  {
    Finding.check;
    severity;
    module_name = module_name ctx;
    source = source_of ctx d.Ir.decl_id;
    location = d.Ir.decl_span;
    message;
    suggestion;
  }

let expr_finding ctx check severity (e : Ir.expr) message suggestion =
  {
    Finding.check;
    severity;
    module_name = module_name ctx;
    source = source_of ctx (Ir.expr_id e);
    location = span_or_module ctx (Ir.expr_id e);
    message;
    suggestion;
  }

let node_finding ctx check severity node message suggestion =
  {
    Finding.check;
    severity;
    module_name = module_name ctx;
    source = source_of ctx node;
    location = span_or_module ctx node;
    message;
    suggestion;
  }

let module_finding ctx check severity message suggestion =
  {
    Finding.check;
    severity;
    module_name = module_name ctx;
    source = source_of ctx ctx.module_.Ir.module_id;
    location = ctx.module_.Ir.module_span;
    message;
    suggestion;
  }

let rec iter_expr f (e : Ir.expr) =
  f e;
  match e with
  | Ir.App { args; _ } -> List.iter (iter_expr f) args
  | Ir.Lambda { params; body; _ } ->
      List.iter
        (fun p -> Option.iter (iter_expr f) p.Ir.param_type)
        params;
      iter_expr f body
  | Ir.Let { binder_body; body; _ } ->
      iter_expr f binder_body;
      iter_expr f body
  | Ir.Name _ | Ir.Str _ | Ir.Int _ | Ir.Bool _ | Ir.Unknown _ -> ()

let declarations_where ctx pred =
  List.filter pred ctx.module_.Ir.declarations

let actions ctx =
  declarations_where ctx (fun d ->
      d.Ir.kind = Ir.Def && d.Ir.qualifier = Some Ir.Action)

(* A pure def is excluded from the reporting set only when
   one of its parameters is referenced in the body. A parameter reads
   as a free name, not a module-local declaration, so the tautology classifier
   would count it as no state reference and report a false tautology. The
   exclusion is scoped to that shape: a parameterised plain val, a
   parameterised Temporal, and a pure def whose parameters are unused are
   reported like their nullary forms. *)
let parameter_referenced (d : Ir.declaration) =
  d.Ir.params <> []
  && (match d.Ir.body with
      | None -> false
      | Some body ->
          let refs = Symbols.referenced body in
          List.exists
            (fun (p : Ir.param) ->
              List.exists
                (fun (name, _) -> String.equal name p.Ir.param_name)
                refs.Symbols.refs)
            d.Ir.params)

(* A declaration is a QL006
   subject only when it is a proposition. A tautology claim is meaningful about
   a proposition and false about a constant, so the subject set consults the
   decoded type and, when the type is absent, the body shape. `bool` decodes as
   an [Ir.Unknown] type node with kind "bool"; a parameterised declaration
   carries its function type, whose result is the proposition's type. *)
let type_is_bool (e : Ir.expr) =
  match e with
  | Ir.Unknown { kind = "bool"; _ } -> true
  | Ir.Unknown { kind = "oper"; raw; _ } -> (
      match raw with
      | `Assoc fs -> (
          match List.assoc_opt "res" fs with
          | Some (`Assoc res) -> List.assoc_opt "kind" res = Some (`String "bool")
          | _ -> false)
      | _ -> false)
  | _ -> false

(* The proposition opcodes are the existing IR constructors: the five
   connectives, equality, and the integer comparisons that produce a boolean.
   A boolean literal is a proposition too; a string, set or integer literal is
   not. *)
let is_proposition_opcode = function
  | Ir.And | Ir.Or | Ir.Not | Ir.Implies | Ir.Iff | Ir.Eq | Ir.Neq -> true
  | Ir.Other ("igt" | "igte" | "ilt" | "ilte") -> true
  | _ -> false

let is_proposition_body (e : Ir.expr) =
  match e with
  | Ir.App { opcode; _ } -> is_proposition_opcode opcode
  | Ir.Bool _ -> true
  | _ -> false

let is_proposition_subject (d : Ir.declaration) =
  match d.Ir.type_annotation with
  | Some t -> type_is_bool t
  | None -> (
      match d.Ir.body with
      | Some body -> is_proposition_body body
      | None -> false)

(* The QL006 reporting subjects. Pure declarations are subjects like a plain
   `val`; a parameterised pure def whose parameter is
   referenced is a function, not a property - its param is not a state reading
   and it never serves as an invariant subject. The subject set is narrowed to
   propositions: a declaration that is neither bool-typed
   nor proposition-shaped is a constant, not an invariant. *)
let vals ctx =
  declarations_where ctx (fun d ->
      d.Ir.kind = Ir.Def
      && is_proposition_subject d
      &&
      match d.Ir.qualifier with
      | Some (Ir.Val | Ir.PureVal) -> true
      | Some Ir.PureDef -> not (parameter_referenced d)
      | _ -> false)

let is_variant (e : Ir.expr) =
  match e with
  | Ir.App { opcode = Ir.Other "variant"; _ } -> true
  | _ -> false

(* Assignment coverage follows calls to module
   actions. Only a callee in [Symbols.actions] contributes - a pure def, a val
   or any other declaration is not an action and is never credited. A
   zero-argument call decodes as a [Name] node and a call with arguments as an
   [App]; both are calls when the name resolves to a module action. A visited
   path breaks recursion: an action that reaches a cycle has no census, and
   the cycle is reported once at Info. *)
let action_callees ctx (e : Ir.expr) =
  let names = Hashtbl.create 8 in
  let add name =
    if Symbols.mem ctx.symbols.Symbols.actions name then
      Hashtbl.replace names name ()
  in
  let rec walk bound node =
    match node with
    | Ir.Name { name; _ } -> if not (List.mem name bound) then add name
    | Ir.App { opcode = Ir.Other name; args; _ } ->
        if not (List.mem name bound) then add name;
        List.iter (walk bound) args
    | Ir.App { args; _ } -> List.iter (walk bound) args
    | Ir.Lambda { params; body; _ } ->
        let bound = List.map (fun p -> p.Ir.param_name) params @ bound in
        walk bound body
    | Ir.Let { binder; binder_body; body; _ } ->
        walk bound binder_body;
        walk (binder :: bound) body
    | Ir.Str _ | Ir.Int _ | Ir.Bool _ | Ir.Unknown _ -> ()
  in
  walk [] e;
  List.sort String.compare (Hashtbl.to_seq_keys names |> List.of_seq)

(* ---- QL001 thin actions -------------------------------------------------- *)

let logic_opcodes =
  [
    "iadd"; "isub"; "imul"; "idiv"; "imod"; "ipow"; "ineg";
    "eq"; "neq"; "igt"; "igte"; "ilt"; "ilte";
    "union"; "intersect"; "exclude"; "diff"; "powerset"; "flatten"; "Set";
    "with"; "Rec";
  ]

let is_logic_opcode = function
  | Ir.Other op -> List.mem op logic_opcodes
  | _ -> false

let non_pure_ref ctx (e : Ir.expr) =
  let resolves name =
    match Symbols.find_opt ctx.symbols.Symbols.by_name name with
    | Some symbol -> symbol.Symbols.sym_decl.Ir.qualifier = Some Ir.PlainDef
    | None -> false
  in
  match e with
  | Ir.Name { name; _ } when resolves name -> Some name
  | Ir.App { opcode = Ir.Other name; _ } when resolves name -> Some name
  | _ -> None

(* A thin body is one that is neither an all/any
   composition nor a call to a module action whose own body is one. A `nondet`
   prefix decodes as a [Let], so the composition is found through let binders.
   One level only: the callee's body is inspected, never its callees. Only
   module actions count - a `pure def` is never credited. *)
let rec composition_where p (e : Ir.expr) =
  match e with
  | Ir.App { opcode; _ } when p opcode -> true
  | Ir.Let { body; _ } -> composition_where p body
  | _ -> false

let action_composition =
  composition_where (function Ir.ActionAll | Ir.ActionAny -> true | _ -> false)

(* QL009 requires an `any` specifically. The Let-aware walk is
   shared with QL001's all/any test, so a `nondet` prefix is seen through
   while an `all` composition still fails the step shape test. *)
let any_composition =
  composition_where (function Ir.ActionAny -> true | _ -> false)

let calls_composing_action ctx (e : Ir.expr) =
  List.exists
    (fun name ->
      match Symbols.find_opt ctx.symbols.Symbols.actions name with
      | Some (d : Ir.declaration) -> (
          match d.Ir.body with
          | Some body -> action_composition body
          | None -> false)
      | None -> false)
    (action_callees ctx e)

let is_thin_action ctx (body : Ir.expr) =
  (not (action_composition body)) && not (calls_composing_action ctx body)

let check_thin_actions ctx =
  List.concat_map
    (fun (d : Ir.declaration) ->
      match d.Ir.body with
      | None -> []
      | Some body ->
          let findings = ref [] in
          let add f = findings := f :: !findings in
          (match body with
          | _ when is_thin_action ctx body ->
              let refs = Symbols.referenced body in
              if refs.Symbols.has_unknown then
                add
                  (decl_finding ctx Finding.QL001 Finding.Info d
                     (Printf.sprintf
                        "unmodelled expression spine; thinness coverage for `%s` skipped"
                        d.Ir.name)
                     None)
              else
                add
                  (decl_finding ctx Finding.QL001 Finding.Warn d
                     "action body is not an all/any composition"
                     (Some "wrap the guards and assignments in `all { ... }`"))
          | _ -> ());
          iter_expr
            (fun e ->
              match e with
              | Ir.App { opcode = Ir.ActionAny; args; _ } ->
                  List.iter
                    (fun arg ->
                      match arg with
                      | Ir.App
                          {
                            opcode = Ir.Assign;
                            args =
                              [ Ir.Name { name = lhs_name; _ };
                                Ir.Name { name = rhs_name; _ } ];
                            _;
                          }
                        when lhs_name = rhs_name ->
                          add
                            (expr_finding ctx Finding.QL001 Finding.Warn arg
                               (Printf.sprintf
                                  "no-op fallback branch assigns `%s` to itself"
                                  lhs_name)
                               (Some "disable the unused action instead"))
                      | _ -> ())
                    args
              | Ir.App { opcode = Ir.Assign; args = _ :: rhs :: _; _ } -> (
                  match rhs with
                  | Ir.App { opcode; _ } when is_logic_opcode opcode ->
                      add
                        (expr_finding ctx Finding.QL001 Finding.Warn rhs
                           "assignment embeds inline business logic"
                           (Some "lift the expression into a pure def"))
                  | Ir.Unknown _ ->
                      add
                        (expr_finding ctx Finding.QL001 Finding.Info rhs
                           "unmodelled expression spine in an assignment; inline-logic coverage is incomplete"
                           None)
                  | _ -> ())
              | _ -> ())
            body;
          iter_expr
            (fun e ->
              match non_pure_ref ctx e with
              | Some name ->
                  add
                    (expr_finding ctx Finding.QL001 Finding.Warn e
                       (Printf.sprintf
                          "action calls state-reading def `%s`" name)
                       (Some "lift the dependency into a pure def"))
              | None -> ())
            body;
          List.rev !findings)
    (actions ctx)

(* ---- QL002 enums over strings ------------------------------------------- *)

type str_context = Neutral | Compare | Assign_rhs

let check_enums_over_strings ctx =
  let findings = ref [] in
  let consider (s : Ir.expr) =
    match s with
    | Ir.Str n ->
        findings :=
          expr_finding ctx Finding.QL002 Finding.Warn s
            (Printf.sprintf "raw string literal %S" n.value)
            (Some "model the choice as a sum type")
          :: !findings
    | _ -> ()
  in
  let rec walk mode (e : Ir.expr) =
    match e with
    | Ir.App { opcode = (Ir.Eq | Ir.Neq); args; _ } ->
        List.iter (walk Compare) args
    | Ir.App { opcode = Ir.Assign; args; _ } -> (
        match args with
        | lhs :: rhs :: _ ->
            walk Neutral lhs;
            walk Assign_rhs rhs
        | _ -> ())
    | Ir.App { opcode = Ir.Other "Rec"; args; _ } ->
        List.iteri
          (fun i arg -> if i mod 2 = 0 then walk Neutral arg else walk mode arg)
          args
    | Ir.App { opcode = Ir.Other "with"; args; _ } -> (
        match args with
        | base :: field :: rest ->
            walk mode base;
            walk Neutral field;
            List.iter (walk mode) rest
        | _ -> List.iter (walk mode) args)
    | Ir.App { opcode = Ir.Other "field"; args = base :: _name :: _; _ } ->
        walk mode base
    | Ir.App { opcode = Ir.Other "field"; _ } -> ()
    | Ir.App { opcode = Ir.Other ("then" | "assert" | "expect"); _ } -> ()
    | Ir.Str _ -> if mode <> Neutral then consider e
    | Ir.App { args; _ } -> List.iter (walk mode) args
    | Ir.Lambda { body; _ } -> walk mode body
    | Ir.Let { binder_body; body; _ } ->
        walk mode binder_body;
        walk mode body
    | Ir.Name _ | Ir.Int _ | Ir.Bool _ | Ir.Unknown _ -> ()
  in
  List.iter
    (fun (d : Ir.declaration) ->
      match d.Ir.body with
      | Some body
        when d.Ir.kind = Ir.Def
             && (d.Ir.qualifier = Some Ir.Action
                || d.Ir.qualifier = Some Ir.Val) ->
          walk Neutral body
      | _ -> ())
    ctx.module_.Ir.declarations;
  List.rev !findings

(* ---- QL003 record grouping ---------------------------------------------- *)

let assigned_names ?(include_stutters = true) (e : Ir.expr) =
  let names = Hashtbl.create 8 in
  iter_expr
    (fun node ->
      match node with
      | Ir.App { opcode = Ir.Assign; args = Ir.Name { name; _ } :: rest; _ } ->
          let stutter =
            match rest with
            | Ir.Name { name = rhs; _ } :: _ -> rhs = name
            | _ -> false
          in
          if include_stutters || not stutter then Hashtbl.replace names name ()
      | _ -> ())
    e;
  List.sort String.compare (Hashtbl.to_seq_keys names |> List.of_seq)

let check_record_grouping ctx =
  let business_actions =
    List.filter
      (fun (d : Ir.declaration) ->
        d.Ir.name <> "init" && d.Ir.name <> "step")
      (actions ctx)
  in
  let var_names =
    Hashtbl.to_seq_keys ctx.symbols.Symbols.vars |> List.of_seq
    |> List.sort String.compare
  in
  let assignments =
    List.concat_map
      (fun (d : Ir.declaration) ->
        match d.Ir.body with
        | None -> []
        | Some body ->
            List.map
              (fun n -> (n, d.Ir.name))
              (assigned_names ~include_stutters:false body))
      business_actions
  in
  let action_set var =
    assignments
    |> List.filter_map (fun (name, action) ->
           if name = var then Some action else None)
    |> List.sort_uniq String.compare
  in
  let groups = Hashtbl.create 8 in
  List.iter
    (fun var ->
      let set = action_set var in
      if List.length set >= 2 then begin
        let key = String.concat "\000" set in
        let existing =
          match Hashtbl.find_opt groups key with Some xs -> xs | None -> []
        in
        Hashtbl.replace groups key (var :: existing)
      end)
    var_names;
  Hashtbl.fold
    (fun _ vars acc ->
      match vars with
      | [] | [ _ ] -> acc
      | first :: _ ->
          let first_decl =
            match Symbols.find_opt ctx.symbols.Symbols.vars first with
            | Some d -> d
            | None -> assert false
          in
          let set = action_set first in
          let message =
            Printf.sprintf
              "vars %s are always assigned together (in %s); consider one record"
              (String.concat ", " (List.rev vars))
              (String.concat ", " set)
          in
          decl_finding ctx Finding.QL003 Finding.Warn first_decl message
            (Some
               "Assignments made by a called helper action are not visible to this census.")
          :: acc)
    groups []
  |> List.rev

(* ---- QL006 non-trivial invariants --------------------------------------- *)

type dep_kind = Var_dep | Const_dep | Opaque_dep of string list | No_dep

(* Var outranks Opaque, which outranks Const. An Opaque dependency is never
   reported as const-only: the state path exists but is not analysable from
   the IR (a non-pure def, an absent body, a cycle). *)
let merge_dep a b =
  match (a, b) with
  | Var_dep, _ | _, Var_dep -> Var_dep
  | Opaque_dep xs, Opaque_dep ys -> Opaque_dep (xs @ ys)
  | Opaque_dep xs, _ | _, Opaque_dep xs -> Opaque_dep xs
  | Const_dep, _ | _, Const_dep -> Const_dep
  | No_dep, No_dep -> No_dep

let is_comparison_opcode = function
  | Ir.Eq | Ir.Neq -> true
  | Ir.Other ("igt" | "igte" | "ilt" | "ilte") -> true
  | _ -> false

let rec is_atom_like (e : Ir.expr) =
  match e with
  | Ir.Name _ | Ir.Int _ | Ir.Str _ | Ir.Bool _ -> true
  | Ir.App { opcode = Ir.Other "field"; args = [ base; Ir.Str _ ]; _ } ->
      is_atom_like base
  | _ -> false

let is_literal_comparison (e : Ir.expr) =
  match e with
  | Ir.App { opcode; args = [ a; b ]; _ } ->
      is_comparison_opcode opcode && is_atom_like a && is_atom_like b
  | _ -> false

let check_non_trivial_invariants ctx =
  let decls = Hashtbl.create 16 in
  List.iter
    (fun (d : Ir.declaration) -> Hashtbl.replace decls d.Ir.name d)
    ctx.module_.Ir.declarations;
  let analysable (d : Ir.declaration) =
    match (d.Ir.kind, d.Ir.qualifier, d.Ir.body) with
    | Ir.Def, Some (Ir.Val | Ir.PureVal | Ir.PureDef), Some _ -> true
    | _ -> false
  in
  let refs_of (d : Ir.declaration) body =
    let seed = List.map (fun (p : Ir.param) -> p.Ir.param_name) d.Ir.params in
    let refs = Symbols.referenced_names ~seed ctx.symbols body in
    (List.map fst refs.Symbols.refs, refs.Symbols.has_unknown)
  in
  let rec dependency_kind visited name =
    if List.mem name visited then Opaque_dep [ name ]
    else if Symbols.mem ctx.symbols.Symbols.vars name then Var_dep
    else if Symbols.mem ctx.symbols.Symbols.consts name then Const_dep
    else
      match Hashtbl.find_opt decls name with
      | None -> No_dep
      | Some d ->
          if not (analysable d) then Opaque_dep [ name ]
          else
            match d.Ir.body with
            | None -> Opaque_dep [ name ]
            | Some body ->
                let refs, has_unknown = refs_of d body in
                let dep =
                  List.fold_left
                    (fun acc ref ->
                      merge_dep acc (dependency_kind (name :: visited) ref))
                    No_dep refs
                in
                if has_unknown then merge_dep dep (Opaque_dep [ name ])
                else dep
  in
  List.concat_map
    (fun (d : Ir.declaration) ->
      match d.Ir.body with
      | None -> []
      | Some body when is_variant body -> []
      | Some body ->
          let names, has_unknown = refs_of d body in
          let dep =
            List.fold_left
              (fun acc ref -> merge_dep acc (dependency_kind [ d.Ir.name ] ref))
              No_dep names
          in
          let findings = ref [] in
          let add f = findings := f :: !findings in
          if has_unknown then
            add
              (expr_finding ctx Finding.QL006 Finding.Info body
                 "unmodelled expression spine; var references may be incomplete"
                 None);
          (match dep with
          | Var_dep ->
              if is_literal_comparison body then
                add
                  (decl_finding ctx Finding.QL006 Finding.Warn d
                     "invariant is a literal bound or type check only"
                     (Some "add a structural invariant over the model state"))
              else (
                (* The declaration is a subject by its type but
                   its body is a call, so QL006 would otherwise stay silent.
                   Name the refusal; never replace a tautology fail. *)
                match body with
                | Ir.App { opcode; _ } when not (is_proposition_opcode opcode) ->
                    add
                      (expr_finding ctx Finding.QL006 Finding.Info body
                         "invariant body is a call; QL006 did not evaluate it"
                         None)
                | _ -> ())
          | Opaque_dep names ->
              let names = List.sort_uniq String.compare names in
              add
                (decl_finding ctx Finding.QL006 Finding.Warn d
                   (Printf.sprintf
                      "invariant depends on unanalysed `%s`; a state dependency cannot be ruled out"
                      (String.concat "`, `" names))
                   (Some
                      "make the dependency pure or inline it so the state path is visible"))
          | Const_dep ->
              add
                (decl_finding ctx Finding.QL006 Finding.Warn d
                   "invariant references only constants, not state (premise-check candidate)"
                   None)
          | No_dep ->
              add
                (decl_finding ctx Finding.QL006 Finding.Fail d
                   "invariant references no state variable or constant (tautology over state)"
                   (Some "assert a property of the model state")));
          List.rev !findings)
    (vals ctx)

(* ---- QL007 IR half: init assigns every var exactly once ----------------- *)

let assignment_counts (e : Ir.expr) =
  let counts = Hashtbl.create 8 in
  iter_expr
    (fun node ->
      match node with
      | Ir.App { opcode = Ir.Assign; args = Ir.Name { name; _ } :: _; _ } ->
          let n = Option.value (Hashtbl.find_opt counts name) ~default:0 in
          Hashtbl.replace counts name (n + 1)
      | _ -> ())
    e;
  counts

let check_init_assignments ctx =
  let var_names =
    Hashtbl.to_seq_keys ctx.symbols.Symbols.vars |> List.of_seq
    |> List.sort String.compare
  in
  match
    List.find_opt (fun (d : Ir.declaration) -> d.Ir.name = "init") (actions ctx)
  with
  | None ->
      [
        module_finding ctx Finding.QL007 Finding.Fail
          "module has no `init` action; no variable is initialised"
          (Some "add `action init = all { ... }` assigning every var");
      ]
  | Some init -> (
      match init.Ir.body with
      | None -> []
      | Some body ->
          let refs = Symbols.referenced body in
          if refs.Symbols.has_unknown then
            [
              decl_finding ctx Finding.QL007 Finding.Info init
                "unmodelled expression spine; init assignment coverage is incomplete"
                None;
            ]
          else
            let counts = assignment_counts body in
            List.filter_map
              (fun var ->
                match Hashtbl.find_opt counts var with
                | None | Some 0 ->
                    Some
                      (decl_finding ctx Finding.QL007 Finding.Fail init
                         (Printf.sprintf "init does not assign `%s`" var)
                         (Some
                            (Printf.sprintf
                               "%s' = ... in init. Assignments made by a called helper action are not visible to this census."
                               var)))
                | Some 1 -> None
                | Some n ->
                    Some
                      (decl_finding ctx Finding.QL007 Finding.Fail init
                         (Printf.sprintf
                            "init assigns `%s` %d times (exactly one assignment required)"
                            var n)
                         (Some "remove the duplicate assignment")))
              var_names)

(* ---- QL008 per-action var assignment ------------------------------------ *)

let is_composer ctx (d : Ir.declaration) =
  match d.Ir.body with
  | Some (Ir.App { opcode = Ir.ActionAny; args; _ }) ->
      args <> []
      && List.for_all
           (fun arg ->
             match arg with
             | Ir.Name { name; _ } ->
                 Symbols.mem ctx.symbols.Symbols.actions name
             | Ir.App { opcode = Ir.Other name; _ } ->
                 Symbols.mem ctx.symbols.Symbols.actions name
             | _ -> false)
           args
  | _ -> false

type assignment_census = Assigned of string list | Cycle of string list

let cycle_declarations name path =
  let rec take = function
    | [] -> []
    | x :: xs -> if String.equal x name then [ x ] else x :: take xs
  in
  take path

let assignment_census ctx =
  let memo = Hashtbl.create 16 in
  let rec visit path name =
    if List.mem name path then Cycle (cycle_declarations name path)
    else
      match Hashtbl.find_opt memo name with
      | Some result -> result
      | None ->
          let result =
            match Symbols.find_opt ctx.symbols.Symbols.actions name with
            | None -> Assigned []
            | Some (d : Ir.declaration) -> (
                match d.Ir.body with
                | None -> Assigned []
                | Some body ->
                    let direct = assigned_names body in
                    List.fold_left
                      (fun acc callee ->
                        match acc with
                        | Cycle _ -> acc
                        | Assigned names -> (
                            match visit (name :: path) callee with
                            | Cycle cycle -> Cycle cycle
                            | Assigned more ->
                                Assigned
                                  (List.sort_uniq String.compare (more @ names))))
                      (Assigned direct) (action_callees ctx body))
          in
          Hashtbl.replace memo name result;
          result
  in
  fun name -> visit [] name

let check_var_per_action ctx =
  let var_names =
    Hashtbl.to_seq_keys ctx.symbols.Symbols.vars |> List.of_seq
    |> List.sort String.compare
  in
  let census = assignment_census ctx in
  let action_decls = actions ctx in
  let cycle_findings =
    let seen = Hashtbl.create 4 in
    List.filter_map
      (fun (d : Ir.declaration) ->
        match census d.Ir.name with
        | Assigned _ -> None
        | Cycle cycle ->
            let cycle = List.sort String.compare cycle in
            let key = String.concat "\000" cycle in
            if Hashtbl.mem seen key then None
            else begin
              Hashtbl.replace seen key ();
              Some
                (decl_finding ctx Finding.QL008 Finding.Info d
                   (Printf.sprintf
                      "call cycle among %s; no assignment census is claimed through it"
                      (String.concat ", "
                         (List.map (fun n -> "`" ^ n ^ "`") cycle)))
                   (Some "break the call cycle; a cycle cannot be censused"))
            end)
      action_decls
  in
  cycle_findings
  @ List.concat_map
      (fun (d : Ir.declaration) ->
        if d.Ir.name = "init" || d.Ir.name = "step" || is_composer ctx d then []
        else
          match d.Ir.body with
          | None -> []
          | Some body ->
              let refs = Symbols.referenced body in
              if refs.Symbols.has_unknown then
                [
                  decl_finding ctx Finding.QL008 Finding.Info d
                    (Printf.sprintf
                       "unmodelled expression spine; assignment coverage for `%s` skipped"
                       d.Ir.name)
                    None;
                ]
              else
                match census d.Ir.name with
                | Cycle _ -> []
                | Assigned assigned ->
                    List.filter_map
                      (fun var ->
                        if List.mem var assigned then None
                        else
                          Some
                            (decl_finding ctx Finding.QL008 Finding.Warn d
                               (Printf.sprintf
                                  "action %s does not visibly assign `%s`"
                                  d.Ir.name var)
                               (Some
                                  (Printf.sprintf
                                     "%s' = %s."
                                     var var))))
                      var_names)
      action_decls

(* ---- QL009 step exists and is complete ----------------------------------- *)

(* Reachability follows calls to module actions.
   The accumulator is a set of names, visited once: a cycle among actions is
   traversed and every member is reachable (unlike QL008's census, where a
   cycle refuses the claim). One visited set serves the whole traversal from
   `step` - the root is always `step`, so no per-action memo is needed. *)
let reachable_action_names ctx (root : Ir.expr) =
  let seen = Hashtbl.create 16 in
  let rec visit name =
    if not (Hashtbl.mem seen name) then begin
      Hashtbl.replace seen name ();
      match Symbols.find_opt ctx.symbols.Symbols.actions name with
      | None -> ()
      | Some (d : Ir.declaration) -> (
          match d.Ir.body with
          | None -> ()
          | Some body -> List.iter visit (action_callees ctx body))
    end
  in
  List.iter visit (action_callees ctx root);
  List.sort String.compare (Hashtbl.to_seq_keys seen |> List.of_seq)

let check_step_complete ctx =
  if not (is_entry_module ctx) then []
  else
  let actions = actions ctx in
  let names = List.map (fun (d : Ir.declaration) -> d.Ir.name) actions in
  match List.filter (fun n -> n = "step") names with
  | [] ->
      [
        module_finding ctx Finding.QL009 Finding.Warn
          "module has no `step` action"
          (Some "add `action step = any { ... }` over every action");
      ]
  | _ :: _ ->
      let step = List.find (fun (d : Ir.declaration) -> d.Ir.name = "step") actions in
      let findings = ref [] in
      let add f = findings := f :: !findings in
      let step_body = step.Ir.body in
      let step_unknown =
        match step_body with
        | Some body -> (Symbols.referenced body).Symbols.has_unknown
        | None -> false
      in
      if step_unknown then
        (* A body the check cannot read is an info coverage gap,
           never a shape or reachability classification. *)
        add
          (decl_finding ctx Finding.QL009 Finding.Info step
             "unmodelled expression spine; step composition and reachability coverage is incomplete"
             None)
      else begin
        (match step_body with
        | Some body when any_composition body -> ()
        | _ ->
            add
              (decl_finding ctx Finding.QL009 Finding.Warn step
                 "step body is not an any composition of actions"
                 (Some "use `action step = any { ... }`.")));
        let covered =
          match step_body with
          | None -> []
          | Some body -> reachable_action_names ctx body
        in
        List.iter
          (fun (d : Ir.declaration) ->
            if d.Ir.name <> "init" && d.Ir.name <> "step"
               && not (List.mem d.Ir.name covered)
            then
              add
                (decl_finding ctx Finding.QL009 Finding.Warn d
                   (Printf.sprintf
                      "action %s is not visibly reachable from step"
                      d.Ir.name)
                   (Some
                      (Printf.sprintf
                         "add %s to the step branches."
                         d.Ir.name))))
          actions
      end;
      List.rev !findings

(* ---- QP001 literal-false folding ---------------------------------------- *)

let check_literal_false_property ctx =
  List.concat_map
    (fun (d : Ir.declaration) ->
      let is_property =
        d.Ir.kind = Ir.Def
        &&
        match d.Ir.qualifier with
        | Some (Ir.Val | Ir.Temporal | Ir.PureVal) -> true
        | Some Ir.PureDef -> not (parameter_referenced d)
        | _ -> false
      in
      if not is_property then []
      else
        match d.Ir.body with
        | None -> []
        | Some body when is_variant body -> []
        | Some body -> (
            match Qcalc.classify body with
            | Qcalc.Const_false ->
                [
                  expr_finding ctx Finding.QP001 Finding.Fail body
                    "property body is constant false"
                    (Some "remove the contradiction or fix the premise");
                ]
            | Qcalc.Const_true ->
                [
                  expr_finding ctx Finding.QP001 Finding.Fail body
                    "property body is constant true (void property)"
                    (Some "assert something that can fail");
                ]
            | Qcalc.Varies -> []
            | Qcalc.Refused reason ->
                [
                  expr_finding ctx Finding.QP001 Finding.Info body
                    (Printf.sprintf
                       "property body could not be classified: %s" reason)
                    (Some "model the missing connective or restate the property");
                ]))
    ctx.module_.Ir.declarations

(* ---- QP002 state-reading pure def ---------------------------------------- *)

let check_state_reading_pure_def ctx =
  let pure_declarations =
    declarations_where ctx (fun d ->
        d.Ir.kind = Ir.Def
        && (d.Ir.qualifier = Some Ir.PureDef
           || d.Ir.qualifier = Some Ir.PureVal))
  in
  List.concat_map
    (fun (d : Ir.declaration) ->
      match d.Ir.body with
      | None -> []
      | Some body ->
          let what =
            match d.Ir.qualifier with
            | Some Ir.PureVal -> "pure val"
            | _ -> "pure def"
          in
          let suggestion =
            match d.Ir.qualifier with
            | Some Ir.PureVal -> Some "drop `pure` or remove the state read"
            | _ -> Some "make it a non-pure def or pass the value as a parameter"
          in
          let seed =
            List.map (fun (p : Ir.param) -> p.Ir.param_name) d.Ir.params
          in
          let refs = Symbols.referenced_names ~seed ctx.symbols body in
          let hits =
            List.filter_map
              (fun (name, node) ->
                if Symbols.mem ctx.symbols.Symbols.vars name then
                  Some
                    (node_finding ctx Finding.QP002 Finding.Fail node
                       (Printf.sprintf "%s `%s` reads state variable `%s`" what
                          d.Ir.name name)
                       suggestion)
                else None)
              refs.Symbols.refs
          in
          if hits = [] && refs.Symbols.has_unknown then
            [
              decl_finding ctx Finding.QP002 Finding.Info d
                "unmodelled expression spine; state reads may be incomplete"
                None;
            ]
          else hits)
    pure_declarations

(* The declaration-level counterpart: a declaration kind outside the
   measured set is carried as a non-subject and its coverage gap is stated as
   an info note. It is never counted as a reporting subject. *)
let check_unmodelled_declarations ctx =
  List.filter_map
    (fun (d : Ir.declaration) ->
      match d.Ir.kind with
      | Ir.NonSubject (Ir.Unmodelled { kind }) ->
          Some
            (decl_finding ctx Finding.QP002 Finding.Info d
               (Printf.sprintf
                  "unmodelled declaration kind %S; state reads may be \
                   incomplete" kind)
               None)
      | _ -> None)
    ctx.module_.Ir.declarations

let run_ir_checks ctx =
  Finding.sort
    (List.concat
       [
         check_thin_actions ctx;
         check_enums_over_strings ctx;
         check_record_grouping ctx;
         check_non_trivial_invariants ctx;
         check_var_per_action ctx;
         check_step_complete ctx;
         check_literal_false_property ctx;
         check_unmodelled_declarations ctx;
         check_state_reading_pure_def ctx;
       ])
