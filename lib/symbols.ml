(** Module-local symbol table and reference collection.

    Declaration order is derived from the source map: quint 0.33.1 emits
    declarations in phase 4 toposort order, not source order (verified from
    source: quintParserFrontend.ts:342), so [sym_order] sorts
    by declaration span start. Reference resolution is module-local
    (README, Scope limits). Licence: AGPLv3 - see LICENSE. *)

type symbol = {
  sym_name : string;
  sym_decl : Ir.declaration;
  sym_order : int;
}

type t = {
  by_name : (string, symbol) Hashtbl.t;
  ordered : symbol list;
  vars : (string, Ir.declaration) Hashtbl.t;
  actions : (string, Ir.declaration) Hashtbl.t;
  pure_defs : (string, Ir.declaration) Hashtbl.t;
  vals : (string, Ir.declaration) Hashtbl.t;
  consts : (string, Ir.declaration) Hashtbl.t;
  defs : (string, Ir.declaration) Hashtbl.t;
  resolution : string Ir.IntMap.t;  (* node id -> resolved declaration name *)
}

let build ?(resolution = Ir.IntMap.empty) (m : Ir.module_) =
  let sorted =
    List.sort
      (fun a b ->
        let ai = a.Ir.decl_span.Ir.start_pos.Ir.index in
        let bi = b.Ir.decl_span.Ir.start_pos.Ir.index in
        match compare ai bi with 0 -> String.compare a.Ir.name b.Ir.name | c -> c)
      m.Ir.declarations
  in
  let by_name = Hashtbl.create (List.length sorted) in
  let vars = Hashtbl.create 8 and actions = Hashtbl.create 8 in
  let pure_defs = Hashtbl.create 8 and vals = Hashtbl.create 8 in
  let consts = Hashtbl.create 8 and defs = Hashtbl.create 8 in
  let ordered =
    List.filter_map
      (fun (i, d) ->
        let symbol = { sym_name = d.Ir.name; sym_decl = d; sym_order = i } in
        match d.Ir.kind with
        | Ir.NonSubject _ -> None
        | Ir.Var ->
            Hashtbl.replace by_name d.Ir.name symbol;
            Hashtbl.replace vars d.Ir.name d;
            Some symbol
        | Ir.Const ->
            Hashtbl.replace by_name d.Ir.name symbol;
            Hashtbl.replace consts d.Ir.name d;
            Some symbol
        | Ir.TypeDef ->
            Hashtbl.replace by_name d.Ir.name symbol;
            Some symbol
        | Ir.Def ->
            Hashtbl.replace by_name d.Ir.name symbol;
            Hashtbl.replace defs d.Ir.name d;
            (match d.Ir.qualifier with
            | Some Ir.Action -> Hashtbl.replace actions d.Ir.name d
            | Some Ir.PureDef -> Hashtbl.replace pure_defs d.Ir.name d
            | Some Ir.Val -> Hashtbl.replace vals d.Ir.name d
            | _ -> ());
            Some symbol)
      (List.mapi (fun i d -> (i, d)) sorted)
  in
  { by_name; ordered; vars; actions; pure_defs; vals; consts; defs; resolution }

let mem table name = Hashtbl.mem table name
let find_opt table name = Hashtbl.find_opt table name

type references = { refs : (string * Ir.node_id) list; has_unknown : bool }

let referenced ?(seed : string list = []) (e : Ir.expr) =
  let refs = ref [] in
  let has_unknown = ref false in
  let add name id = refs := (name, id) :: !refs in
  let rec walk bound e =
    match e with
    | Ir.Name { id; name } -> if not (List.mem name bound) then add name id
    | Ir.App { id; opcode; args; _ } -> (
        (match opcode with
        | Ir.Other name -> add name id
        | _ -> ());
        List.iter (walk bound) args)
    | Ir.Lambda { params; body; _ } ->
        let bound = List.map (fun p -> p.Ir.param_name) params @ bound in
        walk bound body
    | Ir.Let { binder; binder_body; body; _ } ->
        walk bound binder_body;
        walk (binder :: bound) body
    | Ir.Unknown _ -> has_unknown := true
    | Ir.Str _ | Ir.Int _ | Ir.Bool _ -> ()
  in
  walk seed e;
  { refs = List.rev !refs; has_unknown = !has_unknown }

let referenced_names ?seed tbl e =
  let r = referenced ?seed e in
  let resolve (name, id) =
    match Ir.IntMap.find_opt id tbl.resolution with
    | Some resolved -> resolved
    | None -> name
  in
  let refs =
    List.filter_map
      (fun (name, id) ->
        let name = resolve (name, id) in
        if Hashtbl.mem tbl.by_name name then Some (name, id) else None)
      r.refs
  in
  { r with refs }
