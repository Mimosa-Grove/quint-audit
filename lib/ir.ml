(** Typed IR for quint's parse output.

    The types mirror quint's parse output, plus a [Let] node measured
    on quint 0.33.1 (nondet and let bindings). Ids are quint node ids; spans
    come from the source map. See README.md (How it works).
    Licence: AGPLv3 - see LICENSE. *)

type node_id = int

type position = {
  line : int;   (* 0-based, as emitted by quint *)
  column : int; (* 0-based, as emitted by quint *)
  index : int;  (* byte offset; valid because the input is ASCII *)
}

type span = { start_pos : position; end_pos : position }

module IntMap = Map.Make (Int)

type opcode =
  | And
  | Or
  | Not
  | Implies
  | Iff
  | Eq
  | Neq
  | ActionAll
  | ActionAny
  | Assign
  | Other of string

type expr =
  | Name of { id : node_id; name : string }
  | Str of { id : node_id; value : string }
  | Int of { id : node_id; value : int }
  | Bool of { id : node_id; value : bool }
  | App of { id : node_id; opcode : opcode; args : expr list }
  | Lambda of { id : node_id; params : param list; body : expr }
  | Let of { id : node_id; binder : string; binder_body : expr; body : expr }
  | Unknown of { id : node_id; kind : string; raw : Yojson.Safe.t }

and param = {
  param_id : node_id;
  param_name : string;
  param_type : expr option;
}

let expr_id = function
  | Name n -> n.id
  | Str n -> n.id
  | Int n -> n.id
  | Bool n -> n.id
  | App n -> n.id
  | Lambda n -> n.id
  | Let n -> n.id
  | Unknown n -> n.id

type non_subject =
  | Import of { proto_name : string option; qualified_name : string option }
  | Instance of { proto_name : string option; qualified_name : string option }
  | Assume of { assumption : expr }
  | Unmodelled of { kind : string }

type decl_kind =
  | Const
  | Var
  | TypeDef
  | Def
  | NonSubject of non_subject

type qualifier =
  | PureDef
  | PureVal
  | Action
  | Val
  | Temporal
  | Run
  | PlainDef
  | OtherQualifier of string

type declaration = {
  decl_id : node_id;
  name : string;
  kind : decl_kind;
  qualifier : qualifier option;
  type_annotation : expr option;
  params : param list;
  body : expr option;
  decl_span : span;
}

type module_ = {
  module_id : node_id;
  module_name : string;
  declarations : declaration list;
  module_span : span;
}

type program = {
  modules : module_ list;
  source_path : string;
  source_text : string;
  spans : span IntMap.t;
  sources : string IntMap.t;  (* node id -> the source file its span names *)
  resolution : string IntMap.t;  (* node id -> resolved declaration name *)
}

(* The entry module is the module whose defining file is
   the analysed spec. The check and the report share this test, so a scoped
   status cannot diverge from the check that produced it. *)
let is_entry_module (program : program) (m : module_) =
  let defining_file =
    match IntMap.find_opt m.module_id program.sources with
    | Some path -> path
    | None -> program.source_path
  in
  String.equal defining_file program.source_path

let string_of_decl_kind = function
  | Const -> "const"
  | Var -> "var"
  | TypeDef -> "typedef"
  | Def -> "def"
  | NonSubject (Import _) -> "import"
  | NonSubject (Instance _) -> "instance"
  | NonSubject (Assume _) -> "assume"
  | NonSubject (Unmodelled { kind }) -> kind

let string_of_qualifier = function
  | PureDef -> "puredef"
  | PureVal -> "pureval"
  | Action -> "action"
  | Val -> "val"
  | Temporal -> "temporal"
  | Run -> "run"
  | PlainDef -> "def"
  | OtherQualifier s -> s

let opcode_of_string = function
  | "and" -> And
  | "or" -> Or
  | "not" -> Not
  | "implies" -> Implies
  | "iff" -> Iff
  | "eq" -> Eq
  | "neq" -> Neq
  | "actionAll" -> ActionAll
  | "actionAny" -> ActionAny
  | "assign" -> Assign
  | s -> Other s

let string_of_opcode = function
  | And -> "and"
  | Or -> "or"
  | Not -> "not"
  | Implies -> "implies"
  | Iff -> "iff"
  | Eq -> "eq"
  | Neq -> "neq"
  | ActionAll -> "actionAll"
  | ActionAny -> "actionAny"
  | Assign -> "assign"
  | Other s -> s

let is_connective = function
  | And | Or | Not | Implies | Iff -> true
  | _ -> false
