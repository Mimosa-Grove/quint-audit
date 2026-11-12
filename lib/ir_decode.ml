(** Hand-written typed decoder for quint's parse IR.

    The decode is the schema check: every consumed field
    is validated, and a malformed IR is a failure naming the JSON field path.
    Unknown node kinds survive as [Ir.Unknown] with their raw JSON.
    See README.md (How it works). Licence: AGPLv3 - see LICENSE. *)

type decode_error =
  | Missing_field of { path : string; expected : string; source : string }
  | Wrong_type of { path : string; expected : string; actual : string; json : Yojson.Safe.t }
  | Invalid_value of { path : string; reason : string }
  | Empty_collection of { path : string; expected : string }
  | Span_missing of { node : int; source : string }
  | Span_invalid of { node : int; reason : string }
  | Parse_failed of { source : string; rc : int; errors : Yojson.Safe.t }
  | Non_ascii of { offset : int }
  | Source_unreadable of { path : string; reason : string }
  | Source_non_ascii of { path : string; offset : int }

let type_name = function
  | `Null -> "null"
  | `Bool _ -> "bool"
  | `Int _ | `Intlit _ | `Float _ -> "number"
  | `String _ -> "string"
  | `Assoc _ -> "object"
  | `List _ -> "array"
  | `Tuple _ -> "tuple"
  | `Variant _ -> "variant"

let preview json =
  let s = Yojson.Safe.to_string json in
  if String.length s > 160 then String.sub s 0 160 ^ "..." else s

let describe_error ~source = function
  | Missing_field { path; expected; _ } ->
      Printf.sprintf "%s: missing field %s (expected %s)" source path expected
  | Wrong_type { path; expected; actual; json } ->
      Printf.sprintf "%s: %s: expected %s, got %s (%s)" source path expected
        actual (preview json)
  | Invalid_value { path; reason } ->
      Printf.sprintf "%s: %s: %s" source path reason
  | Empty_collection { path; expected } ->
      Printf.sprintf "%s: %s: expected non-empty %s" source path expected
  | Span_missing { node; _ } ->
      Printf.sprintf "%s: node %d has no source-map entry" source node
  | Span_invalid { node; reason } ->
      Printf.sprintf "%s: source-map node %d: %s" source node reason
  | Parse_failed { errors; rc; _ } ->
      Printf.sprintf "%s: parse reported errors (rc %d): %s" source rc
        (preview errors)
  | Non_ascii { offset } ->
      Printf.sprintf "%s: source is not ASCII: byte at offset %d" source offset
  | Source_unreadable { path; reason } ->
      Printf.sprintf "%s: source file could not be read: %s" path reason
  | Source_non_ascii { path; offset } ->
      Printf.sprintf "%s: source is not ASCII: byte at offset %d" path offset

let non_ascii_offset text =
  let rec go i =
    if i >= String.length text then None
    else if Char.code text.[i] > 127 then Some i
    else go (i + 1)
  in
  go 0

(* A relative source path must stay inside the parse root: a leading `..`
   segment would read a file the map has no authority over. Absolute paths
   are used as given, because the measured corpus maps name imports that way. *)
let relative_escaping_root path =
  let rec go depth = function
    | [] -> true
    | "" :: rest | "." :: rest -> go depth rest
    | ".." :: rest -> depth > 0 && go (depth - 1) rest
    | _ :: rest -> go (depth + 1) rest
  in
  not (go 0 (String.split_on_char '/' path))

let read_source_file path =
  try
    let ic = open_in_bin path in
    Ok
      (Fun.protect
         ~finally:(fun () -> close_in_noerr ic)
         (fun () -> really_input_string ic (in_channel_length ic)))
  with Sys_error reason -> Error (Source_unreadable { path; reason })

let decode_program_inner ~ir ~map ~source_path ~source_text =
  let source = source_path in
  let ( let* ) = Result.bind in
  let field p f = if p = "" then f else p ^ "." ^ f in
  let idx p i = Printf.sprintf "%s[%d]" p i in
  let span_ids = ref [] in
  let note_id id = if id >= 0 then span_ids := id :: !span_ids in
  let wrong path expected json =
    Error (Wrong_type { path; expected; actual = type_name json; json })
  in
  let as_obj path = function
    | `Assoc fs -> Ok fs
    | json -> wrong path "object" json
  in
  let as_list path = function
    | `List xs -> Ok xs
    | json -> wrong path "array" json
  in
  let as_string path = function
    | `String s -> Ok s
    | json -> wrong path "string" json
  in
  let as_bool path = function
    | `Bool b -> Ok b
    | json -> wrong path "bool" json
  in
  let as_int path = function
    | `Int i -> Ok i
    | `Intlit s -> (
        match int_of_string_opt s with
        | Some i -> Ok i
        | None -> Error (Invalid_value { path; reason = "not an integer: " ^ s }))
    | `Float f when Float.is_integer f -> Ok (int_of_float f)
    | json -> wrong path "number" json
  in
  let req fs path name expected =
    match List.assoc_opt name fs with
    | Some v -> Ok v
    | None ->
        Error (Missing_field { path = field path name; expected; source })
  in
  let opt fs name = List.assoc_opt name fs in
  (* ---- the sources the map names --------------------------------------- *)
  let* map_fs = as_obj "map" map in
  let* source_index_json = req map_fs "" "sourceIndex" "object" in
  let* source_index_fs = as_obj "sourceIndex" source_index_json in
  let* source_index_0 = req source_index_fs "sourceIndex" "0" "string" in
  let* source_index = as_string "sourceIndex.0" source_index_0 in
  if source_index <> source_path then
    Error
      (Invalid_value
         {
           path = "sourceIndex.0";
           reason = Printf.sprintf "expected %s, got %s" source_path source_index;
         })
  else
    let* source_entries =
      List.fold_left
        (fun acc (key, value) ->
          let* xs = acc in
          match int_of_string_opt key with
          | None ->
              Error
                (Invalid_value
                   {
                     path = "sourceIndex." ^ key;
                     reason = "source index is not an integer";
                   })
          | Some index ->
              let* path = as_string ("sourceIndex." ^ key) value in
              Ok ((index, path) :: xs))
        (Ok []) source_index_fs
    in
    let* source_texts =
      List.fold_left
        (fun acc (index, path) ->
          let* texts = acc in
          if index = 0 then (
            Hashtbl.replace texts 0 source_text;
            Ok texts)
          else if Filename.is_relative path && relative_escaping_root path then
            Error
              (Source_unreadable
                 { path; reason = "the named source escapes the parse root" })
          else
            let* text = read_source_file path in
            match non_ascii_offset text with
            | Some offset -> Error (Source_non_ascii { path; offset })
            | None ->
                Hashtbl.replace texts index text;
                Ok texts)
        (Ok (Hashtbl.create 4)) source_entries
    in
    let source_paths = Hashtbl.create 4 in
    List.iter
      (fun (index, path) -> Hashtbl.replace source_paths index path)
      source_entries;
    let span_sources = Hashtbl.create 128 in
    (* ---- source map ------------------------------------------------------ *)
  let parse_position path json =
    let* fs = as_obj path json in
    let* line_json = req fs path "line" "number" in
    let* line = as_int (field path "line") line_json in
    let* col_json = req fs path "col" "number" in
    let* column = as_int (field path "col") col_json in
    let* index_json = req fs path "index" "number" in
    let* index = as_int (field path "index") index_json in
    Ok { Ir.line; column; index }
  in
  let parse_span node path json =
    let* xs = as_list path json in
    match xs with
    | [ source_json; start_json; end_json ] ->
        let* src = as_int (idx path 0) source_json in
        let* start_pos = parse_position (idx path 1) start_json in
        let* end_pos = parse_position (idx path 2) end_json in
        if start_pos.Ir.index > end_pos.Ir.index then
          Error
            (Span_invalid
               {
                 node;
                 reason =
                   Printf.sprintf "start index %d is after end index %d"
                     start_pos.Ir.index end_pos.Ir.index;
               })
        else
          (match Hashtbl.find_opt source_texts src with
          | None ->
              Error
                (Span_invalid
                   {
                     node;
                     reason =
                       Printf.sprintf
                         "span names source %d, which the source map does not \
                          resolve" src;
                   })
          | Some own_text ->
              let length = String.length own_text in
              if end_pos.Ir.index > length then
                Error
                  (Span_invalid
                     {
                       node;
                       reason =
                         Printf.sprintf "end index %d is past the source length %d"
                           end_pos.Ir.index length;
                     })
              else (
                Hashtbl.replace span_sources node src;
                Ok { Ir.start_pos; end_pos }))
    | _ ->
        Error
          (Span_invalid
             {
               node;
               reason = "expected a three-element [sourceIndex, start, end] entry";
             })
  in
    let* map_table_json = req map_fs "" "map" "object" in
    let* map_entries = as_obj "map.map" map_table_json in
    let spans = Hashtbl.create 128 in
    let* () =
      List.fold_left
        (fun acc (key, value) ->
          let* () = acc in
          match int_of_string_opt key with
          | None ->
              Error
                (Invalid_value
                   { path = "map.map." ^ key; reason = "node id is not an integer" })
          | Some node ->
              let* span = parse_span node ("map.map." ^ key) value in
              Hashtbl.replace spans node span;
              Ok ())
        (Ok ()) map_entries
    in
    (* ---- expression nodes ---------------------------------------------- *)
    let rec decode_type_expr path json =
      let* fs = as_obj path json in
      let* kind_json = req fs path "kind" "string" in
      let* kind = as_string (field path "kind") kind_json in
      let* id =
        match opt fs "id" with
        | None -> Ok (-1)
        | Some j ->
            let* i = as_int (field path "id") j in
            note_id i;
            Ok i
      in
      Ok (Ir.Unknown { id; kind; raw = json })
    and decode_param path json =
      let* fs = as_obj path json in
      let* id_json = req fs path "id" "number" in
      let* id = as_int (field path "id") id_json in
      let* name_json = req fs path "name" "string" in
      let* name = as_string (field path "name") name_json in
      note_id id;
      let* param_type =
        match opt fs "typeAnnotation" with
        | None -> Ok None
        | Some j ->
            let* e = decode_type_expr (field path "typeAnnotation") j in
            Ok (Some e)
      in
      Ok { Ir.param_id = id; param_name = name; param_type }
    and decode_expr path json =
      let* fs = as_obj path json in
      let* kind_json = req fs path "kind" "string" in
      let* kind = as_string (field path "kind") kind_json in
      let* id_json = req fs path "id" "number" in
      let* id = as_int (field path "id") id_json in
      note_id id;
      match kind with
      | "name" ->
          let* name_json = req fs path "name" "string" in
          let* name = as_string (field path "name") name_json in
          Ok (Ir.Name { id; name })
      | "str" ->
          let* value_json = req fs path "value" "string" in
          let* value = as_string (field path "value") value_json in
          Ok (Ir.Str { id; value })
      | "int" ->
          let* value_json = req fs path "value" "number" in
          let* value = as_int (field path "value") value_json in
          Ok (Ir.Int { id; value })
      | "bool" ->
          let* value_json = req fs path "value" "bool" in
          let* value = as_bool (field path "value") value_json in
          Ok (Ir.Bool { id; value })
      | "app" ->
          let* opcode_json = req fs path "opcode" "string" in
          let* opcode_s = as_string (field path "opcode") opcode_json in
          let* args_json = req fs path "args" "array" in
          let* args_list = as_list (field path "args") args_json in
          let* args =
            List.fold_left
              (fun acc (i, j) ->
                let* xs = acc in
                let* e = decode_expr (idx (field path "args") i) j in
                Ok (e :: xs))
              (Ok []) (List.mapi (fun i j -> (i, j)) args_list)
          in
          Ok
            (Ir.App
               {
                 id;
                 opcode = Ir.opcode_of_string opcode_s;
                 args = List.rev args;
               })
      | "lambda" ->
          let* params_json = req fs path "params" "array" in
          let* params_list = as_list (field path "params") params_json in
          let* params =
            List.fold_left
              (fun acc (i, j) ->
                let* xs = acc in
                let* p = decode_param (idx (field path "params") i) j in
                Ok (p :: xs))
              (Ok []) (List.mapi (fun i j -> (i, j)) params_list)
          in
          let* body_json = req fs path "expr" "object" in
          let* body = decode_expr (field path "expr") body_json in
          Ok (Ir.Lambda { id; params = List.rev params; body })
      | "let" ->
          let* opdef_json = req fs path "opdef" "object" in
          let opdef_path = field path "opdef" in
          let* opdef = as_obj opdef_path opdef_json in
          let* binder_json = req opdef opdef_path "name" "string" in
          let* binder = as_string (field opdef_path "name") binder_json in
          let* () =
            match opt opdef "id" with
            | Some j ->
                let* i = as_int (field opdef_path "id") j in
                note_id i;
                Ok ()
            | None -> Ok ()
          in
          let* binder_body_json = req opdef opdef_path "expr" "object" in
          let* binder_body =
            decode_expr (field opdef_path "expr") binder_body_json
          in
          let* body_json = req fs path "expr" "object" in
          let* body = decode_expr (field path "expr") body_json in
          Ok (Ir.Let { id; binder; binder_body; body })
      | other -> Ok (Ir.Unknown { id; kind = other; raw = json })
    in
    (* ---- declarations and modules -------------------------------------- *)
    let qualifier_of_string = function
      | "puredef" -> Ir.PureDef
      | "pureval" -> Ir.PureVal
      | "action" -> Ir.Action
      | "val" -> Ir.Val
      | "temporal" -> Ir.Temporal
      | "run" -> Ir.Run
      | "def" -> Ir.PlainDef
      | s -> Ir.OtherQualifier s
    in
    let decode_opt_string fs path name =
      match opt fs name with
      | None -> Ok None
      | Some j ->
          let* s = as_string (field path name) j in
          Ok (Some s)
    in
    let decode_declaration path json =
      let* fs = as_obj path json in
      let* id_json = req fs path "id" "number" in
      let* id = as_int (field path "id") id_json in
      let* kind_json = req fs path "kind" "string" in
      let* kind_s = as_string (field path "kind") kind_json in
      note_id id;
      let* kind =
        match kind_s with
        | "const" -> Ok Ir.Const
        | "var" -> Ok Ir.Var
        | "typedef" -> Ok Ir.TypeDef
        | "def" -> Ok Ir.Def
        | "import" ->
            let* proto_name = decode_opt_string fs path "protoName" in
            let* qualified_name = decode_opt_string fs path "qualifiedName" in
            Ok (Ir.NonSubject (Ir.Import { proto_name; qualified_name }))
        | "instance" ->
            let* proto_name = decode_opt_string fs path "protoName" in
            let* qualified_name = decode_opt_string fs path "qualifiedName" in
            Ok (Ir.NonSubject (Ir.Instance { proto_name; qualified_name }))
        | "assume" ->
            let* assumption_json = req fs path "assumption" "object" in
            let* assumption =
              decode_expr (field path "assumption") assumption_json
            in
            Ok (Ir.NonSubject (Ir.Assume { assumption }))
        | other -> Ok (Ir.NonSubject (Ir.Unmodelled { kind = other }))
      in
      let is_def = kind_s = "def" in
      let* name =
        match kind with
        | Ir.NonSubject _ -> (
            match opt fs "name" with
            | Some j -> as_string (field path "name") j
            | None -> Ok "")
        | _ ->
            let* name_json = req fs path "name" "string" in
            as_string (field path "name") name_json
      in
      let* qualifier =
        match kind with
        | Ir.NonSubject _ -> Ok None
        | _ -> (
            match opt fs "qualifier" with
            | None -> Ok None
            | Some j ->
                let* s = as_string (field path "qualifier") j in
                Ok (Some (qualifier_of_string s)))
      in
      let* type_annotation =
        match opt fs "typeAnnotation" with
        | None -> Ok None
        | Some j ->
            let* e = decode_type_expr (field path "typeAnnotation") j in
            Ok (Some e)
      in
      let* body, params =
        match kind with
        | Ir.NonSubject _ -> Ok (None, [])
        | _ -> (
            match opt fs "expr" with
            | None ->
                if is_def then
                  Error
                    (Missing_field
                       { path = field path "expr"; expected = "object"; source })
                else Ok (None, [])
            | Some expr_json ->
                let* root = decode_expr (field path "expr") expr_json in
                if is_def then
                  match root with
                  | Ir.Lambda { params; body; _ } -> Ok (Some body, params)
                  | other -> Ok (Some other, [])
                else Ok (Some root, []))
      in
      let* span =
        match Hashtbl.find_opt spans id with
        | Some sp -> Ok sp
        | None -> Error (Span_missing { node = id; source })
      in
      Ok
        {
          Ir.decl_id = id;
          name;
          kind;
          qualifier;
          type_annotation;
          params;
          body;
          decl_span = span;
        }
    in
    let decode_module path json =
      let* fs = as_obj path json in
      let* id_json = req fs path "id" "number" in
      let* id = as_int (field path "id") id_json in
      let* name_json = req fs path "name" "string" in
      let* name = as_string (field path "name") name_json in
      note_id id;
      let* decls_json = req fs path "declarations" "array" in
      let* decls_list = as_list (field path "declarations") decls_json in
      let* declarations =
        List.fold_left
          (fun acc (i, j) ->
            let* xs = acc in
            let* d = decode_declaration (idx (field path "declarations") i) j in
            Ok (d :: xs))
          (Ok []) (List.mapi (fun i j -> (i, j)) decls_list)
      in
      let declarations = List.rev declarations in
      let seen = Hashtbl.create 16 in
      let* () =
        List.fold_left
          (fun acc d ->
            let* () = acc in
            match d.Ir.kind with
            | Ir.NonSubject _ -> Ok ()
            | _ -> (
                match Hashtbl.find_opt seen d.Ir.name with
                | None ->
                    Hashtbl.add seen d.Ir.name ();
                    Ok ()
                | Some () ->
                    Error
                      (Invalid_value
                         {
                           path = field path "declarations";
                           reason =
                             Printf.sprintf "duplicate declaration name %S"
                               d.Ir.name;
                         })))
          (Ok ()) declarations
      in
      let* module_span =
        match Hashtbl.find_opt spans id with
        | Some sp -> Ok sp
        | None -> Error (Span_missing { node = id; source })
      in
      let src =
        match Hashtbl.find_opt span_sources id with Some src -> src | None -> 0
      in
      let* own_text =
        match Hashtbl.find_opt source_texts src with
        | Some text -> Ok text
        | None ->
            Error
              (Span_invalid
                 {
                   node = id;
                   reason =
                     Printf.sprintf
                       "module span names source %d, which the source map does \
                        not resolve" src;
                 })
      in
      let end_index = module_span.Ir.end_pos.Ir.index in
      if end_index >= String.length own_text || own_text.[end_index] <> '}' then
        Error
          (Span_invalid
             { node = id; reason = "module end index does not point at the closing brace" })
      else Ok { Ir.module_id = id; module_name = name; declarations; module_span }
    in
    let* ir_fs = as_obj "ir" ir in
    let* errors_json = req ir_fs "" "errors" "array" in
    let* errors_list = as_list "errors" errors_json in
    let* () =
      if errors_list = [] then Ok ()
      else Error (Parse_failed { source; rc = 0; errors = `List errors_list })
    in
    let* stage_json = req ir_fs "" "stage" "string" in
    let* stage = as_string "stage" stage_json in
    if stage <> "parsing" then
      Error
        (Invalid_value
           {
             path = "stage";
             reason = Printf.sprintf "expected \"parsing\", got %S" stage;
           })
    else
      let* modules_json = req ir_fs "" "modules" "array" in
      let* module_list = as_list "modules" modules_json in
      let* () =
        if module_list = [] then
          Error (Empty_collection { path = "modules"; expected = "module array" })
        else Ok ()
      in
      let* modules =
        List.fold_left
          (fun acc (i, j) ->
            let* xs = acc in
            let* m = decode_module (idx "modules" i) j in
            Ok (m :: xs))
          (Ok []) (List.mapi (fun i j -> (i, j)) module_list)
      in
      let* () =
        List.fold_left
          (fun acc node ->
            let* () = acc in
            if Hashtbl.mem spans node then Ok ()
            else Error (Span_missing { node; source }))
          (Ok ()) (List.sort_uniq compare !span_ids)
      in
      let spans =
        Hashtbl.fold (fun k v acc -> Ir.IntMap.add k v acc) spans Ir.IntMap.empty
      in
      (* The source file each node's span belongs to, so a finding can name it
         even when the span sits in an imported file. *)
      let sources =
        Hashtbl.fold
          (fun node index acc ->
            let path =
              match Hashtbl.find_opt source_paths index with
              | Some path -> path
              | None -> source_path
            in
            Ir.IntMap.add node path acc)
          span_sources Ir.IntMap.empty
      in
      let* table_json = req ir_fs "" "table" "object" in
      let* table_fs = as_obj "table" table_json in
      let* resolution =
        List.fold_left
          (fun acc (key, value) ->
            let* mp = acc in
            match int_of_string_opt key with
            | None ->
                Error
                  (Invalid_value
                     {
                       path = "table." ^ key;
                       reason = "node id is not an integer";
                     })
            | Some id -> (
                match value with
                | `Assoc fields -> (
                    match List.assoc_opt "name" fields with
                    | None ->
                        Error
                          (Missing_field
                             {
                               path = field ("table." ^ key) "name";
                               expected = "string";
                               source;
                             })
                    | Some name_json ->
                        let* name =
                          as_string (field ("table." ^ key) "name") name_json
                        in
                        Ok (Ir.IntMap.add id name mp))
                | json ->
                    Error
                      (Wrong_type
                         {
                           path = "table." ^ key;
                           expected = "object";
                           actual = type_name json;
                           json;
                         })))
          (Ok Ir.IntMap.empty) table_fs
      in
      Ok
        {
          Ir.modules = List.rev modules;
          source_path;
          source_text;
          spans;
          sources;
          resolution;
        }

let decode_program ~ir ~map ~source_path ~source_text =
  match non_ascii_offset source_text with
  | Some offset -> Error (Non_ascii { offset })
  | None -> decode_program_inner ~ir ~map ~source_path ~source_text

let read_json path =
  try Ok (Yojson.Safe.from_file path)
  with
  | Sys_error msg -> Error msg
  | Yojson.Json_error msg -> Error msg

let decode_program_from_files ~ir_path ~map_path ~source_path ~source_text =
  match read_json ir_path with
  | Error msg -> Error (Invalid_value { path = ir_path; reason = msg })
  | Ok ir -> (
      match read_json map_path with
      | Error msg -> Error (Invalid_value { path = map_path; reason = msg })
      | Ok map -> decode_program ~ir ~map ~source_path ~source_text)
