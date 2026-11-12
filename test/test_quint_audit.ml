(* quint-audit test suite: decoder, checks, qcalc/rundisc mirrors, report. *)

open Quint_audit

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let n = in_channel_length ic in
      really_input_string ic n)

let failf fmt = Printf.ksprintf (fun s -> Alcotest.fail s) fmt

let fixture_dir = "fixtures"

let source_index_of_map map =
  match map with
  | `Assoc fs -> (
      match List.assoc_opt "sourceIndex" fs with
      | Some (`Assoc sfs) -> (
          match List.assoc_opt "0" sfs with
          | Some (`String s) -> s
          | _ -> failf "fixture map has no sourceIndex.0 string")
      | _ -> failf "fixture map has no sourceIndex object")
  | _ -> failf "fixture map is not an object"

type raw_fixture = { ir : Yojson.Safe.t; map : Yojson.Safe.t; source : string; path : string }

let raw_fixture name =
  let source = read_file (Filename.concat fixture_dir ("specs/" ^ name ^ ".qnt")) in
  let ir = Yojson.Safe.from_file (Filename.concat fixture_dir ("ir/" ^ name ^ ".json")) in
  let map = Yojson.Safe.from_file (Filename.concat fixture_dir ("ir/" ^ name ^ "-map.json")) in
  { ir; map; source; path = source_index_of_map map }

let decode_raw r =
  Ir_decode.decode_program ~ir:r.ir ~map:r.map ~source_path:r.path ~source_text:r.source

let decode_fixture name =
  match decode_raw (raw_fixture name) with
  | Ok program -> program
  | Error error ->
      failf "fixture %s failed to decode: %s" name
        (Ir_decode.describe_error ~source:name error)

let context program =
  match program.Ir.modules with
  | [ m ] ->
      let symbols = Symbols.build ~resolution:program.Ir.resolution m in
      Checks.{ program; module_ = m; symbols }
  | _ -> failf "fixture is not single-module"

let run_checks program = Checks.run_ir_checks (context program)

let findings_for check program =
  List.filter (fun f -> f.Finding.check = check) (run_checks program)

let has_substring haystack needle =
  let n = String.length needle and h = String.length haystack in
  let rec go i =
    if i + n > h then false
    else if String.sub haystack i n = needle then true
    else go (i + 1)
  in
  n = 0 || go 0

let check_has_substring label needle s =
  Alcotest.(check bool) label true (has_substring s needle)

let count_severity severity findings =
  List.length (List.filter (fun f -> f.Finding.severity = severity) findings)

(* ---------- JSON mutation helpers for decoder tests ---------- *)

let assoc_field name = function
  | `Assoc fs -> (
      match List.assoc_opt name fs with
      | Some v -> v
      | None -> failf "missing JSON field %s" name)
  | _ -> failf "expected a JSON object for field %s" name

let replace_field name value = function
  | `Assoc fs -> `Assoc ((name, value) :: List.remove_assoc name fs)
  | _ -> failf "expected a JSON object to replace %s" name

let module0 ir =
  match assoc_field "modules" ir with
  | `List (m :: _) -> m
  | _ -> failf "expected a non-empty modules array"

let replace_module0 m ir =
  match assoc_field "modules" ir with
  | `List (_ :: rest) -> replace_field "modules" (`List (m :: rest)) ir
  | _ -> failf "expected a non-empty modules array"

let declarations m = match assoc_field "declarations" m with `List ds -> ds | _ -> failf "declarations"

let replace_declarations ds m = replace_field "declarations" (`List ds) m

let declaration_named name ir =
  match List.find_opt (fun d -> assoc_field "name" d = `String name) (declarations (module0 ir)) with
  | Some d -> d
  | None -> failf "no declaration named %s" name

let replace_declaration name f ir =
  let m = module0 ir in
  let ds = declarations m in
  let ds = List.map (fun d -> if assoc_field "name" d = `String name then f d else d) ds in
  replace_module0 (replace_declarations ds m) ir

let map_entry_id ir name = assoc_field "id" (declaration_named name ir)

let entry_key ir name =
  match map_entry_id ir name with `Int i -> string_of_int i | _ -> failf "declaration id is not an int"

let map_entries map = assoc_field "map" map

let replace_map_entry key value map =
  replace_field "map" (replace_field key value (map_entries map)) map

let entry_of_key key map = assoc_field key (map_entries map)

let first_table_entry ir =
  match assoc_field "table" ir with
  | `Assoc fs -> (
      match
        List.find_opt
          (fun (_, v) ->
            match v with `Assoc efs -> List.mem_assoc "name" efs | _ -> false)
          fs
      with
      | Some entry -> entry
      | None -> failf "no named table entry")
  | _ -> failf "table is not an object"

let replace_table_entry key value ir =
  replace_field "table" (replace_field key value (assoc_field "table" ir)) ir

(* ---------- decoder-mirror helpers ---------- *)

let expect_decode label result =
  match result with
  | Ok program -> program
  | Error error ->
      failf "%s: expected decode, got %s" label
        (Ir_decode.describe_error ~source:"test" error)

let expect_refuse label result =
  match result with
  | Ok _ -> failf "%s: expected a refusal, got Ok" label
  | Error _ -> ()

let add_source path map =
  let si = assoc_field "sourceIndex" map in
  replace_field "sourceIndex" (replace_field "1" (`String path) si) map

let set_span_source key src map =
  match entry_of_key key map with
  | `List [ _; start; finish ] ->
      replace_map_entry key (`List [ `Int src; start; finish ]) map
  | _ -> failf "span %s is not a three-element list" key

let set_span_end key index map =
  match entry_of_key key map with
  | `List [ src; start; `Assoc efs ] ->
      let finish =
        `Assoc (("index", `Int index) :: List.remove_assoc "index" efs)
      in
      replace_map_entry key (`List [ src; start; finish ]) map
  | _ -> failf "span %s has no object end position" key

let imported_spec name = Filename.concat fixture_dir ("specs/" ^ name ^ ".qnt")

let last_brace_offset name =
  let s = read_file (imported_spec name) in
  let rec go i =
    if i < 0 then failf "fixture %s has no closing brace" name
    else if s.[i] = '}' then i
    else go (i - 1)
  in
  go (String.length s - 1)

let module_key ir =
  match assoc_field "id" (module0 ir) with
  | `Int i -> string_of_int i
  | _ -> failf "module id is not an int"

(* ---------- sha256 ---------- *)

let test_sha256 () =
  Alcotest.(check string) "empty"
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    (Sha256.digest_bytes "");
  Alcotest.(check string) "abc"
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    (Sha256.digest_bytes "abc");
  Alcotest.(check string) "long"
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    (Sha256.digest_bytes
       "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")

(* ---------- decoder ---------- *)

let expect_error label pred = function
  | Ok _ -> failf "%s: expected a decode error, got Ok" label
  | Error error -> if not (pred error) then failf "%s: unexpected error %s" label (Ir_decode.describe_error ~source:"test" error)

let test_decode_clean () =
  let program = decode_fixture "clean" in
  Alcotest.(check int) "one module" 1 (List.length program.Ir.modules);
  let m = List.hd program.Ir.modules in
  Alcotest.(check string) "module name" "Clean" m.Ir.module_name;
  Alcotest.(check bool) "declarations present" true (List.length m.Ir.declarations > 0)

let test_decode_unknown_preserved () =
  let raw = raw_fixture "clean" in
  let mutate = function
    | `Assoc fs -> `Assoc (List.map (fun (k, v) -> if k = "kind" then (k, `String "futureKind") else (k, v)) fs)
    | other -> other
  in
  let ir =
    replace_declaration "bound"
      (fun d -> replace_field "expr" (mutate (assoc_field "expr" d)) d)
      raw.ir
  in
  let raw = { raw with ir } in
  match decode_raw raw with
  | Error error -> failf "unknown node refused: %s" (Ir_decode.describe_error ~source:"test" error)
  | Ok program ->
      let d = List.find (fun (d : Ir.declaration) -> d.Ir.name = "bound") (List.hd program.Ir.modules).Ir.declarations in
      (match d.Ir.body with
      | Some (Ir.Unknown { kind; _ }) -> Alcotest.(check string) "unknown kind preserved" "futureKind" kind
      | _ -> failf "expected an Unknown body for bound");
      let findings = findings_for Finding.QP001 program in
      Alcotest.(check int) "unknown reports one info" 1 (count_severity Finding.Info findings)

let test_decode_missing_field () =
  let raw = raw_fixture "clean" in
  let m = module0 raw.ir in
  let ds = declarations m in
  let first = List.hd ds in
  let first = `Assoc (List.remove_assoc "name" (match first with `Assoc fs -> fs | _ -> [])) in
  let ir = replace_module0 (replace_declarations (first :: List.tl ds) m) raw.ir in
  expect_error "missing name"
    (function
      | Ir_decode.Missing_field { path; _ } ->
          has_substring path "modules[0].declarations[0].name"
      | _ -> false)
    (decode_raw { raw with ir })

let test_decode_wrong_type () =
  let raw = raw_fixture "clean" in
  let m = module0 raw.ir in
  let ir = replace_module0 (replace_field "id" (`String "not-a-number") m) raw.ir in
  expect_error "module id type"
    (function
      | Ir_decode.Wrong_type { path; expected; _ } ->
          has_substring path "modules[0].id" && expected = "number"
      | _ -> false)
    (decode_raw { raw with ir })

let test_decode_empty_modules () =
  let raw = raw_fixture "clean" in
  let ir = replace_field "modules" (`List []) raw.ir in
  expect_error "empty modules"
    (function Ir_decode.Empty_collection { path; _ } -> path = "modules" | _ -> false)
    (decode_raw { raw with ir })

let test_decode_errors_array () =
  let raw = raw_fixture "clean" in
  let ir = replace_field "errors" (`List [ `Assoc [ ("explanation", `String "boom") ] ]) raw.ir in
  expect_error "errors non-empty"
    (function Ir_decode.Parse_failed { errors; _ } -> errors <> `List [] | _ -> false)
    (decode_raw { raw with ir })

let test_decode_stage () =
  let raw = raw_fixture "clean" in
  let ir = replace_field "stage" (`String "typechecking") raw.ir in
  expect_error "stage"
    (function Ir_decode.Invalid_value { path; _ } -> path = "stage" | _ -> false)
    (decode_raw { raw with ir })

let test_decode_non_ascii () =
  let raw = raw_fixture "clean" in
  let source = raw.source ^ "caf\xc3\xa9" in
  expect_error "non-ascii"
    (function Ir_decode.Non_ascii { offset } -> offset = String.length raw.source + 3 | _ -> false)
    (decode_raw { raw with source });
  (* The ASCII precondition is widened to every source the map names. *)
  let tmp = Filename.temp_file "quint-audit-import" ".qnt" in
  let oc = open_out_bin tmp in
  output_string oc "x\xc3\xa9";
  close_out oc;
  Fun.protect
    ~finally:(fun () -> Sys.remove tmp)
    (fun () ->
      let key = entry_key raw.ir "bound" in
      let map =
        raw.map |> add_source tmp |> set_span_source key 1 |> set_span_end key 1
      in
      expect_error "imported non-ascii"
        (function
          | Ir_decode.Source_non_ascii { offset; _ } -> offset = 1
          | _ -> false)
        (decode_raw { raw with map }))

let test_decode_span_missing () =
  let raw = raw_fixture "clean" in
  let key = entry_key raw.ir "bound" in
  let map = replace_field "map" (`Assoc (List.remove_assoc key (match map_entries raw.map with `Assoc fs -> fs | _ -> []))) raw.map in
  expect_error "span missing"
    (function Ir_decode.Span_missing { node = _; source = _ } -> true | _ -> false)
    (decode_raw { raw with map })

let test_decode_span_invalid () =
  let raw = raw_fixture "clean" in
  let key = entry_key raw.ir "bound" in
  let broken =
    match entry_of_key key raw.map with
    | `List [ idx; start; _finish ] -> `List [ idx; start; `Assoc [ ("line", `Int 0); ("col", `Int 0); ("index", `Int 0) ] ]
    | _ -> failf "unexpected map entry"
  in
  expect_error "span invalid"
    (function Ir_decode.Span_invalid { node = _; reason = _ } -> true | _ -> false)
    (decode_raw { raw with map = replace_map_entry key broken raw.map })

let test_decode_module_brace () =
  let raw = raw_fixture "clean" in
  let module_id = match assoc_field "id" (module0 raw.ir) with `Int i -> string_of_int i | _ -> failf "module id" in
  let broken =
    match entry_of_key module_id raw.map with
    | `List [ idx; _start; _finish ] -> `List [ idx; `Assoc [ ("line", `Int 0); ("col", `Int 0); ("index", `Int 0) ]; `Assoc [ ("line", `Int 0); ("col", `Int 0); ("index", `Int 0) ] ]
    | _ -> failf "unexpected module map entry"
  in
  expect_error "module brace"
    (function Ir_decode.Span_invalid { node = _; reason = _ } -> true | _ -> false)
    (decode_raw { raw with map = replace_map_entry module_id broken raw.map })

let test_decode_source_index_mismatch () =
  let raw = raw_fixture "clean" in
  expect_error "sourceIndex mismatch"
    (function Ir_decode.Invalid_value { path; _ } -> path = "sourceIndex.0" | _ -> false)
    (decode_raw { raw with path = "/different/path.qnt" })

let test_decode_duplicate_name () =
  let raw = raw_fixture "clean" in
  let m = module0 raw.ir in
  let ds = declarations m in
  let name0 = assoc_field "name" (List.hd ds) in
  let ds = List.mapi (fun i d -> if i = 1 then replace_field "name" name0 d else d) ds in
  let ir = replace_module0 (replace_declarations ds m) raw.ir in
  expect_error "duplicate name"
    (function Ir_decode.Invalid_value { reason; _ } -> has_substring reason "duplicate" | _ -> false)
    (decode_raw { raw with ir })

(* A malformed table entry is a decode failure, never a silent
   skip: the table is a consumed field. *)
let test_decode_table_bad_entry () =
  let raw = raw_fixture "clean" in
  let key, _ = first_table_entry raw.ir in
  let ir = replace_table_entry key (`String "not-an-object") raw.ir in
  expect_error "table entry type"
    (function
      | Ir_decode.Wrong_type { path; expected; _ } ->
          has_substring path ("table." ^ key) && expected = "object"
      | _ -> false)
    (decode_raw { raw with ir })

let test_decode_table_missing_name () =
  let raw = raw_fixture "clean" in
  let key, entry = first_table_entry raw.ir in
  let stripped =
    match entry with
    | `Assoc fs -> `Assoc (List.remove_assoc "name" fs)
    | _ -> failf "named entry is not an object"
  in
  let ir = replace_table_entry key stripped raw.ir in
  expect_error "table entry name"
    (function
      | Ir_decode.Missing_field { path; _ } -> path = "table." ^ key ^ ".name"
      | _ -> false)
    (decode_raw { raw with ir })

(* ---------- the decode contract mirror ----------

   These fixtures assert spec/irdecode.qnt at the decoder boundary. The
   source-map cases are EXPECTED-DECODE / EXPECTED-REFUSE per the contract;
   the imported-span and module-extent shapes are refusals by design. *)

let test_decode_imported_span_past_main_length () =
  let raw = raw_fixture "clean" in
  let key = entry_key raw.ir "bound" in
  let own_end = last_brace_offset "imported_ok" in
  let map =
    raw.map
    |> add_source (imported_spec "imported_ok")
    |> set_span_source key 1
    |> set_span_end key own_end
  in
  ignore
    (expect_decode "imported span past the main length"
       (decode_raw { raw with map }));
  (* A named source that cannot be read is refused loudly with its path. *)
  let missing =
    raw.map
    |> add_source "/nonexistent/imported-missing.qnt"
    |> set_span_source key 1
    |> set_span_end key 10
  in
  expect_error "named source absent"
    (function
      | Ir_decode.Source_unreadable { path; _ } -> has_substring path "imported-missing"
      | _ -> false)
    (decode_raw { raw with map = missing })

let test_decode_imported_span_past_own_source () =
  let raw = raw_fixture "clean" in
  let key = entry_key raw.ir "bound" in
  let map =
    raw.map
    |> add_source (imported_spec "imported_short")
    |> set_span_source key 1
    |> set_span_end key 300
  in
  expect_refuse "imported span past its own source" (decode_raw { raw with map });
  (* A span naming a source the map does not resolve is malformed too. *)
  let unknown_source =
    raw.map
    |> add_source (imported_spec "imported_short")
    |> set_span_source key 2
    |> set_span_end key 100
  in
  expect_refuse "span names an unmapped source"
    (decode_raw { raw with map = unknown_source })

let test_decode_imported_span_in_both_ranges () =
  let raw = raw_fixture "clean" in
  let key = entry_key raw.ir "bound" in
  let map =
    raw.map
    |> add_source (imported_spec "imported_ok")
    |> set_span_source key 1
    |> set_span_end key 300
  in
  ignore
    (expect_decode "imported span inside both ranges" (decode_raw { raw with map }))

let test_decode_module_imported_brace () =
  let raw = raw_fixture "clean" in
  let key = module_key raw.ir in
  let own_end = last_brace_offset "imported_ok" in
  let map =
    raw.map
    |> add_source (imported_spec "imported_ok")
    |> set_span_source key 1
    |> set_span_end key own_end
  in
  ignore
    (expect_decode "imported module end at its own brace"
       (decode_raw { raw with map }))

let test_decode_module_wrong_source_brace () =
  let raw = raw_fixture "clean" in
  let key = module_key raw.ir in
  (* 481 is the clean file's closing brace; it is past the short imported
     file's length, so the main byte must not be used. *)
  let map =
    raw.map
    |> add_source (imported_spec "imported_short")
    |> set_span_source key 1
    |> set_span_end key 481
  in
  expect_refuse "module end uses the main file's brace"
    (decode_raw { raw with map })

let test_decode_main_span_past_own_source () =
  let raw = raw_fixture "clean" in
  let key = entry_key raw.ir "bound" in
  let map = set_span_end key 500 raw.map in
  expect_refuse "main span past its own source" (decode_raw { raw with map })

(* i_span_refusal_set: a span is refused exactly when it is malformed. *)
let test_decode_span_refusal_set () =
  let raw = raw_fixture "clean" in
  let key = entry_key raw.ir "bound" in
  ignore (expect_decode "a valid span decodes" (decode_raw raw));
  expect_refuse "unknown source"
    (decode_raw { raw with map = raw.map |> set_span_source key 3 });
  expect_refuse "unordered range"
    (decode_raw { raw with map = raw.map |> set_span_end key 0 });
  expect_refuse "past its own source"
    (decode_raw { raw with map = raw.map |> set_span_end key 500 })

let test_declaration_const_is_nonsubject () =
  let program = decode_fixture "clean" in
  Alcotest.(check bool) "const is not a census subject" false
    (List.exists
       (fun (d : Ir.declaration) -> d.Ir.name = "LIMIT")
       (Checks.vals (context program)))

let test_declaration_var_is_nonsubject () =
  let program = decode_fixture "clean" in
  Alcotest.(check bool) "var is not a census subject" false
    (List.exists
       (fun (d : Ir.declaration) -> d.Ir.name = "x")
       (Checks.vals (context program)))

let test_declaration_typedef_is_nonsubject () =
  let program = decode_fixture "clean" in
  Alcotest.(check bool) "typedef is not a census subject" false
    (List.exists
       (fun (d : Ir.declaration) -> d.Ir.name = "Role")
       (Checks.vals (context program)))

let test_declaration_def_is_subject () =
  let program = decode_fixture "clean" in
  Alcotest.(check bool) "def val is a reporting subject" true
    (List.exists
       (fun (d : Ir.declaration) -> d.Ir.name = "bound")
       (Checks.vals (context program)))

let test_decode_import_declaration () =
  let raw = raw_fixture "clean" in
  let id =
    match assoc_field "id" (declaration_named "LIMIT" raw.ir) with
    | `Int i -> i
    | _ -> failf "const id is not an int"
  in
  let replacement =
    `Assoc
      [
        ("id", `Int id);
        ("kind", `String "import");
        ("protoName", `String "Clean");
        ("qualifiedName", `String "c");
      ]
  in
  let ir = replace_declaration "LIMIT" (fun _ -> replacement) raw.ir in
  let program =
    expect_decode "import declaration decodes" (decode_raw { raw with ir })
  in
  let base = List.length (Checks.vals (context (decode_fixture "clean"))) in
  Alcotest.(check int) "import adds no census subject" base
    (List.length (Checks.vals (context program)));
  (* Two nameless imports in one module decode: the name field is not a
     duplicate-name or a schema requirement for a carried non-subject. *)
  let second_id =
    match assoc_field "id" (declaration_named "bound" raw.ir) with
    | `Int i -> i
    | _ -> failf "bound id is not an int"
  in
  let second =
    `Assoc
      [
        ("id", `Int second_id);
        ("kind", `String "import");
        ("protoName", `String "Other");
      ]
  in
  let ir =
    let m = module0 raw.ir in
    let ds = declarations m in
    let swapped =
      List.map
        (fun d ->
          match assoc_field "id" d with
          | `Int i when i = id -> replacement
          | `Int i when i = second_id -> second
          | _ -> d)
        ds
    in
    replace_module0 (replace_declarations swapped m) raw.ir
  in
  ignore
    (expect_decode "two nameless imports decode" (decode_raw { raw with ir }))

let test_decode_instance_declaration () =
  let raw = raw_fixture "clean" in
  let id =
    match assoc_field "id" (declaration_named "LIMIT" raw.ir) with
    | `Int i -> i
    | _ -> failf "const id is not an int"
  in
  let replacement =
    `Assoc
      [
        ("id", `Int id);
        ("kind", `String "instance");
        ("identityOverride", `Bool false);
        ("protoName", `String "Clean");
        ("overrides", `List []);
      ]
  in
  let ir = replace_declaration "LIMIT" (fun _ -> replacement) raw.ir in
  let program =
    expect_decode "instance declaration decodes" (decode_raw { raw with ir })
  in
  let base = List.length (Checks.vals (context (decode_fixture "clean"))) in
  Alcotest.(check int) "instance adds no census subject" base
    (List.length (Checks.vals (context program)))

let test_decode_assume_declaration () =
  let raw = raw_fixture "clean" in
  let ir =
    replace_declaration "bound"
      (fun d ->
        `Assoc
          [
            ("id", assoc_field "id" d);
            ("kind", `String "assume");
            ("name", `String "bound");
            ("assumption", assoc_field "expr" d);
          ])
      raw.ir
  in
  let program =
    expect_decode "assume declaration decodes" (decode_raw { raw with ir })
  in
  Alcotest.(check bool) "assume is not a census subject" false
    (List.exists
       (fun (d : Ir.declaration) -> d.Ir.name = "bound")
       (Checks.vals (context program)))

let test_decode_future_declaration () =
  let raw = raw_fixture "clean" in
  let ir =
    replace_declaration "bound"
      (fun d -> replace_field "kind" (`String "futureKind") d)
      raw.ir
  in
  let program =
    expect_decode "unknown declaration kind decodes as a non-subject"
      (decode_raw { raw with ir })
  in
  Alcotest.(check bool) "future kind is not a census subject" false
    (List.exists
       (fun (d : Ir.declaration) -> d.Ir.name = "bound")
       (Checks.vals (context program)));
  (* The coverage gap stays visible as an info finding. *)
  let infos = findings_for Finding.QP002 program in
  Alcotest.(check bool) "unknown kind reports an info coverage gap" true
    (List.exists
       (fun (f : Finding.finding) ->
         f.Finding.severity = Finding.Info
         && has_substring f.Finding.message "unmodelled declaration kind")
       infos)

(* i_known_kind_decodes: every kind the pinned parser emits decodes. *)
let test_decode_known_kind_decodes () =
  let program = decode_fixture "clean" in
  let kinds =
    List.concat_map
      (fun (m : Ir.module_) ->
        List.map
          (fun (d : Ir.declaration) -> Ir.string_of_decl_kind d.Ir.kind)
          m.Ir.declarations)
      program.Ir.modules
  in
  List.iter
    (fun kind ->
      Alcotest.(check bool) (kind ^ " decodes") true (List.mem kind kinds))
    [ "const"; "var"; "typedef"; "def" ]

(* ---------- qcalc ---------- *)

let next_id = ref 0

let new_id () =
  incr next_id;
  !next_id

let name s = Ir.Name { id = new_id (); name = s }
let boolean b = Ir.Bool { id = new_id (); value = b }
let unknown k = Ir.Unknown { id = new_id (); kind = k; raw = `Null }
let app op args = Ir.App { id = new_id (); opcode = op; args }

let result_string = Qcalc.string_of_result

let test_qcalc_pool () =
  let x = name "x" and y = name "y" in
  let cases =
    [
      ("implies tautology", app Ir.Implies [ x; x ], Qcalc.Const_true);
      ("and not", app Ir.And [ x; app Ir.Not [ x ] ], Qcalc.Const_false);
      ("or not", app Ir.Or [ x; app Ir.Not [ x ] ], Qcalc.Const_true);
      ("or true", app Ir.Or [ boolean true; x ], Qcalc.Const_true);
      ("and false", app Ir.And [ boolean false; x ], Qcalc.Const_false);
      ("implies literals", app Ir.Implies [ boolean true; boolean false ], Qcalc.Const_false);
      ("iff not", app Ir.Iff [ x; app Ir.Not [ x ] ], Qcalc.Const_false);
      ("or xy", app Ir.Or [ x; y ], Qcalc.Varies);
      ("and xy", app Ir.And [ x; y ], Qcalc.Varies);
      ("eq identity", app Ir.Eq [ x; x ], Qcalc.Const_true);
      ("eq distinct", app Ir.Eq [ name "x"; name "y" ], Qcalc.Varies);
      ( "eq node identity",
        app Ir.Eq
          [ app Ir.Or [ name "x"; name "y" ]; app Ir.Or [ name "x"; name "y" ] ],
        Qcalc.Const_true );
      ( "eq node distinct",
        app Ir.Eq
          [ app Ir.Or [ name "x"; name "y" ]; app Ir.And [ name "x"; name "y" ] ],
        Qcalc.Varies );
      ("neq identity", app Ir.Neq [ x; x ], Qcalc.Const_false);
      ("implies nodes", app Ir.Implies [ app Ir.Or [ x; y ]; app Ir.Or [ x; y ] ], Qcalc.Const_true);
      ("wrap top", app Ir.Or [ name "x"; name "y" ], Qcalc.Varies);
    ]
  in
  List.iter (fun (label, body, expected) ->
      Alcotest.(check string) label (result_string expected) (result_string (Qcalc.classify body)))
    cases

let test_qcalc_spines () =
  Alcotest.(check bool) "spine and refused" true
    (match Qcalc.classify (app Ir.And [ unknown "spine"; name "x" ]) with Qcalc.Refused _ -> true | _ -> false);
  Alcotest.(check bool) "spine eq refused even when identical" true
    (match Qcalc.classify (app Ir.Eq [ unknown "spine"; unknown "spine" ]) with Qcalc.Refused _ -> true | _ -> false)

let gen_bool_expr =
  let leaf =
    QCheck.Gen.(oneof [ map boolean bool; map name (oneof [ return "x"; return "y"; return "z" ]) ])
  in
  let rec gen_expr depth =
    if depth <= 0 then leaf
    else
      QCheck.Gen.oneof_weighted
        [
          (2, leaf);
          (1, QCheck.Gen.map boolean QCheck.Gen.bool);
          (2, QCheck.Gen.map (fun a -> app Ir.Not [ a ]) (gen_expr (depth - 1)));
          (3, QCheck.Gen.map2 (fun a b -> app Ir.And [ a; b ]) (gen_expr (depth - 1)) (gen_expr (depth - 1)));
          (3, QCheck.Gen.map2 (fun a b -> app Ir.Or [ a; b ]) (gen_expr (depth - 1)) (gen_expr (depth - 1)));
          (2, QCheck.Gen.map2 (fun a b -> app Ir.Implies [ a; b ]) (gen_expr (depth - 1)) (gen_expr (depth - 1)));
          (2, QCheck.Gen.map2 (fun a b -> app Ir.Iff [ a; b ]) (gen_expr (depth - 1)) (gen_expr (depth - 1)));
          (1, QCheck.Gen.map2 (fun a b -> app Ir.Eq [ a; b ]) (gen_expr (depth - 1)) (gen_expr (depth - 1)));
          (1, QCheck.Gen.map2 (fun a b -> app Ir.Neq [ a; b ]) (gen_expr (depth - 1)) (gen_expr (depth - 1)));
        ]
  in
  QCheck.Gen.(int_range 0 3 >>= fun depth -> gen_expr depth)

let rec eval_concrete env (e : Ir.expr) =
  match e with
  | Ir.Bool { value; _ } -> value
  | Ir.Name { name; _ } -> (
      match List.assoc_opt name env with
      | Some v -> v
      | None -> failf "unbound variable %s in concrete evaluator" name)
  | Ir.App { opcode = Ir.And; args; _ } -> List.for_all (eval_concrete env) args
  | Ir.App { opcode = Ir.Or; args; _ } -> List.exists (eval_concrete env) args
  | Ir.App { opcode = Ir.Not; args = [ a ]; _ } -> not (eval_concrete env a)
  | Ir.App { opcode = Ir.Implies; args = [ a; b ]; _ } ->
      (not (eval_concrete env a)) || eval_concrete env b
  | Ir.App { opcode = Ir.Iff; args = [ a; b ]; _ } ->
      eval_concrete env a = eval_concrete env b
  | Ir.App { opcode = Ir.Eq; args = [ a; b ]; _ } ->
      eval_concrete env a = eval_concrete env b
  | Ir.App { opcode = Ir.Neq; args = [ a; b ]; _ } ->
      eval_concrete env a <> eval_concrete env b
  | _ -> failf "concrete evaluator met an unsupported node"

let assignments vars =
  let rec go = function
    | [] -> [ [] ]
    | v :: rest ->
        List.concat_map
          (fun tail -> [ (v, true) :: tail; (v, false) :: tail ])
          (go rest)
  in
  go vars

let generated_vars = [ "x"; "y"; "z" ]

let prop_exhaustive =
  QCheck.Test.make ~count:300 ~name:"qcalc i_exhaustive: no refusal on modelled bodies"
    QCheck.(make ~print:Qcalc.canonical_string gen_bool_expr)
    (fun e -> match Qcalc.classify e with Qcalc.Refused _ -> false | _ -> true)

let prop_sound_true =
  QCheck.Test.make ~count:300 ~name:"qcalc i_sound_true: const-true is true everywhere"
    QCheck.(make ~print:Qcalc.canonical_string gen_bool_expr)
    (fun e ->
      match Qcalc.classify e with
      | Qcalc.Const_true ->
          List.for_all (fun env -> eval_concrete env e) (assignments generated_vars)
      | _ -> true)

let prop_sound_false =
  QCheck.Test.make ~count:300 ~name:"qcalc i_sound_false: const-false is false everywhere"
    QCheck.(make ~print:Qcalc.canonical_string gen_bool_expr)
    (fun e ->
      match Qcalc.classify e with
      | Qcalc.Const_false ->
          List.for_all (fun env -> not (eval_concrete env e)) (assignments generated_vars)
      | _ -> true)

let prop_refuse =
  QCheck.Test.make ~count:100 ~name:"qcalc i_refuse_unknown: a spine is never a pass"
    QCheck.(make ~print:Qcalc.canonical_string gen_bool_expr)
    (fun e ->
      match Qcalc.classify (app Ir.And [ e; unknown "spine" ]) with
      | Qcalc.Refused _ -> true
      | _ -> false)

let prop_eq_identity =
  QCheck.Test.make ~count:200 ~name:"qcalc i_eq_identity: eq(P,P) is const-true"
    QCheck.(make ~print:Qcalc.canonical_string gen_bool_expr)
    (fun e -> Qcalc.classify (app Ir.Eq [ e; e ]) = Qcalc.Const_true)

let prop_eq_distinct =
  QCheck.Test.make ~count:200 ~name:"qcalc i_eq_identity: eq(P,Q) distinct varies"
    QCheck.(pair QCheck.(make ~print:Qcalc.canonical_string gen_bool_expr) QCheck.(make ~print:Qcalc.canonical_string gen_bool_expr))
    (fun (a, b) ->
      if Qcalc.canonical_string a = Qcalc.canonical_string b then true
      else match Qcalc.classify (app Ir.Eq [ a; b ]) with Qcalc.Varies -> true | _ -> false)

(* ---------- rundisc ---------- *)

let test_rundisc_table () =
  let facts = Run_disc.all_facts () in
  Alcotest.(check int) "48 fact combinations" 48 (List.length facts);
  List.iter
    (fun f ->
      let outcomes =
        [ Run_disc.Passed; Run_disc.Failed; Run_disc.Did_not_run ]
        |> List.filter (fun o -> o = Run_disc.classify f)
      in
      Alcotest.(check int) "exactly one classification" 1 (List.length outcomes);
      (match Run_disc.classify f with
      | Run_disc.Passed ->
          Alcotest.(check bool) "passed needs rc zero" true (f.Run_disc.rc = Run_disc.Zero);
          Alcotest.(check bool) "passed needs success summary" true f.Run_disc.success_summary;
          Alcotest.(check bool) "passed needs non-empty output" false f.Run_disc.empty_output;
          Alcotest.(check bool) "passed is not a timeout" false f.Run_disc.timed_out
      | Run_disc.Failed ->
          Alcotest.(check bool) "failed needs rc nonzero" true (f.Run_disc.rc = Run_disc.Nonzero);
          Alcotest.(check bool) "failed needs failure summary" true f.Run_disc.failure_summary
      | Run_disc.Did_not_run -> ());
      if f.Run_disc.rc = Run_disc.Zero && f.Run_disc.empty_output then
        Alcotest.(check bool) "masked crash never passes" false
          (Run_disc.classify f = Run_disc.Passed);
      if f.Run_disc.timed_out then
        Alcotest.(check bool) "timeout is did-not-run" true
          (Run_disc.classify f = Run_disc.Did_not_run);
      Alcotest.(check bool) "verdict iff failed" true
        (Run_disc.verdict f = (Run_disc.classify f = Run_disc.Failed)))
    facts

let prop_rundisc =
  QCheck.Test.make ~count:500 ~name:"rundisc i_passed_requires_proof / i_failed_requires_proof / i_no_verdict / i_timeout: three-state invariants over the fact domain"
    QCheck.(map (fun i -> List.nth (Run_disc.all_facts ()) i) (int_range 0 47))
    (fun f ->
      let outcome = Run_disc.classify f in
      let passed_ok =
        outcome <> Run_disc.Passed
        || (f.Run_disc.rc = Run_disc.Zero && f.Run_disc.success_summary
           && (not f.Run_disc.empty_output) && not f.Run_disc.timed_out)
      in
      let failed_ok =
        outcome <> Run_disc.Failed
        || (f.Run_disc.rc = Run_disc.Nonzero && f.Run_disc.failure_summary
           && not f.Run_disc.empty_output)
      in
      let timeout_ok = (not f.Run_disc.timed_out) || outcome = Run_disc.Did_not_run in
      let verdict_ok = Run_disc.verdict f = (outcome = Run_disc.Failed) in
      passed_ok && failed_ok && timeout_ok && verdict_ok)

let mk_facts rc timed_out success failure empty =
  Run_disc.
    {
      rc;
      timed_out;
      success_summary = success;
      failure_summary = failure;
      empty_output = empty;
    }

let test_init_verdict_cases () =
  let pass = mk_facts Run_disc.Zero false true false false in
  let fail = mk_facts Run_disc.Nonzero false false true false in
  let string_of = Run_disc.string_of_evidence in
  Alcotest.(check string) "rust pass is evidence" "passed"
    (string_of (Run_disc.init_verdict "rust" pass));
  Alcotest.(check string) "typescript pass is not evidence" "not-evidence"
    (string_of (Run_disc.init_verdict "typescript" pass));
  Alcotest.(check string) "rust error is failed" "failed"
    (string_of (Run_disc.init_verdict "rust" fail));
  Alcotest.(check string) "typescript error is failed" "failed"
    (string_of (Run_disc.init_verdict "typescript" fail));
  Alcotest.(check string) "unpinned is not evidence" "not-evidence"
    (string_of (Run_disc.init_verdict "" pass))

let prop_init_evidence =
  QCheck.Test.make ~count:500
    ~name:"rundisc i_init_pass_requires_rust / i_ts_pass_not_evidence / i_init_error_both / i_unpinned_not_evidence: backend x facts"
    QCheck.(pair (int_range 0 2) (int_range 0 47))
    (fun (b, i) ->
      let backend = List.nth [ "rust"; "typescript"; "" ] b in
      let f = List.nth (Run_disc.all_facts ()) i in
      let verdict = Run_disc.init_verdict backend f in
      let classified = Run_disc.classify f in
      let pass_requires_rust =
        match verdict with
        | Run_disc.Evidence Run_disc.Passed -> backend = "rust"
        | _ -> true
      in
      let ts_pass_not_evidence =
        not
          (backend = "typescript" && classified = Run_disc.Passed
          && verdict = Run_disc.Evidence Run_disc.Passed)
      in
      let error_both =
        classified <> Run_disc.Failed
        || (backend <> "rust" && backend <> "typescript")
        || verdict = Run_disc.Evidence Run_disc.Failed
      in
      let unpinned = backend <> "" || verdict = Run_disc.Not_evidence in
      pass_requires_rust && ts_pass_not_evidence && error_both && unpinned)

(* ---------- runner parsers ---------- *)

let test_runner_witness_parse () =
  let text =
    "[ok] No violation found (25ms at 200 traces/second).\nWitnesses:\n\
     bound was witnessed in 5 trace(s) out of 5 explored (100.00%)\n\
     hasRole was witnessed in 0 trace(s) out of 5 explored (0.00%)"
  in
  Alcotest.(check (list (triple string int int)))
    "witness counts"
    [ ("bound", 5, 5); ("hasRole", 0, 5) ]
    (Runner.parse_witness_counts text)

let test_runner_state_parse () =
  let text =
    "An example execution:\n\n[State 0] { mbt::actionTaken: \"init\", x: 0 }\n\n\
     [State 1]\n{\n  mbt::actionTaken: \"advance\",\n  x: 1\n}\n\n\
     [violation] Found an issue\n"
  in
  let states = Runner.parse_states text in
  Alcotest.(check int) "two states" 2 (List.length states);
  let last = List.nth states 1 in
  Alcotest.(check int) "last index" 1 (fst last);
  Alcotest.(check (option string)) "action attributed" (Some "advance")
    (Runner.action_of_state (snd last));
  check_has_substring "multi-line state body" "x: 1" (snd last)

(* A Sys_error reason names the evidence by role, not by
   the per-run temp path. Two unreadable files with identical content must
   produce byte-equal reasons; the errno text survives. *)
let test_runner_sys_error_path_independent () =
  let make name =
  let path = Filename.temp_file name ".itf.json" in
  let oc = open_out path in
  output_string oc {|{"states": [{}]}|};
  close_out oc;
  Unix.chmod path 0o000;
  path
  in
  let a = make "quint-audit-itf-a" and b = make "quint-audit-itf-b" in
  Fun.protect
  ~finally:(fun () ->
    List.iter
      (fun p ->
        (try Unix.chmod p 0o600 with _ -> ());
        try Sys.remove p with _ -> ())
      [ a; b ])
  (fun () ->
    let readable p =
      try
        let ic = open_in_bin p in
        close_in ic;
        true
      with Sys_error _ -> false
    in
    if readable a || readable b then Alcotest.skip ()
    else
      let reason p =
        match Runner.itf_trace p with
        | Error reason -> reason
        | Ok _ -> failf "unreadable file decoded unexpectedly"
      in
      let first = reason a and second = reason b in
      Alcotest.(check string) "Sys_error reason is byte-equal unmasked" first
        second;
      check_has_substring "reason keeps the errno text" "Permission denied"
        first)

(* ---------- checks ---------- *)

let check_clean check fixture =
  let findings = findings_for check (decode_fixture fixture) in
  Alcotest.(check int) (fixture ^ " passes " ^ Finding.string_of_check check) 0
    (List.length findings)

let test_ql001 () =
  let findings = findings_for Finding.QL001 (decode_fixture "ql001_thin") in
  Alcotest.(check bool) "has inline logic" true
    (List.exists (fun f -> has_substring f.Finding.message "inline business logic") findings);
  Alcotest.(check bool) "has no-op fallback" true
    (List.exists (fun f -> has_substring f.Finding.message "no-op fallback") findings);
  Alcotest.(check bool) "has state-reading call" true
    (List.exists (fun f -> has_substring f.Finding.message "state-reading def") findings);
  Alcotest.(check int) "three QL001 findings" 3 (List.length findings);
  check_clean Finding.QL001 "ql001_clean"

let test_ql002 () =
  let findings = findings_for Finding.QL002 (decode_fixture "ql002_strings") in
  Alcotest.(check int) "three raw strings" 3 (List.length findings);
  Alcotest.(check bool) "names the literal" true
    (List.exists (fun f -> has_substring f.Finding.message "\"leader\"") findings);
  check_clean Finding.QL002 "ql002_clean"

let test_ql002_field () =
  let findings = findings_for Finding.QL002 (decode_fixture "ql002_field") in
  Alcotest.(check int) "one real string" 1 (List.length findings);
  check_has_substring "names the real literal" "\"leader\"" (List.hd findings).Finding.message;
  check_clean Finding.QL002 "ql002_field_clean"

let test_ql003 () =
  let findings = findings_for Finding.QL003 (decode_fixture "ql003_grouping") in
  Alcotest.(check int) "one candidate group" 1 (List.length findings);
  let message = (List.hd findings).Finding.message in
  check_has_substring "lists a" "a" message;
  check_has_substring "lists b" "b" message;
  Alcotest.(check bool) "warn only" true
    ((List.hd findings).Finding.severity = Finding.Warn);
  (match (List.hd findings).Finding.suggestion with
  | Some s -> check_has_substring "composition blind spot" "helper action" s
  | None -> failf "grouping has no suggestion");
  check_clean Finding.QL003 "ql003_clean"

let test_ql006 () =
  let findings = findings_for Finding.QL006 (decode_fixture "ql006_invariants") in
  Alcotest.(check int) "one fail" 1 (count_severity Finding.Fail findings);
  Alcotest.(check int) "one warn" 1 (count_severity Finding.Warn findings);
  Alcotest.(check bool) "literal fails" true
    (List.exists
       (fun f -> f.Finding.severity = Finding.Fail && has_substring f.Finding.message "no state variable")
       findings);
  Alcotest.(check bool) "premise warns" true
    (List.exists
       (fun f -> f.Finding.severity = Finding.Warn && has_substring f.Finding.message "constants")
       findings);
  check_clean Finding.QL006 "ql006_clean"

let test_ql006_chain () =
  let findings = findings_for Finding.QL006 (decode_fixture "ql006_chain") in
  Alcotest.(check int) "val chain has no findings" 0 (List.length findings);
  check_clean Finding.QL006 "ql006_chain_clean"

(* A val whose state path runs through an opaque non-pure def
   must warn as an unanalysed dependency, never claim const-only. This
   fixture's original subjects are non-propositions, so they are silent;
   the lattice claim is carried by the bool-typed comparison control below. *)
let test_ql006_opaque_def () =
  let findings = findings_for Finding.QL006 (decode_fixture "ql006_opaque_def") in
  Alcotest.(check int) "non-proposition subjects are silent" 0
    (List.length findings)

(* The negative control. A bool-typed proposition whose
   state path runs through an opaque non-pure def still warns as an unanalysed
   dependency, never claims const-only. *)
let test_ql006_opaque_def_control () =
  let findings =
    findings_for Finding.QL006 (decode_fixture "ql006_opaque_control")
  in
  Alcotest.(check int) "one finding" 1 (List.length findings);
  Alcotest.(check int) "it is a warn" 1 (count_severity Finding.Warn findings);
  Alcotest.(check int) "no const-only claim" 0
    (List.length
       (List.filter
          (fun f -> has_substring f.Finding.message "only constants")
          findings));
  List.iter
    (fun f ->
      check_has_substring "unanalysed dependency" "unanalysed" f.Finding.message;
      check_has_substring "names the opaque def" "stateDef" f.Finding.message)
    findings

(* QL006 traverses pure vals; a val built on a state-reading pure
   val is not falsely failed as a tautology. The pure val is
   itself a reporting subject, so its literal-comparison body is the one warn;
   the dependent val still has no finding. *)
let test_ql006_pure_chain () =
  let findings = findings_for Finding.QL006 (decode_fixture "ql006_pure_chain") in
  Alcotest.(check int) "one literal-bound warn" 1 (List.length findings);
  Alcotest.(check int) "the warn is a warn" 1
    (count_severity Finding.Warn findings);
  check_has_substring "literal bound named" "literal bound"
    (List.hd findings).Finding.message

(* Pure val and nullary pure def declarations are QL006/QP001 reporting
   subjects. A parameterised pure def is a function, not a property, and stays
   a dependency node only (the fixture carries `inc(v)` as the control). *)
let test_ql006_pure_tautology () =
  let findings =
    findings_for Finding.QL006 (decode_fixture "ql006_pure_tautology")
  in
  Alcotest.(check int) "two pure tautology fails" 2
    (count_severity Finding.Fail findings);
  Alcotest.(check int) "no non-fail findings" 2 (List.length findings);
  List.iter
    (fun f ->
      check_has_substring "tautology class" "tautology over state"
        f.Finding.message)
    findings

(* A declaration that is not a proposition is not a QL006
   subject, whatever its qualifier: an untyped literal set, a set constant,
   a typed string constant. *)
let test_ql006_subject_constants () =
  let findings =
    findings_for Finding.QL006 (decode_fixture "ql006_subject_constants")
  in
  Alcotest.(check int) "no QL006 finding for a non-proposition" 0
    (List.length findings)

(* The subject set still admits genuine boolean
   tautologies - a declared bool, an Eq proposition, a Not proposition. *)
let test_ql006_subject_propositions () =
  let findings =
    findings_for Finding.QL006 (decode_fixture "ql006_subject_propositions")
  in
  Alcotest.(check int) "three tautology fails" 3
    (count_severity Finding.Fail findings);
  Alcotest.(check int) "no other findings" 3 (List.length findings);
  List.iter
    (fun f ->
      check_has_substring "tautology class" "tautology over state"
        f.Finding.message)
    findings

(* Two real corpus shapes: an int constant that the subject-set rule
   leaves silent, and an `and` proposition that stays a legitimate
   tautology fail. *)
let test_ql006_corpus_shapes () =
  let findings =
    findings_for Finding.QL006 (decode_fixture "ql006_corpus_shapes")
  in
  Alcotest.(check int) "only the proposition is reported" 1
    (List.length findings);
  Alcotest.(check int) "the proposition is a fail" 1
    (count_severity Finding.Fail findings);
  check_has_substring "tautology class" "tautology over state"
    (List.hd findings).Finding.message

(* A bool-typed declaration whose body is a call is in the
   subject set by its type but QL006 cannot analyse it. The check must name the
   refusal as an Info rather than leave the declaration silent. *)
let test_ql006_call_refusal () =
  let findings =
    findings_for Finding.QL006 (decode_fixture "ql006_call_refusal")
  in
  Alcotest.(check int) "one refusal" 1 (List.length findings);
  Alcotest.(check int) "the refusal is an info" 1
    (count_severity Finding.Info findings);
  check_has_substring "refusal text"
    "invariant body is a call; QL006 did not evaluate it"
    (List.hd findings).Finding.message

(* A declaration whose own parameter shares a module var's
   name. Unseeded, the parameter is counted as a module reference and the body
   reads as a literal bound; seeded, the declaration references no state and is
   a tautology. The cell pins the seeded result. *)
let test_ql006_param_seed () =
  let findings = findings_for Finding.QL006 (decode_fixture "ql006_param_seed") in
  Alcotest.(check int) "one finding" 1 (List.length findings);
  Alcotest.(check int) "the parameter is not a module reference" 1
    (count_severity Finding.Fail findings);
  check_has_substring "tautology class" "tautology over state"
    (List.hd findings).Finding.message

let test_qp001_pure_tautology () =
  let findings =
    findings_for Finding.QP001 (decode_fixture "ql006_pure_tautology")
  in
  Alcotest.(check int) "two constant-true fails" 2
    (count_severity Finding.Fail findings);
  List.iter
    (fun f ->
      check_has_substring "constant true named" "constant true"
        f.Finding.message)
    findings

(* The nullary guard is scoped to the shape it was written
   for. A parameterised plain val, a parameterised Temporal, and a pure def
   whose parameter is unused are reporting subjects. *)
let test_ql006_parameterised_subjects () =
  let findings =
    findings_for Finding.QL006 (decode_fixture "ql006_param_subjects")
  in
  Alcotest.(check int) "parameterised val is reported" 1
    (count_severity Finding.Fail findings);
  Alcotest.(check int) "nothing else is reported" 1 (List.length findings);
  check_has_substring "tautology class" "tautology over state"
    (List.hd findings).Finding.message

let test_qp001_parameterised_subjects () =
  let findings =
    findings_for Finding.QP001 (decode_fixture "ql006_param_subjects")
  in
  Alcotest.(check int) "parameterised val and temporal are reported" 2
    (count_severity Finding.Fail findings);
  List.iter
    (fun f ->
      check_has_substring "constant false named" "constant false"
        f.Finding.message)
    findings

(* The bound itself: a parameterised pure def whose parameter is referenced in
   the body is a function, not a property. The parameter reads as a free name,
   which the tautology classifier would count as no state reference and report
   as "references no state variable" - a false tautology. That shape stays
   excluded; an unused parameter does not change the classification, so it is
   reported. *)
let test_ql006_pure_parameter_bound () =
  let findings =
    findings_for Finding.QL006 (decode_fixture "ql006_pure_param_bound")
  in
  Alcotest.(check int) "only the unused-parameter pure def is reported" 1
    (List.length findings);
  check_has_substring "tautology class" "tautology over state"
    (List.hd findings).Finding.message

let test_qp001_pure_parameter_bound () =
  let findings =
    findings_for Finding.QP001 (decode_fixture "ql006_pure_param_bound")
  in
  Alcotest.(check int) "only the unused-parameter pure def is reported" 1
    (List.length findings);
  check_has_substring "constant true named" "constant true"
    (List.hd findings).Finding.message

(* QP002 keeps its own finding on a state-reading pure declaration; the
   QL006 subjects in this fixture are constants, so the QL006 half is
   the silence on `2 + 1`; the bool tautology control below carries the
   teeth. *)
let test_pure_state_reading_single_report () =
  let program = decode_fixture "qp002_pureval" in
  let qp002 = findings_for Finding.QP002 program in
  Alcotest.(check int) "QP002 reports the state-reading pure val once" 1
    (List.length qp002);
  check_has_substring "QP002 names the declaration" "`bad`"
    (List.hd qp002).Finding.message;
  let ql006 = findings_for Finding.QL006 program in
  Alcotest.(check int) "QL006 is silent on the constant pure val" 0
    (List.length ql006)

(* The negative control. A bool-typed genuine tautology
   still produces a QL006 fail. *)
let test_pure_state_reading_bool_control () =
  let findings =
    findings_for Finding.QL006 (decode_fixture "ql006_bool_tautology")
  in
  Alcotest.(check int) "one finding" 1 (List.length findings);
  Alcotest.(check int) "it is a fail" 1 (count_severity Finding.Fail findings);
  check_has_substring "tautology class" "tautology over state"
    (List.hd findings).Finding.message

let test_ql008 () =
  let findings = findings_for Finding.QL008 (decode_fixture "ql008_vars") in
  Alcotest.(check int) "one gap" 1 (List.length findings);
  let f = List.hd findings in
  check_has_substring "names y" "`y`" f.Finding.message;
  (* The walk follows helper-action calls, so the direct-only caveat
     is removed from the headline, and the composition note is gone from
     the suggestion, which is now the stutter only. *)
  Alcotest.(check bool) "direct-only caveat removed" false
    (has_substring f.Finding.message "direct assignments only");
  (match f.Finding.suggestion with
  | Some s -> Alcotest.(check string) "stutter suggestion" "y' = y." s
  | None -> failf "gap has no suggestion");
  check_clean Finding.QL008 "ql008_clean"

(* Assignment coverage follows calls to module actions, recursively. The
   cycle fixture's IR is mutated directly: quint parse refuses cyclic
   declarations with QNT099, so a cycle can only be exercised at the IR
   layer. *)
let test_ql008_helper_all () = check_clean Finding.QL008 "ql008_helper_all"

let test_ql008_helper_partial () =
  let findings =
    findings_for Finding.QL008 (decode_fixture "ql008_helper_partial")
  in
  Alcotest.(check int) "the helper's own stutter plus the wrapper's gap" 2
    (List.length findings);
  List.iter
    (fun f ->
      check_has_substring "names the unassigned var" "`b`" f.Finding.message;
      Alcotest.(check bool) "does not name the assigned var" false
        (has_substring f.Finding.message "`a`"))
    findings;
  Alcotest.(check int) "the wrapper is credited for `a`" 1
    (List.length
       (List.filter
          (fun f -> has_substring f.Finding.message "action wrapper")
          findings))

let test_ql008_helper_chain () = check_clean Finding.QL008 "ql008_helper_chain"

let test_ql008_helper_cycle () =
  let findings =
    findings_for Finding.QL008 (decode_fixture "ql008_helper_cycle")
  in
  Alcotest.(check int) "one cycle finding" 1 (List.length findings);
  let f = List.hd findings in
  Alcotest.(check bool) "info severity" true (f.Finding.severity = Finding.Info);
  check_has_substring "names ping" "`ping`" f.Finding.message;
  check_has_substring "names pong" "`pong`" f.Finding.message;
  Alcotest.(check int) "no census is claimed through the cycle" 0
    (count_severity Finding.Warn findings)

let test_ql008_stutter () =
  let findings = findings_for Finding.QL008 (decode_fixture "ql008_stutter") in
  Alcotest.(check int) "one stutter warning" 1 (List.length findings);
  let f = List.hd findings in
  Alcotest.(check bool) "warn severity" true
    (f.Finding.severity = Finding.Warn);
  check_has_substring "names b" "`b`" f.Finding.message;
  (match f.Finding.suggestion with
  | Some s ->
      Alcotest.(check string) "suggestion unchanged"
        "b' = b."
        s
  | None -> failf "stutter has no suggestion")

let test_ql008_pure_def () =
  let findings = findings_for Finding.QL008 (decode_fixture "ql008_pure_def") in
  Alcotest.(check int) "a pure def contributes no credit" 2
    (List.length findings);
  List.iter
    (fun f ->
      Alcotest.(check bool) "warn severity" true
        (f.Finding.severity = Finding.Warn);
      check_has_substring "the called pure def is not credited" "action wrapper"
        f.Finding.message)
    findings;
  Alcotest.(check bool) "names a" true
    (List.exists (fun f -> has_substring f.Finding.message "`a`") findings);
  Alcotest.(check bool) "names b" true
    (List.exists (fun f -> has_substring f.Finding.message "`b`") findings)

let test_ql009 () =
  let incomplete = findings_for Finding.QL009 (decode_fixture "ql009_step") in
  Alcotest.(check int) "one missing action" 1 (List.length incomplete);
  check_has_substring "names b" "b" (List.hd incomplete).Finding.message;
  Alcotest.(check bool) "headline drops the direct-only caveat" false
    (has_substring (List.hd incomplete).Finding.message "not visible");
  (match (List.hd incomplete).Finding.suggestion with
  | Some s ->
      Alcotest.(check string) "suggestion is the bare instruction"
        "add b to the step branches." s
  | None -> failf "omission has no suggestion");
  let missing = findings_for Finding.QL009 (decode_fixture "ql009_missing") in
  Alcotest.(check int) "missing step" 1 (List.length missing);
  check_has_substring "says no step" "no `step`" (List.hd missing).Finding.message;
  check_clean Finding.QL009 "ql009_clean"

(* Reachability and thinness follow calls to module actions. *)
let test_ql009_reach_helper () =
  check_clean Finding.QL009 "ql009_helper_reach"

let test_ql009_orphan () =
  let findings = findings_for Finding.QL009 (decode_fixture "ql009_orphan") in
  Alcotest.(check int) "one genuinely unreachable action" 1
    (List.length findings);
  check_has_substring "names the orphan" "action b is not visibly reachable"
    (List.hd findings).Finding.message

let test_ql009_cycle () = check_clean Finding.QL009 "ql009_cycle"

(* The step shape test is Let-aware. A `nondet` prefix decodes
   as a Let and the any composition sits under the binder: without the
   Let-aware walk, the shape warn would fire on a type-correct spec. *)
let test_ql009_let_step () =
  let findings = findings_for Finding.QL009 (decode_fixture "ql009_let_step") in
  Alcotest.(check int) "a let-wrapped any composition is complete" 0
    (List.length findings)

(* An unreadable body is an Info coverage gap, never a
   classification. The IR is doctored in the decoder mirror style: the body's
   kind becomes one the decoder preserves as Unknown, node id and span
   unchanged. *)
let unknown_body id = `Assoc [ ("kind", `String "futureSpine"); ("id", `Int id) ]

let doctor_decl_body name ir =
  replace_declaration name
    (fun d ->
      let id =
        match assoc_field "id" (assoc_field "expr" d) with
        | `Int i -> i
        | _ -> failf "doctored declaration body id is not an int"
      in
      replace_field "expr" (unknown_body id) d)
    ir

let test_ql001_unknown_body () =
  let raw = raw_fixture "ql001_thin_leaf" in
  let program =
    expect_decode "doctored QL001 body"
      (decode_raw { raw with ir = doctor_decl_body "advance" raw.ir })
  in
  let findings = findings_for Finding.QL001 program in
  Alcotest.(check int) "no thin warn over an unreadable body" 0
    (count_severity Finding.Warn findings);
  Alcotest.(check int) "one info coverage gap" 1 (List.length findings);
  let f = List.hd findings in
  Alcotest.(check bool) "info severity" true
    (f.Finding.severity = Finding.Info);
  check_has_substring "names the gap" "thinness coverage for `advance` skipped"
    f.Finding.message

let test_ql009_unknown_step () =
  let raw = raw_fixture "ql009_step" in
  let program =
    expect_decode "doctored step body"
      (decode_raw { raw with ir = doctor_decl_body "step" raw.ir })
  in
  let findings = findings_for Finding.QL009 program in
  Alcotest.(check int) "no hard classification over an unreadable step" 0
    (count_severity Finding.Warn findings);
  Alcotest.(check int) "one info coverage gap" 1 (List.length findings);
  let f = List.hd findings in
  Alcotest.(check bool) "info severity" true
    (f.Finding.severity = Finding.Info);
  check_has_substring "says coverage is incomplete" "coverage is incomplete"
    f.Finding.message

let thin_messages fixture =
  findings_for Finding.QL001 (decode_fixture fixture)
  |> List.filter (fun f -> has_substring f.Finding.message "not an all/any composition")

let test_ql001_wrapper () =
  Alcotest.(check int) "wrapper call is not thin" 0
    (List.length (thin_messages "ql001_wrapper"))

let test_ql001_thin_leaf () =
  Alcotest.(check int) "genuinely thin action still warns" 1
    (List.length (thin_messages "ql001_thin_leaf"))

let test_ql001_pure_call () =
  Alcotest.(check int) "pure def callee gets no credit" 1
    (List.length (thin_messages "ql001_pure_call"))

let test_qp001 () =
  let findings = findings_for Finding.QP001 (decode_fixture "qp001_literal_false") in
  Alcotest.(check int) "two fails" 2 (count_severity Finding.Fail findings);
  Alcotest.(check bool) "const-false named" true
    (List.exists (fun f -> has_substring f.Finding.message "constant false") findings);
  Alcotest.(check bool) "const-true named" true
    (List.exists (fun f -> has_substring f.Finding.message "constant true") findings);
  check_clean Finding.QP001 "qp001_clean"

let test_qp002 () =
  let findings = findings_for Finding.QP002 (decode_fixture "qp002_puredef") in
  Alcotest.(check int) "one fail" 1 (List.length findings);
  Alcotest.(check bool) "fail severity" true ((List.hd findings).Finding.severity = Finding.Fail);
  check_has_substring "names x" "`x`" (List.hd findings).Finding.message;
  Alcotest.(check bool) "no QNT200 attribution" false
    (has_substring (List.hd findings).Finding.message "QNT200");
  check_clean Finding.QP002 "qp002_clean"

let test_qp002_pureval () =
  let findings = findings_for Finding.QP002 (decode_fixture "qp002_pureval") in
  Alcotest.(check int) "one fail" 1 (List.length findings);
  let f = List.hd findings in
  Alcotest.(check bool) "fail severity" true (f.Finding.severity = Finding.Fail);
  check_has_substring "names bad" "`bad`" f.Finding.message;
  check_has_substring "names x" "`x`" f.Finding.message;
  check_has_substring "no QNT200 attribution" "pure val" f.Finding.message;
  check_clean Finding.QP002 "qp002_pureval_clean"

(* The declaration's own parameters are bound before the `vars`
   test: a parameter that shares a module var's name is not a state read,
   a shadowed var still is, and over-seeding and the `let` binder path
   stay unchanged. *)
let test_qp002_param_shadow () = check_clean Finding.QP002 "qp002_param_shadow"

let test_qp002_param_renamed () =
  check_clean Finding.QP002 "qp002_param_renamed"

let test_qp002_genuine_read () =
  let findings =
    findings_for Finding.QP002 (decode_fixture "qp002_genuine_read")
  in
  Alcotest.(check int) "one fail" 1 (List.length findings);
  Alcotest.(check bool) "fail severity" true
    ((List.hd findings).Finding.severity = Finding.Fail);
  check_has_substring "names pl" "`pl`" (List.hd findings).Finding.message

let test_qp002_let_shadow () = check_clean Finding.QP002 "qp002_let_shadow"

let test_clean_spec () =
  let findings = run_checks (decode_fixture "clean") in
  Alcotest.(check int) "clean fixture has no findings at all" 0 (List.length findings)

(* ---------- report ---------- *)

let program_findings program =
  List.concat_map
    (fun (m : Ir.module_) ->
      let symbols = Symbols.build ~resolution:program.Ir.resolution m in
      Checks.run_ir_checks Checks.{ program; module_ = m; symbols })
    program.Ir.modules

let report_of name threshold =
  let program = decode_fixture name in
  Report.make ~spec_path:(name ^ ".qnt") ~quint_version:"0.33.1"
    ~ir_sha256:"deadbeef" ~parse_ms:12 ~mode:"ir" ~threshold program
    (program_findings program)

let json_field name = function
  | `Assoc fs -> ( match List.assoc_opt name fs with Some v -> v | None -> failf "no JSON field %s" name)
  | _ -> failf "expected JSON object"

let status_of_check doc id =
  match json_field "checks" doc with
  | `List checks ->
      List.find_map
        (fun c ->
          if json_field "id" c = `String id then
            match json_field "status" c with `String s -> Some s | _ -> None
          else None)
        checks
  | _ -> failf "checks is not a list"

let test_report_human () =
  let report = report_of "ql006_invariants" `Fail in
  let human = Report.human report in
  List.iter
    (fun id -> check_has_substring ("row " ^ id) id human)
    [ "QL001"; "QL002"; "QL003"; "QL004"; "QL005"; "QL006"; "QL007"; "QL008"; "QL009"; "QL010"; "QL011"; "QP001"; "QP002" ];
  check_has_substring "skipped rows named" "skipped (requires run)" human;
  check_has_substring "deferred row named" "deferred" human;
  check_has_substring "module header" "module Ql006Invariants" human;
  check_has_substring "top issues" "Top issues" human;
  Alcotest.(check int) "fail threshold exit 1" 1 report.Report.exit_code

(* The human renderer carries Info text on every row that
   has an Info finding, not only a Pass row - the JSON carries it regardless. *)
let test_report_mixed_severity_info () =
  let program = decode_fixture "clean" in
  let module_name =
    match program.Ir.modules with
    | m :: _ -> m.Ir.module_name
    | [] -> failf "clean fixture has no modules"
  in
  let module_span =
    match program.Ir.modules with
    | m :: _ -> m.Ir.module_span
    | [] -> failf "clean fixture has no modules"
  in
  let finding severity message =
    {
      Finding.check = Finding.QL004;
      severity;
      module_name;
      source = "clean.qnt";
      location = module_span;
      message;
      suggestion = None;
    }
  in
  let findings =
    [
      finding Finding.Info
        "partial ITF evidence: analysed 1 of 5 sampled trace files (1 states)";
      finding Finding.Warn "action `b` was not exercised in 5 sampled traces";
    ]
  in
  let report =
    Report.make ~run_mode:true ~spec_path:"mixed.qnt" ~quint_version:"0.33.1"
      ~ir_sha256:"deadbeef" ~parse_ms:12 ~mode:"ir+run" ~threshold:`Fail program
      findings
  in
  let human = Report.human report in
  check_has_substring "warn row carries the Info message" "partial ITF evidence"
    human;
  check_has_substring "warn row still states the issue count" "issue(s)" human

let test_report_json () =
  let report = report_of "ql006_invariants" `Fail in
  let doc = Report.json report in
  let _ = json_field "tool" doc in
  let _ = json_field "spec" doc in
  let quint = json_field "quint" doc in
  Alcotest.(check string) "quint version" "0.33.1"
    (match json_field "version" quint with `String s -> s | _ -> failf "version not a string");
  let checks = match json_field "checks" doc with `List xs -> xs | _ -> failf "checks not a list" in
  Alcotest.(check int) "13 rows, one module" 13 (List.length checks);
  let statuses =
    List.map (fun c -> match json_field "status" c with `String s -> s | _ -> "") checks
  in
  Alcotest.(check bool) "QL005 deferred in words" true
    (List.exists (fun (c, s) -> s = "skipped" && json_field "id" c = `String "QL005") (List.combine checks statuses));
  let findings = match json_field "findings" doc with `List xs -> xs | _ -> failf "findings" in
  List.iter
    (fun f ->
      let _ = json_field "check" f in
      let _ = json_field "severity" f in
      let _ = json_field "module" f in
      let _ = json_field "start" f in
      let _ = json_field "end" f in
      let _ = json_field "message" f in
      let _ = json_field "suggestion" f in
      ())
    findings;
  let summary = json_field "summary" doc in
  (* Findings grouped by source, and the dedup accounting. *)
  let grouped =
    match json_field "sources" doc with
    | `List xs -> xs
    | _ -> failf "sources is not a list"
  in
  let group_source g =
    match json_field "source" g with
    | `String s -> s
    | _ -> failf "source group has no source string"
  in
  let group_findings g =
    match json_field "findings" g with
    | `List xs -> xs
    | _ -> failf "source group has no findings list"
  in
  let grouped_findings = List.concat_map group_findings grouped in
  Alcotest.(check int) "every finding is grouped exactly once"
    (List.length findings)
    (List.length grouped_findings);
  Alcotest.(check bool) "each group's findings carry the group's source" true
    (List.for_all
       (fun g ->
         List.for_all
           (fun j -> json_field "source" j = `String (group_source g))
           (group_findings g))
       grouped);
  let dedup = json_field "dedup" doc in
  let int_field name =
    match json_field name dedup with
    | `Int n -> n
    | _ -> failf "dedup.%s is not an integer" name
  in
  Alcotest.(check int) "dedup.reported matches the findings array"
    (List.length findings) (int_field "reported");
  Alcotest.(check int) "dedup accounting adds up"
    (int_field "emitted")
    (int_field "reported" + int_field "removed");
  (match json_field "fail" summary with `Int n -> Alcotest.(check bool) "summary fail > 0" true (n > 0) | _ -> failf "fail count")
  ;
  Alcotest.(check int) "exit field" 1 (match json_field "exit" doc with `Int n -> n | _ -> failf "exit")

(* Every finding names the source file its span belongs to.
   The fixture's orphan span is moved to a second source: the finding then
   carries the imported path in the record, the JSON and the human line. *)
let test_report_source_imported () =
  let raw = raw_fixture "ql009_step" in
  let key = entry_key raw.ir "b" in
  let map =
    raw.map |> add_source (imported_spec "imported_ok")
    |> set_span_source key 1
    |> set_span_end key 300
  in
  let program =
    expect_decode "imported finding span" (decode_raw { raw with map })
  in
  let findings = program_findings program in
  let ql009 =
    List.filter (fun f -> f.Finding.check = Finding.QL009) findings
  in
  Alcotest.(check int) "one QL009 finding" 1 (List.length ql009);
  Alcotest.(check string) "finding source is the imported file"
    "fixtures/specs/imported_ok.qnt" (List.hd ql009).Finding.source;
  let report =
    Report.make ~spec_path:"ql009_step.qnt" ~quint_version:"0.33.1"
      ~ir_sha256:"deadbeef" ~parse_ms:12 ~mode:"ir" ~threshold:`Fail program
      findings
  in
  let doc = Report.json report in
  let jsons =
    match json_field "findings" doc with
    | `List xs -> xs
    | _ -> failf "findings is not a list"
  in
  Alcotest.(check bool) "every JSON finding carries a source string" true
    (jsons <> []
    && List.for_all
         (fun j ->
           match json_field "source" j with
           | `String s -> s <> ""
           | _ -> false)
         jsons);
  Alcotest.(check string) "JSON names the imported file"
    "fixtures/specs/imported_ok.qnt"
    (match json_field "source" (List.hd jsons) with
    | `String s -> s
    | _ -> failf "source field is not a string");
  check_has_substring "human line names the imported file" "imported_ok.qnt"
    (Report.human report)

(* One finding per (check, severity, source, span-start,
   message). A definition reached through two import paths is analysed twice
   in the IR module list; the report emits its findings once, in a
   source/span/check order that does not depend on module iteration order. *)
let test_report_dedup_same_definition () =
  let program = decode_fixture "ql009_step" in
  let m = List.hd program.Ir.modules in
  let doubled = { program with Ir.modules = m :: program.Ir.modules } in
  let findings = program_findings doubled in
  Alcotest.(check bool) "the duplicated module emits every finding twice" true
    (List.length findings > 0 && List.length findings mod 2 = 0);
  let report =
    Report.make ~spec_path:"ql009_step.qnt" ~quint_version:"0.33.1"
      ~ir_sha256:"deadbeef" ~parse_ms:12 ~mode:"ir" ~threshold:`Fail doubled
      findings
  in
  Alcotest.(check int) "every finding reported once"
    (List.length findings / 2)
    (List.length report.Report.findings);
  Alcotest.(check int) "the pre-dedup emission count is carried"
    (List.length findings)
    report.Report.emitted;
  (* Order-independent: reversing the module iteration order gives the same
     reported list, byte for byte. *)
  let reversed = { program with Ir.modules = List.rev doubled.Ir.modules } in
  let report_reversed =
    Report.make ~spec_path:"ql009_step.qnt" ~quint_version:"0.33.1"
      ~ir_sha256:"deadbeef" ~parse_ms:12 ~mode:"ir" ~threshold:`Fail reversed
      (program_findings reversed)
  in
  Alcotest.(check string) "dedup does not depend on module order"
    (Yojson.Safe.to_string (json_field "findings" (Report.json report)))
    (Yojson.Safe.to_string (json_field "findings" (Report.json report_reversed)))

(* ---------- status vocabulary and the dedup seam pin ---------- *)

let ir_span start finish =
  {
    Ir.start_pos = { Ir.line = 0; column = start; index = start };
    end_pos = { Ir.line = 0; column = finish; index = finish };
  }

(* A module whose defining file is not the analysed spec gets no QL009
   finding. Its QL009 row is `skipped` with a scope reason in the JSON and in
   words in the human table, and summary.skipped counts it. The module span is
   moved to the imported fixture, so every other check still classifies the
   module and the report has one non-entry module. *)
let scoped_module_program () =
  let raw = raw_fixture "ql009_step" in
  let key = module_key raw.ir in
  let own_end = last_brace_offset "imported_ok" in
  let map =
    raw.map
    |> add_source (imported_spec "imported_ok")
    |> set_span_source key 1
    |> set_span_end key own_end
  in
  expect_decode "imported module" (decode_raw { raw with map })

let test_report_ql009_scope_skipped () =
  let program = scoped_module_program () in
  let findings = program_findings program in
  let report =
    Report.make ~spec_path:"ql009_step.qnt" ~quint_version:"0.33.1"
      ~ir_sha256:"deadbeef" ~parse_ms:12 ~mode:"ir" ~threshold:`Fail program
      findings
  in
  let doc = Report.json report in
  Alcotest.(check (option string)) "imported module QL009 is skipped"
    (Some "skipped") (status_of_check doc "QL009");
  let summary = json_field "summary" doc in
  Alcotest.(check int) "summary.skipped counts the scoped row" 6
    (match json_field "skipped" summary with
    | `Int n -> n
    | _ -> failf "skipped count is not an integer");
  check_has_substring "human row states the scope reason" "out of scope"
    (Report.human report)

(* Control: linting the helper directly keeps its QL009 row and its
   `warn` status; the scope skip is relative to the analysed spec. *)
let test_report_ql009_entry_keeps_warn () =
  let doc = Report.json (report_of "ql009_step" `Fail) in
  Alcotest.(check (option string)) "the entry module keeps its warn status"
    (Some "warn") (status_of_check doc "QL009")

(* Every serialised finding carries a start and an end. The location is
   total, so a module-level finding serialises the module span. *)
let test_report_findings_always_carry_spans () =
  let program = decode_fixture "clean" in
  let m = List.hd program.Ir.modules in
  let finding =
    {
      Finding.check = Finding.QL004;
      severity = Finding.Info;
      module_name = m.Ir.module_name;
      source = "clean.qnt";
      location = m.Ir.module_span;
      message = "coverage note";
      suggestion = None;
    }
  in
  let report =
    Report.make ~spec_path:"clean.qnt" ~quint_version:"0.33.1"
      ~ir_sha256:"deadbeef" ~parse_ms:12 ~mode:"ir" ~threshold:`Fail program
      [ finding ]
  in
  let jsons =
    match json_field "findings" (Report.json report) with
    | `List xs -> xs
    | _ -> failf "findings is not a list"
  in
  Alcotest.(check int) "the crafted finding serialises" 1 (List.length jsons);
  let is_position = function
    | `Assoc fs ->
        List.mem_assoc "line" fs && List.mem_assoc "col" fs
        && List.mem_assoc "index" fs
    | _ -> false
  in
  List.iter
    (fun j ->
      Alcotest.(check bool) "start is a position object" true
        (is_position (json_field "start" j));
      Alcotest.(check bool) "end is a position object" true
        (is_position (json_field "end" j)))
    jsons

(* Maintenance seam: if two findings share the dedup key, no third
   finding sorts strictly between them, and normalise collapses the key group
   and only it. Severity is a function of the check and message in production,
   so a row sharing the sort prefix shares the key. *)
let seam_finding ~module_name ~check ~severity ~message ~src ~start ~finish () =
  {
    Finding.check;
    severity;
    module_name;
    source = src;
    location = ir_span start finish;
    message;
    suggestion = None;
  }

let test_report_dedup_seam () =
  let key_group =
    [
      seam_finding ~module_name:"Alpha" ~check:Finding.QL001
        ~severity:Finding.Warn ~message:"same message" ~src:"x.qnt" ~start:10
        ~finish:20 ();
      seam_finding ~module_name:"Omega" ~check:Finding.QL001
        ~severity:Finding.Warn ~message:"same message" ~src:"x.qnt" ~start:10
        ~finish:25 ();
      seam_finding ~module_name:"Beta" ~check:Finding.QL001
        ~severity:Finding.Warn ~message:"same message" ~src:"x.qnt" ~start:10
        ~finish:30 ();
    ]
  in
  let outsiders =
    [
      (* before the group by message *)
      seam_finding ~module_name:"Alpha" ~check:Finding.QL001
        ~severity:Finding.Warn ~message:"aaa" ~src:"x.qnt" ~start:10 ~finish:20
        ();
      (* after the group by check id *)
      seam_finding ~module_name:"Alpha" ~check:Finding.QL002
        ~severity:Finding.Warn ~message:"same message" ~src:"x.qnt" ~start:10
        ~finish:20 ();
      (* before the group by source path *)
      seam_finding ~module_name:"Alpha" ~check:Finding.QL001
        ~severity:Finding.Warn ~message:"same message" ~src:"w.qnt" ~start:5
        ~finish:5 ();
    ]
  in
  let findings = key_group @ outsiders in
  let between a c b =
    Finding.compare_report_order a c < 0 && Finding.compare_report_order c b < 0
  in
  List.iter
    (fun a ->
      List.iter
        (fun b ->
          if Finding.same_finding a b then
            List.iter
              (fun c ->
                if (not (Finding.same_finding a c)) && between a c b then
                  failf "a distinct finding sorts inside the dedup key group")
              findings)
        findings)
    findings;
  let normalised = Finding.normalise findings in
  Alcotest.(check int) "one row per key plus the outsiders" 4
    (List.length normalised);
  let key_survivors =
    List.filter (fun f -> List.memq f normalised) key_group
  in
  Alcotest.(check int) "the key group collapses to one row" 1
    (List.length key_survivors);
  List.iter
    (fun f ->
      Alcotest.(check bool) "every outsider survives" true
        (List.memq f normalised))
    outsiders

let test_exit_codes_and_thresholds () =
  let clean = report_of "clean" `Fail in
  Alcotest.(check int) "clean exits 0" 0 clean.Report.exit_code;
  let warns = report_of "ql001_thin" `Fail in
  Alcotest.(check int) "warn-only exits 0 at fail threshold" 0 warns.Report.exit_code;
  let warns_strict = report_of "ql001_thin" `Warn in
  Alcotest.(check int) "warn trips the warn threshold" 1 warns_strict.Report.exit_code;
  let fail = report_of "qp001_literal_false" `Fail in
  Alcotest.(check int) "fail exits 1" 1 fail.Report.exit_code

let check_ids doc =
  match json_field "checks" doc with
  | `List checks ->
      List.map
        (fun c ->
          match json_field "id" c with
          | `String s -> s
          | _ -> failf "check id is not a string")
        checks
  | _ -> failf "checks is not a list"

(* The JSON checks array order is pinned, per module. *)
let test_report_check_order () =
  let doc = Report.json (report_of "ql006_invariants" `Fail) in
  let expected = List.map Finding.string_of_check Finding.all_checks in
  Alcotest.(check (list string)) "checks array order" expected (check_ids doc)

(* QP003 is defined-but-silent; no dedicated zombie can hide in a
   row count because the id is asserted absent by name. *)
let test_qp003_absent () =
  let program = decode_fixture "qp003_fwd" in
  let findings = run_checks program in
  Alcotest.(check int) "no QP003 finding" 0
    (List.length (List.filter (fun f -> f.Finding.check = Finding.QP003) findings));
  let doc = Report.json (report_of "qp003_fwd" `Fail) in
  Alcotest.(check bool) "no QP003 check row" false (List.mem "QP003" (check_ids doc));
  let report = report_of "qp003_fwd" `Fail in
  Alcotest.(check int) "fwd shape exits 0" 0 report.Report.exit_code

(* ---------- pipeline (requires quint) ---------- *)

let quint_available () =
  match Quint_parse.resolve ~quint:None with Ok _ -> true | Error _ -> false

let fixture_path name =
  Filename.concat (Sys.getcwd ()) ("fixtures/specs/" ^ name ^ ".qnt")

let with_pipeline name f =
  if not (quint_available ()) then Alcotest.skip ()
  else
    match Lint.run { Lint.quint = None; threshold = `Fail } (fixture_path name) with
    | Ok result -> f result
    | Error error ->
        failf "pipeline failed: %s" (Analysis.describe ~quint_path:"quint" error)

let test_pipeline_clean () =
  with_pipeline "clean" (fun result ->
      Alcotest.(check int) "clean pipeline exit 0" 0 result.Lint.report.Report.exit_code;
      check_has_substring "human report" "module Clean" result.Lint.human;
      Alcotest.(check bool) "a clean report never says fix the fails" false
        (has_substring result.Lint.human "Fix the fails above"))

let test_pipeline_fail () =
  with_pipeline "qp001_literal_false" (fun result ->
      Alcotest.(check int) "fail pipeline exit 1" 1 result.Lint.report.Report.exit_code)

let findings_of result = result.Lint.report.Report.findings

let source_basename (f : Finding.finding) = Filename.basename f.Finding.source

(* Attribution is the defining file at every import depth,
   not only one level. The leaf's QP002 finding names the leaf file. *)
let test_pipeline_attribution_two_levels () =
  with_pipeline "unit_chain_entry" (fun result ->
      let leaf_rows =
        List.filter
          (fun (f : Finding.finding) ->
            f.Finding.check = Finding.QP002
            && f.Finding.module_name = "UnitLeaf")
          (findings_of result)
      in
      Alcotest.(check int) "the leaf finding is reported once" 1
        (List.length leaf_rows);
      Alcotest.(check string) "two-level import attribution names the leaf file"
        "unit_leaf.qnt"
        (source_basename (List.hd leaf_rows)))

(* A finding in an imported module is reported once,
   against that module's file. *)
let test_pipeline_import_reported_once () =
  with_pipeline "unit_entry" (fun result ->
      let helper_rows =
        List.filter
          (fun (f : Finding.finding) ->
            f.Finding.check = Finding.QP002
            && f.Finding.module_name = "UnitHelper")
          (findings_of result)
      in
      Alcotest.(check int) "two helper declarations, two rows" 2
        (List.length helper_rows);
      Alcotest.(check bool) "every helper row names the helper file" true
        (List.for_all
           (fun f -> source_basename f = "unit_helper.qnt")
           helper_rows))

(* QL009 asks a runnable-unit question, so it
   classifies only the entry module. The imported helper gets no QL009 row;
   linting the helper directly keeps its row (documented asymmetry). *)
let test_pipeline_ql009_entry_only () =
  with_pipeline "unit_entry" (fun result ->
      let helper_rows =
        List.filter
          (fun (f : Finding.finding) ->
            f.Finding.check = Finding.QL009
            && f.Finding.module_name = "UnitHelper")
          (findings_of result)
      in
      Alcotest.(check int) "no QL009 row for the imported helper" 0
        (List.length helper_rows);
      let entry_rows =
        List.filter
          (fun (f : Finding.finding) ->
            f.Finding.check = Finding.QL009
            && f.Finding.module_name = "UnitEntry")
          (findings_of result)
      in
      Alcotest.(check int) "the runnable entry has no QL009 row" 0
        (List.length entry_rows));
  with_pipeline "unit_helper" (fun result ->
      let rows =
        List.filter
          (fun (f : Finding.finding) ->
            f.Finding.check = Finding.QL009
            && f.Finding.module_name = "UnitHelper")
          (findings_of result)
      in
      Alcotest.(check int) "the helper as entry keeps its QL009 row" 1
        (List.length rows);
      check_has_substring "the helper entry row is the no-step class"
        "no `step` action" (List.hd rows).Finding.message;
      Alcotest.(check (option string)) "the helper entry row status is warn"
        (Some "warn")
        (status_of_check (Report.json result.Lint.report) "QL009"))

let test_pipeline_cache () =
  if not (quint_available ()) then Alcotest.skip ()
  else begin
    Ir_facts.reset ();
    let path = fixture_path "clean" in
    (match Lint.run { Lint.quint = None; threshold = `Fail } path with
    | Ok _ -> ()
    | Error e -> failf "first run: %s" (Analysis.describe ~quint_path:"quint" e));
    (match Lint.run { Lint.quint = None; threshold = `Fail } path with
    | Ok _ -> ()
    | Error e -> failf "second run: %s" (Analysis.describe ~quint_path:"quint" e));
    Alcotest.(check int) "parse-once-per-process" 1 !Ir_facts.parse_count
  end

let test_pipeline_errors () =
  let expect label pred run =
    match run with
    | Ok _ -> failf "%s: expected an analysis error" label
    | Error error -> if not (pred error) then failf "%s: unexpected error" label
  in
  expect "missing file"
    (function Analysis.Io _ -> true | _ -> false)
    (Lint.run { Lint.quint = None; threshold = `Fail } "fixtures/specs/no_such_spec.qnt");
  expect "non-ascii"
    (function Analysis.Non_ascii _ -> true | _ -> false)
    (Lint.run { Lint.quint = None; threshold = `Fail } (fixture_path "bad_nonascii"));
  if quint_available () then
    expect "parse failure"
      (function Analysis.Parse_failed _ -> true | _ -> false)
      (Lint.run { Lint.quint = None; threshold = `Fail } (fixture_path "bad_parse"))

let masked_doc doc =
  match json_field "quint" doc with
  | `Assoc fs ->
      replace_field "quint"
        (`Assoc (("parse_ms", `Int 0) :: List.remove_assoc "parse_ms" fs))
        doc
  | _ -> failf "quint field is not an object"

let lint_json name =
  match Lint.run { Lint.quint = None; threshold = `Fail } (fixture_path name) with
  | Ok result -> Report.json result.Lint.report
  | Error error ->
      failf "pipeline failed: %s" (Analysis.describe ~quint_path:"quint" error)

(* The stability claim, as a two-run cell. The whole JSON
   document is compared with the only varying field (quint.parse_ms) masked;
   the findings and summary subvalues are compared byte for byte. *)
let test_report_two_run_stability () =
  if not (quint_available ()) then Alcotest.skip ()
  else begin
    Ir_facts.reset ();
    let a = lint_json "ql006_invariants" in
    Ir_facts.reset ();
    let b = lint_json "ql006_invariants" in
    Alcotest.(check string) "whole JSON stable with parse_ms masked"
      (Yojson.Safe.to_string (masked_doc a))
      (Yojson.Safe.to_string (masked_doc b));
    Alcotest.(check string) "findings byte-equal"
      (Yojson.Safe.to_string (json_field "findings" a))
      (Yojson.Safe.to_string (json_field "findings" b));
    Alcotest.(check string) "summary byte-equal"
      (Yojson.Safe.to_string (json_field "summary" a))
      (Yojson.Safe.to_string (json_field "summary" b))
  end

(* ---------- full subcommand (run-driving end to end) ---------- *)

let full_config =
  Lint.
    {
      max_samples = 5;
      max_steps = 5;
      seed = Some "0x2";
      run_timeout_s = 120.0;
      invariants = [];
    }

let with_full ?(invariants = []) name f =
  if not (quint_available ()) then Alcotest.skip ()
  else
    match
      Lint.run_full { Lint.quint = None; threshold = `Fail }
        { full_config with Lint.invariants = invariants }
        (fixture_path name)
    with
    | Ok result -> f result
    | Error error ->
        failf "full pipeline failed: %s"
          (Analysis.describe ~quint_path:"quint" error)

let test_full_clean () =
  with_full ~invariants:[ "belowLimit" ] "full_clean" (fun result ->
      Alcotest.(check int) "clean full exit 0" 0
        result.Lint.report.Report.exit_code;
      check_has_substring "mode ir+run" "mode ir+run" result.Lint.human;
      check_has_substring "sample pins in the report"
        "run: backend rust, samples 5, steps 5, seed 0x2" result.Lint.human;
      let doc = Report.json result.Lint.report in
      List.iter
        (fun id ->
          Alcotest.(check (option string))
            (id ^ " ran") (Some "pass") (status_of_check doc id))
        [ "QL004"; "QL007"; "QL010"; "QL011" ])

let test_full_violation () =
  with_full ~invariants:[ "small" ] "full_violation" (fun result ->
      Alcotest.(check int) "violation full exit 1" 1
        result.Lint.report.Report.exit_code;
      Alcotest.(check bool) "QL011 names the action" true
        (List.exists
           (fun f ->
             f.Finding.check = Finding.QL011
             && f.Finding.severity = Finding.Fail
             && has_substring f.Finding.message "advance")
           result.Lint.report.Report.findings);
      let doc = Report.json result.Lint.report in
      Alcotest.(check (option string)) "QL010 passes at init" (Some "pass")
        (status_of_check doc "QL010");
      Alcotest.(check (option string)) "QL011 fails" (Some "fail")
        (status_of_check doc "QL011"))

let test_full_init_false () =
  with_full ~invariants:[ "inRange" ] "full_init_false" (fun result ->
      Alcotest.(check int) "false init exits 1" 1
        result.Lint.report.Report.exit_code;
      Alcotest.(check bool) "QL007 fails on a false init" true
        (List.exists
           (fun f ->
             f.Finding.check = Finding.QL007
             && f.Finding.severity = Finding.Fail)
           result.Lint.report.Report.findings);
      let doc = Report.json result.Lint.report in
      Alcotest.(check (option string)) "QL010 does not claim a pass"
        (Some "warn") (status_of_check doc "QL010"))

let test_full_no_init_init_error () =
  with_full "full_no_init" (fun result ->
      Alcotest.(check int) "no-init full exits 1" 1
        result.Lint.report.Report.exit_code;
      let ql007 =
        List.filter
          (fun f ->
            f.Finding.check = Finding.QL007 && f.Finding.severity = Finding.Fail)
          result.Lint.report.Report.findings
      in
      Alcotest.(check int) "two QL007 fails (IR half + run half)" 2
        (List.length ql007);
      Alcotest.(check bool) "IR half names the missing init" true
        (List.exists
           (fun f ->
             has_substring f.Finding.message "module has no `init` action")
           ql007);
      Alcotest.(check bool) "run half carries the QNT404 detail" true
        (List.exists
           (fun f ->
             has_substring f.Finding.message "init raises an error"
             && has_substring f.Finding.message "QNT404")
           ql007);
      check_has_substring "report printed with the QL007 rows" "QL007"
        result.Lint.human;
      let doc = Report.json result.Lint.report in
      Alcotest.(check (option string)) "QL010 not evaluated" (Some "warn")
        (status_of_check doc "QL010");
      Alcotest.(check (option string)) "QL011 not evaluated" (Some "warn")
        (status_of_check doc "QL011"))

(* The CLI boundary is the contract surface: the test drives the built
   binary, never the library, so an exit-code regression dies here. A
   timeout is a genuine did-not-run. *)
let run_cli args =
  let out_path = Filename.temp_file "quint-audit-cli-out" ".txt" in
  let err_path = Filename.temp_file "quint-audit-cli-err" ".txt" in
  let out_fd =
    Unix.openfile out_path [ Unix.O_WRONLY; Unix.O_TRUNC ] 0o600
  in
  let err_fd =
    Unix.openfile err_path [ Unix.O_WRONLY; Unix.O_TRUNC ] 0o600
  in
  let argv = Array.of_list ("../bin/quint_audit_cli.exe" :: args) in
  let pid = Unix.create_process argv.(0) argv Unix.stdin out_fd err_fd in
  Unix.close out_fd;
  Unix.close err_fd;
  let _, status = Unix.waitpid [] pid in
  let code = match status with Unix.WEXITED n -> n | _ -> -1 in
  let out = read_file out_path and err = read_file err_path in
  Sys.remove out_path;
  Sys.remove err_path;
  (code, out, err)

let test_cli_full_did_not_run_exit_2 () =
  if not (quint_available ()) then Alcotest.skip ()
  else
    let code, _, err =
      run_cli
        [
          "full";
          fixture_path "full_clean";
          "--max-samples=5";
          "--max-steps=5";
          "--seed=0x2";
          "--run-timeout=0.001";
        ]
    in
    Alcotest.(check int) "CLI did-not-run exits 2" 2 code;
    check_has_substring "diagnostic names the init stage" "run: QL007 init:" err;
    check_has_substring "diagnostic is the timeout shape" "timed_out=true" err

(* The exit contract is one vocabulary: cmdliner's 123/124/125 defaults are
   mapped to 2, and every help page carries the README's cause list. *)
let test_cli_exit_contract () =
  let expect_code label expected args =
    let code, _, _ = run_cli args in
    Alcotest.(check int) label expected code
  in
  expect_code "--format=yaml exits 2" 2
    [ "lint"; "--format=yaml"; fixture_path "clean" ];
  expect_code "--fail-on=bogus exits 2" 2
    [ "lint"; "--fail-on=bogus"; fixture_path "clean" ];
  expect_code "--bogus exits 2" 2
    [ "lint"; "--bogus"; fixture_path "clean" ];
  expect_code "--max-samples=x exits 2" 2
    [ "lint"; "--max-samples=x"; fixture_path "clean" ];
  expect_code "no arguments exits 2" 2 [];
  let code, help, _ = run_cli [ "--help=plain" ] in
  Alcotest.(check int) "help exits 0" 0 code;
  List.iter
    (fun phrase -> check_has_substring ("help names: " ^ phrase) phrase help)
    [
      "on success.";
      "when findings meet the threshold.";
      "usage error";
      "missing quint";
      "non-ASCII input";
      "parse failure";
      "typed decode failure";
      "did not execute";
      "internal error";
    ];
  List.iter
    (fun code -> Alcotest.(check bool) ("help has no exit " ^ code) false
        (has_substring help code))
    [ "123"; "124"; "125" ];
  if quint_available () then begin
    expect_code "clean run exits 0" 0 [ "lint"; fixture_path "clean" ];
    expect_code "findings run exits 1" 1 [ "lint"; fixture_path "qp001_literal_false" ]
  end

(* The role split: an undeclared state-reading val is a witness (QL004)
   only; QL010/QL011 judge only the vals named by --invariant. Declaring
   the same val restores the invariant reading - with the real violation. *)
let test_full_witness_invariant_roles () =
  if not (quint_available ()) then Alcotest.skip ()
  else begin
    with_full "full_witness_initonly" (fun result ->
        Alcotest.(check int) "undeclared witness exits 0" 0
          result.Lint.report.Report.exit_code;
        Alcotest.(check bool) "no QL011 fail on an undeclared witness" false
          (List.exists
             (fun f ->
               f.Finding.check = Finding.QL011
               && f.Finding.severity = Finding.Fail)
             result.Lint.report.Report.findings);
        let doc = Report.json result.Lint.report in
        Alcotest.(check (option string)) "QL011 not evaluated" (Some "warn")
          (status_of_check doc "QL011");
        Alcotest.(check (option string)) "QL004 witness ran" (Some "pass")
          (status_of_check doc "QL004"));
    with_full ~invariants:[ "initOnly" ] "full_witness_initonly"
      (fun result ->
        Alcotest.(check int) "declared invariant exits 1" 1
          result.Lint.report.Report.exit_code;
        Alcotest.(check bool) "declared violation names the action" true
          (List.exists
             (fun f ->
               f.Finding.check = Finding.QL011
               && f.Finding.severity = Finding.Fail
               && has_substring f.Finding.message "advance")
             result.Lint.report.Report.findings))
  end

(* A wrapper that drops --out-itf from run invocations: the coverage run
   passes (rc 0) but writes no evidence. *)
let noitf_wrapper () =
  let real =
    match Quint_parse.resolve ~quint:None with
    | Ok p -> p
    | Error reason -> failf "quint not resolved: %s" reason
  in
  let path = Filename.temp_file "quint-noitf" ".sh" in
  let script =
    Printf.sprintf
      "#!/bin/sh\n\
       real=%s\n\
       if [ \"$1\" = \"run\" ]; then\n\
      \  args=\"\"\n\
      \  for a in \"$@\"; do\n\
      \    case \"$a\" in --out-itf=*) ;; *) args=\"$args $a\" ;; esac\n\
      \  done\n\
      \  exec \"$real\" $args\n\
       fi\n\
       exec \"$real\" \"$@\"\n"
      (Filename.quote real)
  in
  let oc = open_out path in
  output_string oc script;
  close_out oc;
  Unix.chmod path 0o755;
  path

let test_full_missing_itf_evidence () =
  if not (quint_available ()) then Alcotest.skip ()
  else
    let wrapper = noitf_wrapper () in
    Fun.protect
      ~finally:(fun () -> Sys.remove wrapper)
      (fun () ->
        match
          Lint.run_full
            { Lint.quint = Some wrapper; threshold = `Fail }
            full_config (fixture_path "full_clean")
        with
        | Ok result ->
            failf
              "missing ITF evidence produced a report (exit %d) instead of a \
               did-not-run diagnostic"
              result.Lint.report.Report.exit_code
        | Error (Analysis.Run_failed { stage; reason }) ->
            Alcotest.(check string) "coverage stage" "QL004 action coverage"
              stage;
            check_has_substring "diagnostic names the missing evidence"
              "no ITF evidence" reason
        | Error error ->
            failf "unexpected analysis error: %s"
              (Analysis.describe ~quint_path:"quint" error))

(* A shell wrapper around the resolved quint binary: [body] runs with `real`
   bound to quint and receives quint's argv unchanged. *)
let quint_wrapper name body =
  let real =
    match Quint_parse.resolve ~quint:None with
    | Ok p -> p
    | Error reason -> failf "quint not resolved: %s" reason
  in
  let path = Filename.temp_file name ".sh" in
  let oc = open_out path in
  Printf.fprintf oc "#!/bin/sh\nreal=%s\n%s\n" (Filename.quote real) body;
  close_out oc;
  Unix.chmod path 0o755;
  path

(* Run normally, then truncate every written ITF file to zero bytes
   (present but undecodable evidence). *)
let truncate_itf_wrapper () =
  quint_wrapper "quint-truncate-itf"
    {|
pattern=""
for a in "$@"; do
  case "$a" in
    --out-itf=*) pattern="${a#--out-itf=}" ;;
  esac
done
"$real" "$@"
rc=$?
if [ -n "$pattern" ]; then
  base="${pattern%\{seq\}.itf.json}"
  for f in "${base}"*.itf.json; do
    if [ -e "$f" ]; then : > "$f"; fi
  done
fi
exit $rc
|}

(* Run normally, then make every written ITF file unreadable (a Sys_error at
   decode time). *)
let chmod_itf_wrapper () =
  quint_wrapper "quint-chmod-itf"
    {|
pattern=""
for a in "$@"; do
  case "$a" in
    --out-itf=*) pattern="${a#--out-itf=}" ;;
  esac
done
"$real" "$@"
rc=$?
if [ -n "$pattern" ]; then
  base="${pattern%\{seq\}.itf.json}"
  for f in "${base}"*.itf.json; do
    if [ -e "$f" ]; then chmod 000 "$f"; fi
  done
fi
exit $rc
|}

(* Run normally, then keep only trace 0 of the written ITF files (partial
   evidence). *)
let keep_first_itf_wrapper () =
  quint_wrapper "quint-partial-itf"
    {|
pattern=""
for a in "$@"; do
  case "$a" in
    --out-itf=*) pattern="${a#--out-itf=}" ;;
  esac
done
"$real" "$@"
rc=$?
if [ -n "$pattern" ]; then
  base="${pattern%\{seq\}.itf.json}"
  keep="${base}0.itf.json"
  for f in "${base}"*.itf.json; do
    if [ "$f" != "$keep" ]; then rm -f "$f"; fi
  done
fi
exit $rc
|}

let with_wrapper ?(invariants = []) name wrapper f =
  Fun.protect
    ~finally:(fun () -> Sys.remove wrapper)
    (fun () ->
      match
        Lint.run_full { Lint.quint = Some wrapper; threshold = `Fail }
          { full_config with Lint.invariants }
          (fixture_path name)
      with
      | Ok result -> f result
      | Error error ->
          Error
            (Analysis.describe ~quint_path:"quint" error))

(* ITF files that exist but cannot be decoded are analysis-incomplete
   evidence, not zero coverage: exit 2, never a warn-only report. *)
let test_full_corrupt_itf_evidence () =
  if not (quint_available ()) then Alcotest.skip ()
  else
    let wrapper = truncate_itf_wrapper () in
    match
      with_wrapper "full_clean" wrapper (fun result -> Ok result)
    with
    | Ok result ->
        failf
          "corrupt ITF evidence produced a report (exit %d) instead of a \
           did-not-run diagnostic"
          result.Lint.report.Report.exit_code
    | Error reason ->
        check_has_substring "diagnostic names the coverage stage"
          "QL004 action coverage" reason;
        check_has_substring "diagnostic names the undecodable evidence"
          "could not be decoded" reason

(* A decodable trace whose states carry no state object is
   not observed evidence. Five empty-state files, and five files whose states
   are scalars, both read as zero observed states - the coverage verdict is
   about states, not files. *)
let rewritten_itf_wrapper name content =
  quint_wrapper name
    (Printf.sprintf
       {|
pattern=""
for a in "$@"; do
  case "$a" in
    --out-itf=*) pattern="${a#--out-itf=}" ;;
  esac
done
"$real" "$@"
rc=$?
if [ -n "$pattern" ]; then
  base="${pattern%%\{seq\}.itf.json}"
  for f in "${base}"*.itf.json; do
    if [ -e "$f" ]; then printf '%%s' '%s' > "$f"; fi
  done
fi
exit $rc
|}
       content)

let empty_state_itf_wrapper () =
  rewritten_itf_wrapper "quint-empty-state-itf" {|{"states": []}|}

let scalar_state_itf_wrapper () =
  rewritten_itf_wrapper "quint-scalar-state-itf" {|{"states": [1,2]}|}

let test_full_zero_state_itf_evidence () =
  if not (quint_available ()) then Alcotest.skip ()
  else
    let expect_zero_states label wrapper =
      match with_wrapper "full_clean" wrapper (fun result -> Ok result) with
      | Ok result ->
          failf
            "%s: zero observed states produced a report (exit %d) instead of a \
             did-not-run diagnostic"
            label result.Lint.report.Report.exit_code
      | Error reason ->
          check_has_substring
            (label ^ ": names the coverage stage")
            "QL004 action coverage" reason;
          check_has_substring
            (label ^ ": names zero observed states")
            "no observed states" reason;
          check_has_substring
            (label ^ ": names the file count read")
            "5 ITF trace files" reason
    in
    expect_zero_states "empty states" (empty_state_itf_wrapper ());
    expect_zero_states "scalar states" (scalar_state_itf_wrapper ())

(* A state object is an observation only when it binds at
   least one variable. Empty objects, #meta-only objects and action-marker-only
   shells are analysis-incomplete evidence (exit 2). A
   genuine trace still analyses. *)
let object_shell_itf_wrapper () =
  rewritten_itf_wrapper "quint-object-shell-itf" {|{"states": [{}]}|}

let meta_only_itf_wrapper () =
  rewritten_itf_wrapper "quint-meta-only-itf"
    {|{"states": [{"#meta": {"index": 0}}]}|}

let marker_only_itf_wrapper () =
  rewritten_itf_wrapper "quint-marker-only-itf"
    {|{"states": [{"mbt::actionTaken": "advance"}]}|}

let vars_empty_itf_wrapper () =
  rewritten_itf_wrapper "quint-vars-empty-itf" {|{"states": [{"vars": {}}]}|}

let test_full_shell_state_itf_evidence () =
  if not (quint_available ()) then Alcotest.skip ()
  else begin
    let expect_no_observed label wrapper =
      match with_wrapper "full_clean" wrapper (fun result -> Ok result) with
      | Ok result ->
          failf
            "%s: a state shell produced a report (exit %d) instead of a \
             did-not-run diagnostic"
            label result.Lint.report.Report.exit_code
      | Error reason ->
          check_has_substring
            (label ^ ": names the coverage stage")
            "QL004 action coverage" reason;
          check_has_substring
            (label ^ ": names zero observed states")
            "no observed states" reason
    in
    expect_no_observed "empty object states" (object_shell_itf_wrapper ());
    expect_no_observed "#meta-only states" (meta_only_itf_wrapper ());
    expect_no_observed "action-marker-only states" (marker_only_itf_wrapper ());
    expect_no_observed "empty vars container" (vars_empty_itf_wrapper ());
    match
      with_wrapper "full_clean" (keep_first_itf_wrapper ()) (fun result ->
          Ok result)
    with
    | Error reason -> failf "genuine trace failed the analysis: %s" reason
    | Ok result ->
        Alcotest.(check int) "genuine trace still exits 0" 0
          result.Lint.report.Report.exit_code
  end

(* Report-health mirror (spec/irdecode.qnt).
   A junk-valued binding plus an action marker is not an observation.
   A file mixing accepted and refused states discloses the refused
   count, not only the file-level counts. *)
let junk_value_itf_wrapper () =
  rewritten_itf_wrapper "quint-junk-value-itf"
    {|{"states": [{"x": null, "mbt::actionTaken": "advance"}]}|}

let vars_junk_entry_itf_wrapper () =
  rewritten_itf_wrapper "quint-vars-junk-entry-itf"
    {|{"states": [{"vars": {"x": {}}}]}|}

let test_full_junk_value_itf_evidence () =
  if not (quint_available ()) then Alcotest.skip ()
  else begin
    let expect_no_observed label wrapper =
      match with_wrapper "full_clean" wrapper (fun result -> Ok result) with
      | Ok result ->
          failf
            "%s: a junk-valued state produced a report (exit %d) instead of a \
             did-not-run diagnostic"
            label result.Lint.report.Report.exit_code
      | Error reason ->
          check_has_substring (label ^ ": names zero observed states")
            "no observed states" reason
    in
    expect_no_observed "null binding" (junk_value_itf_wrapper ());
    expect_no_observed "empty-object vars entry" (vars_junk_entry_itf_wrapper ())
  end

let mixed_first_itf_wrapper () =
  quint_wrapper "quint-mixed-first-itf"
    {|
pattern=""
for a in "$@"; do
  case "$a" in
    --out-itf=*) pattern="${a#--out-itf=}" ;;
  esac
done
"$real" "$@"
rc=$?
if [ -n "$pattern" ]; then
  base="${pattern%\{seq\}.itf.json}"
  first="${base}0.itf.json"
  if [ -e "$first" ]; then
    printf '%s' '{"states": [{}, {"vars": {"x": 0}}, {"vars": {"x": 1}}]}' > "$first"
  fi
fi
exit $rc
|}

let test_full_refused_state_disclosed () =
  if not (quint_available ()) then Alcotest.skip ()
  else
    match
      with_wrapper "full_clean" (mixed_first_itf_wrapper ()) (fun result ->
          Ok result)
    with
    | Error reason -> failf "mixed evidence failed the analysis: %s" reason
    | Ok result ->
        Alcotest.(check int) "mixed evidence still exits 0" 0
          result.Lint.report.Report.exit_code;
        let disclosed message =
          has_substring message "refused" && has_substring message "1"
        in
        let finding =
          List.find_map
            (fun f ->
              if disclosed f.Finding.message then Some f.Finding.message
              else None)
            result.Lint.report.Report.findings
        in
        (match finding with
        | Some message ->
            check_has_substring "human report carries the refused count" message
              result.Lint.human
        | None ->
            Alcotest.fail
              "the report does not disclose the refused state count")

(* The decode diagnostic names the evidence by ROLE, so
   two runs on identical input produce byte-equal text. The absolute path it
   used to interpolate carried the per-run random temp name. *)
let test_full_corrupt_itf_diagnostic_stable () =
  if not (quint_available ()) then Alcotest.skip ()
  else
    let wrapper = truncate_itf_wrapper () in
    Fun.protect
      ~finally:(fun () -> Sys.remove wrapper)
      (fun () ->
        let describe () =
          match
            Lint.run_full
              { Lint.quint = Some wrapper; threshold = `Fail }
              full_config (fixture_path "full_clean")
          with
          | Ok result ->
              failf
                "corrupt ITF evidence produced a report (exit %d) instead of a \
                 did-not-run diagnostic"
                result.Lint.report.Report.exit_code
          | Error error -> Analysis.describe ~quint_path:"quint" error
        in
        let first = describe () and second = describe () in
        Alcotest.(check string) "decode diagnostic is byte-stable unmasked"
          first second)

(* The Sys_error diagnostic names the evidence by ROLE too.
   Two runs on identical input are byte-equal unmasked and never name the
   per-run temp file. *)
let test_full_unreadable_itf_diagnostic_stable () =
  if not (quint_available ()) then Alcotest.skip ()
  else
    let wrapper = chmod_itf_wrapper () in
    Fun.protect
      ~finally:(fun () -> Sys.remove wrapper)
      (fun () ->
        let describe () =
          match
            Lint.run_full
              { Lint.quint = Some wrapper; threshold = `Fail }
              full_config (fixture_path "full_clean")
          with
          | Ok result ->
              failf
                "unreadable ITF evidence produced a report (exit %d) instead \
                 of a did-not-run diagnostic"
                result.Lint.report.Report.exit_code
          | Error error -> Analysis.describe ~quint_path:"quint" error
        in
        let first = describe () and second = describe () in
        Alcotest.(check string)
          "unreadable diagnostic is byte-stable unmasked" first second;
        check_has_substring "diagnostic keeps the errno text"
          "Permission denied" first;
        Alcotest.(check bool) "diagnostic does not name the temp evidence"
          false (has_substring first "quint-audit-itf-"))

(* Partial ITF evidence is analysed, and the report discloses the count
   it read. *)
let test_full_partial_itf_evidence () =
  if not (quint_available ()) then Alcotest.skip ()
  else
    let wrapper = keep_first_itf_wrapper () in
    match with_wrapper "full_clean" wrapper (fun result -> Ok result) with
    | Error reason -> failf "partial evidence failed the analysis: %s" reason
    | Ok result ->
        Alcotest.(check int) "partial evidence still exits 0" 0
          result.Lint.report.Report.exit_code;
        let ql004 =
          List.filter
            (fun f -> f.Finding.check = Finding.QL004)
            result.Lint.report.Report.findings
        in
        Alcotest.(check bool) "partial evidence is disclosed" true
          (List.exists
             (fun f ->
               has_substring f.Finding.message "partial ITF evidence"
               && has_substring f.Finding.message "1 of 5")
             ql004)

(* The human report states the evidence it analysed, matching the JSON's
   "partial ITF evidence: analysed 1 of 5 sampled trace files
   (6 states)". *)
let test_full_partial_itf_human_count () =
  if not (quint_available ()) then Alcotest.skip ()
  else
    let wrapper = keep_first_itf_wrapper () in
    match with_wrapper "full_clean" wrapper (fun result -> Ok result) with
    | Error reason -> failf "partial evidence failed the analysis: %s" reason
    | Ok result -> (
        match
          List.find_map
            (fun f ->
              if
                f.Finding.check = Finding.QL004
                && f.Finding.severity = Finding.Info
              then Some f.Finding.message
              else None)
            result.Lint.report.Report.findings
        with
        | None -> Alcotest.fail "no partial-evidence Info finding"
        | Some message ->
            check_has_substring "human report carries the JSON message" message
              result.Lint.human)

(* A supplied --invariant name resolves to a declaration or it is a
   usage error; it is never silently dropped. *)
let invariant_usage_error name invariants =
  if not (quint_available ()) then Alcotest.skip ()
  else
    match
      Lint.run_full { Lint.quint = None; threshold = `Fail }
        { full_config with Lint.invariants }
        (fixture_path name)
    with
    | Ok result ->
        failf
          "a supplied --invariant name produced a report (exit %d) instead of \
           a usage diagnostic"
          result.Lint.report.Report.exit_code
    | Error (Analysis.Run_failed { stage; reason }) -> (stage, reason)
    | Error error ->
        failf "unexpected analysis error: %s"
          (Analysis.describe ~quint_path:"quint" error)

let test_full_invariant_name_missing () =
  let _stage, reason = invariant_usage_error "full_clean" [ "nope" ] in
  check_has_substring "diagnostic names the missing declaration" "no declaration" reason;
  check_has_substring "diagnostic names the supplied name" "nope" reason

let test_full_invariant_name_action () =
  let _stage, reason = invariant_usage_error "full_clean" [ "advance" ] in
  check_has_substring "diagnostic names the declaration" "advance" reason;
  check_has_substring "diagnostic names the shape" "action" reason

(* fc8 analog: a pure def shape is not an invariant subject, even though quint
   would evaluate it. Before the fix this run reported exit 1 from QP002 and
   the false "no --invariant declaration was supplied" warn. *)
let test_full_invariant_name_pure_def () =
  let _stage, reason =
    invariant_usage_error "full_invariant_puredef" [ "readsState" ]
  in
  check_has_substring "diagnostic names the declaration" "readsState" reason;
  check_has_substring "diagnostic names the shape" "pure def" reason

let test_full_invariant_name_pure_val () =
  let _stage, reason =
    invariant_usage_error "full_invariant_pureval" [ "voidP" ]
  in
  check_has_substring "diagnostic names the declaration" "voidP" reason;
  check_has_substring "diagnostic names the shape" "pure val" reason

(* Quint's refusal to evaluate a non-boolean invariant (QNT500) is a
   run error, not a QL010 violation. *)
let test_full_invariant_nonboolean () =
  if not (quint_available ()) then Alcotest.skip ()
  else
    match
      Lint.run_full { Lint.quint = None; threshold = `Fail }
        { full_config with Lint.invariants = [ "nonBoolean" ] }
        (fixture_path "full_invariant_nonboolean")
    with
    | Ok result ->
        failf
          "a non-boolean invariant produced a report (exit %d) instead of a \
           run-error diagnostic"
          result.Lint.report.Report.exit_code
    | Error (Analysis.Run_failed { stage; reason }) ->
        check_has_substring "diagnostic names the QL010 stage" "QL010" stage;
        check_has_substring "diagnostic names the QNT code" "QNT500" reason
    | Error error ->
        failf "unexpected analysis error: %s"
          (Analysis.describe ~quint_path:"quint" error)

(* The failure-marker match is structural. A run whose output carries an
   unrelated QNT-tagged warning is still a did-not-run, and the false-init
   detail is not replaced by that line. *)
let passthrough_wrapper () =
  quint_wrapper "quint-passthrough" {|
exec "$real" "$@"
|}

let qntnote_wrapper () =
  quint_wrapper "quint-qntnote"
    {|
"$real" "$@"
rc=$?
printf '%s\n' "warning: [QNT000] unrelated diagnostic line" >&2
exit $rc
|}

let masked_wrapper () =
  quint_wrapper "quint-masked"
    {|
if [ "$1" = "run" ]; then
  "$real" "$@" >/dev/null 2>&1
  exit 1
fi
exec "$real" "$@"
|}

let masked_note_wrapper note =
  quint_wrapper "quint-masked-note"
    (Printf.sprintf
       {|
if [ "$1" = "run" ]; then
  "$real" "$@" >/dev/null 2>&1
  printf '%%s\n' "%s" >&2
  exit 1
fi
exec "$real" "$@"
|}
       note)

let test_full_failure_marker_structural () =
  if not (quint_available ()) then Alcotest.skip ()
  else
    let expect_did_not_run label wrapper =
      match with_wrapper "full_clean" wrapper (fun result -> Ok result) with
      | Ok result ->
          failf "%s: the masked run produced a report (exit %d)" label
            result.Lint.report.Report.exit_code
      | Error reason ->
          check_has_substring (label ^ ": did-not-run diagnostic")
            "did not complete" reason
    in
    expect_did_not_run "masked crash" (masked_wrapper ());
    expect_did_not_run "masked crash with an unrelated QNT note"
      (masked_note_wrapper
         "warning: [QNT000] transport layer note");
    expect_did_not_run "masked crash with a lowercase QNT tag"
      (masked_note_wrapper "error: [qnt404] lowercased tag note")

let test_full_false_init_detail () =
  if not (quint_available ()) then Alcotest.skip ()
  else
    let message_of wrapper =
      match
        with_wrapper ~invariants:[ "inRange" ] "full_init_false" wrapper
          (fun result -> Ok result)
      with
      | Error reason -> failf "a false init failed the analysis: %s" reason
      | Ok result ->
          Alcotest.(check int) "false init still exits 1" 1
            result.Lint.report.Report.exit_code;
          match
            List.find_map
              (fun f ->
                if
                  f.Finding.check = Finding.QL007
                  && f.Finding.severity = Finding.Fail
                then Some f.Finding.message
                else None)
              result.Lint.report.Report.findings
          with
          | Some message -> message
          | None -> failf "a false init has no QL007 fail"
    in
    let plain = message_of (passthrough_wrapper ()) in
    let noted = message_of (qntnote_wrapper ()) in
    check_has_substring "control detail is the false-init shape"
      "init returns false" plain;
    Alcotest.(check string)
      "the unrelated QNT note does not change the detail" plain noted;
    Alcotest.(check bool) "no error attribution from the unrelated note" false
      (has_substring noted "raises an error")

(* ---------- spec-cell and README sync ---------- *)

let find_sub haystack needle =
  let n = String.length needle and h = String.length haystack in
  let rec go i =
    if i + n > h then None
    else if String.sub haystack i n = needle then Some i
    else go (i + 1)
  in
  go 0

let quoted_after line marker =
  match find_sub line marker with
  | None -> None
  | Some i ->
      let start = i + String.length marker in
      (match String.index_from_opt line start '"' with
      | None -> None
      | Some j -> Some (String.sub line start (j - start)))

let source_lines path = String.split_on_char '\n' (read_file path)

(* Dune runs the suite from _build/default/test; a direct run from the
   project root resolves the same files through the second candidate. *)
let pick paths =
  match List.find_opt Sys.file_exists paths with
  | Some path -> path
  | None -> List.hd paths

let spec_cell_map_path =
  pick [ "../docs/spec-cell-map.jdn"; "docs/spec-cell-map.jdn" ]

let readme_path = pick [ "../README.md"; "README.md" ]
let cli_source_path = pick [ "../bin/quint_audit_cli.ml"; "bin/quint_audit_cli.ml" ]

let test_source_path =
  pick [ "test_quint_audit.ml"; "test/test_quint_audit.ml" ]

let spec_files =
  [
    ("qcalc.qnt", pick [ "../spec/qcalc.qnt"; "spec/qcalc.qnt" ]);
    ("rundisc.qnt", pick [ "../spec/rundisc.qnt"; "spec/rundisc.qnt" ]);
    ("irdecode.qnt", pick [ "../spec/irdecode.qnt"; "spec/irdecode.qnt" ]);
  ]

let invariant_names path =
  List.filter_map
    (fun line ->
      let t = String.trim line in
      if String.length t > 4 && String.sub t 0 4 = "val " then
        let rest = String.sub t 4 (String.length t - 4) in
        let name =
          match String.index_opt rest ' ' with
          | Some i -> String.sub rest 0 i
          | None -> rest
        in
        if String.length name > 2 && name.[0] = 'i' && name.[1] = '_' then
          Some name
        else None
      else None)
    (source_lines path)

let suite_cell_names path =
  let text = read_file path in
  let quoted_strings marker =
    let n = String.length text and m = String.length marker in
    let rec scan i acc =
      if i + m > n then List.rev acc
      else if String.sub text i m = marker then
        match String.index_from_opt text (i + m) '"' with
        | None -> List.rev acc
        | Some q -> (
            match String.index_from_opt text (q + 1) '"' with
            | None -> List.rev acc
            | Some e ->
                let s = String.sub text (q + 1) (e - q - 1) in
                scan (e + 1) (s :: acc))
      else scan (i + 1) acc
    in
    scan 0 []
  in
  quoted_strings "Alcotest.test_case" @ quoted_strings "~name:"

let normalise_ws s =
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let rec skip_spaces j =
    if j < n && (s.[j] = ' ' || s.[j] = '\t') then skip_spaces (j + 1) else j
  in
  let rec go i spaced =
    if i >= n then ()
    else
      match s.[i] with
      | '\\' when i + 1 < n && s.[i + 1] = '\n' ->
          go (skip_spaces (i + 2)) spaced
      | (' ' | '\t' | '\n' | '\r') as _c ->
          if not spaced then Buffer.add_char b ' ';
          go (i + 1) true
      | c ->
          Buffer.add_char b c;
          go (i + 1) false
  in
  go 0 false;
  Buffer.contents b

type map_row = { invariant : string; spec : string; cell : string }

let read_map path =
  List.filter_map
    (fun line ->
      let t = String.trim line in
      if t = "" || t.[0] = '#' then None
      else
        match
          ( quoted_after line ":invariant \"",
            quoted_after line ":spec \"",
            quoted_after line ":cell \"" )
        with
        | Some invariant, Some spec, Some cell -> Some { invariant; spec; cell }
        | _ -> failf "malformed map row: %s" line)
    (source_lines path)

(* The map is data, checked against both authorities: the .qnt files for the
   invariant set, the registered suite for the cell names. A row that drifts
   fails here and names the row. *)
let test_spec_cell_map_mirror () =
  let map = read_map spec_cell_map_path in
  let cells = suite_cell_names test_source_path in
  List.iter
    (fun (spec, path) ->
      List.iter
        (fun invariant ->
          if
            not
              (List.exists
                 (fun (r : map_row) ->
                   r.invariant = invariant && r.spec = spec)
                 map)
          then
            failf "%s: invariant %s has no row in docs/spec-cell-map.jdn" spec
              invariant)
        (invariant_names path))
    spec_files;
  List.iter
    (fun (r : map_row) ->
      if not (List.mem r.cell cells) then
        failf "map row %s: cell %S is not registered in the suite" r.invariant
          r.cell;
      if not (has_substring r.cell r.invariant) then
        failf "map row %s: cell %S does not carry the invariant name"
          r.invariant r.cell;
      match List.assoc_opt r.spec spec_files with
      | None -> failf "map row %s: unknown spec %s" r.invariant r.spec
      | Some path ->
          if not (List.mem r.invariant (invariant_names path)) then
            failf "map row names invariant %s, absent from %s" r.invariant
              r.spec)
    map

let numbered_section path start_marker end_marker =
  let rec go i inside acc = function
    | [] -> List.rev acc
    | line :: rest ->
        if (not inside) && has_substring line start_marker then
          go (i + 1) true acc rest
        else if inside && has_substring line end_marker then List.rev acc
        else if inside then go (i + 1) true ((i, line) :: acc) rest
        else go (i + 1) false acc rest
  in
  go 1 false [] (source_lines path)

let dash_options line =
  let n = String.length line in
  let rec go i acc =
    if i + 1 >= n then List.rev acc
    else if line.[i] = '-' && line.[i + 1] = '-' then begin
      let j = ref (i + 2) in
      while
        !j < n
        &&
        (let c = line.[!j] in
         (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c = '-')
      do
        incr j
      done;
      if !j > i + 2 then go !j (String.sub line (i + 2) (!j - i - 2) :: acc)
      else go (i + 2) acc
    end
    else go (i + 1) acc
  in
  go 0 []

let contract_causes =
  [
    "usage error";
    "missing quint";
    "non-ASCII input";
    "parse failure";
    "typed decode failure";
    "a run that did not execute";
    "internal error";
  ]

(* README versus implementation: catalogue ids, the exit contract, and the
   option set. Failures name the artefact and the line. *)
let test_readme_sync () =
  let readme = readme_path in
  let implemented = List.map Finding.string_of_check Finding.all_checks in
  let catalogue =
    numbered_section readme "## The check catalogue" "## Scope limits"
  in
  let table_ids =
    List.filter_map
      (fun (line_no, line) ->
        let t = String.trim line in
        if String.length t > 0 && t.[0] = '|' then
          let cells =
            String.split_on_char '|' t
            |> List.map String.trim
            |> List.filter (fun s -> s <> "")
          in
          match cells with
          | id :: _
            when String.length id = 5
                 && (String.sub id 0 2 = "QL" || String.sub id 0 2 = "QP") ->
              Some (line_no, id)
          | _ -> None
        else None)
      catalogue
  in
  List.iter
    (fun (line_no, id) ->
      if not (List.mem id implemented) then
        failf "README.md:%d: catalogue id %s is not implemented (lib/finding.ml)"
          line_no id)
    table_ids;
  List.iter
    (fun id ->
      if not (List.exists (fun (_, line) -> has_substring line id) catalogue)
      then
        failf
          "README.md: implemented id %s is not documented in the check catalogue"
          id)
    implemented;
  let exit_section =
    numbered_section readme "### Exit codes" "### Machine-readable output"
  in
  let exit_meaning code =
    List.find_map
      (fun (line_no, line) ->
        let cells =
          String.split_on_char '|' line
          |> List.map String.trim
          |> List.filter (fun s -> s <> "")
        in
        match cells with
        | c :: meaning :: _ when c = code -> Some (line_no, meaning)
        | _ -> None)
      exit_section
  in
  List.iter
    (fun (code, needle) ->
      match exit_meaning code with
      | None -> failf "README.md: exit-code row %s is missing" code
      | Some (line_no, meaning) ->
          if not (has_substring meaning needle) then
            failf "README.md:%d: exit %s row does not state %S" line_no code
              needle)
    [ ("0", "threshold"); ("1", "threshold") ];
  (match exit_meaning "2" with
  | None -> failf "README.md: exit-code row 2 is missing"
  | Some (line_no, meaning) ->
      List.iter
        (fun cause ->
          if not (has_substring meaning cause) then
            failf "README.md:%d: exit 2 row does not state %S" line_no cause)
        contract_causes);
  List.iter
    (fun (line_no, line) ->
      if
        has_substring line "123" || has_substring line "124"
        || has_substring line "125"
      then
        failf "README.md:%d: exit table carries a cmdliner default code" line_no)
    exit_section;
  let cli = normalise_ws (read_file cli_source_path) in
  List.iter
    (fun cause ->
      if not (has_substring cli cause) then
        failf "bin/quint_audit_cli.ml: exit contract does not state %S" cause)
    contract_causes;
  List.iter
    (fun (line_no, line) ->
      List.iter
        (fun option ->
          if not (has_substring cli ("\"" ^ option ^ "\"")) then
            failf
              "README.md:%d: option --%s is not defined in bin/quint_audit_cli.ml"
              line_no option)
        (dash_options line))
    (numbered_section readme "## Usage" "### Exit codes")

(* Composite spec invariants: the component cells, joined. *)
let test_spec_i_source_map_contract () =
  test_decode_main_span_past_own_source ();
  test_decode_imported_span_past_main_length ();
  test_decode_imported_span_past_own_source ();
  test_decode_imported_span_in_both_ranges ();
  test_decode_span_refusal_set ();
  test_decode_module_brace ();
  test_decode_module_imported_brace ();
  test_decode_module_wrong_source_brace ()

let test_spec_i_decl_kind_report_contract () =
  test_decode_import_declaration ();
  test_decode_instance_declaration ();
  test_decode_assume_declaration ();
  test_declaration_const_is_nonsubject ();
  test_declaration_def_is_subject ();
  test_decode_future_declaration ();
  test_decode_known_kind_decodes ();
  if quint_available () then begin
    test_full_junk_value_itf_evidence ();
    test_full_shell_state_itf_evidence ();
    test_full_refused_state_disclosed ()
  end

let test_spec_i_contract () =
  test_spec_i_source_map_contract ();
  test_spec_i_decl_kind_report_contract ()

(* ---------- runner ---------- *)

let () =
  Alcotest.run "quint-audit"
    [
      ("sha256", [ Alcotest.test_case "vectors" `Quick test_sha256 ]);
      ( "decode",
        [
          Alcotest.test_case "clean fixture decodes" `Quick test_decode_clean;
          Alcotest.test_case "unknown node preserved" `Quick test_decode_unknown_preserved;
          Alcotest.test_case "missing field names the path" `Quick test_decode_missing_field;
          Alcotest.test_case "wrong type names the path" `Quick test_decode_wrong_type;
          Alcotest.test_case "empty modules" `Quick test_decode_empty_modules;
          Alcotest.test_case "non-empty errors array" `Quick test_decode_errors_array;
          Alcotest.test_case "wrong stage" `Quick test_decode_stage;
          Alcotest.test_case "non-ASCII refused with offset" `Quick test_decode_non_ascii;
          Alcotest.test_case "missing map entry" `Quick test_decode_span_missing;
          Alcotest.test_case "invalid span" `Quick test_decode_span_invalid;
          Alcotest.test_case
            "irdecode i_module_end_is_own_closing_brace: module end is not a brace"
            `Quick test_decode_module_brace;
          Alcotest.test_case "sourceIndex mismatch" `Quick test_decode_source_index_mismatch;
          Alcotest.test_case "duplicate declaration name" `Quick test_decode_duplicate_name;
          Alcotest.test_case "table entry is not an object" `Quick test_decode_table_bad_entry;
          Alcotest.test_case "table entry has no name" `Quick test_decode_table_missing_name;
        ] );
      ( "irdecode",
        [
          Alcotest.test_case
            "irdecode i_imported_span_uses_own_source: imported span past main length EXPECTED-DECODE"
            `Quick test_decode_imported_span_past_main_length;
          Alcotest.test_case
            "irdecode i_no_silent_wrong_span: imported span past own source EXPECTED-REFUSE"
            `Quick test_decode_imported_span_past_own_source;
          Alcotest.test_case
            "irdecode i_span_decode_within_own_source: imported span inside both ranges EXPECTED-DECODE"
            `Quick test_decode_imported_span_in_both_ranges;
          Alcotest.test_case
            "irdecode i_imported_module_uses_own_source: imported module brace EXPECTED-DECODE"
            `Quick test_decode_module_imported_brace;
          Alcotest.test_case
            "irdecode i_no_wrong_source_brace: module end uses main brace EXPECTED-REFUSE"
            `Quick test_decode_module_wrong_source_brace;
          Alcotest.test_case
            "irdecode i_main_range_is_own_range: main span past own source EXPECTED-REFUSE"
            `Quick test_decode_main_span_past_own_source;
          Alcotest.test_case
            "irdecode i_nonsubject_not_in_census: const is a non-subject"
            `Quick test_declaration_const_is_nonsubject;
          Alcotest.test_case "declaration: var is a non-subject" `Quick
            test_declaration_var_is_nonsubject;
          Alcotest.test_case "declaration: typedef is a non-subject" `Quick
            test_declaration_typedef_is_nonsubject;
          Alcotest.test_case
            "irdecode i_census_is_subject: def is a reporting subject"
            `Quick test_declaration_def_is_subject;
          Alcotest.test_case
            "irdecode i_import_instance_evidence: import and instance decode as non-subjects EXPECTED-DECODE"
            `Quick test_decode_import_declaration;
          Alcotest.test_case "declaration: instance decodes as a non-subject EXPECTED-DECODE"
            `Quick test_decode_instance_declaration;
          Alcotest.test_case
            "irdecode i_assume_evidence: assume decodes as a non-subject EXPECTED-DECODE"
            `Quick test_decode_assume_declaration;
          Alcotest.test_case
            "irdecode i_unknown_kind_non_subject: unknown kind decodes as a non-subject EXPECTED-DECODE"
            `Quick test_decode_future_declaration;
          Alcotest.test_case
            "irdecode i_span_refusal_set: refusal is exactly the malformed set"
            `Quick test_decode_span_refusal_set;
          Alcotest.test_case
            "irdecode i_known_kind_decodes: every known kind decodes" `Quick
            test_decode_known_kind_decodes;
          Alcotest.test_case
            "irdecode i_source_map_contract: the eight source-map invariants"
            `Quick test_spec_i_source_map_contract;
          Alcotest.test_case
            "irdecode i_decl_kind_report_contract: the declaration and report-health invariants"
            `Quick test_spec_i_decl_kind_report_contract;
          Alcotest.test_case "irdecode i_contract: both composites" `Quick
            test_spec_i_contract;
        ] );
      ( "qcalc",
        [
          Alcotest.test_case "18-body pool" `Quick test_qcalc_pool;
          Alcotest.test_case "spine refusal" `Quick test_qcalc_spines;
          QCheck_alcotest.to_alcotest prop_exhaustive;
          QCheck_alcotest.to_alcotest prop_sound_true;
          QCheck_alcotest.to_alcotest prop_sound_false;
          QCheck_alcotest.to_alcotest prop_refuse;
          QCheck_alcotest.to_alcotest prop_eq_identity;
          QCheck_alcotest.to_alcotest prop_eq_distinct;
        ] );
      ( "rundisc",
        [
          Alcotest.test_case "rundisc i_total: 48-fact table" `Quick test_rundisc_table;
          QCheck_alcotest.to_alcotest prop_rundisc;
          Alcotest.test_case "init evidence cases" `Quick test_init_verdict_cases;
          QCheck_alcotest.to_alcotest prop_init_evidence;
        ] );
      ( "runner",
        [
          Alcotest.test_case "witness count parse" `Quick test_runner_witness_parse;
          Alcotest.test_case "state parse" `Quick test_runner_state_parse;
          Alcotest.test_case "Sys_error reason is path-independent" `Quick
            test_runner_sys_error_path_independent;
        ] );
      ( "checks",
        [
          Alcotest.test_case "QL001" `Quick test_ql001;
          Alcotest.test_case "QL002" `Quick test_ql002;
          Alcotest.test_case "QL002 field accessor" `Quick test_ql002_field;
          Alcotest.test_case "QL003" `Quick test_ql003;
          Alcotest.test_case "QL006" `Quick test_ql006;
          Alcotest.test_case "QL006 val chain" `Quick test_ql006_chain;
          Alcotest.test_case "QL006 opaque def" `Quick test_ql006_opaque_def;
          Alcotest.test_case "QL006 opaque def control" `Quick
            test_ql006_opaque_def_control;
          Alcotest.test_case "QL006 pure val chain" `Quick test_ql006_pure_chain;
          Alcotest.test_case "QL006 pure tautology" `Quick test_ql006_pure_tautology;
          Alcotest.test_case "QL006 subject constants" `Quick
            test_ql006_subject_constants;
          Alcotest.test_case "QL006 subject propositions" `Quick
            test_ql006_subject_propositions;
          Alcotest.test_case "QL006 corpus shapes" `Quick
            test_ql006_corpus_shapes;
          Alcotest.test_case "QL006 call refusal" `Quick
            test_ql006_call_refusal;
          Alcotest.test_case "QL006 param seed" `Quick test_ql006_param_seed;
          Alcotest.test_case "QP001 pure tautology" `Quick test_qp001_pure_tautology;
          Alcotest.test_case "QL006 parameterised subjects" `Quick
            test_ql006_parameterised_subjects;
          Alcotest.test_case "QP001 parameterised subjects" `Quick
            test_qp001_parameterised_subjects;
          Alcotest.test_case "QL006 pure parameter bound" `Quick
            test_ql006_pure_parameter_bound;
          Alcotest.test_case "QP001 pure parameter bound" `Quick
            test_qp001_pure_parameter_bound;
          Alcotest.test_case "pure state-reading single report" `Quick
            test_pure_state_reading_single_report;
          Alcotest.test_case "pure state-reading bool control" `Quick
            test_pure_state_reading_bool_control;
          Alcotest.test_case "QL008" `Quick test_ql008;
          Alcotest.test_case "QL008 helper assigns all" `Quick
            test_ql008_helper_all;
          Alcotest.test_case "QL008 helper assigns some" `Quick
            test_ql008_helper_partial;
          Alcotest.test_case "QL008 helper chain" `Quick
            test_ql008_helper_chain;
          Alcotest.test_case "QL008 helper cycle" `Quick
            test_ql008_helper_cycle;
          Alcotest.test_case "QL008 genuine stutter" `Quick
            test_ql008_stutter;
          Alcotest.test_case "QL008 pure def control" `Quick
            test_ql008_pure_def;
          Alcotest.test_case "QL009" `Quick test_ql009;
          Alcotest.test_case "QL009 reachable through helper" `Quick
            test_ql009_reach_helper;
          Alcotest.test_case "QL009 genuine orphan" `Quick test_ql009_orphan;
          Alcotest.test_case "QL009 call cycle" `Quick test_ql009_cycle;
          Alcotest.test_case "QL009 let-wrapped step" `Quick
            test_ql009_let_step;
          Alcotest.test_case "QL009 unknown step body" `Quick
            test_ql009_unknown_step;
          Alcotest.test_case "QL001 unknown body" `Quick test_ql001_unknown_body;
          Alcotest.test_case "finding source attribution" `Quick
            test_report_source_imported;
          Alcotest.test_case "QL001 wrapper call" `Quick test_ql001_wrapper;
          Alcotest.test_case "QL001 genuinely thin action" `Quick
            test_ql001_thin_leaf;
          Alcotest.test_case "QL001 pure def control" `Quick
            test_ql001_pure_call;
          Alcotest.test_case "QP001" `Quick test_qp001;
          Alcotest.test_case "QP002" `Quick test_qp002;
          Alcotest.test_case "QP002 pure val" `Quick test_qp002_pureval;
          Alcotest.test_case "QP002 parameter shadow" `Quick
            test_qp002_param_shadow;
          Alcotest.test_case "QP002 renamed parameter" `Quick
            test_qp002_param_renamed;
          Alcotest.test_case "QP002 genuine state read" `Quick
            test_qp002_genuine_read;
          Alcotest.test_case "QP002 let binder shadow" `Quick
            test_qp002_let_shadow;
          Alcotest.test_case "clean fixture has no findings" `Quick test_clean_spec;
        ] );
      ( "report",
        [
          Alcotest.test_case "human table" `Quick test_report_human;
          Alcotest.test_case "json shape" `Quick test_report_json;
          Alcotest.test_case "exit codes and thresholds" `Quick test_exit_codes_and_thresholds;
          Alcotest.test_case "checks array order" `Quick test_report_check_order;
          Alcotest.test_case "dedup: same definition reported once" `Quick
            test_report_dedup_same_definition;
          Alcotest.test_case "QL009 scope row is skipped" `Quick
            test_report_ql009_scope_skipped;
          Alcotest.test_case "QL009 entry row keeps warn" `Quick
            test_report_ql009_entry_keeps_warn;
          Alcotest.test_case "findings always carry spans" `Quick
            test_report_findings_always_carry_spans;
          Alcotest.test_case "dedup seam pin" `Quick test_report_dedup_seam;
          Alcotest.test_case "QP003 absent" `Quick test_qp003_absent;
          Alcotest.test_case "mixed-severity row carries Info text" `Quick
            test_report_mixed_severity_info;
        ] );
      ( "pipeline",
        [
          Alcotest.test_case "clean exits 0" `Quick test_pipeline_clean;
          Alcotest.test_case "finding exits 1" `Quick test_pipeline_fail;
          Alcotest.test_case "two-level import attribution" `Quick
            test_pipeline_attribution_two_levels;
          Alcotest.test_case "imported finding reported once" `Quick
            test_pipeline_import_reported_once;
          Alcotest.test_case "QL009 classifies the entry module only" `Quick
            test_pipeline_ql009_entry_only;
          Alcotest.test_case "parse-once cache" `Quick test_pipeline_cache;
          Alcotest.test_case "analysis errors exit 2" `Quick test_pipeline_errors;
          Alcotest.test_case "two-run stability" `Quick test_report_two_run_stability;
          Alcotest.test_case "full clean exits 0" `Quick test_full_clean;
          Alcotest.test_case "full violation names the action" `Quick test_full_violation;
          Alcotest.test_case "full false init fails QL007" `Quick test_full_init_false;
          Alcotest.test_case "full witness/invariant roles" `Quick
            test_full_witness_invariant_roles;
          Alcotest.test_case "full no init is a run error" `Quick
            test_full_no_init_init_error;
          Alcotest.test_case "full missing ITF evidence is exit 2" `Quick
            test_full_missing_itf_evidence;
          Alcotest.test_case "full corrupt ITF evidence is exit 2" `Quick
            test_full_corrupt_itf_evidence;
          Alcotest.test_case "full zero-state ITF evidence is exit 2" `Quick
            test_full_zero_state_itf_evidence;
          Alcotest.test_case
            "pipeline i_marker_is_not_a_binding: state shells are exit 2"
            `Quick test_full_shell_state_itf_evidence;
          Alcotest.test_case "full corrupt ITF diagnostic is byte-stable"
            `Quick test_full_corrupt_itf_diagnostic_stable;
          Alcotest.test_case "full unreadable ITF diagnostic is byte-stable"
            `Quick test_full_unreadable_itf_diagnostic_stable;
          Alcotest.test_case "full partial ITF evidence is disclosed" `Quick
            test_full_partial_itf_evidence;
          Alcotest.test_case "full partial ITF human report carries the count"
            `Quick test_full_partial_itf_human_count;
          Alcotest.test_case "full invariant name missing is exit 2" `Quick
            test_full_invariant_name_missing;
          Alcotest.test_case "full invariant name action is exit 2" `Quick
            test_full_invariant_name_action;
          Alcotest.test_case "full invariant name pure def is exit 2" `Quick
            test_full_invariant_name_pure_def;
          Alcotest.test_case "full invariant name pure val is exit 2" `Quick
            test_full_invariant_name_pure_val;
          Alcotest.test_case "full non-boolean invariant is exit 2" `Quick
            test_full_invariant_nonboolean;
          Alcotest.test_case "full failure marker is structural" `Quick
            test_full_failure_marker_structural;
          Alcotest.test_case "full false-init detail is stable" `Quick
            test_full_false_init_detail;
          Alcotest.test_case "CLI did-not-run exits 2" `Quick
            test_cli_full_did_not_run_exit_2;
          Alcotest.test_case "CLI exit contract" `Quick test_cli_exit_contract;
          Alcotest.test_case
            "pipeline i_pass_requires_real_binding / i_no_pass_on_junk: junk-valued state is not an observation"
            `Quick test_full_junk_value_itf_evidence;
          Alcotest.test_case
            "pipeline i_refused_disclosed: refused state is disclosed"
            `Quick test_full_refused_state_disclosed;
        ] );
      ( "sync",
        [
          Alcotest.test_case "spec invariant to cell map" `Quick
            test_spec_cell_map_mirror;
          Alcotest.test_case "README catalogue, exits and options" `Quick
            test_readme_sync;
        ] );
    ]
