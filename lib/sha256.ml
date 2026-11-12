(** SHA-256, FIPS 180-4.

    Used for the IR digest in the report. Stdlib only: [Digest] is MD5 and no
    crypto library is a production dependency. Licence: AGPLv3 - see LICENSE. *)

let k =
  Array.map Int32.of_string
    [|
      "0x428a2f98"; "0x71374491"; "0xb5c0fbcf"; "0xe9b5dba5";
      "0x3956c25b"; "0x59f111f1"; "0x923f82a4"; "0xab1c5ed5";
      "0xd807aa98"; "0x12835b01"; "0x243185be"; "0x550c7dc3";
      "0x72be5d74"; "0x80deb1fe"; "0x9bdc06a7"; "0xc19bf174";
      "0xe49b69c1"; "0xefbe4786"; "0x0fc19dc6"; "0x240ca1cc";
      "0x2de92c6f"; "0x4a7484aa"; "0x5cb0a9dc"; "0x76f988da";
      "0x983e5152"; "0xa831c66d"; "0xb00327c8"; "0xbf597fc7";
      "0xc6e00bf3"; "0xd5a79147"; "0x06ca6351"; "0x14292967";
      "0x27b70a85"; "0x2e1b2138"; "0x4d2c6dfc"; "0x53380d13";
      "0x650a7354"; "0x766a0abb"; "0x81c2c92e"; "0x92722c85";
      "0xa2bfe8a1"; "0xa81a664b"; "0xc24b8b70"; "0xc76c51a3";
      "0xd192e819"; "0xd6990624"; "0xf40e3585"; "0x106aa070";
      "0x19a4c116"; "0x1e376c08"; "0x2748774c"; "0x34b0bcb5";
      "0x391c0cb3"; "0x4ed8aa4a"; "0x5b9cca4f"; "0x682e6ff3";
      "0x748f82ee"; "0x78a5636f"; "0x84c87814"; "0x8cc70208";
      "0x90befffa"; "0xa4506ceb"; "0xbef9a3f7"; "0xc67178f2";
    |]

let rotr x n =
  Int32.logor (Int32.shift_right_logical x n) (Int32.shift_left x (32 - n))

let block h block =
  let w = Array.make 64 0l in
  for i = 0 to 15 do
    let b = i * 4 in
    w.(i) <-
      Int32.logor
        (Int32.shift_left (Int32.of_int (Char.code block.[b])) 24)
        (Int32.logor
           (Int32.shift_left (Int32.of_int (Char.code block.[b + 1])) 16)
           (Int32.logor
              (Int32.shift_left (Int32.of_int (Char.code block.[b + 2])) 8)
              (Int32.of_int (Char.code block.[b + 3]))))
  done;
  for i = 16 to 63 do
    let s0 =
      Int32.logxor (rotr w.(i - 15) 7)
        (Int32.logxor (rotr w.(i - 15) 18) (Int32.shift_right_logical w.(i - 15) 3))
    in
    let s1 =
      Int32.logxor (rotr w.(i - 2) 17)
        (Int32.logxor (rotr w.(i - 2) 19) (Int32.shift_right_logical w.(i - 2) 10))
    in
    w.(i) <- Int32.add (Int32.add w.(i - 16) s0) (Int32.add w.(i - 7) s1)
  done;
  let a = ref h.(0) and b = ref h.(1) and c = ref h.(2) and d = ref h.(3) in
  let e = ref h.(4) and f = ref h.(5) and g = ref h.(6) and hh = ref h.(7) in
  for i = 0 to 63 do
    let s1 =
      Int32.logxor (rotr !e 6) (Int32.logxor (rotr !e 11) (rotr !e 25))
    in
    let ch = Int32.logxor (Int32.logand !e !f) (Int32.logand (Int32.lognot !e) !g) in
    let t1 =
      Int32.add (Int32.add (Int32.add !hh s1) ch) (Int32.add k.(i) w.(i))
    in
    let s0 =
      Int32.logxor (rotr !a 2) (Int32.logxor (rotr !a 13) (rotr !a 22))
    in
    let maj =
      Int32.logxor (Int32.logand !a !b)
        (Int32.logxor (Int32.logand !a !c) (Int32.logand !b !c))
    in
    let t2 = Int32.add s0 maj in
    hh := !g;
    g := !f;
    f := !e;
    e := Int32.add !d t1;
    d := !c;
    c := !b;
    b := !a;
    a := Int32.add t1 t2
  done;
  h.(0) <- Int32.add h.(0) !a;
  h.(1) <- Int32.add h.(1) !b;
  h.(2) <- Int32.add h.(2) !c;
  h.(3) <- Int32.add h.(3) !d;
  h.(4) <- Int32.add h.(4) !e;
  h.(5) <- Int32.add h.(5) !f;
  h.(6) <- Int32.add h.(6) !g;
  h.(7) <- Int32.add h.(7) !hh

let digest_bytes s =
  let len = String.length s in
  let h =
    [|
      0x6a09e667l; 0xbb67ae85l; 0x3c6ef372l; 0xa54ff53al;
      0x510e527fl; 0x9b05688cl; 0x1f83d9abl; 0x5be0cd19l;
    |]
  in
  let full = len / 64 in
  for i = 0 to full - 1 do
    block h (String.sub s (i * 64) 64)
  done;
  let rest = len - (full * 64) in
  let tail = Bytes.make 128 '\000' in
  Bytes.blit_string s (full * 64) tail 0 rest;
  Bytes.set tail rest '\x80';
  let tail_len = if rest < 56 then 64 else 128 in
  let bits = Int64.mul (Int64.of_int len) 8L in
  for i = 0 to 7 do
    let shift = 56 - (i * 8) in
    Bytes.set tail (tail_len - 8 + i)
      (Char.chr
         (Int64.to_int (Int64.logand (Int64.shift_right_logical bits shift) 0xffL)))
  done;
  for i = 0 to (tail_len / 64) - 1 do
    block h (Bytes.sub_string tail (i * 64) 64)
  done;
  let buf = Buffer.create 64 in
  Array.iter (fun x -> Buffer.add_string buf (Printf.sprintf "%08lx" x)) h;
  Buffer.contents buf
