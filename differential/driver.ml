(* Differential test driver (ADR 0037, decision 6).

   Reads the file `cargo run -p goat_checker --example core_corpus` writes, one
   program per line:

       MODE <TAB> SEXP <TAB> VERDICT <TAB> SOURCE

   MODE is `U` when every function and call in the program has one parameter
   or argument (the Coq calculus is curried, so the two languages agree on the
   whole program) and `N` when some has several (the Rust checker accepts only
   saturated calls, which the curried calculus also accepts, so only an
   acceptance can be compared).  SEXP is the program as a locally nameless
   term; VERDICT is `ERR` or `OK <canonical type>`.

   Runs the extracted, proven algorithm on each program and fails on any
   disagreement in acceptance or in the type up to renaming of variables. *)

open Goat_infer

(* ---- the program syntax ---- *)

type sexp = Atom of string | List of sexp list

let tokenize s =
  let n = String.length s in
  let rec go i acc =
    if i >= n then List.rev acc
    else
      match s.[i] with
      | ' ' | '\t' -> go (i + 1) acc
      | '(' -> go (i + 1) ("(" :: acc)
      | ')' -> go (i + 1) (")" :: acc)
      | _ ->
          let j = ref i in
          while !j < n && s.[!j] <> ' ' && s.[!j] <> '(' && s.[!j] <> ')' do incr j done;
          go !j (String.sub s i (!j - i) :: acc)
  in
  go 0 []

let parse_sexp s =
  let rec one = function
    | "(" :: rest ->
        let rec items acc = function
          | ")" :: rest -> (List (List.rev acc), rest)
          | toks ->
              let x, rest = one toks in
              items (x :: acc) rest
        in
        items [] rest
    | tok :: rest when tok <> ")" -> (Atom tok, rest)
    | _ -> failwith "malformed s-expression"
  in
  match one (tokenize s) with x, [] -> x | _ -> failwith "trailing tokens"

let int_of = function Atom a -> int_of_string a | List _ -> failwith "expected a number"

let rec exp_of = function
  | Atom "t" -> E_true
  | Atom "f" -> E_false
  | List [ Atom "b"; i ] -> E_fvar_b (int_of i)
  | List [ Atom "n"; k ] -> E_num (int_of k)
  | List [ Atom "abs"; e ] -> E_abs (exp_of e)
  | List [ Atom "app"; f; a ] -> E_app (exp_of f, exp_of a)
  | List [ Atom "let"; v; b ] -> E_let (exp_of v, exp_of b)
  | List [ Atom "proj"; e; l ] -> E_proj (exp_of e, int_of l)
  | List (Atom "rec" :: fields) ->
      List.fold_right
        (fun f rest ->
          match f with
          | List [ l; e ] -> Fs_cons (int_of l, exp_of e, rest)
          | _ -> failwith "malformed field")
        fields Fs_nil
      |> fun fs -> E_rec fs
  | _ -> failwith "malformed term"

(* ---- the canonical type ---- *)

(* Fields in label order (a stable sort, so equal labels keep their order, which
   is the scoped-label equivalence), variables numbered by first occurrence. *)
let canonical_type t =
  let vars = ref [] in
  let name a =
    let a = Atom.nat_of a in
    match List.assoc_opt a !vars with
    | Some i -> i
    | None ->
        let i = List.length !vars in
        vars := (a, i) :: !vars;
        i
  in
  let b = Buffer.create 64 in
  let rec typ = function
    | Typ_Number -> Buffer.add_string b "Number"
    | Typ_Bool -> Buffer.add_string b "Bool"
    | Typ_Arrow (x, y) ->
        Buffer.add_char b '(';
        typ x;
        Buffer.add_string b " -> ";
        typ y;
        Buffer.add_char b ')'
    | Typ_Record r ->
        let rec spine fields = function
          | Row_Empty -> (List.rev fields, None)
          | Row_Var a -> (List.rev fields, Some a)
          | Row_Ext (l, t, rest) -> spine ((l, t) :: fields) rest
        in
        let fields, tail = spine [] r in
        let fields = List.stable_sort (fun (l, _) (m, _) -> compare l m) fields in
        Buffer.add_char b '{';
        List.iteri
          (fun i (l, t) ->
            if i > 0 then Buffer.add_string b ", ";
            Buffer.add_string b (Printf.sprintf "l%d: " l);
            typ t)
          fields;
        (match tail with
        | None -> ()
        | Some a ->
            Buffer.add_string b (if fields = [] then "| " else " | ");
            Buffer.add_string b (Printf.sprintf "v%d" (name a)));
        Buffer.add_char b '}'
    | Typ_Var a -> Buffer.add_string b (Printf.sprintf "v%d" (name a))
  in
  typ t;
  Buffer.contents b

(* ---- the comparison ---- *)

let fuel = 100_000

let () =
  let path = if Array.length Sys.argv > 1 then Sys.argv.(1) else "-" in
  let ic = if path = "-" then stdin else open_in path in
  let unary = ref 0 and curried = ref 0 and skipped = ref 0 and bad = ref 0 in
  let line_no = ref 0 in
  (try
     while true do
       let line = input_line ic in
       incr line_no;
       match String.split_on_char '\t' line with
       | mode :: sexp :: verdict :: source ->
           let ours =
             match infer_closed fuel (exp_of (parse_sexp sexp)) with
             | Some t -> "OK " ^ canonical_type t
             | None -> "ERR"
           in
           let report () =
             incr bad;
             Printf.printf "MISMATCH line %d\n  source:  %s\n  term:    %s\n  rust:    %s\n  coq:     %s\n"
               !line_no (String.concat "" source) sexp verdict ours
           in
           (match mode with
           | "U" -> incr unary; if ours <> verdict then report ()
           | "N" when verdict <> "ERR" -> incr curried; if ours <> verdict then report ()
           | "N" -> incr skipped
           | _ -> failwith ("unknown mode " ^ mode))
       | _ -> failwith (Printf.sprintf "line %d is not MODE<TAB>SEXP<TAB>VERDICT<TAB>SOURCE" !line_no)
     done
   with End_of_file -> ());
  Printf.printf
    "programs compared: %d (one-parameter: %d, curried accepts: %d), skipped: %d, mismatches: %d\n"
    (!unary + !curried) !unary !curried !skipped !bad;
  if !bad > 0 || !unary + !curried = 0 then exit 1
