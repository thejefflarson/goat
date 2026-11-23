(* Differential test driver (ADR 0037, decision 6).

   Reads the file `cargo run -p goat_checker --example core_corpus` writes, one
   program per line:

       MODE <TAB> SEXP <TAB> VERDICT <TAB> SOURCE

   MODE is `U` when every function and call in the program has one parameter
   or argument (the Coq calculus is curried, so the two languages agree on the
   whole program) and `N` when some has several (the Rust checker accepts only
   saturated calls, which the curried calculus also accepts, so only an
   acceptance can be compared).  SEXP is the program as a locally nameless
   term; VERDICT is `ERR` or `OK <canonical type>`.  MODE is `R` when the
   checker gives some part of the program a recursive type.  Its canonical
   type may then contain `(mu mK. T)`, a recursive type whose bound variable
   `mK` is named by its depth, and is compared as a regular tree: two types
   are equal when their unfoldings are, up to renaming of variables.  The
   algorithm builds recursive types and the coercions they need only up to a
   head `fold` or `unfold` (a deeper difference is a deep coercion, which it
   refuses); a program it refuses is counted, not compared.

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

let bop_of = function
  | "add" -> Bop_add
  | "sub" -> Bop_sub
  | "mul" -> Bop_mul
  | "div" -> Bop_div
  | "fdiv" -> Bop_fdiv
  | "rem" -> Bop_rem
  | "lt" -> Bop_lt
  | "lte" -> Bop_lte
  | "gt" -> Bop_gt
  | "gte" -> Bop_gte
  | "eq" -> Bop_eq
  | "ne" -> Bop_ne
  | o -> failwith ("unknown operator " ^ o)

let rec fields_of fields =
  List.fold_right
    (fun f rest ->
      match f with
      | List [ l; List [ Atom "meth"; e ] ] -> Fs_meth (int_of l, exp_of e, rest)
      | List [ l; e ] -> Fs_cons (int_of l, exp_of e, rest)
      | _ -> failwith "malformed field")
    fields Fs_nil

and exp_of = function
  | Atom "t" -> E_true
  | Atom "f" -> E_false
  | Atom "u" -> E_unit
  | List [ Atom "d"; k ] -> E_dec (int_of k)
  | List (Atom "str" :: bytes) -> E_str (List.map int_of bytes)
  | List [ Atom "if"; c; a; b ] -> E_ite (exp_of c, exp_of a, exp_of b)
  | List [ Atom "bin"; Atom o; a; b ] -> E_bin (exp_of a, bop_of o, exp_of b)
  | List [ Atom "float"; e ] -> E_tofloat (exp_of e)
  | List [ Atom "b"; i ] -> E_fvar_b (int_of i)
  | List [ Atom "n"; k ] -> E_num (int_of k)
  | List [ Atom "abs"; e ] -> E_abs (exp_of e)
  | List [ Atom "app"; f; a ] -> E_app (exp_of f, exp_of a)
  | List [ Atom "let"; v; b ] -> E_let (exp_of v, exp_of b)
  | List [ Atom "proj"; e; l ] -> E_proj (exp_of e, int_of l)
  | List (Atom "rec" :: fields) -> E_rec (fields_of fields)
  | List [ Atom "spread"; e; l; v ] -> E_spread (exp_of e, int_of l, exp_of v)
  | List [ Atom "restrict"; e; l ] -> E_restrict (exp_of e, int_of l)
  | List [ Atom "letrec"; List (Atom "rec" :: fields); body ] ->
      E_letrec (fields_of fields, exp_of body)
  | _ -> failwith "malformed term"

(* ---- the canonical type ---- *)

(* Fields in label order (a stable sort, so equal labels keep their order, which
   is the scoped-label equivalence), variables numbered by first occurrence. *)
let canonical_type d t =
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
    | Typ_Int -> Buffer.add_string b "Number"
    | Typ_Float -> Buffer.add_string b "Float"
    | Typ_Bool -> Buffer.add_string b "Bool"
    | Typ_Unit -> Buffer.add_string b "Unit"
    | Typ_String -> Buffer.add_string b "String"
    | Typ_Arrow (x, y) ->
        Buffer.add_char b '(';
        typ x;
        Buffer.add_string b " -> ";
        typ y;
        Buffer.add_char b ')'
    | Typ_Record r ->
        (* A presence entry is a field when its presence is Unit, absent (and
           dropped) when it is Bool, and keeps its presence variable otherwise. *)
        let rec spine fields = function
          | Row_Empty -> (List.rev fields, None)
          | Row_Var a -> (List.rev fields, Some a)
          | Row_Ext (l, t, rest) -> spine ((l, None, t) :: fields) rest
          | Row_Maybe (l, Typ_Unit, t, rest) -> spine ((l, None, t) :: fields) rest
          | Row_Maybe (_, Typ_Bool, _, rest) -> spine fields rest
          | Row_Maybe (l, p, t, rest) -> spine ((l, Some p, t) :: fields) rest
        in
        let fields, tail = spine [] r in
        let fields = List.stable_sort (fun (l, _, _) (m, _, _) -> compare l m) fields in
        Buffer.add_char b '{';
        List.iteri
          (fun i (l, pres, t) ->
            if i > 0 then Buffer.add_string b ", ";
            Buffer.add_string b (Printf.sprintf "l%d" l);
            (match pres with
            | None -> ()
            | Some (Typ_Var a) -> Buffer.add_string b (Printf.sprintf "^v%d" (name a))
            | Some _ -> Buffer.add_string b "^?");
            Buffer.add_string b ": ";
            typ t)
          fields;
        (match tail with
        | None -> ()
        | Some a ->
            Buffer.add_string b (if fields = [] then "| " else " | ");
            Buffer.add_string b (Printf.sprintf "v%d" (name a)));
        Buffer.add_char b '}'
    | Typ_Var a -> (
        match d a with
        | K_Literal -> Buffer.add_string b "Number"
        | _ -> Buffer.add_string b (Printf.sprintf "v%d" (name a)))
  in
  typ t;
  Buffer.contents b


(* ---- types as regular trees ---- *)

type tree =
  | TNum | TFloat | TBool | TUnit | TStr
  | TArrow of tree * tree
  | TRecord of (int * int option * tree) list * int option
  | TVar of int
  | TBound of int
  | TMu of int * tree

(* The canonical text of a recursive type: `canonical_type`'s grammar with
   `(mu mK. T)` and `mK` added. *)
let tree_of_text s =
  let n = String.length s in
  let pos = ref 0 in
  let fail () = failwith ("malformed type: " ^ s) in
  let peek () = if !pos < n then s.[!pos] else '\000' in
  let eat str =
    let l = String.length str in
    if !pos + l <= n && String.sub s !pos l = str then pos := !pos + l else fail ()
  in
  let looking_at str =
    let l = String.length str in
    !pos + l <= n && String.sub s !pos l = str
  in
  let number () =
    let i = !pos in
    while !pos < n && s.[!pos] >= '0' && s.[!pos] <= '9' do incr pos done;
    if !pos = i then fail () else int_of_string (String.sub s i (!pos - i))
  in
  let rec typ () =
    if looking_at "Number" then (eat "Number"; TNum)
    else if looking_at "Float" then (eat "Float"; TFloat)
    else if looking_at "Bool" then (eat "Bool"; TBool)
    else if looking_at "Unit" then (eat "Unit"; TUnit)
    else if looking_at "String" then (eat "String"; TStr)
    else
      match peek () with
      | 'v' -> incr pos; TVar (number ())
      | 'm' -> incr pos; TBound (number ())
      | '(' ->
          incr pos;
          if looking_at "mu m" then begin
            eat "mu m";
            let k = number () in
            eat ". ";
            let body = typ () in
            eat ")";
            TMu (k, body)
          end else begin
            let a = typ () in
            eat " -> ";
            let b = typ () in
            eat ")";
            TArrow (a, b)
          end
      | '{' ->
          incr pos;
          let fields = ref [] and tail = ref None in
          let field () =
            eat "l";
            let l = number () in
            let pres = if looking_at "^v" then (eat "^v"; Some (number ())) else None in
            eat ": ";
            fields := (l, pres, typ ()) :: !fields
          in
          if looking_at "| v" then (eat "| v"; tail := Some (number ()))
          else if peek () <> '}' then begin
            field ();
            let continue = ref true in
            while !continue do
              if looking_at ", " then (eat ", "; field ())
              else if looking_at " | v" then (eat " | v"; tail := Some (number ()); continue := false)
              else continue := false
            done
          end;
          eat "}";
          TRecord (List.rev !fields, !tail)
      | _ -> fail ()
  in
  let t = typ () in
  if !pos <> n then fail () else t

(* The algorithm's type as a tree; a bound index becomes the depth of its
   binder, as in the text. *)
let tree_of_typ d t =
  let rec typ depth = function
    | Typ_Int -> TNum
    | Typ_Float -> TFloat
    | Typ_Bool -> TBool
    | Typ_Unit -> TUnit
    | Typ_String -> TStr
    | Typ_Arrow (x, y) -> TArrow (typ depth x, typ depth y)
    | Typ_Record r ->
        let rec spine fields = function
          | Row_Empty -> (List.rev fields, None)
          | Row_Var a -> (List.rev fields, Some (Atom.nat_of a))
          | Row_Ext (l, t, rest) -> spine ((l, None, typ depth t) :: fields) rest
          | Row_Maybe (l, Typ_Unit, t, rest) -> spine ((l, None, typ depth t) :: fields) rest
          | Row_Maybe (_, Typ_Bool, _, rest) -> spine fields rest
          | Row_Maybe (l, Typ_Var p, t, rest) -> spine ((l, Some (Atom.nat_of p), typ depth t) :: fields) rest
          | Row_Maybe (l, _, t, rest) -> spine ((l, Some (-1), typ depth t) :: fields) rest
        in
        let fields, tail = spine [] r in
        TRecord (List.stable_sort (fun (l, _, _) (m, _, _) -> compare l m) fields, tail)
    | Typ_Var a -> (
        match d a with K_Literal -> TNum | _ -> TVar (Atom.nat_of a))
    | Typ_Bvar i -> TBound (depth - 1 - i)
    | Typ_Mu b -> TMu (depth, typ (depth + 1) b)
    | Typ_Grp _ -> failwith "tag group"
  in
  typ 0 t

(* Bisimulation with assumed pairs: a pair of recursive types met again is
   taken as equal, and the variables of the two sides correspond one to one. *)
let trees_equal a b =
  let left = Hashtbl.create 16 and right = Hashtbl.create 16 in
  let same_var i j =
    match Hashtbl.find_opt left i, Hashtbl.find_opt right j with
    | None, None -> Hashtbl.add left i j; Hashtbl.add right j i; true
    | Some j', Some i' -> j' = j && i' = i
    | _ -> false
  in
  let rec subst k u = function
    | TBound j when j = k -> u
    | TMu (j, body) when j = k -> TMu (j, body)
    | TMu (j, body) -> TMu (j, subst k u body)
    | TArrow (x, y) -> TArrow (subst k u x, subst k u y)
    | TRecord (fields, tail) ->
        TRecord (List.map (fun (l, p, t) -> (l, p, subst k u t)) fields, tail)
    | t -> t
  in
  let assumed = ref [] in
  let rec go a b =
    List.mem (a, b) !assumed
    ||
    match a, b with
    | TMu (k, body), _ -> assumed := (a, b) :: !assumed; go (subst k a body) b
    | _, TMu (k, body) -> assumed := (a, b) :: !assumed; go a (subst k b body)
    | TNum, TNum | TFloat, TFloat | TBool, TBool | TUnit, TUnit | TStr, TStr -> true
    | TArrow (x, y), TArrow (x', y') -> go x x' && go y y'
    | TRecord (f, t), TRecord (f', t') ->
        List.length f = List.length f'
        && List.for_all2
             (fun (l, p, x) (l', p', x') ->
               l = l' && (match p, p' with
                          | None, None -> true
                          | Some i, Some j -> if i < 0 || j < 0 then i = j else same_var i j
                          | _ -> false)
               && go x x')
             f f'
        && (match t, t' with
            | None, None -> true
            | Some i, Some j -> same_var i j
            | _ -> false)
    | TVar i, TVar j -> same_var i j
    | TBound i, TBound j -> i = j
    | _ -> false
  in
  go a b

(* ---- the comparison ---- *)

let fuel = 100_000

let () =
  let path = if Array.length Sys.argv > 1 then Sys.argv.(1) else "-" in
  let ic = if path = "-" then stdin else open_in path in
  let unary = ref 0 and curried = ref 0 and skipped = ref 0 and bad = ref 0 in
  let recursive = ref 0 and rec_compared = ref 0 and rec_refused = ref 0 and row_knots = ref 0 in
  let line_no = ref 0 in
  (try
     while true do
       let line = input_line ic in
       incr line_no;
       match String.split_on_char '\t' line with
       | mode :: sexp :: verdict :: source ->
           let solved = infer_closed_env fuel (exp_of (parse_sexp sexp)) in
           let ours =
             match solved with
             | Some (d, t) -> (try "OK " ^ canonical_type d t with Match_failure _ -> "OK ?")
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
           | "R" | "K" -> (
               incr recursive;
               match solved with
               | None ->
                   incr (if mode = "K" then row_knots else rec_refused);
                   let source = String.concat "" source in
                   Printf.printf "refused line %d: %s\n" !line_no
                     (if String.length source > 100 then String.sub source 0 100 ^ "..." else source)
               | Some (d, t) ->
                   incr rec_compared;
                   let theirs = String.sub verdict 3 (String.length verdict - 3) in
                   if verdict = "ERR" || not (trees_equal (tree_of_typ d t) (tree_of_text theirs))
                   then report ())
           | _ -> failwith ("unknown mode " ^ mode))
       | _ -> failwith (Printf.sprintf "line %d is not MODE<TAB>SEXP<TAB>VERDICT<TAB>SOURCE" !line_no)
     done
   with End_of_file -> ());
  Printf.printf
    "programs compared: %d (one-parameter: %d, curried accepts: %d), skipped: %d, \
     recursive-type programs: %d (compared: %d, refused: %d, of which a row that must knot: %d), mismatches: %d\n"
    (!unary + !curried + !rec_compared) !unary !curried !skipped !recursive !rec_compared (!rec_refused + !row_knots) !row_knots !bad;
  if !bad > 0 || !unary + !curried = 0 then exit 1
