(* Compares the parser extracted from proofs/GoatPegExec.v with parser::interp.

   It reads what parser/examples/parse_dump.rs writes (differential/README.md):
   one line per source with its parser tokens and the tree the Rust parser built,
   or ERR.  The extracted [parse_fuel] reads the same tokens, and the trees are
   compared as text.  Running out of fuel, a difference in a tree, or a parse on
   one side only is printed and the exit status is 1. *)

let string_of_chars cs = String.init (List.length cs) (List.nth cs)

let chars s = List.init (String.length s) (String.get s)

let unescape s =
  let buf = Buffer.create (String.length s) in
  let i = ref 0 in
  while !i < String.length s do
    if s.[!i] = '%' then begin
      Buffer.add_char buf (Char.chr (int_of_string ("0x" ^ String.sub s (!i + 1) 2)));
      i := !i + 3
    end
    else begin
      Buffer.add_char buf s.[!i];
      incr i
    end
  done;
  Buffer.contents buf

let escape s =
  let buf = Buffer.create (String.length s) in
  String.iter
    (function
      | ('%' | ' ' | '\t' | '\n' | '\r') as c ->
          Buffer.add_string buf (Printf.sprintf "%%%02X" (Char.code c))
      | c -> Buffer.add_char buf c)
    s;
  Buffer.contents buf

let tok_of word =
  let text = unescape (String.sub word 1 (String.length word - 1)) in
  match word.[0] with
  | 'I' -> Goat_parse.TName (chars text)
  | 'N' -> Goat_parse.TNum 0
  | 'S' -> Goat_parse.TStr
  | 'Y' -> Goat_parse.TSym (chars text)
  | _ -> failwith ("unreadable token: " ^ word)

let tok_text = function
  | Goat_parse.TName cs -> "I" ^ escape (string_of_chars cs)
  | TNum _ | TDec _ -> "N"
  | TStr -> "S"
  | TSym cs -> "Y" ^ escape (string_of_chars cs)

let rec tree_text buf = function
  | Goat_parse.Leaf k -> Buffer.add_string buf (tok_text k)
  | Node (r, cs) ->
      Buffer.add_char buf '(';
      Buffer.add_string buf (string_of_chars (Goat_parse.rule_name r));
      List.iter
        (fun c ->
          Buffer.add_char buf ' ';
          tree_text buf c)
        cs;
      Buffer.add_char buf ')'

let ours tokens =
  let fuel = 400 * (List.length tokens + 8) in
  match Goat_parse.parse_fuel fuel tokens with
  | None -> "FUEL"
  | Some Fail -> "ERR"
  | Some (Ok ([ t ], [])) ->
      let buf = Buffer.create 256 in
      tree_text buf t;
      Buffer.contents buf
  | Some (Ok _) -> "SHAPE"

let () =
  let sources = ref 0 and parsed = ref 0 and failures = ref 0 and tokens = ref 0 in
  let ic = open_in Sys.argv.(1) in
  (try
     while true do
       let line = input_line ic in
       match String.split_on_char '\t' line with
       | [ "P"; spelled; expected ] ->
           let words = String.split_on_char ' ' spelled |> List.filter (fun s -> s <> "") in
           incr sources;
           tokens := !tokens + List.length words;
           if expected <> "ERR" then incr parsed;
           let got = try ours (List.map tok_of words) with Stack_overflow -> "STACK" in
           if got <> expected then begin
             incr failures;
             if !failures <= 5 then
               Printf.printf "MISMATCH source %d\n  tokens: %s\n  rust:   %s\n  coq:    %s\n" !sources
                 (if String.length spelled > 300 then String.sub spelled 0 300 ^ "..." else spelled)
                 expected got
           end
       | _ -> failwith ("unreadable line: " ^ line)
     done
   with End_of_file -> ());
  Printf.printf "parse differential: %d sources (%d parse), %d tokens, %d disagreements\n" !sources
    !parsed !tokens !failures;
  if !failures > 0 then exit 1
