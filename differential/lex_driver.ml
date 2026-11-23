(* Compares the lexer extracted from proofs/GoatLex.v with parser::lexer.

   It reads what parser/examples/lex_dump.rs writes (differential/README.md):
   the Unicode identifier tables, then one line per source with the tokens
   the Rust lexer found.  The extracted [lex] gets the Rust tables for the
   code points of 128 and up, and the driver first checks that the model's own
   ASCII answer is the table's.  Any difference in a token's kind or span is
   printed and the exit status is 1. *)

let kind_letter = function
  | Goat_lex.KWhitespace -> 'W'
  | KComment -> 'C'
  | KString -> 'S'
  | KNumber -> 'N'
  | KLiteral -> 'L'
  | KKeyword -> 'K'
  | KName -> 'I'
  | KOperator -> 'O'
  | KPunct -> 'P'
  | KUnknown -> 'U'

let in_ranges ranges c =
  let rec go lo hi =
    lo <= hi
    &&
    let mid = (lo + hi) / 2 in
    let a, b = ranges.(mid) in
    if c < a then go lo (mid - 1) else if c > b then go (mid + 1) hi else true
  in
  go 0 (Array.length ranges - 1)

let tokens_text tokens =
  let at = ref 0 in
  tokens
  |> List.map (fun (t : Goat_lex.token) ->
         let start = !at in
         at := start + List.length t.tx;
         Printf.sprintf "%c:%d:%d" (kind_letter t.kd) start !at)
  |> String.concat " "

let ascii_check () =
  let no_table _ = failwith "the model asked the table about an ASCII code point" in
  for c = 0 to 127 do
    let letter = match Char.chr c with 'A' .. 'Z' | 'a' .. 'z' -> true | _ -> false in
    let digit_or_underscore = match Char.chr c with '0' .. '9' | '_' -> true | _ -> false in
    if Goat_lex.xs no_table c <> letter || Goat_lex.xc no_table c <> (letter || digit_or_underscore)
    then begin
      Printf.printf "MISMATCH ASCII code point %d\n" c;
      exit 1
    end
  done

let () =
  ascii_check ();
  let starts = ref [] and conts = ref [] in
  let tables = ref None in
  let sources = ref 0 and tokens = ref 0 and failures = ref 0 in
  let ic = open_in Sys.argv.(1) in
  (try
     while true do
       let line = input_line ic in
       match String.split_on_char '\t' line with
       | [ "X"; "S"; lo; hi ] -> starts := (int_of_string lo, int_of_string hi) :: !starts
       | [ "X"; "C"; lo; hi ] -> conts := (int_of_string lo, int_of_string hi) :: !conts
       | [ "L"; cps; expected ] ->
           let xid_start, xid_cont =
             match !tables with
             | Some t -> t
             | None ->
                 let starts = Array.of_list (List.rev !starts)
                 and conts = Array.of_list (List.rev !conts) in
                 let t = (in_ranges starts, in_ranges conts) in
                 tables := Some t;
                 t
           in
           let code_points =
             String.split_on_char ' ' cps |> List.filter (fun s -> s <> "") |> List.map int_of_string
           in
           let ours = tokens_text (Goat_lex.lex xid_start xid_cont code_points) in
           incr sources;
           if expected <> "" then tokens := !tokens + List.length (String.split_on_char ' ' expected);
           if ours <> expected then begin
             incr failures;
             if !failures <= 5 then
               Printf.printf "MISMATCH source %d\n  source: %s\n  rust:   %s\n  coq:    %s\n" !sources
                 (if String.length cps > 200 then String.sub cps 0 200 ^ "..." else cps)
                 expected ours
           end
       | _ -> failwith ("unreadable line: " ^ line)
     done
   with End_of_file -> ());
  Printf.printf "lex differential: %d sources, %d tokens, %d disagreements\n" !sources !tokens
    !failures;
  if !failures > 0 then exit 1
