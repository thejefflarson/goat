let fuel = 100_000

let () =
  let ic = open_in Sys.argv.(1) in
  let total = ref 0 and refused = ref 0 in
  let inner = ref 0 and rowv = ref 0 and both = ref 0 and other = ref 0 in
  let line_no = ref 0 in
  let show tag source =
    let source = String.concat "" source in
    Printf.printf "%s line %d: %s\n" tag !line_no
      (if String.length source > 100 then String.sub source 0 100 ^ "..." else source)
  in
  (try
     while true do
       let line = input_line ic in
       incr line_no;
       match String.split_on_char '\t' line with
       | _ :: sexp :: verdict :: source when verdict <> "ERR" ->
           incr total;
           let e = exp_of (parse_sexp sexp) in
           let run t r =
             len_t := t;
             len_r := r;
             let ok = infer_closed_env fuel e <> None in
             len_t := false;
             len_r := false;
             ok
           in
           if not (run false false) then begin
             incr refused;
             if run true false then (incr inner; show "inner variable" source)
             else if run false true then (incr rowv; show "row variable" source)
             else if run true true then (incr both; show "both" source)
             else incr other
           end
       | _ -> ()
     done
   with End_of_file -> ());
  Printf.printf
    "checker-accepted programs: %d, refused by the algorithm: %d (inner variable: %d, row variable: %d, both: %d, other: %d)\n"
    !total !refused !inner !rowv !both !other
