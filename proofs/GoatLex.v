(* The lexer (phase 8, stage 1): source text to tokens, and what makes it
   a lexer: the tokens tile the source with no gap, each is the longest any
   class matches, and a reserved word ends at a word boundary.

   The model reads a source as a list of Unicode code points (the Rust lexer
   reads a UTF-8 [&str], so decoding is the host's, and [make differential]
   compares token spans after converting byte offsets to code-point offsets).
   Each class of token is a function that returns how many code points of the
   rest of the input it matches, 0 for none; the lexer takes the longest
   match, the earlier class on a tie, and an unmatched code point is a token
   of its own (consecutive ones merge).  [lexer.rs] tries the classes in that
   order and takes the first that fits; the differential test checks the two
   agree.

   The Unicode identifier tables are not here.  [xid_start_hi] and
   [xid_cont_hi] answer for code points of 128 and above, and every theorem is
   stated for any answer; ASCII is decided in the model. *)

From Stdlib Require Import List String Ascii Arith Bool Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

Definition is_ws (c : nat) : bool := (c =? 32) || (c =? 9) || (c =? 10) || (c =? 13).
Definition is_nl (c : nat) : bool := (c =? 10) || (c =? 13).
Definition is_digit (c : nat) : bool := (48 <=? c) && (c <=? 57).
Definition ascii_alpha (c : nat) : bool :=
  ((65 <=? c) && (c <=? 90)) || ((97 <=? c) && (c <=? 122)).

Definition cps (s : string) : list nat :=
  map nat_of_ascii (list_ascii_of_string s).

Fixpoint span (p : nat -> bool) (r : list nat) : nat :=
  match r with
  | c :: t => if p c then S (span p t) else 0
  | [] => 0
  end.

Fixpoint prefixb (w r : list nat) : bool :=
  match w, r with
  | [], _ => true
  | a :: w', b :: r' => (a =? b) && prefixb w' r'
  | _ :: _, [] => false
  end.

Inductive kind : Type :=
  | KWhitespace | KComment | KString | KNumber | KLiteral | KKeyword
  | KName | KOperator | KPunct | KUnknown.

Definition kind_eqb (a b : kind) : bool :=
  match a, b with
  | KWhitespace, KWhitespace | KComment, KComment | KString, KString
  | KNumber, KNumber | KLiteral, KLiteral | KKeyword, KKeyword
  | KName, KName | KOperator, KOperator | KPunct, KPunct
  | KUnknown, KUnknown => true
  | _, _ => false
  end.

Record token : Type := mk { kd : kind; tx : list nat }.

Definition fn_keywords : list (list nat) :=
  map cps ["program"; "function"; "fn"].
Definition plain_keywords : list (list nat) :=
  map cps ["if"; "match"; "then"; "else"; "done"; "do"; "repeat"; "times";
           "for"; "and"; "or"; "not"; "return"; "tag"].
Definition start_at : list nat := cps "start at".
Definition literals : list (list nat) := map cps ["true"; "false"].
Definition operators : list (list nat) :=
  map cps ["=="; "!="; "<="; "<"; ">="; ">"; "->"; "//"; "/"; "%"; "+"; "*";
           "-"; "::"].
Definition puncts : list (list nat) :=
  map cps ["("; ")"; "{"; "}"; "["; "]"; "="; ":"; ";"; "|"; ","; "..."; ".";
           "_"].

(* A name is runs of one XID_START and up to this many XID_CONTINUE
   characters. *)
Definition name_run : nat := 254.

Section Lexer.
  Variables (xid_start_hi xid_cont_hi : nat -> bool).

  Definition xs (c : nat) : bool :=
    if c <? 128 then ascii_alpha c else xid_start_hi c.
  Definition xc (c : nat) : bool :=
    if c <? 128 then ascii_alpha c || is_digit c || (c =? 95) else xid_cont_hi c.

  Definition whitespace_len (r : list nat) : nat := span is_ws r.

  Definition not_nl (c : nat) : bool := negb (is_nl c).

  Definition comment_len (r : list nat) : nat :=
    match r with
    | c :: t => if c =? 35 then S (span not_nl t) else 0
    | [] => 0
    end.

  (* The characters after an opening quote, up to and including the closing
     quote; a backslash takes the next character with it. *)
  Fixpoint string_body (esc : bool) (r : list nat) : option nat :=
    match r with
    | [] => None
    | c :: t =>
        if esc then option_map S (string_body false t)
        else if c =? 34 then Some 1
        else option_map S (string_body (c =? 92) t)
    end.

  Definition string_len (r : list nat) : nat :=
    match r with
    | c :: t =>
        if c =? 34 then match string_body false t with Some n => S n | None => 0 end
        else 0
    | [] => 0
    end.

  Definition frac_len (r : list nat) : nat :=
    match r with
    | c :: t => if c =? 46 then S (span is_digit t) else 0
    | [] => 0
    end.

  Definition exp_sign (t : list nat) : nat :=
    match t with [] => 0 | d :: _ => if (d =? 43) || (d =? 45) then 1 else 0 end.

  Definition exp_len (r : list nat) : nat :=
    match r with
    | c :: t =>
        if (c =? 101) || (c =? 69) then
          let e := span is_digit (skipn (exp_sign t) t) in
          if 0 <? e then S (exp_sign t + e) else 0
        else 0
    | [] => 0
    end.

  (* Digits with an optional fraction and exponent, or a bare fraction. *)
  Definition mant_len (r : list nat) : nat :=
    let w := span is_digit r in
    if 0 <? w then w + frac_len (skipn w r)
    else match r with
         | c :: t =>
             if c =? 46 then (let d := span is_digit t in if 0 <? d then S d else 0)
             else 0
         | [] => 0
         end.

  Definition number_len (r : list nat) : nat :=
    let m := mant_len r in
    if m =? 0 then 0 else m + exp_len (skipn m r).

  (* [None]: the next character must start a name.  [Some k]: inside a run
     that takes [k] more continuation characters. *)
  Fixpoint name_sm (st : option nat) (r : list nat) : nat :=
    match r with
    | [] => 0
    | c :: t =>
        match st with
        | Some (S k) =>
            if xc c then S (name_sm (Some k) t)
            else if xs c then S (name_sm (Some name_run) t) else 0
        | _ => if xs c then S (name_sm (Some name_run) t) else 0
        end
    end.

  Definition name_len (r : list nat) : nat := name_sm None r.

  Definition boundary (n : nat) (r : list nat) : bool :=
    match skipn n r with c :: _ => negb (xc c) | [] => true end.

  (* A reserved word is not followed by an identifier character: [done] is a
     keyword, [doner] a name. *)
  Definition word_fits (w r : list nat) : bool :=
    prefixb w r && boundary (List.length w) r.

  Definition word_len (ws : list (list nat)) (r : list nat) : nat :=
    fold_left Nat.max (map (fun w => if word_fits w r then List.length w else 0) ws) 0.

  Definition prefix_len (cs : list (list nat)) (r : list nat) : nat :=
    fold_left Nat.max (map (fun w => if prefixb w r then List.length w else 0) cs) 0.

  Definition classes : list (kind * (list nat -> nat)) :=
    [ (KWhitespace, whitespace_len);
      (KComment, comment_len);
      (KString, string_len);
      (KNumber, number_len);
      (KLiteral, word_len literals);
      (KKeyword, word_len (fn_keywords ++ plain_keywords));
      (KKeyword, word_len [start_at]);
      (KName, name_len);
      (KOperator, prefix_len operators);
      (KPunct, prefix_len puncts) ].

  Fixpoint pick (cl : list (kind * (list nat -> nat))) (r : list nat)
    (acc : kind * nat) : kind * nat :=
    match cl with
    | [] => acc
    | (k, m) :: cl' =>
        let n := m r in
        pick cl' r (if snd acc <? n then (k, n) else acc)
    end.

  (* The token at the start of [r]: the longest match of any class, the
     earlier class on a tie, one code point of unknown kind when none
     matches. *)
  Definition step (r : list nat) : kind * nat :=
    let '(k, n) := pick classes r (KUnknown, 0) in
    if n =? 0 then (KUnknown, 1) else (k, n).

  Fixpoint lex_go (fuel : nat) (r : list nat) : list token :=
    match fuel, r with
    | S f, _ :: _ =>
        let '(k, n) := step r in
        mk k (firstn n r) :: lex_go f (skipn n r)
    | _, _ => []
    end.

  Definition push (t : token) (acc : list token) : list token :=
    match acc with
    | u :: acc' =>
        if kind_eqb (kd t) KUnknown && kind_eqb (kd u) KUnknown
        then mk KUnknown (tx t ++ tx u) :: acc'
        else t :: acc
    | [] => [t]
    end.

  (* Every code point of the source in some token, in order; consecutive
     unrecognized code points are one token. *)
  Definition lex (s : list nat) : list token :=
    fold_right push [] (lex_go (List.length s) s).

End Lexer.

Definition text (ts : list token) : list nat := flat_map tx ts.

Definition is_trivia (t : token) : bool :=
  kind_eqb (kd t) KWhitespace || kind_eqb (kd t) KComment.

Definition sigs (ts : list token) : list token :=
  filter (fun t => negb (kind_eqb (kd t) KWhitespace)) ts.

