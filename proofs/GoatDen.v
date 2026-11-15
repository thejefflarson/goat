(* The denotation of a core-fragment parse tree as an Ott term, and its local
   closure (the denotation half of T1, ADR 0030). *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatMeta.
From Stdlib Require Import Lia.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Open Scope string_scope.

(* ---- closing a variable, and the n-ary forms curried ---- *)

Fixpoint close_exp_rec (k : nat) (x : termvar) (e : exp) {struct e} : exp :=
  match e with
  | e_fvar_b i => e_fvar_b i
  | e_fvar_f y => if y == x then e_fvar_b k else e_fvar_f y
  | e_num n => e_num n
  | e_true => e_true
  | e_false => e_false
  | e_abs b => e_abs (close_exp_rec (S k) x b)
  | e_app a b => e_app (close_exp_rec k x a) (close_exp_rec k x b)
  | e_let a b => e_let (close_exp_rec k x a) (close_exp_rec (S k) x b)
  | e_rec fs => e_rec (close_fields_rec k x fs)
  | e_proj a l => e_proj (close_exp_rec k x a) l
  end
with close_fields_rec (k : nat) (x : termvar) (fs : fields) {struct fs} : fields :=
  match fs with
  | fs_nil => fs_nil
  | fs_cons l e fs' => fs_cons l (close_exp_rec k x e) (close_fields_rec k x fs')
  end.

Definition close_exp (x : termvar) (e : exp) : exp := close_exp_rec 0 x e.

(* program(x1, ..., xk) do b done *)
Definition curry (xs : list termvar) (b : exp) : exp :=
  fold_right (fun x acc => e_abs (close_exp x acc)) b xs.

(* f(a1, ..., ak) *)
Definition apps (f : exp) (args : list exp) : exp := fold_left e_app args f.

(* ---- closing preserves local closure ---- *)

Lemma lc_close_mut :
  (forall e k x, lc_at k e -> lc_at (S k) (close_exp_rec k x e)) /\
  (forall fs k x, lcf_at k fs -> lcf_at (S k) (close_fields_rec k x fs)).
Proof.
  apply exp_fields_mutind.
  - (* bound index: below k, so below S k *)
    intros i k x Hi. simpl in *. lia.
  - (* free variable: x becomes index k, below S k; any other stays *)
    intros y k x _. simpl. destruct (y == x); simpl; [ lia | exact I ].
  - intros n k x _. exact I.
  - intros k x _. exact I.
  - intros k x _. exact I.
  - (* abs: the body is one level deeper *)
    intros b IH k x Hb. simpl in *. exact (IH (S k) x Hb).
  - (* app *)
    intros a IHa b IHb k x [Ha Hb]. simpl.
    split; [ exact (IHa k x Ha) | exact (IHb k x Hb) ].
  - (* let: the body is one level deeper, the value is not *)
    intros a IHa b IHb k x [Ha Hb]. simpl.
    split; [ exact (IHa k x Ha) | exact (IHb (S k) x Hb) ].
  - (* record *)
    intros fs IH k x Hfs. simpl in *. exact (IH k x Hfs).
  - (* projection *)
    intros a IH l k x Ha. simpl in *. exact (IH k x Ha).
  - intros k x _. exact I.
  - (* field list *)
    intros l e IHe fs IHfs k x [He Hfs]. simpl.
    split; [ exact (IHe k x He) | exact (IHfs k x Hfs) ].
Qed.

Lemma lc_curry : forall xs b, lc b -> lc (curry xs b).
Proof.
  intros xs b Hb. induction xs as [| x xs IH]; simpl.
  - exact Hb.
  - assert (Hclose : lc_at 1 (close_exp x (curry xs b)))
      by (apply (proj1 lc_close_mut); exact IH).
    exact Hclose.
Qed.

Lemma lc_apps : forall args f, lc f -> Forall lc args -> lc (apps f args).
Proof.
  intros args. induction args as [| a args IH]; intros f Hf Hargs; simpl.
  - exact Hf.
  - inversion Hargs as [| ? ? Ha Hrest]; subst.
    apply IH; [ split; assumption | assumption ].
Qed.

(* ---- the denotation ---- *)

Definition starts_call (ts : list tree) : Prop :=
  match ts with Node R_call _ :: _ => True | _ => False end.

Fixpoint index_of (l : string) (tbl : list string) : nat :=
  match tbl with
  | [] => 0
  | l' :: tbl' => if String.eqb l l' then 0 else S (index_of l tbl')
  end.

Section Denotation.

  Variable var_of : string -> termvar.
  Variable tbl : list string.

  Definition lab (l : string) : label := index_of l tbl.

  Definition sym (s : string) : tree := Leaf (TSym s).
  Definition ident (x : string) : tree := Node R_name [Leaf (TName x)].

  Inductive Den : tree -> exp -> Prop :=
    | D_num : forall n,
        Den (Node R_number [Leaf (TNum n)]) (e_num n)
    | D_true :
        Den (Node R_boolean [Node R_true_lit [sym "true"]]) e_true
    | D_false :
        Den (Node R_boolean [Node R_false_lit [sym "false"]]) e_false
    | D_name : forall x,
        Den (ident x) (e_fvar_f (var_of x))
    | D_expr : forall cs e,
        Den_block cs e ->
        Den (Node R_expr cs) e
    | D_value : forall cs e,
        Den_chain cs e ->
        Den (Node R_value cs) e
    | D_function : forall kw ps xs cs body,
        Den_params ps xs ->
        Den (Node R_expr cs) body ->
        Den (Node R_function [Leaf kw; sym "("; Node R_params ps; sym ")";
                              sym "do"; Node R_expr cs; sym "done"])
            (curry (List.map var_of xs) body)
    | D_record : forall items fs,
        Den_items items fs ->
        Den (Node R_record (sym "{" :: items)) (e_rec fs)
    | D_local : forall d x v cs body,
        Den_decl d x v ->
        Den (Node R_expr cs) body ->
        Den (Node R_local [d; Node R_expr cs])
            (e_let v (close_exp (var_of x) body))
  with Den_decl : tree -> string -> exp -> Prop :=
    | DD_plain : forall x cs v,
        Den (Node R_value cs) v ->
        Den_decl (Node R_declaration [ident x; sym "="; Node R_value cs]) x v
    | DD_semi : forall x cs v,
        Den (Node R_value cs) v ->
        Den_decl (Node R_declaration [ident x; sym "="; Node R_value cs; sym ";"]) x v
  with Den_block : list tree -> exp -> Prop :=
    | DB_chain : forall cs e,
        Den_chain cs e ->
        Den_block cs e
    | DB_decl : forall d rest x v body,
        Den_decl d x v ->
        Den_block rest body ->
        Den_block (d :: rest) (e_let v (close_exp (var_of x) body))
  with Den_chain : list tree -> exp -> Prop :=
    | DC_head : forall t rest e0 e,
        Den t e0 ->
        Den_posts e0 rest e ->
        Den_chain (t :: rest) e
    | DC_paren : forall cs rest e0 e,
        Den (Node R_expr cs) e0 ->
        Den_posts e0 rest e ->
        Den_chain (sym "(" :: Node R_expr cs :: sym ")" :: rest) e
  with Den_posts : exp -> list tree -> exp -> Prop :=
    | DP_nil : forall e,
        Den_posts e [] e
    | DP_access : forall e l rest e',
        ~ starts_call rest ->
        Den_posts (e_proj e (lab l)) rest e' ->
        Den_posts e (Node R_access [sym "."; ident l] :: rest) e'
    | DP_take : forall e l rest e',
        Den_posts (e_proj e (lab l)) rest e' ->
        Den_posts e (Node R_take [sym "::"; ident l] :: rest) e'
    | DP_dot_call : forall x l args es rest e',
        Den_args args es ->
        Den_posts (apps (e_proj (e_fvar_f x) (lab l)) (e_fvar_f x :: es)) rest e' ->
        Den_posts (e_fvar_f x)
          (Node R_access [sym "."; ident l]
             :: Node R_call [sym "("; Node R_arguments args; sym ")"] :: rest) e'
    | DP_call : forall e args es rest e',
        Den_args args es ->
        Den_posts (apps e es) rest e' ->
        Den_posts e (Node R_call [sym "("; Node R_arguments args; sym ")"] :: rest) e'
  with Den_args : list tree -> list exp -> Prop :=
    | DA_last : forall t e,
        Den t e ->
        Den_args [t] [e]
    | DA_trailing : forall t e,
        Den t e ->
        Den_args [t; sym ","] [e]
    | DA_more : forall t e rest es,
        Den t e ->
        Den_args rest es ->
        Den_args (t :: sym "," :: rest) (e :: es)
  with Den_params : list tree -> list string -> Prop :=
    | DPa_one : forall x,
        Den_params [ident x] [x]
    | DPa_more : forall x rest xs,
        Den_params rest xs ->
        Den_params (ident x :: sym "," :: rest) (x :: xs)
  with Den_items : list tree -> fields -> Prop :=
    | DI_end :
        Den_items [sym "}"] fs_nil
    | DI_field : forall f l e rest fs,
        Den_field f l e ->
        Den_sep rest fs ->
        Den_items (f :: rest) (fs_cons (lab l) e fs)
  with Den_sep : list tree -> fields -> Prop :=
    | DS_end :
        Den_sep [sym "}"] fs_nil
    | DS_more : forall rest fs,
        Den_items rest fs ->
        Den_sep (sym "," :: rest) fs
  with Den_field : tree -> string -> exp -> Prop :=
    | DF : forall l cs e,
        Den (Node R_expr cs) e ->
        Den_field (Node R_field [ident l; sym ":"; Node R_expr cs]) l e.

End Denotation.

Scheme Den_ind' := Induction for Den Sort Prop
with Den_decl_ind' := Induction for Den_decl Sort Prop
with Den_block_ind' := Induction for Den_block Sort Prop
with Den_chain_ind' := Induction for Den_chain Sort Prop
with Den_posts_ind' := Induction for Den_posts Sort Prop
with Den_args_ind' := Induction for Den_args Sort Prop
with Den_params_ind' := Induction for Den_params Sort Prop
with Den_items_ind' := Induction for Den_items Sort Prop
with Den_sep_ind' := Induction for Den_sep Sort Prop
with Den_field_ind' := Induction for Den_field Sort Prop.
Combined Scheme Den_mutind from Den_ind', Den_decl_ind', Den_block_ind',
  Den_chain_ind', Den_posts_ind', Den_args_ind', Den_params_ind',
  Den_items_ind', Den_sep_ind', Den_field_ind'.

(* ---- T1, the denotation half: whatever a derivation denotes is locally closed ---- *)

Lemma den_lc : forall var_of tbl,
  (forall t e, Den var_of tbl t e -> lc e) /\
  (forall d x v, Den_decl var_of tbl d x v -> lc v) /\
  (forall cs e, Den_block var_of tbl cs e -> lc e) /\
  (forall cs e, Den_chain var_of tbl cs e -> lc e) /\
  (forall e0 cs e, Den_posts var_of tbl e0 cs e -> lc e0 -> lc e) /\
  (forall cs es, Den_args var_of tbl cs es -> Forall lc es) /\
  (forall ps xs, Den_params var_of tbl ps xs -> True) /\
  (forall cs fs, Den_items var_of tbl cs fs -> lcf fs) /\
  (forall cs fs, Den_sep var_of tbl cs fs -> lcf fs) /\
  (forall f l e, Den_field var_of tbl f l e -> lc e).
Proof.
  intros var_of tbl.
  apply Den_mutind.
  - (* num *) intros n. exact I.
  - (* true *) exact I.
  - (* false *) exact I.
  - (* name *) intros x. exact I.
  - (* expr *) intros cs e Hblock IH. exact IH.
  - (* value *) intros cs e Hchain IH. exact IH.
  - (* function *)
    intros kw ps xs cs body Hps _ Hbody IHbody.
    assert (Hcurry : lc (curry (List.map var_of xs) body))
      by (apply lc_curry; exact IHbody).
    exact Hcurry.
  - (* record *) intros items fs Hitems IH. exact IH.
  - (* local *)
    intros d x v cs body Hd IHd Hbody IHbody.
    assert (Hclose : lc_at 1 (close_exp (var_of x) body))
      by (apply (proj1 lc_close_mut); exact IHbody).
    exact (conj IHd Hclose).
  - (* decl, plain *) intros x cs v Hv IH. exact IH.
  - (* decl, with semicolon *) intros x cs v Hv IH. exact IH.
  - (* block, chain *) intros cs e Hchain IH. exact IH.
  - (* block, declaration *)
    intros d rest x v body Hd IHd Hrest IHrest.
    assert (Hclose : lc_at 1 (close_exp (var_of x) body))
      by (apply (proj1 lc_close_mut); exact IHrest).
    exact (conj IHd Hclose).
  - (* chain, head *)
    intros t rest e0 e Ht IHt Hposts IHposts. exact (IHposts IHt).
  - (* chain, parenthesised *)
    intros cs rest e0 e Hexpr IHexpr Hposts IHposts. exact (IHposts IHexpr).
  - (* posts, none *) intros e Hlc. exact Hlc.
  - (* posts, access *)
    intros e l rest e' Hnocall Hrest IHrest Hlc.
    assert (Hproj : lc (e_proj e (lab tbl l))) by exact Hlc.
    exact (IHrest Hproj).
  - (* posts, take *)
    intros e l rest e' Hrest IHrest Hlc.
    assert (Hproj : lc (e_proj e (lab tbl l))) by exact Hlc.
    exact (IHrest Hproj).
  - (* posts, dot call: the receiver is a variable, passed first *)
    intros x l args es rest e' Hargs IHargs Hrest IHrest Hlc.
    assert (Hrecv : Forall lc (e_fvar_f x :: es))
      by (apply Forall_cons; [ exact I | exact IHargs ]).
    assert (Happs : lc (apps (e_proj (e_fvar_f x) (lab tbl l)) (e_fvar_f x :: es)))
      by (apply lc_apps; [ exact I | exact Hrecv ]).
    exact (IHrest Happs).
  - (* posts, call *)
    intros e args es rest e' Hargs IHargs Hrest IHrest Hlc.
    assert (Happs : lc (apps e es)) by (apply lc_apps; assumption).
    exact (IHrest Happs).
  - (* args, last *) intros t e Ht IH. exact (Forall_cons e IH (Forall_nil lc)).
  - (* args, trailing comma *) intros t e Ht IH. exact (Forall_cons e IH (Forall_nil lc)).
  - (* args, more *)
    intros t e rest es Ht IHt Hrest IHrest. exact (Forall_cons e IHt IHrest).
  - (* params, one *) intros x. exact I.
  - (* params, more *) intros x rest xs Hrest IH. exact I.
  - (* items, end *) exact I.
  - (* items, field *)
    intros f l e rest fs Hf IHf Hsep IHsep. exact (conj IHf IHsep).
  - (* sep, end *) exact I.
  - (* sep, more *) intros rest fs Hitems IH. exact IH.
  - (* field *) intros l cs e Hexpr IH. exact IH.
Qed.

(* ---- the generated local-closure predicate ---- *)

(* The soundness development reads local closure off [lc_at]; the generated
   [lc_exp] (universal binder clause) is the one ADR 0030 names. They agree on
   locally closed terms. *)

Fixpoint size (e : exp) : nat :=
  match e with
  | e_fvar_b _ | e_fvar_f _ | e_num _ | e_true | e_false => 1
  | e_abs b => S (size b)
  | e_app a b | e_let a b => S (size a + size b)
  | e_rec fs => S (size_fields fs)
  | e_proj a _ => S (size a)
  end
with size_fields (fs : fields) : nat :=
  match fs with
  | fs_nil => 1
  | fs_cons _ e fs' => S (size e + size_fields fs')
  end.

Lemma open_size_mut :
  (forall e k x, size (open_exp_wrt_exp_rec k (e_fvar_f x) e) = size e) /\
  (forall fs k x, size_fields (open_fields_wrt_exp_rec k (e_fvar_f x) fs) = size_fields fs).
Proof.
  apply exp_fields_mutind; simpl; intros.
  - (* bound index *)
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* abs *) rewrite H. reflexivity.
  - (* app *) rewrite H, H0. reflexivity.
  - (* let *) rewrite H, H0. reflexivity.
  - (* rec *) rewrite H. reflexivity.
  - (* proj *) rewrite H. reflexivity.
  - reflexivity.
  - (* cons *) rewrite H, H0. reflexivity.
Qed.

Lemma open_lc_at_mut :
  (forall e n x, lc_at (S n) e -> lc_at n (open_exp_wrt_exp_rec n (e_fvar_f x) e)) /\
  (forall fs n x, lcf_at (S n) fs -> lcf_at n (open_fields_wrt_exp_rec n (e_fvar_f x) fs)).
Proof.
  apply exp_fields_mutind; simpl; intros.
  - (* bound index *)
    destruct (lt_eq_lt_dec n n0) as [[Hlt | Heq] | Hgt]; simpl; [ exact Hlt | exact I | lia ].
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - (* abs *) apply H. assumption.
  - (* app *) destruct H1 as [Ha Hb]. split; [ apply H | apply H0 ]; assumption.
  - (* let *) destruct H1 as [Ha Hb]. split; [ apply H | apply H0 ]; assumption.
  - (* rec *) apply H. assumption.
  - (* proj *) apply H. assumption.
  - exact I.
  - (* cons *) destruct H1 as [He Hfs]. split; [ apply H | apply H0 ]; assumption.
Qed.

Lemma lc_lc_exp_bounded : forall m,
  (forall e, size e <= m -> lc e -> lc_exp e) /\
  (forall fs, size_fields fs <= m -> lcf fs -> lc_fields fs).
Proof.
  induction m as [| m IH]; split; intros t Hsize Hlc.
  - destruct t; simpl in Hsize; lia.
  - destruct t; simpl in Hsize; lia.
  - destruct IH as [IHe IHfs].
    destruct t as [i | x | n | | | b | a b | a b | fs | a l];
      unfold lc, lcf in Hlc; simpl in Hsize, Hlc.
    + lia.
    + apply lc_e_fvar_f.
    + apply lc_e_num.
    + apply lc_e_true.
    + apply lc_e_false.
    + (* abs *)
      apply lc_e_abs. intros x.
      assert (Hopen : lc (open_exp_wrt_exp b (e_fvar_f x)))
        by (apply (proj1 open_lc_at_mut); exact Hlc).
      assert (Hsmaller : size (open_exp_wrt_exp b (e_fvar_f x)) <= m)
        by (unfold open_exp_wrt_exp; rewrite (proj1 open_size_mut); lia).
      exact (IHe _ Hsmaller Hopen).
    + (* app *)
      destruct Hlc as [Ha Hb].
      apply lc_e_app; [ apply IHe | apply IHe ]; try assumption; lia.
    + (* let *)
      destruct Hlc as [Ha Hb].
      apply lc_e_let.
      * apply IHe; [ lia | exact Ha ].
      * intros x.
        assert (Hopen : lc (open_exp_wrt_exp b (e_fvar_f x)))
          by (apply (proj1 open_lc_at_mut); exact Hb).
        assert (Hsmaller : size (open_exp_wrt_exp b (e_fvar_f x)) <= m)
          by (unfold open_exp_wrt_exp; rewrite (proj1 open_size_mut); lia).
        exact (IHe _ Hsmaller Hopen).
    + (* rec *)
      apply lc_e_rec. apply IHfs; [ lia | exact Hlc ].
    + (* proj *)
      apply lc_e_proj. apply IHe; [ lia | exact Hlc ].
  - destruct IH as [IHe IHfs].
    destruct t as [| l e fs]; unfold lc, lcf in Hlc; simpl in Hsize, Hlc.
    + apply lc_fs_nil.
    + destruct Hlc as [He Hfs].
      apply lc_fs_cons; [ apply IHe | apply IHfs ]; try assumption; lia.
Qed.

Lemma lc_lc_exp : forall e, lc e -> lc_exp e.
Proof.
  intros e Hlc.
  exact (proj1 (lc_lc_exp_bounded (size e)) e (le_n _) Hlc).
Qed.
