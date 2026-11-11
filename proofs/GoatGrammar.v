(* Generated from grammar/goat.peg by parser/examples/emit_coq.rs; do not edit. *)
From Coq Require Import String.
Open Scope string_scope.

Inductive terminal : Type :=
  | T_text (s : string)
  | T_name
  | T_number
  | T_string
  | T_eoi.

Inductive rule : Type :=
  | R_goat
  | R_tag_decl
  | R_tag_kw
  | R_group_name
  | R_tag_case
  | R_expr
  | R_sequel
  | R__part
  | R__statement
  | R__more_math
  | R__operand
  | R_value
  | R__infix
  | R_and_op
  | R_or_op
  | R_not_op
  | R_plus
  | R_minus
  | R_multiply
  | R_floor_divide
  | R_divide
  | R_remainder
  | R_equal
  | R_not_equal
  | R_lte
  | R_lt
  | R_gte
  | R_gt
  | R__term
  | R_negation
  | R__postfix
  | R_access
  | R_call
  | R_arguments
  | R__primary
  | R_number
  | R_string
  | R_boolean
  | R_true_lit
  | R_false_lit
  | R_name
  | R_record
  | R__record_item
  | R_spread
  | R_field
  | R_local
  | R_declaration
  | R_foreign_kw
  | R_foreign_decl
  | R_foreign_name
  | R_fn_type
  | R__type_expr
  | R_list_type
  | R_record_type
  | R_field_type
  | R_type_name
  | R_destructure
  | R_record_pattern
  | R_list_pattern
  | R_rest_binding
  | R_function
  | R_params
  | R__param
  | R_conditional
  | R__else_branch
  | R_list
  | R_match_expr
  | R_arm
  | R_pattern
  | R_labels
  | R_literal_pattern
  | R_repeat_loop
  | R_count_loop
  | R_each_loop
  | R_for_kw
  | R_from_kw
  | R_to_kw
  | R_in_kw
.

Inductive pexpr : Type :=
  | E_term (t : terminal)
  | E_rule (r : rule)
  | E_seq (a b : pexpr)
  | E_alt (a b : pexpr)
  | E_star (a : pexpr)
  | E_plus (a : pexpr)
  | E_opt (a : pexpr)
  | E_expect (a : pexpr).

Definition silent (r : rule) : bool :=
  match r with
  | R__part => true
  | R__statement => true
  | R__more_math => true
  | R__operand => true
  | R__infix => true
  | R__term => true
  | R__postfix => true
  | R__primary => true
  | R__record_item => true
  | R__type_expr => true
  | R__param => true
  | R__else_branch => true
  | _ => false
  end.

Definition body (r : rule) : pexpr :=
  match r with
  | R_goat =>
    (E_seq (E_star (E_rule R_tag_decl)) (E_seq (E_opt (E_rule R_expr)) (E_term T_eoi)))
  | R_tag_decl =>
    (E_seq (E_rule R_tag_kw) (E_seq (E_opt (E_seq (E_rule R_group_name) (E_term (T_text "=")))) (E_seq (E_expect (E_rule R_tag_case)) (E_star (E_seq (E_term (T_text "|")) (E_expect (E_rule R_tag_case)))))))
  | R_tag_kw =>
    (E_term (T_text "tag"))
  | R_group_name =>
    (E_rule R_name)
  | R_tag_case =>
    (E_seq (E_rule R_name) (E_opt (E_seq (E_term (T_text "(")) (E_seq (E_rule R__type_expr) (E_seq (E_star (E_seq (E_term (T_text ",")) (E_rule R__type_expr))) (E_term (T_text ")")))))))
  | R_expr =>
    (E_seq (E_rule R__part) (E_seq (E_star (E_seq (E_rule R_sequel) (E_rule R__part))) (E_opt (E_rule R_sequel))))
  | R_sequel =>
    (E_term (T_text ";"))
  | R__part =>
    (E_alt (E_seq (E_plus (E_rule R_declaration)) (E_opt (E_rule R__statement))) (E_rule R__statement))
  | R__statement =>
    (E_seq (E_rule R__operand) (E_star (E_rule R__more_math)))
  | R__more_math =>
    (E_seq (E_rule R__infix) (E_expect (E_rule R__operand)))
  | R__operand =>
    (E_seq (E_star (E_rule R_not_op)) (E_rule R__term))
  | R_value =>
    (E_seq (E_rule R__operand) (E_star (E_rule R__more_math)))
  | R__infix =>
    (E_alt (E_rule R_and_op) (E_alt (E_rule R_or_op) (E_alt (E_rule R_plus) (E_alt (E_rule R_minus) (E_alt (E_rule R_multiply) (E_alt (E_rule R_floor_divide) (E_alt (E_rule R_divide) (E_alt (E_rule R_remainder) (E_alt (E_rule R_equal) (E_alt (E_rule R_not_equal) (E_alt (E_rule R_lte) (E_alt (E_rule R_lt) (E_alt (E_rule R_gte) (E_rule R_gt))))))))))))))
  | R_and_op =>
    (E_term (T_text "and"))
  | R_or_op =>
    (E_term (T_text "or"))
  | R_not_op =>
    (E_term (T_text "not"))
  | R_plus =>
    (E_term (T_text "+"))
  | R_minus =>
    (E_term (T_text "-"))
  | R_multiply =>
    (E_term (T_text "*"))
  | R_floor_divide =>
    (E_term (T_text "//"))
  | R_divide =>
    (E_term (T_text "/"))
  | R_remainder =>
    (E_term (T_text "%"))
  | R_equal =>
    (E_term (T_text "=="))
  | R_not_equal =>
    (E_term (T_text "!="))
  | R_lte =>
    (E_term (T_text "<="))
  | R_lt =>
    (E_term (T_text "<"))
  | R_gte =>
    (E_term (T_text ">="))
  | R_gt =>
    (E_term (T_text ">"))
  | R__term =>
    (E_alt (E_rule R_negation) (E_seq (E_rule R__primary) (E_star (E_rule R__postfix))))
  | R_negation =>
    (E_seq (E_rule R_minus) (E_alt (E_rule R_negation) (E_seq (E_rule R__primary) (E_star (E_rule R__postfix)))))
  | R__postfix =>
    (E_alt (E_rule R_access) (E_rule R_call))
  | R_access =>
    (E_seq (E_term (T_text ".")) (E_expect (E_rule R_name)))
  | R_call =>
    (E_seq (E_term (T_text "(")) (E_seq (E_opt (E_rule R_arguments)) (E_expect (E_term (T_text ")")))))
  | R_arguments =>
    (E_seq (E_rule R_expr) (E_seq (E_star (E_seq (E_term (T_text ",")) (E_rule R_expr))) (E_opt (E_term (T_text ",")))))
  | R__primary =>
    (E_alt (E_rule R_number) (E_alt (E_rule R_string) (E_alt (E_rule R_boolean) (E_alt (E_rule R_destructure) (E_alt (E_rule R_local) (E_alt (E_rule R_function) (E_alt (E_rule R_conditional) (E_alt (E_rule R_match_expr) (E_alt (E_rule R_repeat_loop) (E_alt (E_rule R_count_loop) (E_alt (E_rule R_each_loop) (E_alt (E_rule R_record) (E_alt (E_rule R_list) (E_alt (E_rule R_name) (E_seq (E_term (T_text "(")) (E_seq (E_rule R_expr) (E_expect (E_term (T_text ")")))))))))))))))))))
  | R_number =>
    (E_term T_number)
  | R_string =>
    (E_term T_string)
  | R_boolean =>
    (E_alt (E_rule R_true_lit) (E_rule R_false_lit))
  | R_true_lit =>
    (E_term (T_text "true"))
  | R_false_lit =>
    (E_term (T_text "false"))
  | R_name =>
    (E_term T_name)
  | R_record =>
    (E_seq (E_term (T_text "{")) (E_seq (E_opt (E_seq (E_rule R__record_item) (E_seq (E_star (E_seq (E_term (T_text ",")) (E_rule R__record_item))) (E_opt (E_term (T_text ",")))))) (E_expect (E_term (T_text "}")))))
  | R__record_item =>
    (E_alt (E_rule R_spread) (E_rule R_field))
  | R_spread =>
    (E_seq (E_term (T_text "...")) (E_expect (E_rule R_expr)))
  | R_field =>
    (E_seq (E_rule R_name) (E_seq (E_term (T_text ":")) (E_expect (E_rule R_expr))))
  | R_local =>
    (E_seq (E_rule R_declaration) (E_opt (E_rule R_expr)))
  | R_declaration =>
    (E_seq (E_rule R_name) (E_seq (E_term (T_text "=")) (E_seq (E_expect (E_alt (E_rule R_foreign_decl) (E_rule R_value))) (E_opt (E_term (T_text ";"))))))
  | R_foreign_kw =>
    (E_term (T_text "foreign"))
  | R_foreign_decl =>
    (E_seq (E_rule R_foreign_kw) (E_seq (E_rule R_foreign_name) (E_seq (E_rule R_foreign_name) (E_rule R_fn_type))))
  | R_foreign_name =>
    (E_alt (E_rule R_string) (E_alt (E_rule R_number) (E_alt (E_rule R_boolean) (E_rule R_name))))
  | R_fn_type =>
    (E_seq (E_term (T_text "(")) (E_seq (E_opt (E_seq (E_rule R__type_expr) (E_seq (E_star (E_seq (E_term (T_text ",")) (E_rule R__type_expr))) (E_opt (E_term (T_text ",")))))) (E_seq (E_term (T_text ")")) (E_seq (E_term (T_text "->")) (E_rule R__type_expr)))))
  | R__type_expr =>
    (E_alt (E_rule R_fn_type) (E_alt (E_rule R_list_type) (E_alt (E_rule R_record_type) (E_rule R_type_name))))
  | R_list_type =>
    (E_seq (E_term (T_text "[")) (E_seq (E_rule R__type_expr) (E_term (T_text "]"))))
  | R_record_type =>
    (E_seq (E_term (T_text "{")) (E_seq (E_opt (E_seq (E_rule R_field_type) (E_seq (E_star (E_seq (E_term (T_text ",")) (E_rule R_field_type))) (E_opt (E_term (T_text ",")))))) (E_term (T_text "}"))))
  | R_field_type =>
    (E_seq (E_rule R_name) (E_seq (E_term (T_text ":")) (E_rule R__type_expr)))
  | R_type_name =>
    (E_term T_name)
  | R_destructure =>
    (E_seq (E_alt (E_rule R_record_pattern) (E_rule R_list_pattern)) (E_seq (E_term (T_text "=")) (E_seq (E_expect (E_rule R_value)) (E_seq (E_opt (E_term (T_text ";"))) (E_opt (E_rule R_expr))))))
  | R_record_pattern =>
    (E_seq (E_term (T_text "{")) (E_seq (E_seq (E_alt (E_seq (E_rule R_name) (E_seq (E_star (E_seq (E_term (T_text ",")) (E_rule R_name))) (E_opt (E_seq (E_term (T_text ",")) (E_rule R_rest_binding))))) (E_rule R_rest_binding)) (E_opt (E_term (T_text ",")))) (E_term (T_text "}"))))
  | R_list_pattern =>
    (E_seq (E_term (T_text "[")) (E_seq (E_opt (E_seq (E_alt (E_seq (E_rule R_name) (E_seq (E_star (E_seq (E_term (T_text ",")) (E_rule R_name))) (E_opt (E_seq (E_term (T_text ",")) (E_rule R_rest_binding))))) (E_rule R_rest_binding)) (E_opt (E_term (T_text ","))))) (E_term (T_text "]"))))
  | R_rest_binding =>
    (E_seq (E_term (T_text "...")) (E_rule R_name))
  | R_function =>
    (E_seq (E_alt (E_term (T_text "program")) (E_alt (E_term (T_text "function")) (E_term (T_text "fn")))) (E_seq (E_expect (E_term (T_text "("))) (E_seq (E_opt (E_rule R_params)) (E_seq (E_expect (E_term (T_text ")"))) (E_seq (E_expect (E_term (T_text "do"))) (E_seq (E_opt (E_rule R_expr)) (E_expect (E_term (T_text "done")))))))))
  | R_params =>
    (E_seq (E_rule R__param) (E_star (E_seq (E_term (T_text ",")) (E_rule R__param))))
  | R__param =>
    (E_alt (E_rule R_record_pattern) (E_alt (E_rule R_list_pattern) (E_rule R_name)))
  | R_conditional =>
    (E_seq (E_term (T_text "if")) (E_seq (E_rule R_expr) (E_seq (E_expect (E_term (T_text "then"))) (E_seq (E_expect (E_rule R_expr)) (E_seq (E_opt (E_rule R__else_branch)) (E_expect (E_term (T_text "done"))))))))
  | R__else_branch =>
    (E_seq (E_term (T_text "else")) (E_expect (E_rule R_expr)))
  | R_list =>
    (E_seq (E_term (T_text "[")) (E_seq (E_opt (E_rule R_arguments)) (E_expect (E_term (T_text "]")))))
  | R_match_expr =>
    (E_seq (E_term (T_text "match")) (E_seq (E_expect (E_rule R_expr)) (E_seq (E_expect (E_term (T_text "do"))) (E_seq (E_star (E_rule R_arm)) (E_seq (E_opt (E_rule R__else_branch)) (E_expect (E_term (T_text "done"))))))))
  | R_arm =>
    (E_seq (E_alt (E_rule R_list_pattern) (E_alt (E_rule R_literal_pattern) (E_rule R_pattern))) (E_seq (E_expect (E_term (T_text "then"))) (E_expect (E_rule R_expr))))
  | R_pattern =>
    (E_seq (E_rule R_name) (E_opt (E_seq (E_term (T_text "(")) (E_seq (E_opt (E_rule R_labels)) (E_term (T_text ")"))))))
  | R_labels =>
    (E_seq (E_rule R_name) (E_star (E_seq (E_term (T_text ",")) (E_rule R_name))))
  | R_literal_pattern =>
    (E_alt (E_rule R_number) (E_alt (E_rule R_string) (E_rule R_boolean)))
  | R_repeat_loop =>
    (E_seq (E_term (T_text "repeat")) (E_seq (E_expect (E_rule R_expr)) (E_seq (E_expect (E_term (T_text "times"))) (E_seq (E_expect (E_term (T_text "do"))) (E_seq (E_opt (E_rule R_expr)) (E_expect (E_term (T_text "done"))))))))
  | R_count_loop =>
    (E_seq (E_rule R_for_kw) (E_seq (E_rule R_name) (E_seq (E_rule R_from_kw) (E_seq (E_expect (E_rule R_expr)) (E_seq (E_expect (E_rule R_to_kw)) (E_seq (E_expect (E_rule R_expr)) (E_seq (E_expect (E_term (T_text "do"))) (E_seq (E_opt (E_rule R_expr)) (E_expect (E_term (T_text "done")))))))))))
  | R_each_loop =>
    (E_seq (E_rule R_for_kw) (E_seq (E_rule R_name) (E_seq (E_rule R_in_kw) (E_seq (E_expect (E_rule R_expr)) (E_seq (E_expect (E_term (T_text "do"))) (E_seq (E_opt (E_rule R_expr)) (E_expect (E_term (T_text "done")))))))))
  | R_for_kw =>
    (E_term (T_text "for"))
  | R_from_kw =>
    (E_term (T_text "from"))
  | R_to_kw =>
    (E_term (T_text "to"))
  | R_in_kw =>
    (E_term (T_text "in"))
  end.
