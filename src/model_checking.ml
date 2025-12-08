open Aez
open Smt
open Typed_ast
open Ident

(* ===== UTILS ===== *)

(* Conversion d'un type Lustre en un type Alt-Ergo *)
let asttype_to_smttype = function
  | Asttypes.Tbool -> Type.type_bool
  | Asttypes.Tint -> Type.type_int
  | Asttypes.Treal -> Type.type_real


(* Renvoie la profondeur maximale des -> *)
let max_arrow_depth node =
  let rec calc_depth expr =
    match expr.texpr_desc with
    | TE_const _ | TE_ident _ -> 0
    | TE_pre e -> calc_depth e
    | TE_op (_, es) | TE_app (_, es) | TE_prim (_, es) | TE_tuple es ->
      es |> List.map calc_depth |> List.fold_left max 0
    | TE_arrow (e1, e2) -> 1 + max (calc_depth e1) (calc_depth e2)
  in
  node.tn_equs
  |> List.map (fun equ -> calc_depth equ.teq_expr)
  |> List.fold_left max 0


(* Renvoie true si on veut une formule pour cet opérateur dans le solveur, false sinon *)
let require_formula expr =
  match expr.texpr_desc with
  | TE_op
      ( ( Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge | Op_not | Op_and
        | Op_or | Op_impl ),
        _ ) ->
    true
  | _ -> false


(* Suppose que la liste fait 1 élément et les renvoie *)
let assume_1 = function
  | [ e1 ] -> e1
  | _ -> assert false


(* Suppose que la liste fait 2 éléments et les renvoie *)
let assume_2 = function
  | [ e1; e2 ] -> (e1, e2)
  | _ -> assert false


(* Suppose que la liste fait 3 éléments et les renvoie *)
let assume_3 = function
  | [ e1; e2; e3 ] -> (e1, e2, e3)
  | _ -> assert false


(* ===== SYMBOLES ===== *)

(* Declare un symbole avec son num, son type d'entré et son type de retour *)
let declare_symbol name t_in t_out =
  (* creation d'un symbole *)
  let x = Hstring.make name in
  (* declaration de son type *)
  Symbol.declare x t_in t_out;
  x


(* Declare un symbole à partir d'une variable *)
let get_symbol_from_var (({ name; _ }, ty) : typed_var) =
  declare_symbol name [ Type.type_int ] (asttype_to_smttype ty)


(* Declare un stmbole frais *)
let get_fresh_symbol =
  let cpt = ref ~-1 in
  fun ty () ->
    incr cpt;
    let name = Format.sprintf "aux_%d" !cpt in
    (name, declare_symbol name [ Type.type_int ] (asttype_to_smttype ty))


(* Declare des symboles à partir d'un noeud *)
let get_symbols_from_node aux { tn_input; tn_output; tn_local; _ } :
  (string, Aez.Smt.Symbol.t) Hashtbl.t =
  let symbols = Hashtbl.create 16 in
  let add_symbol ((id, _) as var) =
    var |> get_symbol_from_var |> Hashtbl.replace symbols id.name
  in

  List.iter add_symbol tn_input;
  List.iter add_symbol tn_output;
  List.iter add_symbol tn_local;

  List.iter (fun (name, symbol, _) -> Hashtbl.replace symbols name symbol) aux;

  symbols


(* ===== DÉFINITIONS ===== *)

(* Renvoie une formule du SMT correspondant à une expression donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
let rec get_formula_from_expr
  (symbols : (string, Aez.Smt.Symbol.t) Hashtbl.t) n expr : Aez.Smt.Formula.t =
  match expr.texpr_desc with
  | TE_op (Op_eq, es) -> get_formula_from_lit symbols n Formula.Eq es
  | TE_op (Op_neq, es) -> get_formula_from_lit symbols n Formula.Neq es
  | TE_op (Op_lt, es) -> get_formula_from_lit symbols n Formula.Lt es
  | TE_op (Op_le, es) -> get_formula_from_lit symbols n Formula.Le es
  | TE_op (Op_gt, es) ->
    let expr = { expr with texpr_desc = TE_op (Op_le, es) } in
    Formula.make Formula.Not [ get_formula_from_expr symbols n expr ]
  | TE_op (Op_ge, es) ->
    let expr = { expr with texpr_desc = TE_op (Op_lt, es) } in
    Formula.make Formula.Not [ get_formula_from_expr symbols n expr ]
  | TE_op (Op_not, es) -> get_formula_from_unop symbols n Formula.Not es
  | TE_op (Op_and, es) -> get_formula_from_binop symbols n Formula.And es
  | TE_op (Op_or, es) -> get_formula_from_binop symbols n Formula.Or es
  | TE_op (Op_impl, es) -> get_formula_from_binop symbols n Formula.Imp es
  | _ ->
    Format.printf "Cash on this expression :@.";
    Typed_ast_printer.print_exp Format.std_formatter expr;
    Format.printf "\n%!";
    failwith "We can't make a FORMULA form this expression\n%!"


(* Renvoie une formule du SMT correspondant à une expression unop donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
and get_formula_from_unop symbols n op es =
  match assume_1 es with
  | e1 when require_formula e1 ->
    Formula.make op [ get_formula_from_expr symbols n e1 ]
  | e1 ->
    Formula.make op
      [
        Formula.make_lit Formula.Eq
          [ get_term_from_expr symbols n e1; Term.t_true ];
      ]


(* Renvoie une formule du SMT correspondant à une expression binop donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
and get_formula_from_binop symbols n op es =
  match assume_2 es with
  | e1, e2 when require_formula e1 && require_formula e2 ->
    Formula.make op
      [ get_formula_from_expr symbols n e1; get_formula_from_expr symbols n e2 ]
  | e1, e2 when require_formula e1 ->
    Formula.make op
      [
        get_formula_from_expr symbols n e1;
        Formula.make_lit Formula.Eq
          [ get_term_from_expr symbols n e2; Term.t_true ];
      ]
  | e1, e2 when require_formula e2 ->
    Formula.make op
      [
        Formula.make_lit Formula.Eq
          [ get_term_from_expr symbols n e1; Term.t_true ];
        get_formula_from_expr symbols n e2;
      ]
  | e1, e2 ->
    Formula.make op
      [
        Formula.make_lit Formula.Eq
          [ get_term_from_expr symbols n e1; Term.t_true ];
        Formula.make_lit Formula.Eq
          [ get_term_from_expr symbols n e2; Term.t_true ];
      ]


(* Renvoie une formule du SMT correspondant à une expression littérale donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
and get_formula_from_lit symbols n op es =
  Formula.make_lit op (List.map (get_term_from_expr symbols n) es)


(* Renvoie un terme du SMT correspondant à une expression donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
and get_term_from_expr (symbols : (string, Aez.Smt.Symbol.t) Hashtbl.t) n expr :
  Aez.Smt.Term.t =
  match expr.texpr_desc with
  | TE_const (Cbool false) -> Term.t_false
  | TE_const (Cbool true) -> Term.t_true
  | TE_const (Cint d) -> Term.make_int (Num.Int d)
  | TE_const (Creal r) -> Term.make_real (Num.num_of_string (string_of_float r))
  | TE_ident { name; _ } -> Term.make_app (Hashtbl.find symbols name) [ n ]
  | TE_op ((Op_add | Op_add_f), es) ->
    get_term_from_binop symbols n Term.Plus es
  | TE_op ((Op_sub | Op_sub_f), es) ->
    get_term_from_binop symbols n Term.Minus es
  | TE_op ((Op_mul | Op_mul_f), es) ->
    get_term_from_binop symbols n Term.Mult es
  | TE_op ((Op_div | Op_div_f), es) -> get_term_from_binop symbols n Term.Div es
  | TE_op (Op_mod, es) -> get_term_from_binop symbols n Term.Modulo es
  | TE_op (Op_if, es) ->
    let d1, d2, d3 =
      es |> List.map (get_term_from_expr symbols n) |> assume_3
    in
    Term.make_ite (Formula.make_lit Formula.Eq [ d1; Term.t_true ]) d2 d3
  | TE_app ({ name; _ }, es) ->
    Term.make_app
      (Hashtbl.find symbols name)
      (List.map (get_term_from_expr symbols n) es)
  | TE_prim ({ name; _ }, es) ->
    ignore (name, es);
    failwith "TODO-MC-Op_prim"
  | TE_arrow (e1, e2) ->
    Term.make_ite
      (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
      (get_term_from_expr symbols n e1)
      (get_term_from_expr symbols n e2)
  | TE_pre e ->
    get_term_from_expr symbols
      (Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)))
      e
  | TE_op _ ->
    Format.printf "Cash on this expression :@.";
    Typed_ast_printer.print_exp Format.std_formatter expr;
    Format.printf "\n%!";
    failwith "We can't make a TERM form this expression\n%!"
  | TE_tuple _ -> assert false


(* Renvoie une formule du SMT correspondant à une expression binop donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier et l'opération du SMT
*)
and get_term_from_binop symbols n op es =
  let d1, d2 = es |> List.map (get_term_from_expr symbols n) |> assume_2 in
  Term.make_arith op d1 d2


(* Obtient une definition pour le SMT à partir d'un ensemble d'équations
   Pré-condition : ne pas avoir de tuples dans les équations
*)
let get_def_from_eqs symbols aux eqs : Aez.Smt.Term.t -> Aez.Smt.Formula.t =
  let defs =
    List.map
      begin fun { teq_patt; teq_expr } ->
        let def_name = (List.hd teq_patt.tpatt_desc).name in
        fun n ->
          Formula.make_lit Formula.Eq
            [
              Term.make_app (Hashtbl.find symbols def_name) [ n ];
              get_term_from_expr symbols n teq_expr;
            ]
      end
      eqs
  in

  let defs_aux =
    List.map
      begin fun (_, symbol, expr) ->
        fun n ->
         let aux_def =
           Formula.make_lit Formula.Eq
             [ Term.make_app symbol [ n ]; Term.t_true ]
         in

         let expr_def = get_formula_from_expr symbols n expr in

         Formula.make Formula.And
           [
             Formula.make Formula.Imp [ aux_def; expr_def ];
             Formula.make Formula.Imp [ expr_def; aux_def ];
           ]
      end
      aux
  in

  let final_defs = defs @ defs_aux in
  fun n -> Formula.make Formula.And (List.map (fun def -> def n) final_defs)


(* Obtient la définition delta et p d'un noeud donné
   La définition delta correspond à la conjonction des définitions des équations du noeud
   La définition p assure qu'on veut que la propriété OK soit vraie
*)
let get_defs_from_node aux ({ tn_equs; _ } as node) :
  (Aez.Smt.Term.t -> Aez.Smt.Formula.t) * (Aez.Smt.Term.t -> Aez.Smt.Formula.t)
    =
  let symbols = get_symbols_from_node aux node in
  let delta_def = get_def_from_eqs symbols aux tn_equs in
  let p_def n =
    Formula.make_lit Formula.Eq
      [ Term.make_app (Hashtbl.find symbols "OK") [ n ]; Term.t_true ]
  in
  (delta_def, p_def)


(* ===== PRÉ-PROCESS ===== *)

(* Preprocess une expression pour créer les expressions auxiliaires *)
let rec preprocess_expr ({ texpr_desc; _ } as expr) :
  (string * Aez.Smt.Symbol.t * Typed_ast.t_expr) list * Typed_ast.t_expr =
  let aux, texpr_desc =
    match texpr_desc with
    | TE_op (op, es) when require_formula expr ->
      let aux, es = es |> List.map preprocess_expr |> List.split in
      let expr = { expr with texpr_desc = TE_op (op, es) } in
      let aux_name, aux_symbol = get_fresh_symbol Asttypes.Tbool () in
      let aux_tuple = (aux_name, aux_symbol, expr) in
      let id = Ident.make aux_name Stream in
      (List.flatten ([ aux_tuple ] :: aux), TE_ident id)
    | TE_const _ | TE_ident _ -> ([], texpr_desc)
    | TE_op (op, es) ->
      let aux, es = es |> List.map preprocess_expr |> List.split in
      (List.flatten aux, TE_op (op, es))
    | TE_app (id, es) ->
      let aux, es = es |> List.map preprocess_expr |> List.split in
      (List.flatten aux, TE_app (id, es))
    | TE_prim (id, es) ->
      let aux, es = es |> List.map preprocess_expr |> List.split in
      (List.flatten aux, TE_prim (id, es))
    | TE_arrow (e1, e2) ->
      let aux1, e1 = preprocess_expr e1 in
      let aux2, e2 = preprocess_expr e2 in
      (aux1 @ aux2, TE_arrow (e1, e2))
    | TE_pre e ->
      let aux, e = preprocess_expr e in
      (aux, TE_pre e)
    | TE_tuple _ -> assert false
  in
  (aux, { expr with texpr_desc })


(* Preprocess une équantion pour créer les expressions auxiliaires *)
let preprocess_equ ({ teq_expr; _ } as equ) =
  let aux, teq_expr = preprocess_expr teq_expr in
  (aux, { equ with teq_expr })


(* Preprocess un node pour créer les expressions auxiliaires *)
let preprocess_node ({ tn_equs; _ } as node) =
  let aux, tn_equs = tn_equs |> List.map preprocess_equ |> List.split in
  (List.flatten aux, { node with tn_equs })


(* ===== CAS DE BASE ===== *)

(* Notre solveur pour le cas de base *)
module BMC_solver = Smt.Make (struct end)

(* Définit le cas de base de la propriété *)
let get_base_case node delta p =
  let assume = BMC_solver.assume ~id:0 in
  let entails = BMC_solver.entails ~id:0 in
  let check = BMC_solver.check in

  let basecase_number = 1 + max_arrow_depth node in

  for i = 0 to basecase_number - 1 do
    assume (delta (Term.make_int (Num.Int i)))
  done;
  check ();

  let final_p =
    match basecase_number with
    | 1 -> p (Term.make_int (Num.Int 0))
    | _ ->
      Formula.make Formula.And
        (List.init basecase_number (fun i -> p (Term.make_int (Num.Int i))))
  in
  entails final_p


(* ===== CAS INDUCTIF ===== *)

(* Notre solveur pour le cas inductif *)
module IND_solver = Smt.Make (struct end)

(* Définit le cas inductif *)
let get_ind_case delta p =
  let assume = IND_solver.assume ~id:0 in
  let entails = IND_solver.entails ~id:0 in
  let check = IND_solver.check in

  let n = Term.make_app (declare_symbol "n" [] Type.type_int) [] in
  let sn = Term.make_arith Term.Plus n (Term.make_int (Num.Int 1)) in

  assume (Formula.make_lit Formula.Le [ Term.make_int (Num.Int 0); n ]);
  assume (delta n);
  assume (delta sn);
  assume (p n);
  check ();

  entails (p sn)


(* ===== CHECKING ===== *)

(* Check si la propriété OK est vraie *)
let check node =
  let aux, node = preprocess_node node in
  let delta, p = get_defs_from_node aux node in

  if not (get_base_case node delta p) then Format.printf "FALSE PROPERTY@."
  else if get_ind_case delta p then Format.printf "TRUE PROPERTY@."
  else Format.printf "Don't know@."
