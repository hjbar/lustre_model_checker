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
    let name = Format.sprintf "fresh_%d" !cpt in
    (name, declare_symbol name [ Type.type_int ] (asttype_to_smttype ty))


(* Declare des symboles à partir d'un noeud *)
let get_symbols_from_node { tn_input; tn_output; tn_local; _ } :
  (string, Aez.Smt.Symbol.t) Hashtbl.t =
  let symbols = Hashtbl.create 16 in
  let add_symbol ((id, _) as var) =
    var |> get_symbol_from_var |> Hashtbl.replace symbols id.name
  in

  List.iter add_symbol tn_input;
  List.iter add_symbol tn_output;
  List.iter add_symbol tn_local;

  symbols


(* ===== DÉFINITIONS ===== *)

(* Renvoie une formule du SMT correspondant à une expression donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
let rec get_formula_from_expr
  defs_aux (symbols : (string, Aez.Smt.Symbol.t) Hashtbl.t) n expr :
  Aez.Smt.Formula.t =
  match expr.texpr_desc with
  | TE_op (Op_eq, es) ->
    Formula.make_lit Formula.Eq
      (List.map (get_term_from_expr defs_aux symbols n) es)
  | TE_op (Op_neq, es) ->
    Formula.make_lit Formula.Neq
      (List.map (get_term_from_expr defs_aux symbols n) es)
  | TE_op (Op_lt, es) ->
    Formula.make_lit Formula.Lt
      (List.map (get_term_from_expr defs_aux symbols n) es)
  | TE_op (Op_le, es) ->
    Formula.make_lit Formula.Le
      (List.map (get_term_from_expr defs_aux symbols n) es)
  | TE_op (Op_gt, es) ->
    let expr = { expr with texpr_desc = TE_op (Op_le, es) } in
    Formula.make Formula.Not [ get_formula_from_expr defs_aux symbols n expr ]
  | TE_op (Op_ge, es) ->
    let expr = { expr with texpr_desc = TE_op (Op_lt, es) } in
    Formula.make Formula.Not [ get_formula_from_expr defs_aux symbols n expr ]
  | TE_op (Op_not, es) ->
    Formula.make Formula.Not
      (List.map (get_formula_from_expr defs_aux symbols n) es)
  | TE_op (Op_and, es) ->
    Formula.make Formula.And
      (List.map (get_formula_from_expr defs_aux symbols n) es)
  | TE_op (Op_or, es) ->
    Formula.make Formula.Or
      (List.map (get_formula_from_expr defs_aux symbols n) es)
  | TE_op (Op_impl, es) ->
    Formula.make Formula.Imp
      (List.map (get_formula_from_expr defs_aux symbols n) es)
  | _ ->
    Format.printf "Cash on this expression :@.";
    Typed_ast_printer.print_exp Format.std_formatter expr;
    Format.printf "\n%!";
    failwith "We can't make a FORMULA form this expression\n%!"


(* Renvoie un terme du SMT correspondant à une expression donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
and get_term_from_expr
  defs_aux (symbols : (string, Aez.Smt.Symbol.t) Hashtbl.t) n expr :
  Aez.Smt.Term.t =
  match expr.texpr_desc with
  | TE_const (Cbool false) -> Term.t_false
  | TE_const (Cbool true) -> Term.t_true
  | TE_const (Cint d) -> Term.make_int (Num.Int d)
  | TE_const (Creal r) -> Term.make_real (Num.num_of_string (string_of_float r))
  | TE_ident { name; _ } -> Term.make_app (Hashtbl.find symbols name) [ n ]
  | TE_op ((Op_add | Op_add_f), es) ->
    get_term_from_binop defs_aux symbols n Term.Plus es
  | TE_op ((Op_sub | Op_sub_f), es) ->
    get_term_from_binop defs_aux symbols n Term.Minus es
  | TE_op ((Op_mul | Op_mul_f), es) ->
    get_term_from_binop defs_aux symbols n Term.Mult es
  | TE_op ((Op_div | Op_div_f), es) ->
    get_term_from_binop defs_aux symbols n Term.Div es
  | TE_op (Op_mod, es) -> get_term_from_binop defs_aux symbols n Term.Modulo es
  | TE_op (Op_if, es) ->
    (* On suppose que es soit une liste a trois expressions *)
    let e1, es = (List.hd es, List.tl es) in
    let e2, es = (List.hd es, List.tl es) in
    let e3 = List.hd es in

    Term.make_ite
      (Formula.make_lit Formula.Eq
         [ get_term_from_expr defs_aux symbols n e1; Term.t_true ] )
      (get_term_from_expr defs_aux symbols n e2)
      (get_term_from_expr defs_aux symbols n e3)
  | TE_app ({ name; _ }, es) ->
    Term.make_app
      (Hashtbl.find symbols name)
      (List.map (get_term_from_expr defs_aux symbols n) es)
  | TE_prim ({ name; _ }, es) -> failwith "TODO-MC-Op_prim"
  | TE_arrow (e1, e2) ->
    Term.make_ite
      (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
      (get_term_from_expr defs_aux symbols n e1)
      (get_term_from_expr defs_aux symbols n e2)
  | TE_pre e ->
    get_term_from_expr defs_aux symbols
      (Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)))
      e
  | TE_op
      ( ( Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge | Op_not | Op_and
        | Op_or | Op_impl ),
        es ) ->
    let aux_name, aux = get_fresh_symbol Asttypes.Tbool () in
    Hashtbl.replace symbols aux_name aux;
    defs_aux := (aux, es) :: !defs_aux;
    Term.make_app aux [ n ]
  | TE_tuple _ -> assert false


(* Renvoie une formule du SMT correspondant à une expression binop donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier et l'opération du SMT
*)
and get_term_from_binop defs_aux symbols n op es =
  match es with
  | [] | [ _ ] -> assert false
  | [ e1; e2 ] ->
    Term.make_arith op
      (get_term_from_expr defs_aux symbols n e1)
      (get_term_from_expr defs_aux symbols n e2)
  | e :: es ->
    Term.make_arith op
      (get_term_from_expr defs_aux symbols n e)
      (get_term_from_binop defs_aux symbols n op es)


(* Obtient une definition pour le SMT à partir d'un ensemble d'équations
   Pré-condition : ne pas avoir de tuples dans les équations
*)
let get_def_from_eqs symbols eqs : Aez.Smt.Term.t -> Aez.Smt.Formula.t =
  let defs_aux = ref [] in

  let defs =
    List.map
      begin fun { teq_patt; teq_expr } ->
        let def_name = (List.hd teq_patt.tpatt_desc).name in

        fun n ->
          Formula.make_lit Formula.Eq
            [
              Term.make_app (Hashtbl.find symbols def_name) [ n ];
              get_term_from_expr defs_aux symbols n teq_expr;
            ]
      end
      eqs
  in

  let final_defs_aux = ref [] in
  while !defs_aux <> [] do
    let tmp_aux = ref [] in
    List.iter
      begin fun (aux, es) ->
        let tmp_aux_intern = ref [] in
        let def_aux =
         fun n ->
          let def_auxn =
            Formula.make_lit Formula.Eq [ Term.make_app aux [ n ]; Term.t_true ]
          in
          let def_es =
            es
            |> List.map (get_formula_from_expr tmp_aux_intern symbols n)
            |> Formula.make Formula.And
          in
          Formula.make Formula.And
            [
              Formula.make Formula.Imp [ def_auxn; def_es ];
              Formula.make Formula.Imp [ def_es; def_auxn ];
            ]
        in
        final_defs_aux := def_aux :: !final_defs_aux;
        tmp_aux := !tmp_aux_intern @ !tmp_aux
      end
      !defs_aux;
    defs_aux := !tmp_aux
  done;

  let final_defs = defs @ !final_defs_aux in
  fun n -> Formula.make Formula.And (List.map (fun def -> def n) final_defs)


(* Obtient la définition delta et p d'un noeud donné
   La définition delta correspond à la conjonction des définitions des équations du noeud
   La définition p assure qu'on veut que la propriété OK soit vraie
*)
let get_defs_from_node ({ tn_equs } as node) :
  (Aez.Smt.Term.t -> Aez.Smt.Formula.t) * (Aez.Smt.Term.t -> Aez.Smt.Formula.t)
    =
  let symbols = get_symbols_from_node node in
  let delta_def = get_def_from_eqs symbols tn_equs in
  let p_def n =
    Formula.make_lit Formula.Eq
      [ Term.make_app (Hashtbl.find symbols "OK") [ n ]; Term.t_true ]
  in
  (delta_def, p_def)


(* ===== CAS DE BASE ===== *)

(* Notre solveur pour le cas de base *)
module BMC_solver = Smt.Make (struct end)

(* Définit le cas de base de la propriété *)
let get_base_case node delta p =
  let assume = BMC_solver.assume ~id:0 in
  let entails = BMC_solver.entails ~id:0 in
  let check = BMC_solver.check in

  Format.printf "max_arrow_depth = %d\n%!" (max_arrow_depth node);
  let basecase_number = 1 + max_arrow_depth node in
  Format.printf "basecase_number = %d\n%!" basecase_number;

  for i = 0 to basecase_number - 1 do
    Format.printf "%dème base case\n%!" i;
    let delta_i = delta (Term.make_int (Num.Int i)) in
    Format.printf "Delta(%d) =\n%!" i;
    Formula.print Format.std_formatter delta_i;
    Format.printf "\n%!";
    assume delta_i
  done;
  check ();

  let ok_formula =
    Formula.make Formula.And
      (List.init basecase_number (fun i ->
         Format.printf "%dème p case\n%!" i;
         p (Term.make_int (Num.Int i)) ) )
  in
  Format.printf "OK =\n%!";
  Formula.print Format.std_formatter ok_formula;
  Format.printf "\n%!";
  entails ok_formula


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
  let delta, p = get_defs_from_node node in

  if not (get_base_case node delta p) then Format.printf "FALSE PROPERTY@."
  else if get_ind_case delta p then Format.printf "TRUE PROPERTY@."
  else Format.printf "Don't know@."
