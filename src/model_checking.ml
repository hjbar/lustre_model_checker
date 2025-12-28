open Model_checking_utils
open Typed_ast

let debug = false

(* ===== DÉFINITIONS ===== *)

(* Renvoie une formule du SMT correspondant à une expression donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
let rec get_formula_from_expr symbols n expr =
  match expr.texpr_desc with
  | TE_op (Op_eq, es) -> get_formula_from_lit symbols n formula_eq es
  | TE_op (Op_neq, es) -> get_formula_from_lit symbols n formula_neq es
  | TE_op (Op_lt, es) -> get_formula_from_lit symbols n formula_lt es
  | TE_op (Op_le, es) -> get_formula_from_lit symbols n formula_le es
  | TE_op (Op_gt, es) -> get_formula_from_lit symbols n formula_gt es
  | TE_op (Op_ge, es) -> get_formula_from_lit symbols n formula_ge es
  | TE_op (Op_not, es) -> get_formula_from_unop symbols n formula_not es
  | TE_op (Op_and, es) -> get_formula_from_binop symbols n formula_and es
  | TE_op (Op_or, es) -> get_formula_from_binop symbols n formula_or es
  | TE_op (Op_impl, es) -> get_formula_from_binop symbols n formula_imp es
  | _ ->
    Format.printf "Cash on this expression :@.";
    Typed_ast_printer.print_exp Format.std_formatter expr;
    Format.printf "\n%!";
    failwith "We can't make a FORMULA form this expression\n%!"


(* Renvoie un formule du SMT correspondant à une expression transformée donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
and get_formula_from_expr_transformer symbols n e =
  if require_formula e then get_formula_from_expr symbols n e
  else get_term_from_expr 0 symbols n e =@ term_true


(* Renvoie une formule du SMT correspondant à une expression unop donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
and get_formula_from_unop symbols n unop es =
  let f = es |> assume_1 |> get_formula_from_expr_transformer symbols n in
  unop f


(* Renvoie une formule du SMT correspondant à une expression binop donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
and get_formula_from_binop symbols n binop es =
  let f1, f2 =
    es |> List.map (get_formula_from_expr_transformer symbols n) |> assume_2
  in
  binop f1 f2


(* Renvoie une formule du SMT correspondant à une expression littérale donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
and get_formula_from_lit symbols n op es =
  let e1, e2 = es |> List.map (get_term_from_expr 0 symbols n) |> assume_2 in
  op e1 e2


(* Renvoie un terme du SMT correspondant à une expression donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
and get_term_from_expr arr_length symbols n expr =
  match expr.texpr_desc with
  | TE_const (Cbool false) -> term_false
  | TE_const (Cbool true) -> term_true
  | TE_const (Cint d) -> term_int d
  | TE_const (Creal r) -> term_real r
  | TE_ident { name; _ } -> term_app (Hashtbl.find symbols name) n
  | TE_op ((Op_add | Op_add_f), es) -> get_term_from_binop symbols n term_add es
  | TE_op (Op_sub, [ e ]) -> term_0 -@ get_term_from_expr 0 symbols n e
  | TE_op (Op_sub_f, [ e ]) -> term_0f -@ get_term_from_expr 0 symbols n e
  | TE_op ((Op_sub | Op_sub_f), es) -> get_term_from_binop symbols n term_sub es
  | TE_op ((Op_mul | Op_mul_f), es) -> get_term_from_binop symbols n term_mul es
  | TE_op ((Op_div | Op_div_f), es) -> get_term_from_binop symbols n term_div es
  | TE_op (Op_mod, es) -> get_term_from_binop symbols n term_mod es
  | TE_op (Op_if, es) ->
    let t1, t2, t3 =
      es |> List.map (get_term_from_expr 0 symbols n) |> assume_3
    in
    term_ite (t1 =@ term_true) t2 t3
  | TE_prim ({ name; _ }, es) when name = "int_of_real" ->
    ignore es;
    failwith "TODO-int_of_real"
  | TE_prim ({ name; _ }, es) when name = "real_of_int" ->
    ignore es;
    failwith "TODO-real_of_int"
  | TE_arrow (e1, e2) ->
    term_ite
      (n =@ term_int arr_length)
      (get_term_from_expr 0 symbols n e1)
      (get_term_from_expr (arr_length + 1) symbols n e2)
  | TE_pre e -> get_term_from_expr 0 symbols (n -@ term_1) e
  | TE_prim _ -> assert false
  | TE_app _ -> assert false
  | TE_tuple _ -> assert false
  | TE_op _ ->
    Format.printf "Cash on this expression :@.";
    Typed_ast_printer.print_exp Format.std_formatter expr;
    Format.printf "\n%!";
    failwith "We can't make a TERM form this expression\n%!"


(* Renvoie une formule du SMT correspondant à une expression binop donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier et l'opération du SMT
*)
and get_term_from_binop symbols n binop es =
  let t1, t2 = es |> List.map (get_term_from_expr 0 symbols n) |> assume_2 in
  binop t1 t2


(* Obtient une definition pour le SMT à partir d'un ensemble d'équations
   Pré-condition : ne pas avoir de tuples dans les équations
*)
let get_def_from_eqs symbols aux eqs =
  let defs =
    List.map
      begin fun { teq_patt; teq_expr } ->
        let def_name = (List.hd teq_patt.tpatt_desc).name in
        fun n ->
          term_app (Hashtbl.find symbols def_name) n
          =@ get_term_from_expr 0 symbols n teq_expr
      end
      eqs
  in

  let defs_aux =
    List.map
      begin fun (_, symbol, expr) ->
        fun n ->
         let aux_def = term_app symbol n =@ term_true in
         let expr_def = get_formula_from_expr symbols n expr in

         formula_imp aux_def expr_def &&@ formula_imp expr_def aux_def
      end
      aux
  in

  let final_defs = defs @ defs_aux in

  fun n -> formula_ands (List.map (fun def -> def n) final_defs)


(* Obtient la définition delta et p d'un noeud donné
   La définition delta correspond à la conjonction des définitions des équations du noeud
   La définition p assure qu'on veut que la propriété OK soit vraie
*)
let get_defs_from_node aux ({ tn_equs; _ } as node) =
  let symbols = get_symbols_from_node aux node in
  let delta_def = get_def_from_eqs symbols aux tn_equs in
  let p_def n = term_app (Hashtbl.find symbols "OK") n =@ term_true in
  (delta_def, p_def)


(* ===== PRÉ-PROCESS ===== *)

(* Preprocess une expression pour créer les expressions auxiliaires *)
let rec preprocess_expr ({ texpr_desc; _ } as expr) =
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
    | TE_app _ -> assert false
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

(* Solveur cas de base k-inductif (a k fixe) *)
let get_base_case_k_inductive delta p k =
  let assume = BMC_solver.assume ~id:k in
  let entails = BMC_solver.entails ~id:k in
  let check = BMC_solver.check in

  for i = 0 to k - 1 do
    let delta_i = delta (term_int i) in
    if debug then begin
      Format.printf "delta_%d =\n\t%!" i;
      formula_print delta_i;
      Format.printf "\n\n%!"
    end;
    assume delta_i
  done;
  check ();

  let final_p =
    match k with
    | 1 -> p term_0
    | _ -> formula_ands (List.init k (fun i -> p (term_int i)))
  in
  if debug then begin
    Format.printf "final_p =\n\t%!";
    formula_print final_p;
    Format.printf "\n\n%!"
  end;

  entails final_p


(* ===== CAS INDUCTIF ===== *)

(* Cas inductif pour k-induction (a k fixe) *)
let get_ind_case_k_inductive delta p k =
  let assume = IND_solver.assume ~id:k in
  let entails = IND_solver.entails ~id:k in
  let check = IND_solver.check in

  let n =
    term_app_unit (declare_symbol ("n_k_" ^ string_of_int k) [] type_int)
  in

  assume (term_0 <=@ n);
  assume (delta n);
  assume (p n);

  for i = 1 to k do
    let delta_k = delta (n +@ term_int i) in
    if debug then begin
      Format.printf "delta_n+%d =\n\t%!" i;
      formula_print delta_k;
      Format.printf "\n\n%!"
    end;
    assume delta_k
  done;

  for i = 1 to k - 1 do
    let p_i = p (n +@ term_int i) in
    if debug then begin
      Format.printf "p_n+%d =\n\t%!" i;
      formula_print p_i;
      Format.printf "\n\n%!"
    end;
    assume p_i
  done;
  check ();

  let p_k = p (n +@ term_int k) in
  if debug then begin
    Format.printf "p_n+%d =\n\t%!" k;
    formula_print p_k;
    Format.printf "\n\n%!"
  end;
  entails p_k


(* ===== CHECKING ===== *)

let check node =
  let k = 20 in
  let aux, node = preprocess_node node in
  let delta, p = get_defs_from_node aux node in

  for i = 1 to k do
    Format.printf "Checking k-inductive for k=%d@." i;
    if not (get_base_case_k_inductive delta p i) then begin
      Format.printf "\027[31mFALSE PROPERTY at base case k=%d\027[0m@." i;
      exit 0
    end
    else if get_ind_case_k_inductive delta p i then begin
      Format.printf "\027[32mTRUE PROPERTY at k=%d\027[0m@." i;
      exit 0
    end
  done;
  Format.printf "\027[34mDon't know after k=%d\027[0m@." k
