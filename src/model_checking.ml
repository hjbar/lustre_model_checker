open Utils
open Model_checking_utils
open Typed_ast

let debug = false

(* ===== DÉFINITIONS ===== *)

(* Renvoie un terme du SMT correspondant à une expression donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
let rec get_term_from_expr arr_length types n { texpr_desc; _ } =
  let get_term_from_expr_rec = get_term_from_expr 0 types n in
  let get_term_from_unop unop es =
    let t = es |> assume_1 |> get_term_from_expr_rec in
    unop t
  in
  let get_term_from_binop binop es =
    let t1, t2 = es |> List.map get_term_from_expr_rec |> assume_2 in
    binop t1 t2
  in

  match texpr_desc with
  | TE_const (Cbool false) -> term_false
  | TE_const (Cbool true) -> term_true
  | TE_const (Cint d) -> term_int d
  | TE_const (Creal r) -> term_real r
  | TE_ident { name; _ } ->
    let ty = Hashtbl.find types name in
    term_var (get_symbol name ty n)
  | TE_op (Op_add, es) -> get_term_from_binop term_add_int es
  | TE_op (Op_add_f, es) -> get_term_from_binop term_add_real es
  | TE_op (Op_sub, [ e ]) -> get_term_from_unop term_neg_int [ e ]
  | TE_op (Op_sub_f, [ e ]) -> get_term_from_unop term_neg_real [ e ]
  | TE_op (Op_sub, es) -> get_term_from_binop term_sub_int es
  | TE_op (Op_sub_f, es) -> get_term_from_binop term_sub_real es
  | TE_op (Op_mul, es) -> get_term_from_binop term_mul_int es
  | TE_op (Op_mul_f, es) -> get_term_from_binop term_mul_real es
  | TE_op (Op_div, es) -> get_term_from_binop term_div_int es
  | TE_op (Op_div_f, es) -> get_term_from_binop term_div_real es
  | TE_op (Op_mod, es) -> get_term_from_binop term_mod es
  | TE_op (Op_eq, es) -> get_term_from_binop term_eq es
  | TE_op (Op_neq, es) -> get_term_from_binop term_neq es
  | TE_op (Op_lt, es) -> get_term_from_binop term_lt es
  | TE_op (Op_le, es) -> get_term_from_binop term_le es
  | TE_op (Op_gt, es) -> get_term_from_binop term_gt es
  | TE_op (Op_ge, es) -> get_term_from_binop term_ge es
  | TE_op (Op_not, es) -> get_term_from_unop term_not es
  | TE_op (Op_and, es) -> get_term_from_binop term_and es
  | TE_op (Op_or, es) -> get_term_from_binop term_or es
  | TE_op (Op_impl, es) -> get_term_from_binop term_imp es
  | TE_op (Op_if, es) ->
    let t1, t2, t3 = es |> List.map get_term_from_expr_rec |> assume_3 in
    term_ite (t1 =@ term_true) t2 t3
  | TE_prim ({ name; _ }, es) when name = "int_of_real" ->
    get_term_from_unop term_as_int es
  | TE_prim ({ name; _ }, es) when name = "real_of_int" ->
    get_term_from_unop term_as_real es
  | TE_arrow (e1, e2) ->
    term_ite
      (diff_extract n =@ term_int arr_length)
      (get_term_from_expr_rec e1)
      (get_term_from_expr (arr_length + 1) types n e2)
  | TE_pre e -> get_term_from_expr 0 types (diff_decr n) e
  | TE_prim _ | TE_app _ | TE_tuple _ -> assert false


(* Obtient une definition pour le SMT à partir d'un ensemble d'équations
   Pré-condition : ne pas avoir de tuples dans les équations
*)
let get_def_from_eqs types eqs =
  let defs =
    List.map
      begin fun { teq_patt; teq_expr } ->
        let def_name = (List.hd teq_patt.tpatt_desc).name in
        let def_type = Hashtbl.find types def_name in
        fun n ->
          term_var (get_symbol def_name def_type n)
          =@ get_term_from_expr 0 types n teq_expr
      end
      eqs
  in
  fun n -> term_ands (List.map (fun def -> def n) defs)


(* Obtient la définition delta et p d'un noeud donné
   La définition delta correspond à la conjonction des définitions des équations du noeud
   La définition p assure qu'on veut que la propriété OK soit vraie
*)
let get_defs_from_node ({ tn_equs; _ } as node) =
  let types = get_types_from_node node in
  let delta_def = get_def_from_eqs types tn_equs in
  let p_typ = Hashtbl.find types "OK" in
  let p_def n = term_var (get_symbol "OK" p_typ n) =@ term_true in
  (delta_def, p_def)


(* ===== CAS DE BASE ===== *)

(* Solveur cas de base k-inductif (a k fixe) *)
let get_base_case_k_inductive delta p k =
  let solver = BMC_solver.create () in
  let context = ref [] in

  let assume f =
    context := f :: !context;
    BMC_solver.add solver [ f ]
  in
  let check () =
    if BMC_solver.check solver !context <> `Sat then failwith "Unsat context"
  in
  let entails f = BMC_solver.check solver [ term_not f ] = `Unsat in

  for i = 0 to k - 1 do
    let delta_i = delta (diff_init (term_int i) 0) in
    if debug then begin
      Format.printf "delta_%d =\n\t%!" i;
      term_print delta_i;
      Format.printf "\n\n%!"
    end;
    assume delta_i
  done;
  check ();

  let final_p =
    term_ands (List.init k (fun i -> p (diff_init (term_int i) 0)))
  in
  if debug then begin
    Format.printf "final_p =\n\t%!";
    term_print final_p;
    Format.printf "\n\n%!"
  end;
  entails final_p


(* ===== CAS INDUCTIF ===== *)

(* Cas inductif pour k-induction (a k fixe) *)
let get_ind_case_k_inductive delta p k =
  let solver = IND_solver.create () in
  let context = ref [] in

  let assume f =
    context := f :: !context;
    IND_solver.add solver [ f ]
  in
  let check () =
    if IND_solver.check solver !context <> `Sat then failwith "Unsat context"
  in
  let entails f = IND_solver.check solver [ term_not f ] = `Unsat in

  let n = term_var (declare_symbol ("n_k_" ^ string_of_int k) type_int) in

  let cond = term_0 <=@ n in
  let delta_n = delta (diff_init n 0) in
  let p_n = p (diff_init n 0) in
  if debug then begin
    Format.printf "cond =\n\t%!";
    term_print cond;
    Format.printf "\n\n%!";
    Format.printf "delta_n =\n\t%!";
    term_print delta_n;
    Format.printf "\n\n%!";
    Format.printf "p_n =\n\t%!";
    term_print p_n;
    Format.printf "\n\n%!"
  end;
  assume cond;
  assume delta_n;
  assume p_n;

  for i = 1 to k do
    let delta_k = delta (diff_init n i) in
    if debug then begin
      Format.printf "delta_n+%d =\n\t%!" i;
      term_print delta_k;
      Format.printf "\n\n%!"
    end;
    assume delta_k
  done;

  for i = 1 to k - 1 do
    let p_i = p (diff_init n i) in
    if debug then begin
      Format.printf "p_n+%d =\n\t%!" i;
      term_print p_i;
      Format.printf "\n\n%!"
    end;
    assume p_i
  done;
  check ();

  let p_k = p (diff_init n k) in
  if debug then begin
    Format.printf "p_n+%d =\n\t%!" k;
    term_print p_k;
    Format.printf "\n\n%!"
  end;
  entails p_k


(* ===== CHECKING ===== *)

exception Solved

let check node =
  let delta, p = get_defs_from_node node in
  try
    for i = 1 to max_int do
      Format.printf "Checking k-inductive for k=%d@." i;
      if not (get_base_case_k_inductive delta p i) then begin
        Format.printf "\027[31mFALSE PROPERTY at base case k=%d\027[0m@." i;
        raise Solved
      end
      else if get_ind_case_k_inductive delta p i then begin
        Format.printf "\027[32mTRUE PROPERTY at k=%d\027[0m@." i;
        raise Solved
      end
    done;
    Format.printf "\027[34mDon't know\027[0m@."
  with Solved -> ()
