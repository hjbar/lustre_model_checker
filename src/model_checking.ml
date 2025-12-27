open Smtml
open Typed_ast
open Ident

(* ===== UTILS ===== *)

(* Conversion d'un type Lustre en un type Alt-Ergo *)
let asttype_to_smttype = function
  | Asttypes.Tbool -> Ty.Ty_bool
  | Asttypes.Tint -> Ty.Ty_int
  | Asttypes.Treal -> Ty.Ty_real


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


(* ===== TERM ===== *)

(* Constante Term 0 *)
let term_0 = Expr.value (Value.Int 0)

(* Constante Term 0. *)
let term_0f = Expr.value (Value.Real 0.)

(* Constante Term 1 *)
let term_1 = Expr.value (Value.Int 1)

(* Créer le terme Term d *)
let term_int d = Expr.value (Value.Int d)

(* Créer le terme Term f *)
let term_real f = Expr.value (Value.Real f)

(* Constante True *)

let term_true = Expr.value Value.True

(* Constante False *)

let term_false = Expr.value Value.False

(* Addition entre deux termes *)
let term_add_int t1 t2 = Expr.binop Ty.Ty_int Ty.Binop.Add t1 t2

let ( +@ ) = term_add_int

let term_add_real t1 t2 = Expr.binop Ty.Ty_real Ty.Binop.Add t1 t2

let ( +.@ ) = term_add_real

(* Négation d'un terme *)
let term_neg_int t = Expr.unop Ty.Ty_int Ty.Unop.Neg t

let term_neg_real t = Expr.unop Ty.Ty_real Ty.Unop.Neg t

(* Soustraction entre deux termes *)
let term_sub_int t1 t2 = Expr.binop Ty.Ty_int Ty.Binop.Sub t1 t2

let ( -@ ) = term_sub_int

let term_sub_real t1 t2 = Expr.binop Ty.Ty_real Ty.Binop.Sub t1 t2

let ( -.@ ) = term_sub_real

(* Multiplication entre deux termes *)
let term_mul_int t1 t2 = Expr.binop Ty.Ty_int Ty.Binop.Mul t1 t2

let ( *@ ) = term_add_int

let term_mul_real t1 t2 = Expr.binop Ty.Ty_real Ty.Binop.Mul t1 t2

let ( *.@ ) = term_add_real

(* Division entre deux termes *)
let term_div_int t1 t2 = Expr.binop Ty.Ty_int Ty.Binop.Div t1 t2

let ( /@ ) = term_add_int

let term_div_real t1 t2 = Expr.binop Ty.Ty_real Ty.Binop.Div t1 t2

let ( /.@ ) = term_add_real

(* Modulo entre deux termes *)

let term_mod t1 t2 =
  match (Expr.ty t1, Expr.ty t2) with
  | Ty.Ty_int, Ty.Ty_int -> Expr.binop Ty.Ty_int Ty.Binop.Rem t1 t2
  | Ty.Ty_int, Ty.Ty_real | Ty.Ty_real, Ty.Ty_int | Ty.Ty_real, Ty.Ty_real ->
    Expr.binop Ty.Ty_real Ty.Binop.Rem t1 t2
  | _ -> assert false


(* Application f(x) *)
let term_app f x = Expr.app f [ x ]

(* Application f() *)
let term_app_unit f = Expr.app f []

(* Négation logique d'un terme *)
let term_not t = Expr.unop Ty.Ty_bool Ty.Unop.Not t

(* Conjonction entre deux termes *)
let term_and t1 t2 = Expr.binop Ty.Ty_bool Ty.Binop.And t1 t2

let ( &&@ ) = term_and

let rec term_ands = function
  | [] -> assert false
  | [ t ] -> t
  | [ t1; t2 ] -> term_and t1 t2
  | t :: ts -> term_and t (term_ands ts)


(* Disjonction entre deux termes *)
let term_or t1 t2 = Expr.binop Ty.Ty_bool Ty.Binop.Or t1 t2

let ( ||@ ) = term_or

(* Implication entre deux termes *)
let term_imp t1 t2 = Expr.binop Ty.Ty_bool Ty.Binop.Implies t1 t2

(* Égalité entre deux termes *)
let term_eq t1 t2 = Expr.relop Ty.Ty_bool Ty.Relop.Eq t1 t2

let ( =@ ) = term_eq

(* Non-égalité entre deux termes *)
let term_neq t1 t2 = Expr.relop Ty.Ty_bool Ty.Relop.Ne t1 t2

let ( <>@ ) = term_neq

(* Strictement inférieur pour deux termes *)
let term_lt t1 t2 = Expr.relop Ty.Ty_bool Ty.Relop.Lt t1 t2

let ( <@ ) = term_lt

(* Inférieur ou égal pour deux termes *)
let term_le t1 t2 = Expr.relop Ty.Ty_bool Ty.Relop.Le t1 t2

let ( <=@ ) = term_le

(* Supérieur ou égal pour deux termes *)
let term_ge t1 t2 = Expr.relop Ty.Ty_bool Ty.Relop.Ge t1 t2

let ( >=@ ) = term_ge

(* Strictement supérieur pour deux termes *)
let term_gt t1 t2 = Expr.relop Ty.Ty_bool Ty.Relop.Gt t1 t2

let ( >@ ) = term_gt

(* If-Then-Else pour trois termes *)
let term_ite t1 t2 t3 =
  let ty2 = Expr.ty t2 in
  let ty3 = Expr.ty t3 in
  if ty2 <> ty3 then assert false else Expr.triop ty2 Ty.Triop.Ite t1 t2 t3


(* ===== SYMBOLES ===== *)

(* Declare un symbole pour une constante d'un certain *)
let declare_symbol_cst name ty = Symbol.make ty name

(* Declare un symbole pour une fonction *)
let declare_symbol_fun name = Symbol.make Ty.Ty_app name

(* Declare un symbole frais pour une fonction auxilaire *)
let declare_symbol_fun_aux =
  let cpt = ref ~-1 in
  fun () ->
    incr cpt;
    let name = Format.sprintf "aux_%d" !cpt in
    (name, declare_symbol_fun name)


(* Declare des symboles à partir d'un noeud *)
let get_symbols_from_node aux { tn_input; tn_output; tn_local; _ } =
  let symbols = Hashtbl.create 16 in
  let add_symbol (id, _) =
    id.name |> declare_symbol_fun |> Hashtbl.replace symbols id.name
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
let rec get_formula_from_expr symbols n expr =
  match expr.texpr_desc with
  | TE_op (Op_eq, es) -> get_formula_from_lit symbols n term_eq es
  | TE_op (Op_neq, es) -> get_formula_from_lit symbols n term_neq es
  | TE_op (Op_lt, es) -> get_formula_from_lit symbols n term_lt es
  | TE_op (Op_le, es) -> get_formula_from_lit symbols n term_le es
  | TE_op (Op_gt, es) -> get_formula_from_lit symbols n term_gt es
  | TE_op (Op_ge, es) -> get_formula_from_lit symbols n term_ge es
  | TE_op (Op_not, es) -> get_formula_from_unop symbols n term_not es
  | TE_op (Op_and, es) -> get_formula_from_binop symbols n term_and es
  | TE_op (Op_or, es) -> get_formula_from_binop symbols n term_or es
  | TE_op (Op_impl, es) -> get_formula_from_binop symbols n term_imp es
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
  | e1 when require_formula e1 -> op (get_formula_from_expr symbols n e1)
  | e1 -> op (get_term_from_expr 0 symbols n e1 =@ term_true)


(* Renvoie une formule du SMT correspondant à une expression binop donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier
*)
and get_formula_from_binop symbols n op es =
  match assume_2 es with
  | e1, e2 when require_formula e1 && require_formula e2 ->
    op (get_formula_from_expr symbols n e1) (get_formula_from_expr symbols n e2)
  | e1, e2 when require_formula e1 ->
    op
      (get_formula_from_expr symbols n e1)
      (get_term_from_expr 0 symbols n e2 =@ term_true)
  | e1, e2 when require_formula e2 ->
    op
      (get_term_from_expr 0 symbols n e1 =@ term_true)
      (get_formula_from_expr symbols n e2)
  | e1, e2 ->
    op
      (get_term_from_expr 0 symbols n e1 =@ term_true)
      (get_term_from_expr 0 symbols n e2 =@ term_true)


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
  | TE_op (Op_add, es) -> get_term_from_binop symbols n term_add_int es
  | TE_op (Op_add_f, es) -> get_term_from_binop symbols n term_add_real es
  | TE_op (Op_sub, [ e ]) -> term_neg_int (get_term_from_expr 0 symbols n e)
  | TE_op (Op_sub_f, [ e ]) -> term_neg_real (get_term_from_expr 0 symbols n e)
  | TE_op (Op_sub, es) -> get_term_from_binop symbols n term_sub_int es
  | TE_op (Op_sub_f, es) -> get_term_from_binop symbols n term_sub_real es
  | TE_op (Op_mul, es) -> get_term_from_binop symbols n term_mul_int es
  | TE_op (Op_mul_f, es) -> get_term_from_binop symbols n term_mul_real es
  | TE_op (Op_div, es) -> get_term_from_binop symbols n term_div_int es
  | TE_op (Op_div_f, es) -> get_term_from_binop symbols n term_div_real es
  | TE_op (Op_mod, es) -> get_term_from_binop symbols n term_mod es
  | TE_op (Op_if, es) ->
    let d1, d2, d3 =
      es |> List.map (get_term_from_expr 0 symbols n) |> assume_3
    in
    term_ite (d1 =@ term_true) d2 d3
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
  | TE_op _ ->
    Format.printf "Cash on this expression :@.";
    Typed_ast_printer.print_exp Format.std_formatter expr;
    Format.printf "\n%!";
    failwith "We can't make a TERM form this expression\n%!"
  | TE_app _ -> assert false
  | TE_prim _ -> assert false
  | TE_tuple _ -> assert false


(* Renvoie une formule du SMT correspondant à une expression binop donnée
   Prend en argument l'ensemble des symboles ainsi qu'un terme SMT n entier et l'opération du SMT
*)
and get_term_from_binop symbols n op es =
  let d1, d2 = es |> List.map (get_term_from_expr 0 symbols n) |> assume_2 in
  op d1 d2


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

         term_imp aux_def expr_def &&@ term_imp expr_def aux_def
      end
      aux
  in

  let final_defs = defs @ defs_aux in

  fun n -> term_ands (List.map (fun def -> def n) final_defs)


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
      let aux_name, aux_symbol = declare_symbol_fun_aux () in
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

(* Notre solveur pour le cas de base *)
module BMC_solver = Solver.Batch (Altergo_mappings)

(* Solveur cas de base k-inductif (a k fixe)*)

let get_base_case_k_inductive delta p k =
  let solver = BMC_solver.create () in
  let assumptions = ref [] in
  let assume t =
    assumptions := t :: !assumptions;
    BMC_solver.add solver [ t ]
  in
  let entails t = BMC_solver.check solver [ term_not t ] = `Unsat in
  let check () =
    if BMC_solver.check solver !assumptions <> `Sat then assert false
  in

  for i = 0 to k - 1 do
    let delta_i = delta (term_int i) in
    assume delta_i
  done;
  check ();

  let final_p =
    match k with
    | 1 -> p term_0
    | _ -> term_ands (List.init k (fun i -> p (term_int i)))
  in

  entails final_p


(* ===== CAS INDUCTIF ===== *)

(* Notre solveur pour le cas inductif *)
module IND_solver = Solver.Batch (Altergo_mappings)

(* Cas inductif pour k-induction (a k fixe)*)

let get_ind_case_k_inductive delta p k =
  let solver = IND_solver.create () in
  let assumptions = ref [] in
  let assume t =
    assumptions := t :: !assumptions;
    IND_solver.add solver [ t ]
  in
  let entails t = IND_solver.check solver [ term_not t ] = `Unsat in
  let check () =
    if IND_solver.check solver !assumptions <> `Sat then assert false
  in

  let n =
    term_app_unit (declare_symbol_cst ("n_k_" ^ string_of_int k) Ty.Ty_int)
  in

  assume (term_0 <=@ n);
  assume (delta n);
  assume (p n);

  for i = 1 to k do
    let delta_k = delta (n +@ term_int i) in
    assume delta_k
  done;

  for i = 1 to k - 1 do
    assume (p (n +@ term_int i))
  done;
  check ();
  entails (p (n +@ term_int k))


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
