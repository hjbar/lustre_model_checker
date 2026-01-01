open Utils
open Aez
open Smt
open Typed_ast
open Ident

(* ===== UTILS ===== *)

(* Renvoie true si on veut une formule pour cet opérateur dans le solveur, false sinon *)
let require_formula expr =
  match expr.texpr_desc with
  | TE_op
      ( ( Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge | Op_not | Op_and
        | Op_or | Op_impl ),
        _ ) ->
    true
  | _ -> false


(* ===== TYPES ===== *)

(* Type bool du SMT *)
let type_bool = Type.type_bool

(* Type int du SMT *)
let type_int = Type.type_int

(* Type real du SMT *)
let type_real = Type.type_real

(* Conversion d'un type Lustre en un type Alt-Ergo *)
let asttype_to_smttype = function
  | Asttypes.Tbool -> type_bool
  | Asttypes.Tint -> type_int
  | Asttypes.Treal -> type_real


(* ===== FORMULA ===== *)

(* Formule True *)
let formula_true = Formula.f_true

(* Formule False *)
let formula_false = Formula.f_false

(* Négation d'une formule *)
let formula_not f = Formula.make Formula.Not [ f ]

(* Égalité entre deux termes *)
let formula_eq t1 t2 = Formula.make_lit Formula.Eq [ t1; t2 ]

let ( =@ ) = formula_eq

(* Non-égalité entre deux termes *)
let formula_neq t1 t2 = Formula.make_lit Formula.Neq [ t1; t2 ]

let ( <>@ ) = formula_neq

(* Inférieur ou égal pour deux termes *)
let formula_le t1 t2 = Formula.make_lit Formula.Le [ t1; t2 ]

let ( <=@ ) = formula_le

(* Strictement inférieur pour deux termes *)
let formula_lt t1 t2 = Formula.make_lit Formula.Lt [ t1; t2 ]

let ( <@ ) = formula_lt

(* Strictement supérieur pour deux termes *)
let formula_gt t1 t2 = formula_not (t1 <=@ t2)

let ( >@ ) = formula_gt

(* Supérieur ou égal pour deux termes *)
let formula_ge t1 t2 = formula_not (t1 <@ t2)

let ( >=@ ) = formula_ge

(* Conjonction entre deux formules *)
let formula_and f1 f2 = Formula.make Formula.And [ f1; f2 ]

let ( &&@ ) = formula_and

let formula_ands fs = Formula.make Formula.And fs

(* Disjonction entre deux formules *)
let formula_or f1 f2 = Formula.make Formula.Or [ f1; f2 ]

let ( ||@ ) = formula_or

let formula_ors fs = Formula.make Formula.Or fs

(* Implication entre deux formules *)
let formula_imp f1 f2 = Formula.make Formula.Imp [ f1; f2 ]

(* Affiche une formule donnée *)
let formula_print f = Formula.print Format.std_formatter f

(* ===== NUM ===== *)

(* Constante Num.num 0 *)
let num_0 = Num.Int 0

(* Constante Num.num 1 *)
let num_1 = Num.Int 1

(* Constante Num.num 2 *)
let num_2 = Num.Int 2

(* Conversion d'un float OCaml en un Num.num
   Importé depuis StackOverflow
   https://stackoverflow.com/questions/40219852/string-to-float-in-ocaml-over-and-under-approximation

   expand consiste à convertir un nombre flottant en un développement binaire,
   i.e. expand(x) = floor(x) + ((expand (2 * frac(x)) / 2) si frac(x) <> 0, sinon 0)

   frexp nous donne une décomposition de x telle que x = fl * 2^ex avec 0.5 <= fl < 1 un float OCaml
   Maintenant on calcul expand(fl) * 2^ex avec expand qui converti fl en rationel Num
   Si ex=0 alors x = fl * 2^0 = fl * 1 = fl donc on expand fl sans multiplier par 2^ex
*)
let num_of_float x =
  let rec expand x =
    let fr, wh = modf x in
    Num.add_num
      (Num.Int (int_of_float wh))
      (if fr = 0.0 then num_0 else Num.div_num (expand (2.0 *. fr)) num_2)
  in
  let fl, ex = frexp x in
  if ex <> 0 then Num.mult_num (expand fl) (Num.power_num num_2 (Num.Int ex))
  else expand fl


(* Constante Num.num 0. *)
let num_0f = num_of_float 0.

(* ===== TERM ===== *)

(* Constante True *)
let term_true = Term.t_true

(* Constante False *)
let term_false = Term.t_false

(* Constante Term 0 *)
let term_0 = Term.make_int num_0

(* Constante Term 0. *)
let term_0f = Term.make_real num_0f

(* Constante Term 1 *)
let term_1 = Term.make_int num_1

(* Créer le terme Term d *)
let term_int d = Term.make_int (Num.Int d)

(* Créer le terme Term f *)
let term_real f = Term.make_real (num_of_float f)

(* Addition entre deux termes *)
let term_add t1 t2 = Term.make_arith Term.Plus t1 t2

let ( +@ ) = term_add

(* Soustraction entre deux termes *)
let term_sub t1 t2 = Term.make_arith Term.Minus t1 t2

let ( -@ ) = term_sub

(* Multiplication entre deux termes *)
let term_mul t1 t2 = Term.make_arith Term.Mult t1 t2

let ( *@ ) = term_mul

(* Division entre deux termes *)
let term_div t1 t2 = Term.make_arith Term.Div t1 t2

let ( /@ ) = term_div

(* Modulo entre deux termes *)
let term_mod t1 t2 = Term.make_arith Term.Modulo t1 t2

(* If-Then-Else entre une formule et deux termes *)
let term_ite f1 t2 t3 = Term.make_ite f1 t2 t3

(* Application f(x) *)
let term_app f x = Term.make_app f [ x ]

(* Application f() *)
let term_app_unit f = Term.make_app f []

(* ===== SYMBOLES ===== *)

(* Declare un symbole avec son num, son type d'entré et son type de retour *)
let declare_symbol name t_in t_out =
  let x = Hstring.make name in
  Symbol.declare x t_in t_out;
  x


(* Declare un symbole à partir d'une variable *)
let get_symbol_from_var ({ name; _ }, ty) =
  declare_symbol name [ type_int ] (asttype_to_smttype ty)


(* Declare un stmbole frais *)
let get_fresh_symbol =
 fun ty () ->
  let name = fresh_name ~name:"aux" () in
  (name, declare_symbol name [ type_int ] (asttype_to_smttype ty))


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


(* ===== SOLVER ===== *)

(* Notre solveur pour le cas de base *)
module BMC_solver = Smt.Make (struct end)

(* Notre solveur pour le cas inductif *)
module IND_solver = Smt.Make (struct end)
