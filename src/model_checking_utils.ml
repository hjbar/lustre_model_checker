open Utils
open Smtml
open Typed_ast
open Ident

(* ===== TYPES ===== *)

(* Type bool du SMT *)
let type_bool = Ty.Ty_bool

(* Type int du SMT *)
let type_int = Ty.Ty_int

(* Type real du SMT *)
let type_real = Ty.Ty_real

(* Conversion d'un type Lustre en un type Alt-Ergo *)
let asttype_to_smttype = function
  | Asttypes.Tbool -> type_bool
  | Asttypes.Tint -> type_int
  | Asttypes.Treal -> type_real


(* Renvoie les types associés aux variables *)
let get_types_from_node { tn_input; tn_output; tn_local; _ } =
  let types = Hashtbl.create 16 in
  let get_type (id, ty) =
    Hashtbl.replace types id.name (asttype_to_smttype ty)
  in

  List.iter get_type tn_input;
  List.iter get_type tn_output;
  List.iter get_type tn_local;

  types


(* ===== FORMULA ===== *)

(* Négation d'une formule *)
let term_not f = Expr.unop type_bool Ty.Unop.Not f

(* Égalité entre deux termes *)
let term_eq t1 t2 = Expr.relop type_bool Ty.Relop.Eq t1 t2

let ( =@ ) = term_eq

(* Non-égalité entre deux termes *)
let term_neq t1 t2 = Expr.relop type_bool Ty.Relop.Ne t1 t2

let ( <>@ ) = term_neq

(* Inférieur ou égal pour deux termes *)
let term_le t1 t2 = Expr.relop type_int Ty.Relop.Le t1 t2

let ( <=@ ) = term_le

(* Strictement inférieur pour deux termes *)
let term_lt t1 t2 = Expr.relop type_int Ty.Relop.Lt t1 t2

let ( <@ ) = term_lt

(* Strictement supérieur pour deux termes *)
let term_gt t1 t2 = Expr.relop type_int Ty.Relop.Gt t1 t2

let ( >@ ) = term_gt

(* Supérieur ou égal pour deux termes *)
let term_ge t1 t2 = Expr.relop type_int Ty.Relop.Ge t1 t2

let ( >=@ ) = term_ge

(* Conjonction entre deux formules *)
let term_and f1 f2 = Expr.binop type_bool Ty.Binop.And f1 f2

let ( &&@ ) = term_and

let rec term_ands = function
  | [] -> assert false
  | [ t ] -> t
  | [ t1; t2 ] -> t1 &&@ t2
  | t :: ts -> t &&@ term_ands ts


(* Disjonction entre deux formules *)
let term_or f1 f2 = Expr.binop type_bool Ty.Binop.Or f1 f2

let ( ||@ ) = term_or

(* Implication entre deux formules *)
let term_imp f1 f2 = Expr.binop type_bool Ty.Binop.Implies f1 f2

(* Affiche une formule donnée *)
let term_print f = f |> Expr.to_string |> Format.printf "%s%!"

(* ===== TERM ===== *)

(* Constante True *)
let term_true = Expr.value Value.True

(* Constante False *)
let term_false = Expr.value Value.False

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

(* Addition entre deux termes *)
let term_add_int t1 t2 = Expr.binop type_int Ty.Binop.Add t1 t2

let ( +@ ) = term_add_int

let term_add_real t1 t2 = Expr.binop type_real Ty.Binop.Add t1 t2

let ( +.@ ) = term_add_real

(* Négation d'un terme *)
let term_neg_int t = Expr.unop type_int Ty.Unop.Neg t

let term_neg_real t = Expr.unop type_real Ty.Unop.Neg t

(* Soustraction entre deux termes *)
let term_sub_int t1 t2 = Expr.binop type_int Ty.Binop.Sub t1 t2

let ( -@ ) = term_sub_int

let term_sub_real t1 t2 = Expr.binop type_real Ty.Binop.Sub t1 t2

let ( -.@ ) = term_sub_real

(* Multiplication entre deux termes *)
let term_mul_int t1 t2 = Expr.binop type_int Ty.Binop.Mul t1 t2

let ( *@ ) = term_add_int

let term_mul_real t1 t2 = Expr.binop type_real Ty.Binop.Mul t1 t2

let ( *.@ ) = term_add_real

(* Division entre deux termes *)
let term_div_int t1 t2 = Expr.binop type_int Ty.Binop.Div t1 t2

let ( /@ ) = term_add_int

let term_div_real t1 t2 = Expr.binop type_real Ty.Binop.Div t1 t2

let ( /.@ ) = term_add_real

(* Modulo entre deux termes *)
let term_mod t1 t2 =
  match (Expr.ty t1, Expr.ty t2) with
  | Ty.Ty_int, Ty.Ty_int -> Expr.binop type_int Ty.Binop.Rem t1 t2
  | Ty.Ty_int, Ty.Ty_real | Ty.Ty_real, Ty.Ty_int | Ty.Ty_real, Ty.Ty_real ->
    Expr.binop type_real Ty.Binop.Rem t1 t2
  | _ -> assert false


(* If-Then-Else entre une formule et deux termes *)
let term_ite t1 t2 t3 = Expr.triop type_bool Ty.Triop.Ite t1 t2 t3

(* Variable v *)
let term_var v = Expr.symbol v

(* ===== SYMBOLES ===== *)

(* Type pour l'unicité des n + d
   Pour exprimer que n + 2 == n + 3 - 1 par exemple
*)
type symbol_diff = Expr.t * int

(* Init un symbol_diff *)
let diff_init n d = (n, d)

(* Applique -1 à un symbol_diff *)
let diff_decr (n, d) = (n, d - 1)

(* Extrait la valeur SMT correspondant au symbol_diff(n, d), i.e. n + d *)
let diff_extract (n, d) = n +@ term_int d

(* Declare un symbole avec son num, son type d'entré et son type de retour *)
let declare_symbol name ty =
  let name = fresh_name ~name () in
  Symbol.make ty name


(* Declare un symbole à partir d'une variable et d'un n donné *)
let get_symbol =
  let symbols = Hashtbl.create 16 in
  fun (name : string) ty (n : symbol_diff) ->
    match Hashtbl.find_opt symbols (name, ty, n) with
    | Some symbol_cached -> symbol_cached
    | None ->
      let symbol_cached = declare_symbol name ty in
      Hashtbl.replace symbols (name, ty, n) symbol_cached;
      symbol_cached


(* ===== SOLVER ===== *)

(* Notre solveur pour le cas de base *)
module BMC_solver = Solver.Batch (Z3_mappings)

(* Notre solveur pour le cas inductif *)
module IND_solver = Solver.Batch (Z3_mappings)
