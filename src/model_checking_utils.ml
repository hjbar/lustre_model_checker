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


(* Renvoie les types associés aux variables d'un noeud *)
let get_types_from_node { tn_input; tn_output; tn_local; _ } =
  let types = Hashtbl.create 16 in
  let get_type (id, ty) =
    Hashtbl.replace types id.name (asttype_to_smttype ty)
  in

  List.iter get_type tn_input;
  List.iter get_type tn_output;
  List.iter get_type tn_local;

  types


(* Renvoie le type d'un terme *)
let get_type t = Expr.ty t

(* Check la compatibilité des types *)
let check_type t1 t2 =
  let ty1 = get_type t1 in
  if ty1 <> get_type t2 then failwith "Incompatible types";
  ty1


(* ===== TERM ===== *)

(* Négation logique d'une terme *)
let term_not t = Expr.raw_unop type_bool Ty.Unop.Not t

(* Égalité entre deux termes *)
let term_eq t1 t2 = Expr.raw_relop type_bool Ty.Relop.Eq t1 t2

let ( =@ ) = term_eq

(* Non-égalité entre deux termes *)
let term_neq t1 t2 = Expr.raw_relop type_bool Ty.Relop.Ne t1 t2

let ( <>@ ) = term_neq

(* Inférieur ou égal pour deux termes *)
let term_le t1 t2 =
  let ty = check_type t1 t2 in
  Expr.raw_relop ty Ty.Relop.Le t1 t2


let ( <=@ ) = term_le

(* Strictement inférieur pour deux termes *)
let term_lt t1 t2 =
  let ty = check_type t1 t2 in
  Expr.raw_relop ty Ty.Relop.Lt t1 t2


let ( <@ ) = term_lt

(* Strictement supérieur pour deux termes *)
let term_gt t1 t2 =
  let ty = check_type t1 t2 in
  Expr.raw_relop ty Ty.Relop.Gt t1 t2


let ( >@ ) = term_gt

(* Supérieur ou égal pour deux termes *)
let term_ge t1 t2 =
  let ty = check_type t1 t2 in
  Expr.raw_relop ty Ty.Relop.Ge t1 t2


let ( >=@ ) = term_ge

(* Conjonction entre termes *)
let term_and t1 t2 = Expr.raw_binop type_bool Ty.Binop.And t1 t2

let ( &&@ ) = term_and

let rec term_ands = function
  | [] -> assert false
  | [ t ] -> t
  | [ t1; t2 ] -> t1 &&@ t2
  | t :: ts -> t &&@ term_ands ts


(* Disjonction entre deux termes *)
let term_or t1 t2 = Expr.raw_binop type_bool Ty.Binop.Or t1 t2

let ( ||@ ) = term_or

(* Implication entre deux termes *)
let term_imp t1 t2 = Expr.raw_binop type_bool Ty.Binop.Implies t1 t2

(* Constante True *)
let term_true = Expr.value Value.True

(* Constante False *)
let term_false = Expr.value Value.False

(* Constant Term 0 *)
let term_0 = Expr.value (Value.Int 0)

(* Constant Term 0. *)
let term_0f = Expr.value (Value.Real 0.)

(* Constant Term 1 *)
let term_1 = Expr.value (Value.Int 1)

(* Créer le terme Term d *)
let term_int d = Expr.value (Value.Int d)

(* Créer le terme Term r *)
let term_real r = Expr.value (Value.Real r)

(* Ré-interprète un reel en un entier *)
let term_as_int t =
  t
  |> Expr.raw_unop type_real Ty.Unop.Floor
  |> Expr.raw_cvtop type_real Ty.Cvtop.Reinterpret_int


(* Ré-interprète un entier en un reel *)
let term_as_real t = Expr.raw_cvtop type_int Ty.Cvtop.Reinterpret_float t

(* Variable v *)
let term_var v = Expr.symbol v

(* Addition entre deux termes *)
let term_add_int t1 t2 = Expr.raw_binop type_int Ty.Binop.Add t1 t2

let ( +@ ) = term_add_int

let term_add_real t1 t2 = Expr.raw_binop type_real Ty.Binop.Add t1 t2

let ( +.@ ) = term_add_real

(* Négation d'un terme *)
let term_neg_int t = Expr.raw_unop type_int Ty.Unop.Neg t

let term_neg_real t = Expr.raw_unop type_real Ty.Unop.Neg t

(* Soustraction entre deux termes *)
let term_sub_int t1 t2 = Expr.raw_binop type_int Ty.Binop.Sub t1 t2

let ( -@ ) = term_sub_int

let term_sub_real t1 t2 = Expr.raw_binop type_real Ty.Binop.Sub t1 t2

let ( -.@ ) = term_sub_real

(* Multiplication entre deux termes *)
let term_mul_int t1 t2 = Expr.raw_binop type_int Ty.Binop.Mul t1 t2

let ( *@ ) = term_mul_int

let term_mul_real t1 t2 = Expr.raw_binop type_real Ty.Binop.Mul t1 t2

let ( *.@ ) = term_mul_real

(* Division entre deux termes *)
let term_div_int t1 t2 = Expr.raw_binop type_int Ty.Binop.Div t1 t2

let ( /@ ) = term_div_int

let term_div_real t1 t2 = Expr.raw_binop type_real Ty.Binop.Div t1 t2

let ( /.@ ) = term_div_real

(* Modulo entre deux termes *)
let term_mod t1 t2 =
  match (Expr.ty t1, Expr.ty t2) with
  | Ty.Ty_int, Ty.Ty_int -> Expr.raw_binop type_int Ty.Binop.Rem t1 t2
  | Ty.Ty_int, Ty.Ty_real | Ty.Ty_real, Ty.Ty_int | Ty.Ty_real, Ty.Ty_real ->
    Expr.raw_binop type_real Ty.Binop.Rem t1 t2
  | _ -> assert false


(* If-Then-Else avoir trois termes *)
let term_ite t1 t2 t3 = Expr.triop type_bool Ty.Triop.Ite t1 t2 t3

(* Affiche une terme donné *)
let term_print t = t |> Expr.to_string |> Format.printf "%s%!"

(* ===== SYMBOLES ===== *)

(* Type pour l'unicité des symboles représentant n + d
   Pour exprimer que n + 2 == n + 3 - 1 par exemple
*)
type symbol_diff = Expr.t * int

(* Init un symbol_diff *)
let diff_init n d = (n, d)

(* Applique -1 à un symbol_diff *)
let diff_decr (n, d) = (n, d - 1)

(* Extrait la valeur SMT correspondant au symbol_diff(n, d), i.e. n + d *)
let diff_extract (n, d) = n +@ term_int d

(* Declare un symbole avec son nom et son type *)
let declare_symbol name ty =
  let name = fresh_name ~name () in
  Symbol.make ty name


(* Declare un symbole à partir d'un nom, d'un type et d'un symbol_diff donné *)
let get_symbol =
  let symbols = Hashtbl.create 16 in
  fun (name : string) (ty : Ty.t) (n : symbol_diff) ->
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
