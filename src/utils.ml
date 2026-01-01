open Typed_ast

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


(* Renvoie les éléments d'un tuple *)
let assume_tuple expr =
  match expr.texpr_desc with
  | TE_tuple es -> es
  | _ -> assert false
