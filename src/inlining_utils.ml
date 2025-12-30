open Typed_ast

(* Renvoie True si la liste possède au moins deux éléments, False sinon *)
let have_to_inline = function
  | [] | [ _ ] -> false
  | _ -> true


(* Renvoie une Hashtbl des noms vers leur noeud *)
let hashtbl_from_program nodes =
  let ht = Hashtbl.create 16 in
  List.iter (fun node -> Hashtbl.replace ht node.tn_name.name node) nodes;
  ht
