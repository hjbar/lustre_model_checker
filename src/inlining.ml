(* Explication de l'in-lining :

  On récupère le noeud main du programme lustre.
  On veut in-liner à partir de ce noeud (car c'est celui-ci qu'on veut garder à la fin).
  Ainsi, on regarde dans chaque équation du noeud main si une définition fait appel à un autre noeud.
  Si c'est le cas, on veut remplacer l'appel au noeud par la définition de ce dernier.
  Pour ce faire, ce noeud ne doit pas faire appel à d'autre noeud.
  C'est pour cela que récursivement on in-line tous les appels également dans ce noeud.
  Pour grandement simplifier les choses, on in-line tous les tuples de ce noeud.
  À présent, on veut intégrer ce noeud dans notre noeud main: il ne doit comporter qu'une seule équation.
  Ainsi, on veut in-liner toutes les définitions des variables locales dans la définition des outputs.
  Et à présent, pour in-liner les outputs dans l'appelant, on combine toutes les équantions pour en former qu'une seule.
  Ainsi, on forme un tuple avec tous les outputs : (o1, o2, ..., on) = (e1, e2, ..., en).
  Ces outputs sont maintenant in-liné dans l'appelant: le job est fait.
*)

open Typed_ast
open Ident

(* Renvoie True si la liste possède au moins deux éléments, False sinon *)

let have_to_inline = function
  | [] | [ _ ] -> false
  | _ -> true


(* Renvoie une Hashtbl des noms vers leur noeud *)

let hashtbl_from_nodes nodes =
  let ht = Hashtbl.create 16 in
  List.iter (fun node -> Hashtbl.replace ht node.tn_name.name node) nodes;
  ht


(* Renvoie les équations-outputs d'un noeud *)

let get_outputs node =
  let output_ids = List.map fst node.tn_output in
  List.filter
    (fun equ -> List.mem (List.hd equ.teq_patt.tpatt_desc) output_ids)
    node.tn_equs


(* Récupère l'équation locale si elle existe
   Pré-condition: ne pas avoir de tuples dans les équations *)

let get_local_equ output_id id equs =
  List.find_opt
    begin
      fun eqn ->
        (* On sait qu'on a pas de tuples *)
        let current_id = List.hd eqn.teq_patt.tpatt_desc in
        current_id <> output_id && current_id = id
    end
    equs


(* Remplace l'ident par un autre dans toute l'expression *)

let rec replace_ident old_id new_id e =
  let texpr_desc =
    match e.texpr_desc with
    | TE_ident id -> if id = old_id then TE_ident new_id else TE_ident id
    | TE_const c -> TE_const c
    | TE_op (op, es) -> TE_op (op, List.map (replace_ident old_id new_id) es)
    | TE_app (f, args) -> TE_app (f, List.map (replace_ident old_id new_id) args)
    | TE_prim (id, es) -> TE_prim (id, List.map (replace_ident old_id new_id) es)
    | TE_arrow (e1, e2) ->
      TE_arrow (replace_ident old_id new_id e1, replace_ident old_id new_id e2)
    | TE_pre e -> TE_pre (replace_ident old_id new_id e)
    | TE_tuple es -> TE_tuple (List.map (replace_ident old_id new_id) es)
  in
  { e with texpr_desc }


(* Renvoie un noeud en inlinant tous les tuples
   Pré-condition : avoir in-liné tous les sous-noeuds *)

let inline_tuple node =
  let rec loop equs acc =
    match equs with
    | [] -> List.rev acc
    | equ :: equs -> begin
      match equ.teq_patt.tpatt_desc with
      | [] -> assert false
      | [ left_id ] -> loop equs (equ :: acc)
      | ids ->
        (* On a un tuple, on inline *)
        let types = equ.teq_patt.tpatt_type in
        let zip = List.combine ids types in

        let exprs =
          match equ.teq_expr.texpr_desc with
          | TE_tuple es -> es
          | _ -> assert false (* On a in-liné tous les sous-noeuds *)
        in

        let new_equs =
          List.map2
            begin
              fun (id, ty) e ->
                let tpatt_desc = [ id ] in
                let tpatt_type = [ ty ] in
                let tpatt_loc = equ.teq_patt.tpatt_loc in
                let teq_patt = { tpatt_desc; tpatt_type; tpatt_loc } in

                let teq_expr = e in

                { teq_patt; teq_expr }
            end
            zip exprs
        in

        loop equs (new_equs @ acc)
    end
  in

  let tn_equs = loop node.tn_equs [] in
  { node with tn_equs }


(* Renvoie les outputs en une seule équation grâce à un tuple
   Pré-condition: aucun tuple dans les équations du noeud *)

let combine_outputs_equs node output_equs =
  (* On récupère les idents des outputs *)
  let output_ids = List.map fst node.tn_output in

  (* On trie les équations définissant les outputs selon l'ordre de retour
     Pré-condition: aucun tuple dans les équantions *)
  let rec sort output_ids acc =
    match output_ids with
    | [] -> List.rev acc
    | output_id :: output_ids ->
      let equ =
        List.find
          (* On sait qu'on a aucun tuple *)
          (fun equ -> List.hd equ.teq_patt.tpatt_desc = output_id )
          output_equs
      in
      sort output_ids (equ :: acc)
  in

  (* Une loc par défaut pour re-créer les tuples *)
  let tpatt_loc = (List.hd output_equs).teq_patt.tpatt_loc in
  let texpr_loc = tpatt_loc in

  (* On re-créer les tuples pour renvoyer les outputs
     Pré-condition: aucun tuple dans les équantions *)
  let rec make_tuple output_equs ids tys es =
    match output_equs with
    | [] ->
      let tpatt_desc = List.rev ids in
      let tpatt_type = List.rev tys in
      let teq_patt = { tpatt_desc; tpatt_type; tpatt_loc } in

      let texpr_desc = TE_tuple (List.rev es) in
      let texpr_type = tpatt_type in
      let teq_expr = { texpr_desc; texpr_type; texpr_loc } in

      { teq_patt; teq_expr }
    | output_equ :: output_equs ->
      (* On sait qu'on a aucun tuple *)
      let id = output_equ.teq_patt.tpatt_desc |> List.hd in
      let ty = output_equ.teq_patt.tpatt_type |> List.hd in
      let e = output_equ.teq_expr in

      make_tuple output_equs (id :: ids) (ty :: tys) (e :: es)
  in

  (* Trie les équantions définssant les outputs et les renvoie sous la forme d'un tuple *)
  let output_equs = sort output_ids [] in
  make_tuple output_equs [] [] []


(* Inline une liste d'équations en une unique équation
   Pré-condition: aucun tuple dans les équations *)

let inline_in_node node =
  (* On récupère les équantions définssant les outputs *)
  let output_eqns = get_outputs node in

  (* In-line les équations-locales dans les équantions-output
     Pré-condition: aucun tuple dans les équantions-output *)
  let rec replace output_id e =
    let texpr_desc =
      match e.texpr_desc with
      | TE_ident id -> begin
        match get_local_equ output_id id node.tn_equs with
        | None -> TE_ident id
        | Some eqn -> (replace_ident id output_id eqn.teq_expr).texpr_desc
      end
      | TE_const c -> TE_const c
      | TE_op (op, es) -> TE_op (op, List.map (replace output_id) es)
      | TE_app (f, args) -> TE_app (f, List.map (replace output_id) args)
      | TE_prim (id, es) -> TE_prim (id, List.map (replace output_id) es)
      | TE_arrow (e1, e2) ->
        TE_arrow (replace output_id e1, replace output_id e2)
      | TE_pre e -> TE_pre (replace output_id e)
      | TE_tuple es -> TE_tuple (List.map (replace output_id) es)
    in
    { e with texpr_desc }
  in

  (* On in-line les équations-locales du noeud dans les équantions-outputs,
     puis on les renvoies sur la forme d'un tuple *)
  output_eqns
  |> List.map (fun eqn ->
       (* On sait qu'on n'a pas de tuple *)
       let teq_expr = replace (List.hd eqn.teq_patt.tpatt_desc) eqn.teq_expr in
       { eqn with teq_expr } )
  |> combine_outputs_equs node


(* Remplace les paramètres par les arguments *)

let rec replace_expr ht left_ids f args =
  (* On récupère le noeud, on l'in-line récursivement les sous-noeuds, on in-line les tuples *)
  let node = Hashtbl.find ht f.name |> inline_from_node ht |> inline_tuple in

  (* Pour remplacer efficacement les inputs par les arguments *)
  let mapping_input =
    let map = Hashtbl.create 16 in
    List.iter2
      (fun (input_id, _) arg -> Hashtbl.replace map input_id arg)
      node.tn_input args;
    map
  in

  (* Pour remplacer efficacement les outputs par les variables de l'appelant *)
  let mapping_output =
    let map = Hashtbl.create 16 in
    List.iter2
      (fun (output_id, _) left_id -> Hashtbl.replace map output_id left_id)
      node.tn_output left_ids;
    map
  in

  (* Remplace les inputs et les outputs
     Pré-condition: on a in-liné tous les sous-noeuds *)
  let rec replace e =
    let texpr_desc =
      match e.texpr_desc with
      | TE_ident id -> begin
        match Hashtbl.find_opt mapping_input id with
        | Some new_expr -> new_expr.texpr_desc
        | None -> begin
          match Hashtbl.find_opt mapping_output id with
          | Some new_id -> TE_ident new_id
          | None -> TE_ident id
        end
      end
      | TE_const c -> TE_const c
      | TE_op (op, es) -> TE_op (op, List.map replace es)
      | TE_prim (id, es) -> TE_prim (id, List.map replace es)
      | TE_arrow (e1, e2) -> TE_arrow (replace e1, replace e2)
      | TE_pre e -> TE_pre (replace e)
      | TE_tuple es -> TE_tuple (List.map replace es)
      | TE_app (f, args) -> assert false
    in
    { e with texpr_desc }
  in

  (* On in-line toutes les équantions internes du noeud pour en garder qu'une seule,
     puis on remplace les inputs et outputs *)
  let eqn = inline_in_node node in
  (replace eqn.teq_expr).texpr_desc


(* Renvoie l'expression d'entrée avec chaque appel inliné *)

and inline_from_expr ht left_ids e =
  let texpr_desc =
    match e.texpr_desc with
    | TE_app (f, args) -> replace_expr ht left_ids f args
    | TE_const c -> TE_const c
    | TE_ident id -> TE_ident id
    | TE_op (op, es) -> TE_op (op, inline_from_expr_list ht left_ids es)
    | TE_prim (id, es) -> TE_prim (id, inline_from_expr_list ht left_ids es)
    | TE_arrow (e1, e2) ->
      TE_arrow (inline_from_expr ht left_ids e1, inline_from_expr ht left_ids e2)
    | TE_pre e -> TE_pre (inline_from_expr ht left_ids e)
    | TE_tuple es ->
      (* Cas particulier: on doit remplacer avec seulement les idents correspondant *)
      let rec loop es left_ids acc =
        match (es, left_ids) with
        | [], [] -> List.rev acc
        | e :: es, left_id :: left_ids ->
          let new_e = inline_from_expr ht [ left_id ] e in
          loop es left_ids (new_e :: acc)
        | _ -> assert false
      in
      TE_tuple (loop es left_ids [])
  in
  { e with texpr_desc }


and inline_from_expr_list ht left_ids es =
  List.map (inline_from_expr ht left_ids) es


(* Renvoie l'équation d'entrée avec chaque appel inliné *)

and inline_from_eqn ht eqn =
  let teq_expr = inline_from_expr ht eqn.teq_patt.tpatt_desc eqn.teq_expr in
  { eqn with teq_expr }


(* Renvoie le noeud d'entrée avec chaque sous-noeuds inlinés *)

and inline_from_node ht node =
  let tn_equs = List.map (inline_from_eqn ht) node.tn_equs in
  { node with tn_equs }


(* In-line les sous-noeuds dans le noeud principal *)

let inline nodes main =
  match have_to_inline nodes with
  | false -> List.hd nodes
  | true ->
    let ht = hashtbl_from_nodes nodes in
    let main_node = Hashtbl.find ht main in
    inline_from_node ht main_node
