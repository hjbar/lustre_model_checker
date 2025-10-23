open Typed_ast
open Ident

(* Renvoie True si la liste possède au moins deux éléments, False sinon *)

let have_to_inline = function
  | [] | [ _ ] -> false
  | _ -> true


(* Renvoie une Hashtbl des idents vers leur noeud *)

let hashtbl_from_nodes nodes =
  let ht = Hashtbl.create 16 in
  List.iter (fun node -> Hashtbl.replace ht node.tn_name.name node) nodes;
  ht


(* Renvoie les outputs d'un noeud en inlinant les tuples *)

let get_outputs node =
  let output_ids = List.map fst node.tn_output in

  let rec loop equs acc =
    match equs with
    | [] -> List.rev acc
    | equ :: equs -> begin
      match equ.teq_patt.tpatt_desc with
      | [] -> assert false
      | [ left_id ] ->
        if List.mem left_id output_ids then loop equs (equ :: acc)
        else loop equs acc
      | ids ->
        let types = equ.teq_patt.tpatt_type in
        let zip = List.combine ids types in

        let exprs =
          match equ.teq_expr.texpr_desc with
          | TE_tuple es -> es
          | _ -> assert false
        in

        let new_equs =
          List.map2
            (fun (id, ty) e ->
              let teq_patt =
                {
                  tpatt_desc = [ id ];
                  tpatt_type = [ ty ];
                  tpatt_loc = equ.teq_patt.tpatt_loc;
                }
              in
              let teq_expr = e in
              { teq_patt; teq_expr } )
            zip exprs
        in

        loop equs (new_equs @ acc)
    end
  in
  loop node.tn_equs []


(* Renvoie les outputs en une seule équation avec un tuple
   Pré-condition: aucun tuple dans les équations du noeud *)

let combine_outputs_equs node output_equs =
  let output_ids = List.map fst node.tn_output in

  let rec sort output_ids acc =
    match output_ids with
    | [] -> List.rev acc
    | output_id :: output_ids ->
      let equ =
        List.find
          (fun equ -> List.hd equ.teq_patt.tpatt_desc = output_id)
          output_equs
      in
      sort output_ids (equ :: acc)
  in

  let loc = (List.hd output_equs).teq_patt.tpatt_loc in

  let rec make_tuple output_equs ids tys es =
    match output_equs with
    | [] ->
      let ids = List.rev ids in
      let tys = List.rev tys in
      let es = List.rev es in

      let teq_patt = { tpatt_desc = ids; tpatt_type = tys; tpatt_loc = loc } in

      let teq_expr =
        { texpr_desc = TE_tuple es; texpr_type = tys; texpr_loc = loc }
      in

      { teq_patt; teq_expr }
    | output_equ :: output_equs ->
      let id = output_equ.teq_patt.tpatt_desc |> List.hd in
      let ty = output_equ.teq_patt.tpatt_type |> List.hd in
      let e = output_equ.teq_expr in

      make_tuple output_equs (id :: ids) (ty :: tys) (e :: es)
  in

  let output_equs = sort output_ids [] in
  make_tuple output_equs [] [] []


(* Inline une liste d'équations en une unique équation *)

let inline_in_node ht node =
  let output_eqns = get_outputs node in

  let rec replace left_id e =
    let desc =
      match e.texpr_desc with
      | TE_const c -> TE_const c
      | TE_ident id -> begin
        match
          List.find_opt
            (fun eqn ->
              let current_id = List.hd eqn.teq_patt.tpatt_desc in
              current_id <> left_id && current_id = id )
            node.tn_equs
        with
        | None -> TE_ident id
        | Some eqn -> eqn.teq_expr.texpr_desc
      end
      | TE_op (op, es) -> TE_op (op, List.map (replace left_id) es)
      | TE_app (f, args) -> TE_app (f, List.map (replace left_id) args)
      | TE_prim (id, es) -> TE_prim (id, List.map (replace left_id) es)
      | TE_arrow (e1, e2) -> TE_arrow (replace left_id e1, replace left_id e2)
      | TE_pre e -> TE_pre (replace left_id e)
      | TE_tuple es -> TE_tuple (List.map (replace left_id) es)
    in
    { e with texpr_desc = desc }
  in

  output_eqns
  |> List.map (fun eqn ->
       {
         eqn with
         teq_expr = replace (List.hd eqn.teq_patt.tpatt_desc) eqn.teq_expr;
       } )
  |> combine_outputs_equs node


(* Remplace les paramètres par les arguments *)

let rec replace_expr ht left_ids f args =
  let node = Hashtbl.find ht f.name in
  let node = inline_from_node ht node in

  let mapping_input =
    let map = Hashtbl.create 16 in
    List.iter2
      (fun (input_id, _) arg -> Hashtbl.replace map input_id arg)
      node.tn_input args;
    map
  in

  let mapping_output =
    let map = Hashtbl.create 16 in
    List.iter2
      (fun (output_id, _) left_id -> Hashtbl.replace map output_id left_id)
      node.tn_output left_ids;
    map
  in

  let rec replace e =
    let desc =
      match e.texpr_desc with
      | TE_const c -> TE_const c
      | TE_ident id -> begin
        match Hashtbl.find_opt mapping_input id with
        | None -> begin
          match Hashtbl.find_opt mapping_output id with
          | None -> TE_ident id
          | Some new_id -> TE_ident new_id
        end
        | Some new_expr -> new_expr.texpr_desc
      end
      | TE_op (op, es) -> TE_op (op, List.map replace es)
      | TE_app (f, args) -> replace_expr ht left_ids f args
      | TE_prim (id, es) -> TE_prim (id, List.map replace es)
      | TE_arrow (e1, e2) -> TE_arrow (replace e1, replace e2)
      | TE_pre e -> TE_pre (replace e)
      | TE_tuple es -> TE_tuple (List.map replace es)
    in
    { e with texpr_desc = desc }
  in

  let eqn = inline_in_node ht node in
  (replace eqn.teq_expr).texpr_desc


(* Renvoie l'expression d'entrée avec chaque appel inliné *)

and inline_from_expr ht left_ids e =
  let desc =
    match e.texpr_desc with
    | TE_const c -> TE_const c
    | TE_ident id -> TE_ident id
    | TE_op (op, es) -> TE_op (op, inline_from_expr_list ht left_ids es)
    | TE_app (f, args) -> replace_expr ht left_ids f args
    | TE_prim (id, es) -> TE_prim (id, inline_from_expr_list ht left_ids es)
    | TE_arrow (e1, e2) ->
      TE_arrow (inline_from_expr ht left_ids e1, inline_from_expr ht left_ids e2)
    | TE_pre e -> TE_pre (inline_from_expr ht left_ids e)
    | TE_tuple es ->
      let rec loop es idx acc =
        match es with
        | [] -> List.rev acc
        | e :: es ->
          let left_id = List.nth left_ids idx in
          let new_e = inline_from_expr ht [ left_id ] e in
          loop es (idx + 1) (new_e :: acc)
      in
      TE_tuple (loop es 0 [])
  in
  { e with texpr_desc = desc }


and inline_from_expr_list ht left_ids es =
  List.map (inline_from_expr ht left_ids) es


(* Renvoie l'équation d'entrée avec chaque appel inliné *)

and inline_from_eqn ht eqn =
  {
    eqn with
    teq_expr = inline_from_expr ht eqn.teq_patt.tpatt_desc eqn.teq_expr;
  }


(* Renvoie le noeud d'entrée avec chaque sous-noeuds inlinés *)

and inline_from_node ht node =
  { node with tn_equs = List.map (inline_from_eqn ht) node.tn_equs }


(* In-line les sous-noeuds dans le noeud principal *)

let inline nodes main =
  match have_to_inline nodes with
  | false -> List.hd nodes
  | true ->
    let ht = hashtbl_from_nodes nodes in
    let main_node = Hashtbl.find ht main in
    inline_from_node ht main_node
