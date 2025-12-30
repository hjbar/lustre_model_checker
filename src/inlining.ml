(*

  Explication de l'inlining :


  Si le programme est composé d'un unique noeud,
  alors on inline juste les tuples et on renvoie le noeud.

  Sinon, on récupère le noeud main du programme Lustre.
  Puis, on renomme ce noeud, c'est-à-dire qu'on renomme toutes les variables avec des noms uniques.
  On peut à présent inliner les appels à d'autres noeuds qui se trouve dans le noeud main.
  Pour ce faire, on itère sur toutes les équations du noeud à la recherche d'un appel.
  Lorsque que l'on rencontre un appel, on inline d'abord les appels présent dans les arguments.
  Ensuite, on récupère le noeud concerné par l'appel.
  On commence par inliner les appels de ce dernier, puis on renomme le noeud (pour éviter les conflits
  dûs aux noms des variables), enfin on remplace les inputs par les paramètres de l'appelant.
  Ainsi, on stocke sur le côté les variables locales et les outputs du noeud qu'on traitait à l'origine
  (appelons les extra_locals) ainsi que les équations de ce même noeud (appelons les extra_equs).
  Maintenant, on remplace dans l'expression l'appel au noeud par la variable output du noeud qu'on appelait
  (si il y a plusieurs outputs alors on remplace par un tuple des outputs).
  Une fois ceci fait, on n'a plus d'appel à d'autres noms dans le noeud main.
  On en profite alors on inliner les tuples du noeud main.
  Cela est facile puisque l'on n'a pas d'appel, on a alors toujours des équations de la forme
  v = e ou alors v1, ..., vn = e1, ..., en. On remplace alors cette dernière d'équation par
  n nouvelles équations : v1 = e1 et ... et vn = en.

*)

open Utils
open Inlining_utils
open Typed_ast
open Ident

let debug = false

(* ===== RENAMING ===== *)

(* Renvoie un ident frais à partir d'un ident donné
   Si une ident frais a déjà été créer à partir d'un
   ident donnée alors on renvoie cet ident frais
   Warning: appeler reset_rename_ident avant de renommer un noeud
*)
let rename_ident, reset_rename_ident =
  let fresh_idents = Hashtbl.create 16 in

  let rename_ident ident =
    if ident.name = "OK" then ident
    else
      match Hashtbl.find_opt fresh_idents ident with
      | Some fresh_ident -> fresh_ident
      | None ->
        let fresh_name = fresh_name ~name:("id_" ^ ident.name) () in
        let fresh_ident = Ident.make fresh_name ident.kind in
        Hashtbl.replace fresh_idents ident fresh_ident;
        fresh_ident
  in

  let reset_rename_ident () = Hashtbl.reset fresh_idents in

  (rename_ident, reset_rename_ident)


(* Renvoie une variable fraîche à partir d'une variable donnée
   Si une variable fraîche a déjà été créer à partir d'une variable
   donnée alors on renvoie cette variable fraîche
*)
let rename_var (ident, ty) = (rename_ident ident, ty)

(* Renomme toutes les variables de cette expression
   pour éviter les conflits avec des variables ayant le même nom
*)
let rec rename_expr ({ texpr_desc; _ } as expr) =
  let texpr_desc =
    match texpr_desc with
    | TE_const _ -> texpr_desc
    | TE_ident ident -> TE_ident (rename_ident ident)
    | TE_op (op, es) -> TE_op (op, List.map rename_expr es)
    | TE_app (f, es) -> TE_app (f, List.map rename_expr es)
    | TE_prim (f, es) -> TE_prim (f, List.map rename_expr es)
    | TE_arrow (e1, e2) -> TE_arrow (rename_expr e1, rename_expr e2)
    | TE_pre e -> TE_pre (rename_expr e)
    | TE_tuple es -> TE_tuple (List.map rename_expr es)
  in
  { expr with texpr_desc }


(* Renomme toutes les variables de cette équation
   pour éviter les conflits avec des variables ayant le même nom
*)
let rename_equ { teq_patt; teq_expr } =
  let tpatt_desc = List.map rename_ident teq_patt.tpatt_desc in
  let teq_patt = { teq_patt with tpatt_desc } in

  let teq_expr = rename_expr teq_expr in

  { teq_patt; teq_expr }


(* Renomme toutes les variables de ce noeud
   pour éviter les conflits avec des variables ayant le même nom
*)
let rename_node ({ tn_input; tn_output; tn_local; tn_equs; _ } as node) =
  reset_rename_ident ();

  let tn_input = List.map rename_var tn_input in
  let tn_output = List.map rename_var tn_output in
  let tn_local = List.map rename_var tn_local in
  let tn_equs = List.map rename_equ tn_equs in

  { node with tn_input; tn_output; tn_local; tn_equs }


(* Renomme toutes les variables du programme
   pour éviter les conflits avec des variables ayant le même nom
*)
let rename_program nodes = List.map rename_node nodes

(* ===== CALLS INLINING ===== *)

(* Substitue cet input par cette expression dans cette expression donnée *)
let rec subst_expr ((var, _) as input) expr ({ texpr_desc; _ } as expr_src) =
  let texpr_desc =
    match texpr_desc with
    | TE_const _ -> texpr_desc
    | TE_ident ident ->
      if ident.name = var.name then expr.texpr_desc else texpr_desc
    | TE_op (op, es) -> TE_op (op, List.map (subst_expr input expr) es)
    | TE_app (f, es) -> TE_app (f, List.map (subst_expr input expr) es)
    | TE_prim (f, es) -> TE_prim (f, List.map (subst_expr input expr) es)
    | TE_arrow (e1, e2) ->
      TE_arrow (subst_expr input expr e1, subst_expr input expr e2)
    | TE_pre e -> TE_pre (subst_expr input expr e)
    | TE_tuple es -> TE_tuple (List.map (subst_expr input expr) es)
  in
  { expr_src with texpr_desc }


(* Substitue cet input par cette epression dans cette équation *)
let subst_equ input expr ({ teq_expr; _ } as equ) =
  let teq_expr = subst_expr input expr teq_expr in
  { equ with teq_expr }


(* Substitue cet input par cette expression dans les équations de ce noeud *)
let subst_node input expr ({ tn_equs; _ } as node) =
  let tn_equs = List.map (subst_equ input expr) tn_equs in
  { node with tn_equs }


(* Substitue tous les inputs par ces expressions données *)
let replace_inputs es node =
  List.fold_left2
    (fun node input expr -> subst_node input expr node)
    node node.tn_input es


(* Inline tous les appels de cette expression *)
let rec inline_calls_expr
  nodes extra_locals extra_equs ({ texpr_desc; _ } as expr) =
  let texpr_desc =
    match texpr_desc with
    | TE_const _ -> texpr_desc
    | TE_ident _ -> texpr_desc
    | TE_op (op, es) ->
      TE_op (op, List.map (inline_calls_expr nodes extra_locals extra_equs) es)
    | TE_app (f, es) -> begin
      let es = List.map (inline_calls_expr nodes extra_locals extra_equs) es in

      let f_node =
        f.name
        |> Hashtbl.find nodes
        |> inline_calls_node nodes
        |> rename_node
        |> replace_inputs es
      in

      extra_locals := f_node.tn_output @ !extra_locals;
      extra_locals := f_node.tn_local @ !extra_locals;

      extra_equs := f_node.tn_equs @ !extra_equs;

      match f_node.tn_output with
      | [ (ident, _) ] -> TE_ident ident
      | vars ->
        let es =
          List.map
            begin fun (ident, ty) ->
              let texpr_desc = TE_ident ident in
              let texpr_type = [ ty ] in
              let texpr_loc = (Lexing.dummy_pos, Lexing.dummy_pos) in
              { texpr_desc; texpr_type; texpr_loc }
            end
            vars
        in
        TE_tuple es
    end
    | TE_prim (f, es) ->
      TE_prim (f, List.map (inline_calls_expr nodes extra_locals extra_equs) es)
    | TE_arrow (e1, e2) ->
      let e1 = inline_calls_expr nodes extra_locals extra_equs e1 in
      let e2 = inline_calls_expr nodes extra_locals extra_equs e2 in
      TE_arrow (e1, e2)
    | TE_pre e -> TE_pre (inline_calls_expr nodes extra_locals extra_equs e)
    | TE_tuple es ->
      TE_tuple (List.map (inline_calls_expr nodes extra_locals extra_equs) es)
  in
  { expr with texpr_desc }


(* Inline tous les appels de cette équations *)
and inline_calls_equs nodes extra_locals extra_equs ({ teq_expr; _ } as equ) =
  let teq_expr = inline_calls_expr nodes extra_locals extra_equs teq_expr in
  { equ with teq_expr }


(* Inline tous les appels de ce noeud *)
and inline_calls_node =
  let inlined_nodes = Hashtbl.create 16 in
  fun nodes ({ tn_name; tn_local; tn_equs; _ } as node) ->
    match Hashtbl.find_opt inlined_nodes tn_name with
    | Some inlined_node -> inlined_node
    | None ->
      let extra_locals = ref [] in
      let extra_equs = ref [] in

      let tn_equs =
        List.map (inline_calls_equs nodes extra_locals extra_equs) tn_equs
      in

      let tn_local = !extra_locals @ tn_local in
      let tn_equs = !extra_equs @ tn_equs in

      let inlined_node = { node with tn_local; tn_equs } in
      Hashtbl.replace inlined_nodes tn_name inlined_node;
      inlined_node


(* ===== TUPLES INLINING ===== *)

(* Inline les tuples d'une équation
   Pré-condition: ne pas avoir d'appel à un autre noeud
*)
let inline_tuples_equ ({ teq_patt; teq_expr } as equ) =
  match (teq_patt.tpatt_desc, teq_patt.tpatt_type) with
  | [], _ -> assert false
  | [ _ ], _ -> [ equ ]
  | ids, tys ->
    let es = assume_tuple teq_expr in
    List.map2
      begin fun (id, ty) teq_expr ->
        let tpatt_desc = [ id ] in
        let tpatt_type = [ ty ] in
        let tpatt_loc = (Lexing.dummy_pos, Lexing.dummy_pos) in
        let teq_patt = { tpatt_desc; tpatt_type; tpatt_loc } in

        { teq_patt; teq_expr }
      end
      (List.combine ids tys) es


(* Inline les tuples d'un noeud
   Pré-condition: ne pas avoir d'appel à un autre noeud
*)
let inline_tuples_node ({ tn_equs; _ } as node) =
  let tn_equs = tn_equs |> List.map inline_tuples_equ |> List.flatten in
  { node with tn_equs }


(* ===== Pre NORMALIZATION ===== *)

(* Renvoie un nom frais pour la normalisation *)
let pre_norm_fresh_ident () =
  let fresh_name = fresh_name ~name:"pre_norm_id" () in
  Ident.make fresh_name Ident.Stream


(* Renvoie une expression normalisée à partir d'une expression donnée
   On considère qu'un programme est normalisé lorsque tous les pre sont appliqués à des identifiants
   Pré-condition: ne pas avoir de tuples dans l'expression
*)
let rec normalize_pre_expr extra_vars extra_equs ({ texpr_desc; _ } as expr) =
  let texpr_desc =
    match texpr_desc with
    | TE_const _ -> texpr_desc
    | TE_ident _ -> texpr_desc
    | TE_op (op, es) ->
      TE_op (op, List.map (normalize_pre_expr extra_vars extra_equs) es)
    | TE_app (f, es) ->
      TE_app (f, List.map (normalize_pre_expr extra_vars extra_equs) es)
    | TE_prim (f, es) ->
      TE_prim (f, List.map (normalize_pre_expr extra_vars extra_equs) es)
    | TE_arrow (e1, e2) ->
      let e1 = normalize_pre_expr extra_vars extra_equs e1 in
      let e2 = normalize_pre_expr extra_vars extra_equs e2 in
      TE_arrow (e1, e2)
    | TE_pre teq_expr -> begin
      let teq_expr = normalize_pre_expr extra_vars extra_equs teq_expr in

      match teq_expr.texpr_desc with
      | TE_ident _ -> TE_pre teq_expr
      | _ ->
        let fresh_ident = pre_norm_fresh_ident () in
        let fresh_var = (fresh_ident, assume_1 teq_expr.texpr_type) in
        extra_vars := fresh_var :: !extra_vars;

        let tpatt_desc = [ fresh_ident ] in
        let tpatt_type = teq_expr.texpr_type in
        let tpatt_loc = (Lexing.dummy_pos, Lexing.dummy_pos) in
        let teq_patt = { tpatt_desc; tpatt_type; tpatt_loc } in
        let equ = { teq_patt; teq_expr } in
        extra_equs := equ :: !extra_equs;

        let texpr_desc = TE_ident fresh_ident in
        TE_pre { teq_expr with texpr_desc }
    end
    | TE_tuple _ -> assert false
  in
  { expr with texpr_desc }


(* Renvoie une équation normalisée à partir d'une équation donnée
   On considère qu'un programme est normalisé lorsque tous les pre sont appliqués à des identifiants
   Pré-condition: ne pas avoir de tuples dans l'équation
*)
let normalize_pre_equ extra_vars extra_equs ({ teq_expr; _ } as equ) =
  let teq_expr = normalize_pre_expr extra_vars extra_equs teq_expr in
  { equ with teq_expr }


(* Renvoie un noeud normalisé à partir d'une noeud donné
   On considère qu'un programme est normalisé lorsque tous les pre sont appliqués à des identifiants
   Pré-condition: ne pas avoir de tuples dans le noeud
*)
let normalize_pre_node ({ tn_equs; tn_local; _ } as node) =
  let extra_vars = ref [] in
  let extra_equs = ref [] in

  let tn_equs = List.map (normalize_pre_equ extra_vars extra_equs) tn_equs in

  let tn_local = !extra_vars @ tn_local in
  let tn_equs = !extra_equs @ tn_equs in

  { node with tn_local; tn_equs }


(* ===== MAIN INLINING FUNCTION ===== *)

(* In-line les sous-noeuds dans le noeud principal *)
let inline program main =
  let main_node =
    match have_to_inline program with
    | false -> List.hd program
    | true ->
      let nodes = hashtbl_from_program program in
      main |> Hashtbl.find nodes |> rename_node |> inline_calls_node nodes
  in
  let main_node = inline_tuples_node main_node in
  (* let main_node = normalize_pre_node main_node in *)
  if debug then Typed_ast_printer.print_node_list_std [ main_node ];
  main_node
