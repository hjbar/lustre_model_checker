open Aez
open Smt

let declare_symbol name t_in t_out =
  let x = Hstring.make name in
  (* creation d'un symbole *)
  Symbol.declare x t_in t_out;
  (* declaration de son type *)
  x


let tic = declare_symbol "tic" [ Type.type_int ] Type.type_bool

let ok = declare_symbol "ok" [ Type.type_int ] Type.type_bool

let cpt = declare_symbol "cpt" [ Type.type_int ] Type.type_int

let aux = declare_symbol "aux" [ Type.type_int ] Type.type_bool

let def_cpt n =
  (* cpt(n) = ite(n = 0, 0, cpt(n-1)) + ite(tic(n), 1, 0) *)
  let ite1 =
    (* ite(n = 0; 0, cpt(n-1)) *)
    Term.make_ite
      (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
      (Term.make_int (Num.Int 0))
      (Term.make_app cpt
         [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ] )
  in

  let ite2 =
    (* ite(tic(n); 1, 0) *)
    Term.make_ite
      (Formula.make_lit Formula.Eq [ Term.make_app tic [ n ]; Term.t_true ])
      (Term.make_int (Num.Int 1))
      (Term.make_int (Num.Int 0))
  in

  (* cpt(n) = ite1 + ite2 *)
  Formula.make_lit Formula.Eq
    [ Term.make_app cpt [ n ]; Term.make_arith Term.Plus ite1 ite2 ]


let def_ok n =
  (* ok(n) = ite(n = 0, true, aux(n)) *)
  Formula.make_lit Formula.Eq
    [
      Term.make_app ok [ n ];
      Term.make_ite
        (Formula.make_lit Formula.Eq [ n; Term.make_int (Num.Int 0) ])
        Term.t_true (Term.make_app aux [ n ]);
    ]


let def_aux n =
  let aux_n =
    (* aux(n) = true *)
    Formula.make_lit Formula.Eq [ Term.make_app aux [ n ]; Term.t_true ]
  in
  let pre_cpt_le_cpt =
    (* cpt(n-1) <= cpt(n) *)
    Formula.make_lit Formula.Le
      [
        Term.make_app cpt
          [ Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)) ];
        Term.make_app cpt [ n ];
      ]
  in
  Formula.make Formula.And
    [
      Formula.make Formula.Imp [ aux_n; pre_cpt_le_cpt ];
      Formula.make Formula.Imp [ pre_cpt_le_cpt; aux_n ];
    ]


let delta_incr n = Formula.make Formula.And [ def_cpt n; def_ok n; def_aux n ]

let p_incr n =
  Formula.make_lit Formula.Eq [ Term.make_app ok [ n ]; Term.t_true ]


module BMC_solver = Smt.Make (struct end)

let () =
  BMC_solver.assume ~id:0 (delta_incr (Term.make_int (Num.Int 0)));
  BMC_solver.assume ~id:0 (delta_incr (Term.make_int (Num.Int 1)));
  BMC_solver.check ()


let base =
  BMC_solver.entails ~id:0
    (Formula.make Formula.And
       [
         p_incr (Term.make_int (Num.Int 0)); p_incr (Term.make_int (Num.Int 1));
       ] )


module IND_solver = Smt.Make (struct end)

let ind =
  let n = Term.make_app (declare_symbol "n" [] Type.type_int) [] in
  let n_plus_one = Term.make_arith Term.Plus n (Term.make_int (Num.Int 1)) in
  IND_solver.assume ~id:0
    (Formula.make_lit Formula.Le [ Term.make_int (Num.Int 0); n ]);
  IND_solver.assume ~id:0 (delta_incr n);
  IND_solver.assume ~id:0 (delta_incr n_plus_one);
  IND_solver.assume ~id:0 (p_incr n);
  IND_solver.check ();
  IND_solver.entails ~id:0 (p_incr n_plus_one)


let example () =
  if not base then Format.printf "Example : FALSE PROPERTY@."
  else if ind then Format.printf "Example : TRUE PROPERTY@."
  else Format.printf "Example : Don’t know@."
