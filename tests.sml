structure TestUtil =
struct
  local
      open LF
  in

  (* This depends on the bullshit we are doing. *)
  fun arrow t1 t2 = EPi ("_", t1, t2)
  fun arrow' (t1, t2) = arrow t1 t2
  infixr -->
  val (op -->) = arrow'
  infix <--
  fun t1 <-- t2 = t2 --> t1

  fun v s = HVar (~1, s)
  fun var s = EAtom (v s)

  (* An earlier version used to be done using spines, and so the tests
   * are still written using utility functions designed for spines. *)
  fun h_app' h [] = h
    | h_app' h (x::xs) = h_app' (HApp (h, x)) xs

  fun h_app h ls = EAtom (h_app' h ls)
  fun c_app c ls = h_app (HConst c) ls
  fun v_app x ls = h_app (v x) ls
  fun e_app e ls = h_app (HExp e) ls
  fun c_0 c = c_app c []
  fun h_0 h = h_app h []

  fun lam (b, e) = ELam (b, NONE, e)
  fun lam' (b, t, e) = ELam (b, SOME t, e)

  end

end

structure Tests =
struct
  open LF TestUtil
  infixr -->
  infix <--

  val nat = c_app "nat" []
  val zero = c_app "z" []
  fun succ n = c_app "s" [n]
  fun plus n1 n2 n3 = c_app "plus" [n1, n2, n3]

  val [x, n, m, p, A, B, e, e', e1, e1', e2, e2', D, D', D'', k, r] =
      map var ["x", "n", "m", "p", "A", "B", "e", "e'", "e1", "e1'", "e2", "e2'", "D", "D'", "D''", "k", "r"]

  (* An encoding of natural numbers and a Twelf-style proof that
   * plus commutes. Of course, we aren't checking that proof here,
   * which relies on Twelf's totality checking of the logic program
   * interpretation of this signature.
   *
   * Also doing this sort of thing is *vastly* more painful when you
   * actually need to spell out *everything. In Twelf certain parameters
   * get left implicit, which *vastly* increases how pleasant it is to use.
   * Implementing that requires unification, though, which is a *lot* more
   * machinery than we've got.
   * (To construct some of the cases here I took my Twelf proof of this
   * stuff, made all the parameters explicit, filled them in with underscores
   * in the proof, and copied what Twelf inferred.)
   *
   * I built a higher order unification system based off of Twelf's for a
   * different project and it got pretty gnarly. I feel like I made a bunch
   * of simplifications since my setting wasn't dependently typed, though I'm
   * not totally sure.
   *
   * (Though it probably wouldn't be too hard to build something that worked
   * for first-order things like this signature.)
   *
   * All of the mistakes I made while writing this did a pretty decent
   * job convincing me that the typechecker works correctly.
   *)
  val nat_test = FromNamed.convertSignature
      [("nat", EType),
       ("z", nat),
       ("s", nat --> nat),

       ("plus", nat --> nat --> nat --> EType),
       ("plus/0",
        EPi ("n", nat, plus zero n n)),
       ("plus/s",
        EPi ("m", nat, EPi ("n", nat, EPi ("p", nat,
             arrow (plus m n p)
                   (plus (succ m) n (succ p)))))),

       (* OK now a proof thing *)
       ("plus-comm",
        EPi ("m", nat, EPi ("n", nat, EPi ("p", nat,
             arrow (plus m n p)
             (arrow
              (plus n m p)
              EType))))),

       ("plus-comm-z",
        EPi ("n", nat, plus n zero n --> EType)),
       ("p-c-z/z",
        c_app "plus-comm-z"
        [zero,
         c_app "plus/0" [zero]]),
       ("p-c-z/s",
        EPi ("n", nat, EPi ("D", plus n zero n,
             c_app "plus-comm-z" [n, D] -->
             c_app "plus-comm-z"
             [succ n,
              c_app "plus/s" [n, zero, n, D]]))),

       ("plus-comm-s",
        EPi ("m", nat, EPi ("n", nat, EPi ("p", nat,
        plus m n p --> plus m (succ n) (succ p) --> EType)))),
       ("p-c-s/z",
        EPi ("m", nat,
        c_app "plus-comm-s"
              [zero, m, m,
               c_app "plus/0" [m], c_app "plus/0" [succ m]])),
       ("p-c-s/s",
        EPi ("m", nat, EPi ("n", nat, EPi ("p", nat,
        EPi ("D", plus m n p,
        EPi ("D'", plus m (succ n) (succ p),
        c_app "plus-comm-s"
              [succ m, n, succ p,
               c_app "plus/s" [m, n, p, D],
               c_app "plus/s" [m, (succ n), (succ p), D']]
        <--
        c_app "plus-comm-s" [m, n, p, D, D']
       )))))),

       ("p-c/z",
        EPi ("m", nat,
        EPi ("D", plus m zero m,
        c_app "plus-comm" [zero, m, m, c_app "plus/0" [m], D]
        <--
        c_app "plus-comm-z" [m, D]
        ))),
       ("p-c/s",
        EPi ("m", nat, EPi ("n", nat, EPi ("p", nat,
        EPi ("D", plus m n p,
        EPi ("D'", plus n m p,
        EPi ("D''", plus n (succ m) (succ p),
        c_app "plus-comm"
              [succ m, n, succ p,
               c_app "plus/s" [m, n, p, D], D'']
        <--
        c_app "plus-comm" [m, n, p, D, D']
        <--
        c_app "plus-comm-s" [n, m, p, D', D'']
       )))))))
      ]

  fun eta1 t e = lam' ("x", t, h_app (v e) [x])
  (*fun eta1 t e = var e*)

  (* An encoding of typing and stepping for
   * the Simply-Typed Lambda Calculus *)
  val tp = c_app "tp" []
  val term = c_app "term" []
  val base = c_app "base" []
  fun arr t1 t2 = c_app "arr" [t1, t2]
  fun eapp t1 t2 = c_app "app" [t1, t2]
  fun elam A t1 = c_app "lam" [A, t1]
  fun eof e A = c_app "of" [e, A]
  fun step e1 e2 = c_app "step" [e1, e2]

  val lambda_test = FromNamed.convertSignature
      [("tp", EType),
       ("base", tp),
       ("arr", tp --> tp --> tp),

       ("term", EType),
       ("app", term --> term --> term),
       ("lam", tp --> (term --> term) --> term),

       ("of", term --> tp --> EType),
       ("of/app",
        EPi ("A", tp, EPi ("B", tp, EPi ("e", term, EPi ("e'", term,
             eof e (arr A B) --> eof e' A --> eof (eapp e e') B))))),
       ("of/lam",
        EPi ("A", tp, EPi ("B", tp, EPi ("e", term --> term,
             (EPi ("e'", term, eof e' A --> eof (v_app "e" [e']) B)) -->
             (eof (elam A (eta1 term "e")) (arr A B)))))),

       ("step", term --> term --> EType),
       ("step/app1",
        EPi ("e1", term, EPi ("e2", term, EPi ("e1'", term,
             step (eapp e1 e2) (eapp e1' e2)
                  <-- step e1 e1'
       )))),

       ("step/beta",
        EPi ("A", tp, EPi ("e1", term --> term, EPi ("e2", term,
             step (eapp (elam A (eta1 term "e1")) e2)
                  (v_app "e1" [e2])
       ))))
      ]

  (*******************************************************************************************)
  val eta_screwup_test = FromNamed.convertSignature
       [("nat", EType),
        ("s", nat --> nat),
        ("fix", (nat --> nat) --> nat),
        ("bs", nat --> EType),
        ("right",
         c_app "bs" [c_app "fix" [lam ("n", succ n)]]),
        ("wrong", c_app "bs" [c_app "fix" [c_0 "s"]])]

  (*******)
  val self_app_fn = FromNamed.convertExp [] (lam ("x", v_app "x" [x]))
  fun hereditaryReduce (ELam (_, _, e1)) e2 = LFSubst.substExp e2 e1
    | hereditaryReduce _ _ = raise Fail "whatever"
  fun omega_reduce_test () =
    hereditaryReduce self_app_fn self_app_fn

  val two_args = lam' ("n", nat, lam' ("m", nat, c_app "add" [m, n]))
  val apply_arg = lam' ("k", nat --> nat --> nat, v_app "k" [c_0 "z"])
  val apply_arg_typ = (nat --> nat --> nat) --> (nat --> nat)
  val tricky_reduce_n = e_app apply_arg [two_args]
  val tricky_reduce = FromNamed.convertSignature
       [("nat", EType),
        ("z", nat),
        ("add", nat --> nat --> nat),
        ("app_arg_test", apply_arg_typ --> EType),
        ("bs1", c_app "app_arg_test" [apply_arg]),

        ("mk", (nat --> nat) --> EType),
        ("bs", c_app "mk" [tricky_reduce_n])
       ]

  (* sltc arithmetic *)
  val b = c_app "b" []
  val fnat = (b --> b) --> b --> b
  val fz = lam' ("s", b --> b, lam' ("z", b, var "z"))
  val fs = lam' ("n", fnat, lam' ("s", b --> b, lam' ("z", b,
                v_app "s" [v_app "n" [var "s", var "z"]])))
  val fplus =
      lam' ("n", fnat, lam' ("m", fnat, lam' ("s", b --> b, lam' ("z", b,
               v_app "m" [var "s", v_app "n" [var "s", var "z"]]))))
  val fmult =
      lam' ("n", fnat, lam' ("m", fnat, lam' ("s", b --> b,
               v_app "m" [v_app "n" [var "s"]])))

  val n1 = e_app fs [fz]
  val n2 = e_app fs [n1]
  val n3 = e_app fs [n2]
  val n4 = e_app fs [n3]

  fun testeq n1 n2 = c_app "heq" [n1, c_app "mkW" [n2]]

  val stlc_maths = FromNamed.convertSignature
       [("b", EType),
        ("z", b),
        ("s", b --> b),
        ("check", (fnat --> fnat) --> (fnat --> fnat --> fnat) -->
                     (fnat --> fnat --> fnat) --> EType),
        ("bs", c_app "check" [fs, fplus, fmult]),
        ("calc", fnat --> EType),
        ("calcb", b --> EType),
        ("_1", c_app "calc" [n2]),
        ("_2", c_app "calc" [e_app fplus [n2, n3]]),
        ("_13", c_app "calc" [e_app fmult [n1, e_app fmult [n4, n4]]]),
        ("_13b", c_app "calcb"
                          [e_app (e_app fmult [n1, e_app fmult [n4, n4]])
                                 [c_app "s" [], zero]]),

        ("W", fnat --> EType),
        ("mkW", EPi ("n", fnat, c_app "W" [n])),
        ("heq", EPi ("n", fnat, c_app "W" [n] --> EType)),
        ("eq1", testeq n1 n1),
        ("eq2", testeq (e_app fplus [n2, n2]) n4),
        ("eq3", testeq (e_app fplus [n2, n4]) (e_app fmult [n3, n2]))
       ]

  val stlc_bug = FromNamed.convertSignature
       [("b", EType),
        ("check", (b --> b) --> EType),
        ("no", EType --> EType)
        (* ("bs", c_app "check" [lam ("x", lam ("y", x))]) *)
       ]

  (*****************************************************************)

  fun println s = print (s ^ "\n")

  fun succeeded f x = (f x; true) handle _ => false

  fun check sg =
      (println "";
       println (PrettyLF.prettySignature sg);
       ignore (TypeCheckLF.checkSignature sg);
       println "")

  fun checkVanilla sg = check (ElaborateLF.elaborateSignature sg)


end
