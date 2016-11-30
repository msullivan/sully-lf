structure TestUtil =
struct
  local
      open LF
  in

  val T = SgFamilyDecl
  val O = SgObjectDecl

  (* This depends on the bullshit we are doing. *)
  fun arrow t1 t2 = EPi ("_", t1, t2)
  fun arrow' (t1, t2) = arrow t1 t2
  infixr -->
  val (op -->) = arrow'
  infix <--
  fun t1 <-- t2 = t2 --> t1

  fun v s = HVar (~1, s)
  fun var s = EApp (v s, SNil)

  fun h_app h ls = EApp (h, listToSpine ls)
  fun c_app c ls = h_app (HConst c) ls
  fun v_app x ls = h_app (v x) ls
  fun c_0 c = c_app c []

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
      [(T, "nat", EType),
       (O, "z", nat),
       (O, "s", nat --> nat),

       (T, "plus", nat --> nat --> nat --> EType),
       (O, "plus/0",
        EPi ("n", nat, plus zero n n)),
       (O, "plus/s",
        EPi ("m", nat, EPi ("n", nat, EPi ("p", nat,
             arrow (plus m n p)
                   (plus (succ m) n (succ p)))))),

       (* OK now a proof thing *)
       (T, "plus-comm",
        EPi ("m", nat, EPi ("n", nat, EPi ("p", nat,
             arrow (plus m n p)
             (arrow
              (plus n m p)
              EType))))),

       (T, "plus-comm-z",
        EPi ("n", nat, plus n zero n --> EType)),
       (O, "p-c-z/z",
        c_app "plus-comm-z"
        [zero,
         c_app "plus/0" [zero]]),
       (O, "p-c-z/s",
        EPi ("n", nat, EPi ("D", plus n zero n,
             c_app "plus-comm-z" [n, D] -->
             c_app "plus-comm-z"
             [succ n,
              c_app "plus/s" [n, zero, n, D]]))),

       (T, "plus-comm-s",
        EPi ("m", nat, EPi ("n", nat, EPi ("p", nat,
        plus m n p --> plus m (succ n) (succ p) --> EType)))),
       (O, "p-c-s/z",
        EPi ("m", nat,
        c_app "plus-comm-s"
              [zero, m, m,
               c_app "plus/0" [m], c_app "plus/0" [succ m]])),
       (O, "p-c-s/s",
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

       (O, "p-c/z",
        EPi ("m", nat,
        EPi ("D", plus m zero m,
        c_app "plus-comm" [zero, m, m, c_app "plus/0" [m], D]
        <--
        c_app "plus-comm-z" [m, D]
        ))),
       (O, "p-c/s",
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

  fun eta1 e = ELam ("x", h_app (v e) [x])

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
      [(T, "tp", EType),
       (O, "base", tp),
       (O, "arr", tp --> tp --> tp),

       (T, "term", EType),
       (O, "app", term --> term --> term),
       (O, "lam", tp --> (term --> term) --> term),

       (T, "of", term --> tp --> EType),
       (O, "of/app",
        EPi ("A", tp, EPi ("B", tp, EPi ("e", term, EPi ("e'", term,
             eof e (arr A B) --> eof e' A --> eof (eapp e e') B))))),
       (O, "of/lam",
        EPi ("A", tp, EPi ("B", tp, EPi ("e", term --> term,
             (EPi ("e'", term, eof e' A --> eof (v_app "e" [e']) B)) -->
             (eof (elam A (eta1 "e")) (arr A B)))))),

       (T, "step", term --> term --> EType),
       (O, "step/app1",
        EPi ("e1", term, EPi ("e2", term, EPi ("e1'", term,
             step (eapp e1 e2) (eapp e1' e2)
                  <-- step e1 e1'
       )))),

       (O, "step/beta",
        EPi ("A", tp, EPi ("e1", term --> term, EPi ("e2", term,
             step (eapp (elam A (eta1 "e1")) e2)
                  (v_app "e1" [e2])
       ))))
      ]

  (*******************************************************************************************)
  val eta_screwup_test = FromNamed.convertSignature
       [(T, "nat", EType),
        (O, "s", nat --> nat),
        (O, "fix", (nat --> nat) --> nat),
        (T, "bs", nat --> EType),
        (O, "right",
         c_app "bs" [c_app "fix" [ELam ("n", succ n)]]),
        (O, "wrong", c_app "bs" [c_app "fix" [c_0 "s"]])]



  (*****************************************************************)

  fun println s = print (s ^ "\n")

  fun succeeded f x = (f x; true) handle _ => false

  fun check sg =
      (println "";
       println (PrettyLF.prettySignature sg);
       ignore (TypeCheckLF.checkSignature sg);
       println "")
(*      handle (e as TypeCheckLF.TypeError s) => (println s; raise e)*)


end
