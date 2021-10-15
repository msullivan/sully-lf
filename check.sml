signature TYPE_CHECK_LF =
sig
  exception TypeError of string

  val expEquality' : LF.exp -> LF.exp -> LF.exp -> unit
  val expEquality : LF.exp -> LF.exp -> unit
  val checkExp : Signature.sg -> LFContext.ctx -> LF.exp -> LF.exp -> unit

  val inferClassifier : LF.exp -> LF.exp
  val checkSignatureEntry : Signature.sg -> LF.sg_entry -> Signature.sg

  val checkSignature : LF.sg -> Signature.sg
end


structure TypeCheckLF :> TYPE_CHECK_LF =
struct

local
  open LFSyntax
  structure Ctx = LFContext
  structure Sig = Signature
in

  exception TypeError of string

  fun requireAtomic exp =
      (case exp of
           EType => ()
         | EAtom _ => ()
         | _ => raise TypeError (PrettyLF.prettyMsg
                                     "required atomic type, got: "
                                     exp))

  fun expEquality e e' =
      (case (e, e') of
           (EKind, EKind) => ()
         | (EType, EType) => ()
         | (EPi (_, e1, e2), EPi (_, e1', e2')) =>
           (expEquality e1 e1'; expEquality e2 e2')
         | (ELam (_, NONE, e), ELam (_, NONE, e')) =>
           expEquality e e'
         | (EAtom h, EAtom h') =>
           atomEquality h h'
         | _ => raise TypeError "exps not equal")
  and atomEquality h h' =
      (case (h, h') of
           (HVar (i, _), HVar (i', _)) =>
           if i = i' then () else
           raise (TypeError ("bound variable mismatch: " ^
                             Int.toString i ^ " vs. " ^ Int.toString i'))
         | (HConst c, HConst c') =>
           if c = c' then () else
           raise (TypeError ("const mismatch: " ^ Const.toStr c ^ " vs. " ^ Const.toStr c'))
         | (HApp (h1, e1), HApp (h2, e2)) =>
           (atomEquality h1 h2; expEquality e1 e2)
         | (HExp _, _) => raise TypeError "not beta-short"
         | (_, HExp _) => raise TypeError "not beta-short"
         | (HApp _, _) => raise TypeError "head vs. app mismatch"
         | (_, HApp _) => raise TypeError "head vs. app mismatch"
         | _ => raise TypeError "const vs. var mismatch")


  fun expEquality' e t t' =
      ((expEquality t t')
       handle TypeError s => raise TypeError (
          "equality failure: " ^ s ^ "\n" ^
          PrettyLF.prettyMsg2 "expected: " t ","  "got: " t' ^ "\n" ^
          PrettyLF.prettyMsg "while checking: " e))

  fun checkExp sg ctx exp typ =
      ((*print (PrettyLF.prettyMsg2 "checking: " exp "," "at: " typ ^ "\n");*)
       case exp of
           EKind => raise TypeError "kind is no classifier"
         | EType => expEquality' exp typ EKind
         | EPi (b, e1, e2) =>
           (checkExp sg ctx e1 EType;
            checkExp sg (Ctx.extend ctx e1) e2 typ)

         | ELam (b, ot, e) =>
           let val (t1, t2) =
               (case typ of EPi (_, t1, t2) => (t1, t2)
                          | _ => raise TypeError "lambda must have pi type")
               (* Type annotation is optional but we might as well check it *)
               val () = Option.app (expEquality' exp t1) ot
           in checkExp sg (Ctx.extend ctx t1) e t2 end
         | EAtom h =>
           let val t' = checkAtom sg ctx h
               val () = requireAtomic t'
           in expEquality' exp typ t' end)

  and checkAtom sg ctx h =
      (case h of
           HVar (n, _) => Ctx.sub ctx n
         | HConst c => Sig.lookup sg c
         | HApp (h', e) =>
           let val t = checkAtom sg ctx h'
               (*val () = print (PrettyLF.prettyMsg "head has type: " t ^ "\n")*)
               val (t1, t2) =
                   (case t of EPi (_, t1, t2) => (t1, t2)
                              | _ => raise TypeError "lhs of app must be pi")
               val () = checkExp sg ctx e t1
           in LFSubst.substExp e t2 end

         | _ => raise TypeError "not beta-short"
      )

  fun checkExp' sg ctx exp typ =
      ((checkExp sg ctx exp typ)
       handle TypeError s => (print ("\nType error: " ^ s ^ "\n"); raise TypeError s))
  val checkExp = checkExp'
  fun expEquality'' e e' =
      ((expEquality e e')
       handle TypeError s => (print ("\nType error: " ^ s ^ "\n"); raise TypeError s))
  val expEquality = expEquality''

  fun inferClassifier e =
      (case e of
           EType => EKind
         | EAtom _ => EType
         | EPi (_, _, e') => inferClassifier e'
         | EKind => raise TypeError "kind not valid as a signature declaration"
         | ELam _ => raise TypeError "lambda not valid as a signature declaration")

  fun checkSignatureEntry sg ((c, exp): LF.sg_entry) =
      let val classifier = inferClassifier exp
          val () = checkExp sg Ctx.empty exp classifier
      in Sig.insert sg c exp end

  fun checkSignature decls =
      foldl (fn (e, sg) => checkSignatureEntry sg e) Sig.empty decls

end
end
