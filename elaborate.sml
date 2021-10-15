
signature ELABORATE_LF =
sig
  val etaExpandAtom : LFSyntax.atom -> LFSyntax.exp -> LFSyntax.exp
  val elaborateExp : Signature.sg -> LFContext.ctx -> LFSyntax.exp
                        -> LFSyntax.exp * LFSyntax.exp
  val elaborateAtom : Signature.sg -> LFContext.ctx -> LFSyntax.atom
                         -> LFSyntax.exp * LFSyntax.exp
  val elaborateSignature : LFSyntax.sg -> LFSyntax.sg
end

structure ElaborateLF : ELABORATE_LF =
struct
  type ctx = LF.binding list

  local
      open LF
      open TypeCheckLF
      structure Ctx = LFContext
      structure Sig = Signature
  in

  val var_cnt = ref 0
  fun fresh_name () =
      let val x = !var_cnt
          val () = var_cnt := x + 1
      in "v" ^ Int.toString x end

  fun checkHead _ ctx (HVar (n, _)) = Ctx.sub ctx n
    | checkHead sg _ (HConst c) = Sig.lookup sg c
    | checkHead _ _ _ = raise TypeError "..."

  (* This is "type-driven" but we really don't care about any part
   * of the type except "pi vs. other". *)
  fun etaExpandAtom atom typ =
      (case typ of
           EPi (_, t1, t2) =>
           (* We have an application that isn't fully eta expanded, so we need to
            * expand it and then recurse.
            * Need to lift it. I hate de bruijn so much. *)
           let val b' = fresh_name ()
               val atom' = LFSubst.liftAtom 1 atom
               val ev = HApp (atom', etaExpandAtom (HVar (0, b')) t1)
               val ev' = etaExpandAtom ev t2
           in ELam (b', NONE, ev') end
         | _ => EAtom (atom))

  fun etaExpandAtom' atom typ = (etaExpandAtom atom typ, typ)

  (* This does type-checking as we go. Per Martens and Crary, this
   * implies that the original program was type-correct as well.
   * Intuitively, the idea is that we are doing type-checking on Classic LF
   * using basically the normal rules, but doing type-equality checking
   * by appealing to the translated Canonical LF terms/types, where
   * that is much easier to do. *)
  fun elaborateExp sg ctx exp =
      ((*print (PrettyLF.prettyMsg2 "elaborating: " exp "," "at: " typ ^ "\n");*)
       case exp of
           EKind => raise TypeError "kind is no classifier"
         | EType => (EType, EKind)
         | EPi (b, e1, e2) =>
           let val (e1', k1) = elaborateExp sg ctx e1
               val () = expEquality' e1' EType k1
               val (e2', k2) = elaborateExp sg (Ctx.extend ctx e1) e2
           in (EPi (b, e1', e2'), k2) end
         | ELam (b, NONE, e) => raise TypeError "missing annotation"
         | ELam (b, SOME t1, e) =>
           let val (t1', k1) = elaborateExp sg ctx t1
               val () = expEquality' t1' EType k1
               val (e', t2) = elaborateExp sg (Ctx.extend ctx t1') e
           in (ELam (b, NONE, e'), EPi (b, t1, t2)) end
         | EAtom at => elaborateAtom sg ctx at
      )
  and elaborateAtom sg ctx at =
      (case at of
           HExp e => elaborateExp sg ctx e
         | HApp (h, e2) =>
           let val (e1, t1, t2) =
                   (case elaborateAtom sg ctx h of
                       (ELam (_, _, e1), EPi (_, t1, t2)) => (e1, t1, t2)
                     | _ => raise TypeError "lhs of app must be pi")
               val (e2', t1') = elaborateExp sg ctx e2
               val () = expEquality' (EAtom at) t1 t1'
           in (LFSubst.substExp e2' e1, LFSubst.substExp e2' t2) end
         | HVar (n, _) => etaExpandAtom' at (Ctx.sub ctx n)
         | HConst c => etaExpandAtom' at (Sig.lookup sg c)
      )

  fun elaborateSignatureEntry (rdecls, sg) ((c, exp): LF.sg_entry) =
      let val () = var_cnt := 0
          val (exp', t) = elaborateExp sg Ctx.empty exp
          val () = expEquality (TypeCheckLF.inferClassifier exp') t
          val sg' = Sig.insert sg c exp'
      in ((c, exp') :: rdecls, sg') end

  fun elaborateSignatureEntry' arg entry =
      ((elaborateSignatureEntry arg entry)
       handle TypeError s => (print ("\nType error: " ^ s ^ "\n"); raise TypeError s))
  val elaborateSignatureEntry = elaborateSignatureEntry'

  fun elaborateSignature decls =
      let val (rdecls, sg) = (
              foldl (fn (e, x) => elaborateSignatureEntry x e) ([], Sig.empty) decls)
      in rev rdecls end
  end
end
