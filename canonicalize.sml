
signature CANONICALIZE_LF =
sig
  val etaExpandExp : Signature.sg -> LFContext.ctx
                       -> LFSyntax.exp -> LFSyntax.exp -> LFSyntax.exp
  val betaNormalizeExp : LFSyntax.exp -> LFSyntax.exp
  val canonicalizeSignature : LFSyntax.sg -> LFSyntax.sg
end

structure CanonicalizeLF : CANONICALIZE_LF =
struct
  type ctx = LF.binding list

  local
      open LF
      structure Ctx = LFContext
      structure Sig = Signature
  in
  exception TypeError of string

  val cnt = ref 0
  fun fresh_name () =
      let val x = !cnt
          val () = cnt := x + 1
      in "v" ^ Int.toString x end

  fun checkHead _ ctx (HVar (n, _)) = Ctx.sub ctx n
    | checkHead sg _ (HConst c) = Sig.lookup sg c
    | checkHead _ _ (HExp (_, t)) = t

  fun appendToSpine e SNil = SApp (e, SNil)
    | appendToSpine e (SApp (e1, s)) = SApp (e1, appendToSpine e s)

  (* This is all "type-driven" but we really don't care about any part
   * of the type except "pi vs. other". *)

  fun etaExpandHead sg ctx h =
      (case h of
           HExp (e, t) => HExp (etaExpandExp sg ctx e t, etaExpandExp sg ctx t EKind)
         | _ => h)
  and etaExpandExp sg ctx exp typ =
      (case exp of
           EKind => raise TypeError "kind is no classifier"
         (* XXX check *)
         | EType => EType
         | EPi (b, e1, e2) =>
           EPi (b, etaExpandExp sg ctx e1 EType, etaExpandExp sg (Ctx.extend ctx e1) e2 typ)
         | ELam (b, e) =>
           let val (t1, t2) =
               (case typ of EPi (_, t1, t2) => (t1, t2)
                          | _ => raise TypeError "lambda must have pi type")
           in ELam (b, etaExpandExp sg (Ctx.extend ctx t1) e t2) end
         | e as (EApp (h, s)) =>
           (case typ of
                EPi (_, t1, t2) =>
                (* We have an application that isn't fully eta expanded, so we need to
                 * expand it and then recurse.
                 * Need to lift it. I hate de bruijn so much. *)
                let val b' = fresh_name ()
                    val (EApp (h', s')) = LFSubst.liftExp 1 e
                    val ev = EApp (HVar (0, b'), SNil)
                    val e'' = ELam (b', EApp (h', appendToSpine ev s'))
                in etaExpandExp sg ctx e'' typ end
              | _ =>
                (* Something *is* fully eta expanded *)
                let val htyp = checkHead sg ctx h
                    val h' = etaExpandHead sg ctx h
                    val s' = etaExpandSpine sg ctx s htyp
                in EApp (h', s') end
           )
      )
  and etaExpandSpine sg ctx s typ =
      (case s of
           SNil => SNil
         | SApp (e, s') =>
           (case typ of
                EPi (_, t1, t2) =>
                SApp (etaExpandExp sg ctx e t1, etaExpandSpine sg ctx s' t2)
              | _ => raise TypeError "expected pi")
      )

  (* here? elsewhere? *)
  fun betaNormalizeExp exp =
      (case exp of
           EKind => EKind
         | EType => EType
         | EPi (b, e1, e2) => EPi (b, betaNormalizeExp e1, betaNormalizeExp e2)
         | ELam (b, e) => ELam (b, betaNormalizeExp e)
         | EApp (HExp (e, t), s) => betaNormalizeExpApp e s
         | EApp (h, s) => EApp (h, betaNormalizeSpine s)
      )
  and betaNormalizeSpine s = mapSpine betaNormalizeExp s
  and betaNormalizeExpApp exp s =
      (case exp of
           EApp (h, s') =>
           let val snew = listToSpine (spineToList s' @ spineToList s)
           in betaNormalizeExp (EApp (h, snew)) end
         | ELam (b, e1) =>
           LFSubst.hereditaryReduce (betaNormalizeExp exp) (betaNormalizeSpine s)
         | _ => raise TypeError "bogus application target"
      )

  fun canonicalizeSignatureEntry (rdecls, sg) ((entry_type, c, exp): LF.sg_entry) =
      let val exp' = etaExpandExp sg Ctx.empty exp EType
          val exp'' = betaNormalizeExp exp'
          val sg' = Sig.insert sg c exp''
      in ((entry_type, c, exp'') :: rdecls, sg') end

  fun canonicalizeSignatureEntry' arg entry =
      ((canonicalizeSignatureEntry arg entry)
       handle TypeError s => (print ("\nType error: " ^ s ^ "\n"); raise TypeError s))
  val canonicalizeSignatureEntry = canonicalizeSignatureEntry'

  fun canonicalizeSignature decls =
      let val (rdecls, sg) = (
              foldl (fn (e, x) => canonicalizeSignatureEntry x e) ([], Sig.empty) decls)
      in rev rdecls end

  end
end
