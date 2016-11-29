signature LF_SUBST =
sig
  val hereditaryReduce : LF.exp -> LF.spine -> LF.exp
  val substExp : int -> LF.exp list -> int -> LF.exp -> LF.exp
  val liftExp : int -> LF.exp -> LF.exp
end


signature CONTEXT =
sig
  type ctx
  val empty : ctx
  val length : ctx -> int
  val sub : ctx -> int -> LF.exp
  val extend : ctx -> LF.exp -> ctx
end

structure LFSubst :> LF_SUBST =
struct

  open LFSyntax

  (* substXMain skip substs substs_len lift exp

     s = substs, n = substs_len, l = lift, m = skip

     if    |s| = n
     then  return exp[0 .. m-1 . s0[^m] .. sn-1[^m] . ^l+m]
   *)
  fun substExpMain skip substs substs_len lift exp =
      (case exp of
           EKind => EKind
         | EType => EType
         | ELam (b, e) =>
           let val e' = substExpMain (skip+1) substs substs_len lift e
           in ELam (b, e') end
         | EPi (b, e1, e2) =>
           let val e1' = substExpMain skip substs substs_len lift e1
               val e2' = substExpMain (skip+1) substs substs_len lift e2
           in EPi (b, e1', e2') end
         | EApp (head, spine) =>
           let val spine' = substSpineMain skip substs substs_len lift spine
           in (case head of
                   HConst c =>
                   EApp (HConst c, spine')
                 | HVar (i, s) =>
                   if i < skip then
                       EApp (HVar (i, s), spine')
                   else if i < skip+substs_len then
                       let val sub = List.nth (substs, i-skip)
                           val sub' = substExpMain 0 [] 0 skip sub
                       (* I'm *pretty* sure all of the index stuff is done.. *)
                       in hereditaryReduce sub' spine end
                   else
                       EApp (HVar (i-substs_len+lift, s), spine'))
           end
      )
  and substSpineMain skip substs substs_len lift spine =
      (case spine of
           SNil => SNil
         | SApp (exp, spine) =>
           let val exp' = substExpMain skip substs substs_len lift exp
               val spine' = substSpineMain skip substs substs_len lift spine
           in SApp (exp', spine') end)

  and hereditaryReduce head spine =
      let fun getBody (ELam (b, e)) n = getBody e (n+1)
            | getBody e n = (e, n)

           fun getSubsts SNil subs = subs
             | getSubsts (SApp (e, s)) subs = getSubsts s (e :: subs)

           val (body, count) = getBody head 0
           val subs = getSubsts spine []

           val () = if count = length subs then ()
                    else raise Fail "bogus application"

      in substExpMain 0 subs (length subs) 0 body end

  fun substExp skip substs lift exp =
      substExpMain skip substs (length substs) lift exp
  fun liftExp lift exp = substExp 0 [] lift exp
end

structure LFContext :> CONTEXT =
struct
  type ctx = LFSyntax.exp list
  val empty = nil
  val length = List.length
  fun sub G n =
      let val t = List.nth (G, n)
      in LFSubst.liftExp (n+1) t end
  fun extend G t = t :: G
end
