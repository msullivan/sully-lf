signature LF_SUBST =
sig
  exception SubstFailure
(*  val hereditaryReduce : LF.exp -> LF.exp -> LF.exp*)
  val substExpFull : int -> LF.exp list -> int -> LF.exp -> LF.exp
  val substExp : LF.exp -> LF.exp -> LF.exp
  val liftExp : int -> LF.exp -> LF.exp
  val liftAtom : int -> LF.atom -> LF.atom
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
  exception SubstFailure

  open LFSyntax

  val debug_depth = ref 0
  fun spaces n = implode (List.tabulate (n, fn _ => #" "))
  fun debug_in f = (print (spaces (2*(!debug_depth)) ^ f () ^ "\n");
                    debug_depth := !debug_depth + 1)
  fun debug_out () = debug_depth := !debug_depth - 1
  fun bail e = (debug_depth := 0; raise e)

  (* comment this out to turn on debug spew *)
  fun debug_in f = ()
  fun debug_out () = ()

  (* substXMain skip substs substs_len lift exp

     s = substs, n = substs_len, l = lift, m = skip

     if    |s| = n
     then  return exp[0 .. m-1 . s0[^m] .. sn-1[^m] . ^l+m]
   *)
  fun substExpMain skip substs substs_len lift exp =
    (debug_in (fn _=>"subst: " ^ PrettyLF.prettyExpParen exp ^
                     "[" ^ (if skip = 0 then "" else ("0 .. " ^ (Int.toString (skip-1)) ^ ".")) ^
                     (String.concatWith " . " (map PrettyLF.prettyExp substs)) ^
                     " . ^" ^ Int.toString (lift+skip) ^ "]");

      case exp of
           EKind => EKind
         | EType => EType
         | ELam (b, ot, e) =>
           let val ot' = Option.map (substExpMain skip substs substs_len lift) ot
               val e' = substExpMain (skip+1) substs substs_len lift e
           in ELam (b, ot', e') end
         | EPi (b, e1, e2) =>
           let val e1' = substExpMain skip substs substs_len lift e1
               val e2' = substExpMain (skip+1) substs substs_len lift e2
           in EPi (b, e1', e2') end
         | EAtom at =>
           (case substAtomMain skip substs substs_len lift at of
                (* This check ensures that termination always terminates,
                 * but also means it only works on eta-long terms. *)
                EAtom at' => EAtom at'
              | _ => raise SubstFailure)
      ) before debug_out ()

  and substAtomMain skip substs substs_len lift atom =
      (case atom of
           HExp e => raise SubstFailure
         | HConst c => EAtom (HConst c)
         | HVar (i, s) =>
           if i < skip then
               EAtom (HVar (i, s))
           else if i < skip+substs_len then
               let val sub = List.nth (substs, i-skip)
                   val sub' = substExpMain 0 [] 0 skip sub
               (* I'm *pretty* sure all of the index stuff is done.. *)
               in sub' end
           else
               EAtom (HVar (i-substs_len+lift, s))
         | HApp (at, e) =>
           let val lhs = substAtomMain skip substs substs_len lift at
               val e' = substExpMain skip substs substs_len lift e
           in (case lhs of
                   EAtom at' => EAtom (HApp (at', e'))
                 (* ... is this right? *)
                 | ELam (_, _, e2) => substExpMain 0 [e'] 1 0 e2
                 | _ => bail SubstFailure
              )
           end
      )

  fun substExpFull skip substs lift exp =
      substExpMain skip substs (length substs) lift exp
  fun substExp subst exp = substExpFull 0 [subst] 0 exp
  fun liftExp lift exp = substExpFull 0 [] lift exp
  fun liftAtom lift atom =
      let val (EAtom atom') = substAtomMain 0 [] 0 lift atom
      in atom' end
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
