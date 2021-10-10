(* To make writing down terms easier:
 * Do a conversion from named to de bruijn.
 * Both use the same syntax but named variables have ~1 as index. *)

signature FROM_NAMED =
sig
  type ctx = LF.binding list

  val convertSignature : LF.sg -> LF.sg

  val convertExp : ctx -> LF.exp -> LF.exp
  val convertHead : ctx -> LF.head -> LF.head
  val convertSpine : ctx -> LF.spine -> LF.spine
end

structure FromNamed : FROM_NAMED =
struct
  type ctx = LF.binding list

  local
      open LF
  in

  fun findIndexBy f y l =
      let fun search' _ nil = NONE
            | search' i (x::xs) = if f (y, x) then SOME i
                                  else search' (i+1) xs
      in search' 0 l end
  fun findIndex (y: string) l = findIndexBy (op =) y l

  fun convertHead G (HVar (~1, "_")) = raise Fail "stop that."
    | convertHead G (HVar (~1, s)) = HVar (valOf (findIndex s G), s)
    | convertHead G (HVar (i, _)) = raise Fail "stop that."
    | convertHead G (HConst c) = HConst c
    | convertHead G (HExp (e, t)) = HExp (convertExp G e, convertExp G t)

  and convertExp G e =
      (case e of
           EKind => EKind
         | EType => EType
         | ELam (b, e) => ELam (b, convertExp (b :: G) e)
         | EPi (b, e1, e2) => EPi (b, convertExp G e1, convertExp (b :: G) e2)
         | EApp (h, s) => EApp (convertHead G h, convertSpine G s))
  and convertSpine G s = LF.mapSpine (convertExp G) s

  fun convertSignature sg =
      map (fn (d, c, e) => (d, c, convertExp [] e)) sg

  end
end
