(* To make writing down terms easier:
 * Do a conversion from named to de bruijn.
 * Both use the same syntax but named variables have ~1 as index. *)

signature FROM_NAMED =
sig
  type ctx = LF.binding list

  val convertSignature : LF.sg -> LF.sg

  val convertExp : ctx -> LF.exp -> LF.exp
  val convertAtom : ctx -> LF.atom -> LF.atom
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

  fun convertAtom G (HVar (~1, "_")) = raise Fail "stop that."
    | convertAtom G (HVar (~1, s)) = HVar (valOf (findIndex s G), s)
    | convertAtom G (HVar (i, _)) = raise Fail "stop that."
    | convertAtom G (HConst c) = HConst c
    | convertAtom G (HApp (h, e)) = HApp (convertAtom G h, convertExp G e)
    | convertAtom G (HExp e) = HExp (convertExp G e)

  and convertExp G e =
      (case e of
           EKind => EKind
         | EType => EType
         | ELam (b, ot, e) =>
           ELam (b, Option.map (convertExp G) ot, convertExp (b :: G) e)
         | EPi (b, e1, e2) => EPi (b, convertExp G e1, convertExp (b :: G) e2)
         | EAtom h => EAtom (convertAtom G h))

  fun convertSignature sg =
      map (fn (c, e) => (c, convertExp [] e)) sg

  end
end
