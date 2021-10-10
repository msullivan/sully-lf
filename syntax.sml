structure Const =
struct
  type const = string
  type t = const

  fun toStr (s: const) = s
  fun eq (x: const, y) = x = y
  val compare = String.compare
end
structure ConstDict = SplayDict(structure Key = Const)

structure LFSyntax =
struct

  type var = int * string
  type const = Const.const
  type binding = string

  datatype head = HVar of var
                | HConst of const
                | HExp of exp * exp (* exp : typ *)

       and exp = EKind
               | EType
               | EPi of binding * exp * exp
               | ELam of binding * exp
               | EApp of head * spine
  (* Should spine just be a list? *)
       and spine = SNil
                 | SApp of exp * spine

  datatype entry_type = SgFamilyDecl | SgObjectDecl
  type sg_entry = entry_type * Const.const * exp
  type sg = sg_entry list

  val listToSpine = foldr SApp SNil
  fun spineToList SNil = nil
    | spineToList (SApp (e, s)) = e :: spineToList s
  (* welp. *)
  fun mapSpine f = listToSpine o map f o spineToList

end
structure LF = LFSyntax
