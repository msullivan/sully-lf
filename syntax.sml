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

  datatype atom = HVar of var
                | HConst of const
                | HExp of exp
                | HApp of atom * exp

       and exp = EKind
               | EType
               | EPi of binding * exp * exp
               | ELam of binding * exp option * exp
               | EAtom of atom

  type sg_entry = Const.const * exp
  type sg = sg_entry list

  fun atomToSpine h =
      let fun loop (HApp (h, e)) s = loop h (e::s)
            | loop h s = (h, s)
      in loop h [] end

end
structure LF = LFSyntax
