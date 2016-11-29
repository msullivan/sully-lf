signature SIGNATURE =
sig
  type sg
  val empty : sg
  val insert : sg -> LF.const -> LF.exp -> sg
  val lookup : sg -> LF.const -> LF.exp
end

structure Signature :> SIGNATURE =
struct
  val SignatureError = Fail

  type sg = LF.exp ConstDict.dict
  val empty = ConstDict.empty

  fun insert' sg c entry =
      if ConstDict.member sg c then
          raise SignatureError (Const.toStr c ^ " is already in signature")
      else ConstDict.insert sg c entry

  fun insert sg c typ = insert' sg c typ

  fun lookup sg c =
      (case ConstDict.find sg c of
           NONE => raise SignatureError (Const.toStr c ^ " not in signature")
         | SOME t => t)
end
