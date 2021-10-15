structure PrettyLF =
struct
  local
      open LF

      structure L = Layout

      val $ = L.str
      val % = L.mayAlign
      val %% = L.freeStyleAlign
      val & = L.seq

      val WIDTH = 80
      val fmt = L.tostringex WIDTH
  in

  (* Config options *)
  val look_good_but_be_wrong = ref true
  val twelf_style_pi = ref true
  val show_exp_atoms = ref false

  fun prettyConst s = s

  fun toLayoutAtom (HVar (i, s)) =
      if !look_good_but_be_wrong then $s
      else $(s ^ "/" ^ Int.toString i)
    | toLayoutAtom (HConst s) = $(prettyConst s)
    | toLayoutAtom (HExp e) =
      if !show_exp_atoms then
          & [$"H[", toLayoutExp e, $"]"]
      else toLayoutExp e
    | toLayoutAtom (h as (HApp _)) =
      let val (h', s) = atomToSpine h in
          & [toLayoutAtom h', $" ", toLayoutSpine s]
      end
  and toLayoutExp e =
      (case e of
           EKind => $"kind"
         | EType => $"type"
         (* Basing this on the variable being called "_" is a bit bogus. *)
         | EPi ("_", e1, e2) =>
           % [&[toLayoutTyParen e1, $" ->"],
              toLayoutExp e2]

         | EPi (b, e1, e2) =>
           % [piPartLayout b e1, toLayoutExp e2]
         | ELam (b, NONE, e) =>
           & [$"\\",
              % [ &[$b, $"."],
                  toLayoutExp e]
             ]
         | ELam (b, SOME t, e) =>
           & [$"\\",
              % [ &[$b, $":", toLayoutExp t, $"."],
                  toLayoutExp e]
             ]
         | EAtom a => toLayoutAtom a)
  and toLayoutSpine s =
      let val layouts = map toLayoutExpParen s
      in %% layouts end

  and toLayoutExpParen (e as ELam _) = L.paren (toLayoutExp e)
    | toLayoutExpParen (e as EAtom (HApp _)) = L.paren (toLayoutExp e)
    | toLayoutExpParen e = toLayoutExp e
  and toLayoutTyParen (e as ELam _) = L.paren (toLayoutExp e)
    | toLayoutTyParen (e as EPi _) = L.paren (toLayoutExp e)
    | toLayoutTyParen e = toLayoutExp e

  and piPartLayout b e1 =
      if !twelf_style_pi then
          &[$"{", $b, $":", toLayoutExp e1, $"}"]
      else
          &[$"pi ", $b, $" : ", toLayoutExp e1, $"."]

  (* A nicer layout for "toplevel" pis *)
  (* Another try that doesn't screw over ->s ?? *)
  fun toLayoutTop2 e =
      let fun loop l (e as EPi ("_", e1, e2)) = loop (&[toLayoutTyParen e1, $" ->"] :: l) e2
            | loop l (EPi (b, e1, e2)) = loop (piPartLayout b e1 :: l) e2
            | loop l e = %[%% (rev l), toLayoutExp e]
      in loop [] e end

  (* Actually, let's combine them. *)
  fun toLayoutTop1 e =
      let fun loop l (e as EPi ("_", _, _)) = %[%% (rev l), toLayoutTop2 e]
            | loop l (EPi (b, e1, e2)) = loop (piPartLayout b e1 :: l) e2
            | loop l e = %[%% (rev l), toLayoutTop2 e]
      in loop [] e end

  val toLayoutTop = toLayoutTop1

  val prettyExp = fmt o toLayoutTop
  val prettyExpParen = fmt o toLayoutExpParen
  val prettyAtom = fmt o toLayoutAtom
  val prettySpine = fmt o toLayoutSpine

  fun prettyMsg msg e = fmt (&[$msg, toLayoutExp e])
  fun prettyMsg2 msg1 e1 sep msg2 e2 =
      fmt (%[ &[$msg1, toLayoutExp e1, $sep],
              &[$msg2, toLayoutExp e2]])

  fun prettyDecl (c, e) = fmt (&[$c, $": ", toLayoutTop e, $"."])

  fun prettySignature sg =
      String.concatWith "\n" (map prettyDecl sg)

  end
end
