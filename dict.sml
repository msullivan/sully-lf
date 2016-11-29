(* Nonsense drop in for SplayDict *)
signature KEY =
sig
    type t
    val eq : t * t -> bool
end

functor SplayDict(structure Key : KEY) =
struct
  type 'a dict = (Key.t * 'a) list
  val empty = []
  fun insert d k v = (k, v) :: d
  fun find d k = Option.map #2 (List.find (fn (k', _) => Key.eq (k, k')) d)
  fun member d k = Option.isSome (find d k)
end
