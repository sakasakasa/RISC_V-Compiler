val f : KNormal.t -> KNormal.t
val globallist : (string * int) list ref
val globals : string list ref
val print_global : (string * int) list  -> unit
val list_include : 'a list -> 'a list -> bool