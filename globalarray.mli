type t = int * tt
and tt = (* MinCamlの構文を表現するデータ型 (caml2html: syntax_t) *)
  | Unit
  | Bool of bool
  | Int of int
  | Float of float
  | Not of t
  | And of t * t
  | Or of t * t
  | Xor of t * t
  | Neg of t
  | Add of t * t
  | Sub of t * t
  | Mul of t * t
  | Div of t * t
  | Rem of t * t
  | FNeg of t
  | FAdd of t * t
  | FSub of t * t
  | FMul of t * t
  | FDiv of t * t
  | Eq of t * t
  | LE of t * t
  | FEq of t * t
  | FLT of t * t
  | FAbs of t
  | FFloor of t
  | ItoF of t
  | FtoI of t
  | FSqrt of t
  | Read
  | FRead
  | Write of t
  | AndI of t * int
  | If of t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of t * t list
  | Tuple of t list
  | GlobalTuple of t list
  | LetTuple of (Id.t * Type.t) list * t * t
  | Array of t * t
  | GlobalArray of t * t
  | Get of t * t
  | Put of t * t * t
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

val f: Syntax.t -> t