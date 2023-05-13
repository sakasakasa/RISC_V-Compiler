
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

let rec g (pos, ebody) = match ebody with
  | Syntax.Unit -> (pos,Unit)
  | Syntax.Bool(b) -> (pos,Bool(b))
  | Syntax.Int(i) -> (pos,Int(i))
  | Syntax.Float(f) -> (pos,Float(f))
  | Syntax.Not(e) -> (pos,Not(g e))
  | Syntax.And(e1,e2) -> (pos,And(g e1,g e2))
  | Syntax.Or(e1,e2) -> (pos,Or(g e1,g e2))
  | Syntax.Xor(e1,e2) -> (pos,Xor(g e1,g e2))
  | Syntax.Neg(e) -> (pos,Neg(g e))
  | Syntax.Add(e1,e2) -> (pos,Add(g e1, g e2))
  | Syntax.Sub(e1,e2) -> (pos,Sub(g e1, g e2))
  | Syntax.Mul(e1,e2) -> (pos,Mul(g e1, g e2))
  | Syntax.Div(e1,e2) -> (pos,Div(g e1, g e2))
  | Syntax.Rem(e1,e2) -> (pos,Rem(g e1, g e2))
  | Syntax.FNeg(e) -> (pos,FNeg(g e))
  | Syntax.FAdd(e1,e2) -> (pos,FAdd(g e1, g e2))
  | Syntax.FSub(e1,e2) -> (pos,FSub(g e1, g e2))
  | Syntax.FMul(e1,e2) -> (pos,FMul(g e1, g e2))
  | Syntax.FDiv(e1,e2) -> (pos,FDiv(g e1, g e2))
  | Syntax.Eq(e1,e2) -> (pos,Eq(g e1, g e2))
  | Syntax.LE(e1,e2) -> (pos,LE(g e1, g e2))
  | Syntax.FEq(e1,e2) -> (pos,FEq(g e1, g e2))
  | Syntax.FLT(e1,e2) -> (pos,FLT(g e1, g e2))
  | Syntax.FAbs(e) -> (pos,FAbs(g e))
  | Syntax.FFloor(e) -> (pos,FFloor(g e))
  | Syntax.ItoF(e) -> (pos,ItoF(g e))
  | Syntax.FtoI(e) -> (pos,FtoI(g e))
  | Syntax.FSqrt(e) -> (pos,FSqrt(g e))
  | Syntax.Read -> (pos,Read)
  | Syntax.FRead -> (pos,FRead)
  | Syntax.Write(e) -> (pos,Write(g e))
  | Syntax.AndI(e,i) -> (pos,AndI(g e,i))
  | Syntax.If(e1,e2,e3) -> (pos,If(g e1,g e2,g e3))
  | Syntax.Let((x,t),e1,e2) -> (pos, Let((x,t),g e1, g e2))
  | Syntax.Var(x) -> (pos,Var(x))
  | Syntax.LetRec({ Syntax.name = (x, t); Syntax.args = yts; Syntax.body = e1 }, e2) ->
     (pos,LetRec({name = (x,t);args = yts; body = g e1}, g e2))
  | Syntax.App(f,xs) -> (pos, App(g f, List.map g xs))
  | Syntax.Tuple(xs) -> (pos, Tuple(List.map g xs))
  | Syntax.LetTuple(xts, e1, e2) -> (pos, LetTuple(xts, g e1, g e2))
  | Syntax.Array(e1, e2) -> (pos,Array(g e1, g e2))
  | Syntax.Get(e1, e2) -> (pos, Get(g e1, g e2))
  | Syntax.Put(e1, e2, e3) -> (pos, Put(g e1, g e2, g e3))

let rec to_garray (pos,ebody) = match ebody with
  | Syntax.Array(x,y) -> (pos,GlobalArray(g x,g y))
  | Syntax.Tuple(es) -> (pos, GlobalTuple(List.map g es))
  | Syntax.Let((x,t),e1,e2) -> (pos,Let((x,t),g e1,to_garray e2))
  | _ -> g (pos, ebody)

let rec f (pos,ebody) = match ebody with
  | Syntax.Let((x,t),e1,e2) -> (pos, Let((x,t),to_garray e1, f e2))
  | e -> g(pos,e)
