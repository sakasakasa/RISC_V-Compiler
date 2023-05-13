open KNormal

let find x env = try M.find x env with Not_found -> x (* 置換のための関数 (caml2html: beta_find) *)

let rec g env (pos, ebody) = (* β簡約ルーチン本体 (caml2html: beta_g) *)
  match ebody with
  | Unit -> pos, Unit
  | Int(i) -> pos, Int(i)
  | Float(d) -> pos, Float(d)
  | Neg(x) -> pos, Neg(find x env)
  | And(x, y) -> pos, And(find x env, find y env)
  | Or(x, y) -> pos, Or(find x env, find y env)
  | Xor(x, y) -> pos, Xor(find x env, find y env)
  | AndI(x, y) -> pos, AndI(find x env, y)
  | FAbs(x) -> pos, FAbs(find x env)
  | ItoF(x) -> pos, ItoF(find x env)
  | FtoI(x) -> pos, FtoI(find x env)
  | FSqrt(x) -> pos, FSqrt(find x env)
  | FFloor(x) -> pos, FFloor(find x env)
  | FEq(x,y) -> pos, FEq(find x env, find y env)
  | FLT(x,y) -> pos, FLT(find x env, find y env)
  | Read -> pos, Read
  | FRead -> pos, FRead
  | Write(x) -> pos, Write(find x env) 
  | Add(x, y) -> pos, Add(find x env, find y env)
  | Sub(x, y) -> pos, Sub(find x env, find y env)
  | Mul(x, y) -> pos, Mul(find x env, find y env)
  | Div(x, y) -> pos, Div(find x env, find y env)
  | Rem(x, y) -> pos, Rem(find x env, find y env)
  | FNeg(x) -> pos, FNeg(find x env)
  | FAdd(x, y) -> pos, FAdd(find x env, find y env)
  | FSub(x, y) -> pos, FSub(find x env, find y env)
  | FMul(x, y) -> pos, FMul(find x env, find y env)
  | FDiv(x, y) -> pos, FDiv(find x env, find y env)
  | IfEq(x, y, e1, e2) -> pos, IfEq(find x env, find y env, g env e1, g env e2)
  | IfLE(x, y, e1, e2) -> pos, IfLE(find x env, find y env, g env e1, g env e2)
  | IfZ(x, e1, e2) -> pos, IfZ(find x env, g env e1, g env e2)
  | IfPos(x, e1, e2) -> pos, IfPos(find x env, g env e1, g env e2)
  | IfNeg(x, e1, e2) -> pos, IfNeg(find x env, g env e1, g env e2)
  | Let((x, t), e1, e2) -> (* letのβ簡約 (caml2html: beta_let) *)
      (match g env e1 with
      | pos', Var(y) ->
          Format.eprintf "beta-reducing %s = %s@." x y;
          g (M.add x y env) e2
      | e1' ->
          let e2' = g env e2 in
          pos, Let((x, t), e1', e2'))
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
    pos, LetRec({ name = xt; args = yts; body = g env e1 }, g env e2)
  | Var(x) -> pos, Var(find x env) (* 変数を置換 (caml2html: beta_var) *)
  | Tuple(xs) -> pos, Tuple(List.map (fun x -> find x env) xs)
  | GlobalTuple(xs) -> pos, GlobalTuple(List.map (fun x -> find x env) xs)
  | LetTuple(xts, y, e) -> pos, LetTuple(xts, find y env, g env e)
  | Array(x, y) -> pos, Array(find x env, find y env)
  | GlobalArray(x, y) -> pos, GlobalArray(find x env, find y env)
  | Get(x, y) -> pos, Get(find x env, find y env)
  | Put(x, y, z) -> pos, Put(find x env, find y env, find z env)
  | App(g, xs) -> pos, App(find g env, List.map (fun x -> find x env) xs)
  | ExtArray(x) -> pos, ExtArray(x)
  | ExtFunApp(x, ys) -> pos, ExtFunApp(x, List.map (fun y -> find y env) ys)

  let f = g M.empty
