open Asm

(*let rec fv_exp com = 
  match com with
  | Nop | Li(_) | FLi(_) | SetL(_) | Comment(_) |  Dummy -> S.empty
  | Mr(x) | Neg(x) -> S.singleton x
  | Add(x,C(y)) | Sub(x,C(y)) | Mul(x,C(y)) | Div(x,C(y)) | Slw(x,C(y)) | Lwz(x,C(y)) | Sra(x,C(y)) -> S.singleton x
  | Add(x,V(y)) | Sub(x,V(y)) | Mul(x,V(y)) | Div(x,V(y)) | Slw(x,V(y)) | Lwz(x,V(y)) | Sra(x,V(y)) -> S.of_list [x;y]
  | Stw(x,y,C(z)) -> S.of_list [x;y]
  | And(x, y) | Or(x, y) | Xor(x, y) | Rem(x,y) | Array(x,y) | FArray(x,y) -> S.of_list [x;y]
  | Stw(x,y,V(z)) -> S.of_list [x;y;z]
  | FMr(x) | FNeg(x) | FAbs(x) | AndI(x,_)-> S.singleton x
  | FAdd(x,y) | FSub(x,y) | FMul(x,y) | FDiv(x,y) | FEq(x,y) | FLT(x,y) -> S.of_list [x;y]
  | Lfd(x,C(y)) -> S.singleton x
  | Lfd(x,V(y)) -> S.of_list [x;y]
  | Stfd(x,y,C(z)) -> S.of_list [x;y]
  | Stfd(x,y,V(z)) -> S.of_list [x;y;z]
  | IfEq(x,C(y),e1,e2) -> S.add x (S.union (fv e1) (fv e2))
  | IfEq(x,V(y),e1,e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | IfLE(x,C(y),e1,e2) -> S.add x (S.union (fv e1) (fv e2))
  | IfLE(x,V(y),e1,e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | IfGE(x,C(y),e1,e2) -> S.add x (S.union (fv e1) (fv e2))
  | IfGE(x,V(y),e1,e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | IfFEq(x,y,e1,e2)   -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | IfFLE(x,y,e1,e2)   -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | IfZ(x,e1,e2)   -> S.add x  (S.union (fv e1) (fv e2))
  | IfPos(x,e1,e2)   -> S.add x(S.union (fv e1) (fv e2))
  | IfNeg(x,e1,e2)   -> S.add x (S.union (fv e1) (fv e2))
  | CallDir(_,il,fl) -> S.union (S.of_list il) (S.of_list fl)
  | CallDir1(_,il,fl) -> S.union (S.of_list il) (S.of_list fl)
  | CallDir2(_,il,fl) -> S.union (S.of_list il) (S.of_list fl)
  | CallDir3(_,il,fl) -> S.union (S.of_list il) (S.of_list fl)
  | CallCls(x,il,fl) -> S.add x (S.union (S.of_list il) (S.of_list fl))
  | Save(x,y) -> S.of_list [x;y]
  | Restore(x) -> S.singleton x
  | FSqrt(x) | FtoI(x) | ItoF(x) | FFloor(x) | Write(x) -> S.singleton x
  | Read -> S.empty
  | FRead -> S.empty
and fv exp = 
  match exp with
  | Ans(_,e1) -> fv_exp e1
  | Let(_,(x,t),e1,e2) -> S.union (fv_exp e1) (S.remove x (fv e2))*)

let rec effect_exp exp = match exp with
  | Stw(_) | Stfd(_)  | CallCls(_) | CallDir(_) | CallDir1(_) | CallDir2(_) | CallDir3(_) | Save(_) | Write(_) | Read | FRead | Array(_) | FArray(_)-> true
  | IfEq(_,_,e1,e2) -> (effect e1) || (effect e2)
  | IfLE(_,_,e1,e2) -> (effect e1) || (effect e2)
  | IfGE(_,_,e1,e2) -> (effect e1) || (effect e2)
  | IfFEq(_,_,e1,e2) -> (effect e1) || (effect e2)
  | IfFLE(_,_,e1,e2) -> (effect e1) || (effect e2)
  | IfZ(_,e1,e2) -> (effect e1) || (effect e2)
  | IfPos(_,e1,e2) -> (effect e1) || (effect e2)
  | IfNeg(_,e1,e2) -> (effect e1) || (effect e2) 
  | _ -> false
and effect e = match e with
  | Let(_,(x,t),e1,e2) -> effect_exp e1 || effect e2 || (List.mem x (fv_exp e1))
  | Ans(_,e1) -> effect_exp e1

let rec g_exp e = match e with
  | IfEq(x,y,e1,e2)  -> IfEq(x,y,g e1,g e2)
  | IfLE(x,y,e1,e2)  -> IfLE(x,y,g e1,g e2)
  | IfGE(x,y,e1,e2)  -> IfGE(x,y,g e1,g e2)
  | IfFEq(x,y,e1,e2) -> IfFEq(x,y,g e1,g e2)
  | IfFLE(x,y,e1,e2) -> IfFLE(x,y,g e1,g e2)
  | IfZ(x,e1,e2)  -> IfZ(x,g e1,g e2)
  | IfPos(x,e1,e2)  -> IfPos(x,g e1,g e2)
  | IfNeg(x,e1,e2)  -> IfNeg(x,g e1,g e2)
  | x -> x 

and g exp =
  match exp with
  | Ans(pos,e) -> Ans(pos,g_exp e)
  | Let(pos,(x,t),e1,e2) ->
     let e2' = g e2 in
     let e1' = g_exp e1 in
     if ((effect_exp e1') || List.mem x (fv e2') || (is_reg x)) then
       Let(pos,(x,t),e1',e2')
     else
       (Printf.eprintf "eliminate variable %s\n" x; e2')

let h { name = Id.L(x); args = ys; fargs = zs; body = e; ret = t } = 
  let e' = e in
  { name = Id.L(x); args = ys; fargs = zs; body = e'; ret = t }

let f (Prog(data,fundefs,e)) = 
  let fundefs' = List.map h fundefs in
  let e' = g e in
  Prog(data,fundefs',e')