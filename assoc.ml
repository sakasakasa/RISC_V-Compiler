(* flatten let-bindings (just for prettier printing) *)

open KNormal

let rec f (pos, ebody) = (* ネストしたletの簡約 (caml2html: assoc_f) *)
  let body = match ebody with
  | IfEq(x, y, e1, e2) -> IfEq(x, y, f e1, f e2)
  | IfLE(x, y, e1, e2) -> IfLE(x, y, f e1, f e2)
  | IfZ(x, e1, e2) -> IfZ(x, f e1, f e2)
  | IfPos(x, e1, e2) -> IfPos(x, f e1, f e2)
  | IfNeg(x, e1, e2) -> IfNeg(x, f e1, f e2)
  | Let(xt, e1, e2) -> (* letの場合 (caml2html: assoc_let) *)
      let rec insert = function
        | pos', Let(yt, e3, e4) -> Let(yt, e3, (pos', insert e4))
        | pos', LetRec(fundefs, e) -> LetRec(fundefs, (pos', insert e))
        | pos', LetTuple(yts, z, e) -> LetTuple(yts, z, (pos', insert e))
        | e -> Let(xt, e, f e2) in
      insert (f e1)
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
      LetRec({ name = xt; args = yts; body = f e1 }, f e2)
  | LetTuple(xts, y, e) -> LetTuple(xts, y, f e)
  | e -> e
  in 
    (pos, body)
