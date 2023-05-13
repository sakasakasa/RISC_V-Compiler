open KNormal

(* インライン展開する関数の最大サイズ (caml2html: inline_threshold) *)
let threshold = ref 100 (* Mainで-inlineオプションによりセットされる *)

let rec size = function
  | IfEq(_, _, (_, e1), (_, e2)) | IfLE(_, _, (_, e1), (_, e2)) | IfZ(_,(_,e1),(_,e2)) | IfPos(_,(_,e1),(_,e2)) | IfNeg(_,(_,e1),(_,e2))
  | Let(_, (_, e1), (_, e2)) | LetRec({ body = (_, e1) }, (_, e2)) -> 1 + size e1 + size e2
  | LetTuple(_, _, (_, e)) -> 1 + size e
  | _ -> 1

let rec g env (pos, ebody) =
  let body = match ebody with (* インライン展開ルーチン本体 (caml2html: inline_g) *)
  | IfEq(x, y, e1, e2) -> IfEq(x, y, g env e1, g env e2)
  | IfLE(x, y, e1, e2) -> IfLE(x, y, g env e1, g env e2)
  | IfZ(x, e1, e2) -> IfZ(x, g env e1, g env e2)
  | IfPos(x, e1, e2) -> IfPos(x, g env e1, g env e2)
  | IfNeg(x, e1, e2) -> IfNeg(x, g env e1, g env e2)
  | Let(xt, e1, e2) -> Let(xt, g env e1, g env e2)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
      let (_, e1body) = e1 in (* 関数定義の場合 (caml2html: inline_letrec) *)
      let env = if size e1body > !threshold then env else M.add x (yts, e1) env in
      LetRec({ name = (x, t); args = yts; body = g env e1}, g env e2)
  | App(x, ys) when M.mem x env -> (* 関数適用の場合 (caml2html: inline_app) *)
      let (zs, e) = M.find x env in
      Format.eprintf "inlining %s@." x;
      let env' =
        List.fold_left2
          (fun env' (z, t) y -> M.add z y env')
          M.empty
          zs
          ys in
      snd (Alpha.g env' e)
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env e)
  | e -> e
  in 
    (pos, body)

let f e = g M.empty e
