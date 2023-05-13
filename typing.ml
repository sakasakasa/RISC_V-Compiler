(* type inference/reconstruction *)

open Syntax

exception Unify of int * Type.t * Type.t
exception Error of int * t * Type.t * Type.t

let extenv = ref M.empty

(* for pretty printing (and type normalization) *)
let rec deref_typ = function (* 型変数を中身でおきかえる関数 (caml2html: typing_deref) *)
  | Type.Fun(t1s, t2) -> Type.Fun(List.map deref_typ t1s, deref_typ t2)
  | Type.Tuple(ts) -> Type.Tuple(List.map deref_typ ts)
  | Type.Array(t) -> Type.Array(deref_typ t)
  | Type.Var({ contents = None } as r) ->
      Format.eprintf "uninstantiated type variable detected; assuming int@.";
      r := Some(Type.Int);
      Type.Int
  | Type.Var({ contents = Some(t) } as r) ->
      let t' = deref_typ t in
      r := Some(t');
      t'
  | t -> t
let rec deref_id_typ (x, t) = (x, deref_typ t)
let rec deref_term (pos, ebody) =
  match ebody with
  | Not(e) -> pos, Not(deref_term e)
  | Neg(e) -> pos, Neg(deref_term e)
  | And(e1,e2) -> pos, And(deref_term e1, deref_term e2)
  | Or(e1,e2) -> pos, Or(deref_term e1, deref_term e2)
  | Xor(e1,e2) -> pos, Xor(deref_term e1, deref_term e2)
  | AndI(e1,e2) -> pos, AndI(deref_term e1, e2)
  | FAbs(e) -> pos, FAbs(deref_term e)
  | ItoF(e) -> pos,  ItoF(deref_term e)
  | FtoI(e) -> pos, FtoI(deref_term e)
  | FSqrt(e) -> pos, FSqrt(deref_term e)
  | FEq(e1,e2) -> pos, FEq(deref_term e1, deref_term e2)
  | FLT(e1,e2) -> pos, FLT(deref_term e1, deref_term e2)
  | Read -> pos, Read
  | FRead -> pos, FRead
  | Write(e) -> pos, Write(deref_term e) 
  | Add(e1, e2) -> pos, Add(deref_term e1, deref_term e2)
  | Sub(e1, e2) -> pos, Sub(deref_term e1, deref_term e2)
  | Eq(e1, e2) -> pos, Eq(deref_term e1, deref_term e2)
  | LE(e1, e2) -> pos, LE(deref_term e1, deref_term e2)
  | FNeg(e) -> pos, FNeg(deref_term e)
  | FAdd(e1, e2) -> pos, FAdd(deref_term e1, deref_term e2)
  | FSub(e1, e2) -> pos, FSub(deref_term e1, deref_term e2)
  | FMul(e1, e2) -> pos, FMul(deref_term e1, deref_term e2)
  | FDiv(e1, e2) -> pos, FDiv(deref_term e1, deref_term e2)
  | If(e1, e2, e3) -> pos, If(deref_term e1, deref_term e2, deref_term e3)
  | Let(xt, e1, e2) -> pos, Let(deref_id_typ xt, deref_term e1, deref_term e2)
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
        pos, LetRec({ name = deref_id_typ xt;
               args = List.map deref_id_typ yts;
               body = deref_term e1 },
             deref_term e2)
  | App(e, es) -> pos, App(deref_term e, List.map deref_term es)
  | Tuple(es) -> pos, Tuple(List.map deref_term es)
  | LetTuple(xts, e1, e2) -> pos, LetTuple(List.map deref_id_typ xts, deref_term e1, deref_term e2)
  | Array(e1, e2) -> pos, Array(deref_term e1, deref_term e2)
  | Get(e1, e2) -> pos, Get(deref_term e1, deref_term e2)
  | Put(e1, e2, e3) -> pos, Put(deref_term e1, deref_term e2, deref_term e3)
  | e -> pos, e

let rec occur r1 = function (* occur check (caml2html: typing_occur) *)
  | Type.Fun(t2s, t2) -> List.exists (occur r1) t2s || occur r1 t2
  | Type.Tuple(t2s) -> List.exists (occur r1) t2s
  | Type.Array(t2) -> occur r1 t2
  | Type.Var(r2) when r1 == r2 -> true
  | Type.Var({ contents = None }) -> false
  | Type.Var({ contents = Some(t2) }) -> occur r1 t2
  | _ -> false

let rec unify pos t1 t2 = (* 型が合うように、型変数への代入をする (caml2html: typing_unify) *)
  match t1, t2 with
  | Type.Unit, Type.Unit | Type.Bool, Type.Bool | Type.Int, Type.Int | Type.Float, Type.Float -> ()
  | Type.Fun(t1s, t1'), Type.Fun(t2s, t2') ->
      (try List.iter2 (unify pos) t1s t2s
      with Invalid_argument(_) -> raise (Unify(pos,t1, t2)));
      unify pos t1' t2'
  | Type.Tuple(t1s), Type.Tuple(t2s) ->
      (try List.iter2 (unify pos) t1s t2s
      with Invalid_argument(_) -> raise (Unify(pos,t1, t2)))
  | Type.Array(t1), Type.Array(t2) -> unify pos t1 t2
  | Type.Var(r1), Type.Var(r2) when r1 == r2 -> ()
  | Type.Var({ contents = Some(t1') }), _ -> unify pos t1' t2
  | _, Type.Var({ contents = Some(t2') }) -> unify pos t1 t2'
  | Type.Var({ contents = None } as r1), _ -> (* 一方が未定義の型変数の場合 (caml2html: typing_undef) *)
      if occur r1 t2 then raise (Unify(pos,t1, t2));
      r1 := Some(t2)
  | _, Type.Var({ contents = None } as r2) ->
      if occur r2 t1 then raise (Unify(pos,t1, t2));
      r2 := Some(t1)
  | _, _ -> raise (Unify(pos,t1, t2))

let rec g pos env e = (* 型推論ルーチン (caml2html: typing_g) *)
  try
    match e with
    | Unit -> Type.Unit
    | Bool(_) -> Type.Bool
    | Int(_) -> Type.Int
    | Float(_) -> Type.Float
    | Not(pos1, e) ->
        unify pos Type.Bool (g pos env e);
        Type.Bool
    | And((pos1,e1),(pos2,e2)) -> 
        unify pos Type.Bool (g pos1 env e1);
        unify pos Type.Bool (g pos2 env e2);
        Type.Bool
    | Or((pos1,e1),(pos2,e2)) -> 
        unify pos Type.Bool (g pos1 env e1);
        unify pos Type.Bool (g pos2 env e2);
        Type.Bool
    | Xor((pos1,e1),(pos2,e2)) -> 
        unify pos Type.Bool (g pos1 env e1);
        unify pos Type.Bool (g pos2 env e2);
        Type.Bool
    | AndI((pos1,e1),e2) -> 
        unify pos Type.Int (g pos1 env e1);
        Type.Int
    | FAbs((pos1,e)) ->
        unify pos Type.Float (g pos1 env e);
        Type.Float
    | FFloor((pos1,e)) ->
        unify pos Type.Float (g pos1 env e);
        Type.Float
    | ItoF((pos1,e)) -> 
        unify pos Type.Int (g pos1 env e);
        Type.Float
    | FtoI((pos1,e)) -> 
        unify pos Type.Float (g pos1 env e);
        Type.Int
    | FSqrt((pos1,e)) -> 
        unify pos Type.Float (g pos1 env e);
        Type.Float
    | FEq((pos1,e1),(pos2,e2)) -> 
        unify pos Type.Float (g pos1 env e1);
        unify pos Type.Float (g pos2 env e2);
        Type.Bool
    | FLT((pos1,e1),(pos2,e2)) -> 
        unify pos Type.Float (g pos1 env e1);
        unify pos Type.Float (g pos2 env e2);
        Type.Bool
    | Read -> Type.Int
    | FRead -> Type.Float
    | Write((_,e)) -> 
         unify pos Type.Int (g pos env e);
         Type.Unit
    | Neg(pos1, e) ->
        unify pos Type.Int (g pos1 env e);
        Type.Int
    | Add((pos1, e1), (pos2, e2)) | Sub((pos1, e1), (pos2, e2)) | Mul((pos1, e1), (pos2, e2)) | Div((pos1, e1), (pos2, e2)) | Rem((pos1, e1), (pos2, e2))  -> (* 足し算（と引き算）の型推論 (caml2html: typing_add) *)
        unify pos Type.Int (g pos1 env e1);
        unify pos Type.Int (g pos2 env e2);
        Type.Int
    | FNeg(pos1, e) ->
        unify pos Type.Float (g pos1 env e);
        Type.Float
    | FAdd((pos1, e1), (pos2, e2)) | FSub((pos1, e1), (pos2, e2)) | FMul((pos1, e1), (pos2, e2)) | FDiv((pos1, e1), (pos2, e2)) ->
        unify pos Type.Float (g pos1 env e1);
        unify pos Type.Float (g pos2 env e2);
        Type.Float
    | Eq((pos1, e1), (pos2, e2)) | LE((pos1, e1), (pos2, e2)) ->
        unify pos (g pos1 env e1) (g pos2 env e2);
        Type.Bool
    | If((pos1, e1), (pos2, e2), (pos3, e3)) ->
        unify pos (g pos1 env e1) Type.Bool;
        let t2 = g pos2 env e2 in
        let t3 = g pos3 env e3 in
        unify pos t2 t3;
        t2
    | Let((x, t), (pos1, e1), (pos2, e2)) -> (* letの型推論 (caml2html: typing_let) *)
        unify pos t (g pos1 env e1);
        g pos2 (M.add x t env) e2
    | Var(x) when M.mem x env -> M.find x env (* 変数の型推論 (caml2html: typing_var) *)
    | Var(x) when M.mem x !extenv -> M.find x !extenv
    | Var(x) -> (* 外部変数の型推論 (caml2html: typing_extvar) *)
        Format.eprintf "free variable %s assumed as external@." x;
        let t = Type.gentyp () in
        extenv := M.add x t !extenv;
        t
    | LetRec({ name = (x, t); args = yts; body = (pos1, e1) }, (pos2, e2)) -> (* let recの型推論 (caml2html: typing_letrec) *)
        let env = M.add x t env in
        unify pos t (Type.Fun(List.map snd yts, g pos1 (M.add_list yts env) e1));
        g pos2 env e2
    | App((pos1, e), es) -> (* 関数適用の型推論 (caml2html: typing_app) *)
        let t = Type.gentyp () in
        unify pos (g pos1 env e) (Type.Fun(List.map (fun (pos2, ebody) -> g pos2 env ebody) es, t));
        t
    | Tuple(es) -> Type.Tuple(List.map (fun (pos1, ebody) -> g pos1 env ebody) es)
    | LetTuple(xts, (pos1, e1), (pos2, e2)) ->
        unify pos (Type.Tuple(List.map snd xts)) (g pos1 env e1);
        g pos2 (M.add_list xts env) e2
    | Array((pos1, e1), (pos2, e2)) -> (* must be a primitive for "polymorphic" typing *)
        unify pos (g pos1 env e1) Type.Int;
        Type.Array(g pos2 env e2)
    | Get((pos1, e1), (pos2, e2)) ->
        let t = Type.gentyp () in
        unify pos (Type.Array(t)) (g pos1 env e1);
        unify pos Type.Int (g pos2 env e2);
        t
    | Put((pos1, e1), (pos2, e2), (pos3, e3)) ->
        let t = g pos3 env e3 in
        unify pos (Type.Array(t)) (g pos1 env e1);
        unify pos Type.Int (g pos2 env e2);
        Type.Unit
  with Unify(pos1,t1, t2) -> raise (Error(pos,deref_term (0, e), deref_typ t1, deref_typ t2))

let f (pos, e) =
  extenv := M.empty;
(*
  (match deref_typ (g M.empty e) with
  | Type.Unit -> ()
  | _ -> Format.eprintf "warning: final result does not have type unit@.");
*)
  (try unify pos Type.Unit (g pos M.empty e)
  with Unify _ -> failwith "top level does not have type unit");
  extenv := M.map deref_typ !extenv;
  deref_term (pos, e)
