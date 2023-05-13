(* translation into PowerPC assembly with infinite number of virtual registers *)

open Asm
open Setglobalarray

let data = ref [] (* ��ư��������������ơ��֥� (caml2html: virtual_data) *)

let classify xts ini addf addi =
  List.fold_left
    (fun acc (x, t) ->
      match t with
      | Type.Unit -> acc
      | Type.Float -> addf acc x
      | _ -> addi acc x t)
    ini
    xts

let separate xts =
  classify
    xts
    ([], [])
    (fun (int, float) x -> (int, float @ [x]))
    (fun (int, float) x _ -> (int @ [x], float))

let expand xts ini addf addi =
  classify
    xts
    ini
    (fun (offset, acc) x ->
      let offset = align offset in
      (offset + 4, addf x offset acc))
    (fun (offset, acc) x t ->
      (offset + 4, addi x t offset acc))

let subst a alist= (* globalな変数に対する置換*)
   try (List.assoc a alist) with Not_found -> a

let subst_list aa alist = 
List.map (fun x -> subst x alist) aa

let rec mapping l (a,b)= (* lに含まれる変数について、globalならばmappingを返す。*)
match l with
| [] -> (a,b)
| x::xs -> if List.mem x !globals then 
           let temp = Id.genid "o" in
           mapping xs ((x,temp)::a,Let(0,(temp, Type.Int), Li(List.assoc x !globallist), b))
           else mapping xs (a,b)

let rec subst_dummy exp body = match exp with (* Dummyを関数本体で置換　*)
| Ans(_,Dummy) -> body
| Let(pos,(x,t),e1,e2) -> Let(pos,(x,t),e1,subst_dummy e2 body)
| _ -> failwith "subst_dummy is supported only for Dummy"

let rec g env (pos, ebody) =
  match ebody with (* ���β��ۥޥ��󥳡������� (caml2html: virtual_g) *)
  | Closure.Unit -> Ans(pos, Nop)
  | Closure.Int(i) -> Ans(pos, Li(i))
  | Closure.Float(d) -> Ans(pos, FLi(d))
  | Closure.Neg(x) -> Ans(pos, Neg(x))
  | Closure.And(x, y) -> Ans(pos, And(x, y))
  | Closure.Or(x, y) -> Ans(pos, Or(x, y))
  | Closure.Xor(x, y) -> Ans(pos, Xor(x, y))
  | Closure.AndI(x, y) -> Ans(pos, AndI(x, y))
  | Closure.FAbs(x) -> Ans(pos, FAbs(x))
  | Closure.ItoF(x) -> Ans(pos, ItoF(x))
  | Closure.FtoI(x) -> Ans(pos, FtoI(x))
  | Closure.FSqrt(x) -> Ans(pos, FSqrt(x))
  | Closure.FFloor(x) -> Ans(pos, FFloor(x))
  | Closure.FEq(x, y) -> Ans(pos, FEq(x, y))
  | Closure.FLT(x, y) -> Ans(pos, FLT(x,y))
  | Closure.Read -> Ans(pos, Read)
  | Closure.FRead -> Ans(pos, FRead)
  | Closure.Write(x) -> Ans(pos, Write(x))
  | Closure.Add(x, y) -> Ans(pos, Add(x, V(y)))
  | Closure.Sub(x, y) -> Ans(pos, Sub(x, V(y)))
  | Closure.Mul(x, y) -> Ans(pos, Mul(x, V(y)))
  | Closure.Div(x, y) -> Ans(pos, Div(x, V(y)))
  | Closure.Rem(x, y) -> Ans(pos, Rem(x, y))
  | Closure.FNeg(x) -> Ans(pos, FNeg(x))
  | Closure.FAdd(x, y) -> Ans(pos, FAdd(x, y))
  | Closure.FSub(x, y) -> Ans(pos, FSub(x, y))
  | Closure.FMul(x, y) -> Ans(pos, FMul(x, y))
  | Closure.FDiv(x, y) -> Ans(pos, FDiv(x, y))
  | Closure.IfEq(x, y, e1, e2) ->
      (match M.find x env with
      | Type.Bool | Type.Int -> Ans(pos, IfEq(x, V(y), g env e1, g env e2))
      | Type.Float -> Ans(pos, IfFEq(x, y, g env e1, g env e2))
      | _ -> failwith "equality supported only for bool, int, and float")
  | Closure.IfLE(x, y, e1, e2) ->
      (match M.find x env with
      | Type.Bool | Type.Int -> Ans(pos, IfLE(x, V(y), g env e1, g env e2))
      | Type.Float -> Ans(pos, IfFLE(x, y, g env e1, g env e2))
      | _ -> failwith "inequality supported only for bool, int, and float")
  | Closure.IfZ(x, e1, e2) ->
      (match M.find x env with
      | Type.Bool | Type.Int -> Ans(pos, IfZ(x, g env e1, g env e2))
      | _ -> failwith "inequality supported only for int, and float")
  | Closure.IfPos(x, e1, e2) ->
      (match M.find x env with
      | Type.Bool | Type.Int -> Ans(pos, IfPos(x, g env e1, g env e2))
      | _ -> failwith "inequality supported only for bool, and float")
  | Closure.IfNeg(x, e1, e2) ->
      (match M.find x env with
      | Type.Bool | Type.Int -> Ans(pos, IfNeg(x, g env e1, g env e2))
      | _ -> failwith "inequality supported only for bool, int, and ")
  | Closure.Let((x, t1), e1, e2) ->
      let e1' = g env e1 in
      let e2' = g (M.add x t1 env) e2 in
      concat pos e1' (x, t1) e2'
  | Closure.Var(x) ->
     let (map,exp_dummy) = mapping [x] ([],Ans(0,Dummy)) in
     let asm = 
      (match M.find x env with
      | Type.Unit -> Ans(pos, Nop)
      | Type.Float -> Ans(pos, FMr(subst x map))
      | _ -> Ans(pos, Mr(subst x map))) in
      subst_dummy exp_dummy asm
  | Closure.MakeCls((x, t), { Closure.entry = l; Closure.actual_fv = ys }, e2) -> (* ��������������� (caml2html: virtual_makecls) *)
      (* Closure�Υ��ɥ쥹�򥻥åȤ��Ƥ��顢��ͳ�ѿ����ͤ򥹥ȥ� *)
      let e2' = g (M.add x t env) e2 in
      let offset, store_fv =
        expand
          (List.map (fun y -> (y, M.find y env)) ys)
          (4, e2')
          (fun y offset store_fv -> seq(pos, Stfd(y, x, C(offset)), store_fv))
          (fun y _ offset store_fv -> seq(pos, Stw(y, x, C(offset)), store_fv)) in
      Let(pos, (x, t), Mr(reg_hp),
          Let(pos, (reg_hp, Type.Int), Add(reg_hp, C(align offset)),
              let z = Id.genid "l" in
              Let(pos, (z, Type.Int), SetL(l),
                  seq(pos, Stw(z, x, C(0)),
                      store_fv))))
  | Closure.AppCls(x, ys) ->
      let (map,exp_dummy) = mapping ys ([],Ans(0,Dummy)) in
      let asm = 
      let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
      Ans(pos, CallCls(x, subst_list int map, subst_list float map)) in
      subst_dummy exp_dummy asm
  | Closure.AppDir(Id.L(x), ys) ->
      let (map,exp_dummy) = mapping ys ([],Ans(0,Dummy)) in
      let asm = 
      let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
      Ans(pos, CallDir(Id.L(x), (subst_list int map), (subst_list float map))) in
      subst_dummy exp_dummy asm
  | Closure.Tuple(xs) -> (* �Ȥ����� (caml2html: virtual_tuple) *)
      let y = Id.genid "t" in
      let (offset, store) =
        expand
          (List.map (fun x -> (x, M.find x env)) xs)
          (0, Ans(pos, Mr(y)))
          (fun x offset store -> seq(pos, Stfd(x, y, C(offset)), store))
          (fun x _ offset store -> seq(pos, Stw(x, y, C(offset)), store))  in
      Let(pos, (y, Type.Tuple(List.map (fun x -> M.find x env) xs)), Mr(reg_hp),
          Let(pos, (reg_hp, Type.Int), Add(reg_hp, C(align offset)),
              store))
  | Closure.LetTuple(xts, y, e2) ->
      let (map,exp_dummy) = mapping [y] ([],Ans(0,Dummy)) in
      let asm = 
      let s = Closure.fv e2 in
      let (offset, load) =
        expand
          xts
          (0, g (M.add_list xts env) e2)
          (fun x offset load ->
            if not (S.mem x s) then load else (* [XX] a little ad hoc optimization *)
            fletd(pos, x, Lfd(subst y map, C(offset)), load))
          (fun x t offset load ->
            if not (S.mem x s) then load else (* [XX] a little ad hoc optimization *)
            Let(pos, (x, t), Lwz(subst y map, C(offset)), load)) in
      load in
      subst_dummy exp_dummy asm
  | Closure.Array(x, y) ->
     let (map,exp_dummy) = mapping [y] ([],Ans(0,Dummy)) in
     let asm = 
       (match M.find y env with
       | Type.Unit -> Ans(pos, Nop)
       | Type.Float -> Ans(pos, FArray(x, subst y map))
       | _ -> Ans(pos, Array(x, subst y map))) in
       subst_dummy exp_dummy asm
  | Closure.Get(x, y) -> (* ������ɤ߽Ф� (caml2html: virtual_get) *)
      let (map,exp_dummy) = mapping [x] ([],Ans(0,Dummy)) in
      let offset = Id.genid "o" in
      let asm = 
      (match M.find x env with
      | Type.Array(Type.Unit) -> Ans(pos, Nop)
      | Type.Array(Type.Float) ->
          Let(pos, (offset, Type.Int), Slw(y, C(2)),
              Ans(pos, Lfd(subst x map, V(offset))))
      | Type.Array(_) ->
          Let(pos, (offset, Type.Int), Slw(y, C(2)),
              Ans(pos, Lwz(subst x map, V(offset))))
      | _ -> assert false) in
      subst_dummy exp_dummy asm
  | Closure.Put(x, y, z) ->
      let (map,exp_dummy) = mapping [x;z] ([],Ans(0,Dummy)) in
      let offset = Id.genid "o" in
      let asm = 
      (match M.find x env with
      | Type.Array(Type.Unit) -> Ans(pos, Nop)
      | Type.Array(Type.Float) ->
          Let(pos, (offset, Type.Int), Slw(y, C(2)),
              Ans(pos, Stfd(subst z map, subst x map, V(offset))))
      | Type.Array(_) ->
          Let(pos, (offset, Type.Int), Slw(y, C(2)),
              Ans(pos, Stw(subst z map, subst x map, V(offset))))
      | _ -> assert false) in
      subst_dummy exp_dummy asm
  | Closure.ExtArray(Id.L(x)) -> Ans(pos, SetL(Id.L("min_caml_" ^ x)))

(* �ؿ��β��ۥޥ��󥳡������� (caml2html: virtual_h) *)

  | _ -> assert false

(* �ץ���������Τβ��ۥޥ��󥳡������� (caml2html: virtual_f) *)
  let print_id_or_imm outchan ioi = 
    match ioi with
    | (V r) -> Printf.fprintf outchan "V %s" r
    | (C i) -> Printf.fprintf outchan "C %d" i
  
  let rec print_id_list outchan tl = 
    match tl with 
    | [] -> ()
    | t::rest -> (
      Printf.fprintf outchan "  %s\n" t;
      print_id_list outchan rest
    )
  
  let rec print_exp outchan e =
    match e with
    | Nop -> Printf.fprintf outchan "Nop\n"
    | Li(i) -> Printf.fprintf outchan "Li %d\n" i
    | FLi(l) -> Printf.fprintf outchan "Fli %f\n" l
    | SetL(Id.L(l)) -> Printf.fprintf outchan "SetL %s\n" l
    | Mr(x) -> Printf.fprintf outchan "Mr %s\n" x
    | Neg(x) -> Printf.fprintf outchan "Neg %s\n" x
    | Add(x,ioi) -> (
        Printf.fprintf outchan "Add %s " x;
        print_id_or_imm outchan ioi;
        Printf.fprintf outchan "\n"
      )
    | Sub(x,ioi) -> (
        Printf.fprintf outchan "Sub %s " x;
        print_id_or_imm outchan ioi;
        Printf.fprintf outchan "\n"
      )
    | Mul(x,ioi) -> (
        Printf.fprintf outchan "Mul %s " x;
        print_id_or_imm outchan ioi;
        Printf.fprintf outchan "\n"
      )
    | Div(x,ioi) -> (
        Printf.fprintf outchan "Div %s " x;
        print_id_or_imm outchan ioi;
        Printf.fprintf outchan "\n"
      )
    | Slw(x,ioi) -> (
        Printf.fprintf outchan "Slw %s " x;
        print_id_or_imm outchan ioi;
        Printf.fprintf outchan "\n"
      )
    | Lwz(x,ioi) -> (
        Printf.fprintf outchan "Lwz %s " x;
        print_id_or_imm outchan ioi;
        Printf.fprintf outchan "\n"
      )
    | Stw(x,y,ioi) -> (
        Printf.fprintf outchan "Stw %s %s " x y;
        print_id_or_imm outchan ioi;
        Printf.fprintf outchan "\n"
      )
    | FMr(x) -> Printf.fprintf outchan "FMr %s\n" x
    | FNeg(x) -> Printf.fprintf outchan "FNeg %s\n" x
    | FAdd(x,y) -> Printf.fprintf outchan "FAdd %s %s\n" x y
    | FSub(x,y) -> Printf.fprintf outchan "FSub %s %s\n" x y
    | FMul(x,y) -> Printf.fprintf outchan "FMul %s %s\n" x y
    | FDiv(x,y) -> Printf.fprintf outchan "FDiv %s %s\n" x y
    | Lfd(x,ioi) -> (
        Printf.fprintf outchan "Lfd %s " x;
        print_id_or_imm outchan ioi;
        Printf.fprintf outchan "\n"
      )
    | Stfd(x,y,ioi) -> (
        Printf.fprintf outchan "Stfd %s %s " x y;
        print_id_or_imm outchan ioi;
        Printf.fprintf outchan "\n"
      )
    | Comment(s) -> (
        Printf.fprintf outchan "%s\n" s
      )
    (* virtual instructions *)
    | IfEq (x,ioi,e1,e2) ->
        (
          Printf.fprintf outchan "IfEq %s " x;
          print_id_or_imm outchan ioi;
          Printf.fprintf outchan "\n";
          print_syntax outchan e1;
          print_syntax outchan e2
        )
    | IfLE (x,ioi,e1,e2) ->
        (
          Printf.fprintf outchan "IfLE %s " x;
          print_id_or_imm outchan ioi;
          Printf.fprintf outchan "\n";
          print_syntax outchan e1;
          print_syntax outchan e2
        )
    | IfGE (x,ioi,e1,e2) ->
        (
          Printf.fprintf outchan "IfGE %s " x;
          print_id_or_imm outchan ioi;
          Printf.fprintf outchan "\n";
          print_syntax outchan e1;
          print_syntax  outchan e2
        )
    | IfFEq (x,y,e1,e2) ->
        (
          Printf.fprintf outchan "IfFEq %s %s\n" x y;
          print_syntax outchan e1;
          print_syntax outchan e2
        )
    | IfFLE (x,y,e1,e2) ->
        (
          Printf.fprintf outchan "IfFLE %s %s\n" x y;
          print_syntax outchan e1;
          print_syntax outchan e2
        )
    | CallDir (Id.L(l),xl,yl) ->
        (
          Printf.fprintf outchan "CallDir %s\n" l;
          Printf.fprintf outchan "int args\n";
          print_id_list outchan xl;
          Printf.fprintf outchan "float args\n";
          print_id_list outchan yl
        )
  
    | _ -> Printf.fprintf outchan "others\n"
    (* 
    | CallCls of Id.t * Id.t list * Id.t list
    | CallDir of Id.l * Id.t list * Id.t list
    | Save of Id.t * Id.t 
    | Restore of Id.t *)
  and print_syntax outchan exp =
    match exp with
    | Ans (_,e) -> (
      Printf.fprintf outchan "Ans\n";
      print_exp outchan e
    )
    | Let (_,(x,t),e,sy) -> (
      Printf.fprintf outchan "Let\n";
      Printf.fprintf outchan "%s\n" x;
      print_exp outchan e;
      print_syntax outchan sy
    )

let h { Closure.name = (Id.L(x), t); Closure.args = yts; Closure.formal_fv = zts; Closure.body = e } =
  let (pos, ebody) = e in
  let (int, float) = separate yts in
  let (offset, load) =
    let zs = fst(List.split zts) in if list_include zs !globals then
      expand
        zts
        (4, g (M.add x t (M.add_list yts (M.add_list zts M.empty))) e)
        (fun z offset load -> load)
        (fun z t offset load -> load)
      else
      expand
        zts
        (4, g (M.add x t (M.add_list yts (M.add_list zts M.empty))) e)
        (fun z offset load ->  fletd(pos, z, Lfd(x, C(offset)), load))
        (fun z t offset load ->  Let(pos, (z, t), Lwz(x, C(offset)), load)) in
  match t with
    | Type.Fun(_, t2) ->
        (*Printf.fprintf stdout "----------------Function = %s\n" x;
        print_syntax stdout load;*)
        { name = Id.L(x); args = int; fargs = float; body = load ; ret = t2 }
    | _ -> assert false
    
let f (Closure.Prog(fundefs, e)) =
  data := [];
  let fundefs = List.map h fundefs in
  let e = g M.empty e in
  Prog(!data, fundefs, e)
    
