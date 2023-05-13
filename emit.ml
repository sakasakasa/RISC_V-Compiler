open Asm
open Id

external gethi : float -> int32 = "gethi"
external getlo : float -> int32 = "getlo"
external get_upper : float -> int32 = "get_upper"
external get_lower : float -> int32 = "get_lower"

let stackset = ref S.empty (* すでにSaveされた変数の集合 (caml2html: emit_stackset) *)
let stackmap = ref ["dummy"] (* Saveされた変数の、スタックにおける位置 (caml2html: emit_stackmap) *)
let save x =
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]
let savef x =
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    (let pad =
      if List.length !stackmap mod 2 = 0 then [] else ["dummy for float"] in
    stackmap := !stackmap @ pad @ [x; x])
let locate x =
  let rec loc = function
    | [] -> []
    | y :: zs when x = y -> 0 :: List.map succ (loc zs)
    | y :: zs -> List.map succ (loc zs) in
  loc !stackmap
let offset x = 4 * List.hd (locate x)
let stacksize () = align ((List.length !stackmap + 1) * 4)

let reg r =
  if is_reg r
  then String.sub r 1 (String.length r - 1)
  else r

let upper n = (n asr 12 + if n land (1 lsl 11) = 0 then 0 else 1) * 4096
let lower n = (n lsl 51) asr 51

let address_list = Hashtbl.create 0

let pc = ref 8
let pcincr () = let n = !pc in pc := n + 4; n
let jpc = ref 8
let jpincr() = (jpc := !jpc + 4)

let check = ref 1 (*0のときsaveあり*)
let check2 = ref 1 (* 0のときSaveがあった　*)

type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 (caml2html: emit_dest) *)
let rec f_nop dest e = match (dest,e) with
| (_,Ans(_,Nop))-> true
| (NonTail(x),Ans(_,Mr(y))) when x = y -> true
| (NonTail(x),Ans(_,FMr(y))) when x = y -> true
| (NonTail(x),(Let(_,(x',t'),Mr(y),e1))) when x' = y -> f_nop (NonTail(x)) e1
| (NonTail(x),(Let(_,(x',t'),FMr(y),e1))) when x' = y -> f_nop (NonTail(x)) e1
| (NonTail(x),Let(_,(x',t'),Nop,e1)) -> f_nop (NonTail(x)) e1
| _ -> false

let load_label pos r label =
  let r' = reg r in
  try
    (Printf.sprintf
      "%d\tlui\t%s, %d\t\t! %d\n%d\taddi\t%s, %s, %d\t\t! %d\n"
      (pcincr()) r' (upper(Hashtbl.find address_list label)) pos (pcincr()) r' r' (lower(Hashtbl.find address_list label)) pos)
  with Not_found -> Printf.printf "LABEL %s NOT FOUND\n" label; Printf.sprintf "Label "^label^" NOT_FOUND\n"


(* 関数呼び出しのために引数を並べ替える(register shuffling) (caml2html: emit_shuffle) *)
let rec shuffle sw xys =
  (* remove identical moves *)
  let _, xys = List.partition (fun (x, y) -> x = y) xys in
  (* find acyclic moves *)
  match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with
  | [], [] -> []
  | (x, y) :: xys, [] -> (* no acyclic moves; resolve a cyclic move *)
      (y, sw) :: (x, y) :: shuffle sw (List.map
                                         (function
                                           | (y', z) when y = y' -> (sw, z)
                                           | yz -> yz)
                                         xys)
  | xys, acyc -> acyc @ shuffle sw xys


let rec g oc = function (* 命令列のアセンブリ生成 (caml2html: emit_g) *)
  | dest, Ans(pos, exp) -> g' oc pos (dest, exp)
  | dest, Let(pos, (x, t), exp, e) ->
  if Peephole.occur2 e then check := 1 else check := 0;
      g' oc pos (NonTail(x), exp);
      (*Printf.fprintf oc "check = %d\n" !check;
      Printf.fprintf oc "check2 = %d\n" !check2;*)
      g oc (dest, e)
and g' oc pos e =
  (* print_int pos; *)
  match e with
  (* 各命令のアセンブリ生成 (caml2html: emit_gprime) *)
  (* 末尾でなかったら計算結果をdestにセット (caml2html: emit_nontail) *)
  | NonTail(_), Nop -> ()
  | NonTail(x), Li(n) ->
      let u = upper n in
      let l = lower n in
      if u = 0 then
        Printf.fprintf oc "%d\taddi\t%s, x0, %d\t\t! %d\n" (pcincr()) (reg x) l pos
      else
        (Printf.fprintf oc "%d\tlui\t%s, %d\t\t! %d\n" (pcincr()) (reg x) u pos;
        if l <> 0 then
          Printf.fprintf oc "%d\taddi\t%s, %s, %d\t\t! %d\n"(pcincr()) (reg x) (reg x) l pos)
  | NonTail(x), FLi(d) ->
      let u = Int32.to_int(get_upper d) * 4096 in
      let l = Int32.to_int(get_lower d) in
      if u = 0 && (l <> 0)then 
        (Printf.fprintf oc "%d\taddi\tx31, x0, %d\t\t! %d\n" (pcincr())  l pos;
        Printf.fprintf oc "%d\timvf\t%s, x31\t\t! %d\n" (pcincr()) (reg x) pos)
      else if u = 0 then 
        Printf.fprintf oc "%d\timvf\t%s, x0\t\t! %d\n" (pcincr()) (reg x) pos
      else
         (Printf.fprintf oc "%d\tlui\tx31, %d\t\t! %d\n" (pcincr()) u pos;
         (if l <> 0 then
            Printf.fprintf oc "%d\taddi\tx31, x31, %d\t\t! %d\n"(pcincr()) l pos);
            Printf.fprintf oc "%d\timvf\t%s, x31\t\t! %d\n" (pcincr()) (reg x) pos )
  | NonTail(x), SetL(Id.L(y)) ->
      let s = load_label pos x y in
      Printf.fprintf oc "%s" s
  | NonTail(x), Mr(y) when x = y -> () 
  | NonTail(x), Mr(y) -> Printf.fprintf oc "%d\taddi\t%s, %s, 0\t\t! %d\n" (pcincr()) (reg x) (reg y) pos
  | NonTail(x), Neg(y) -> Printf.fprintf oc "%d\tsub\t%s, x0, %s\t\t! %d\n" (pcincr())(reg x) (reg y) pos
  | NonTail(x), And(y, z) -> Printf.fprintf oc "%d\tand\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos
  | NonTail(x), Or(y, z) -> Printf.fprintf oc "%d\tor\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos
  | NonTail(x), Xor(y, z) -> Printf.fprintf oc "%d\txor\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos
  | NonTail(x), AndI(y, z) -> Printf.fprintf oc "%d\tandi\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg x) (reg y) z pos
  | NonTail(x), FAbs(y) -> Printf.fprintf oc "%d\tfsgnjx\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg y) pos
  | NonTail(x), ItoF(y) -> Printf.fprintf oc "%d\titof\t%s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) pos
  | NonTail(x), FtoI(y) -> Printf.fprintf oc "%d\tftoi\t%s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) pos
  | NonTail(x), FSqrt(y) -> Printf.fprintf oc "%d\tfsqrt\t%s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) pos
  | NonTail(x), FFloor(y) -> Printf.fprintf oc "%d\tffloor\t%s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) pos
  | NonTail(x), FEq(y, z) -> Printf.fprintf oc "%d\tfeq\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos
  | NonTail(x), FLT(y, z) -> Printf.fprintf oc "%d\tflt\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos
  (*Read, FRead, Write *)
  | NonTail(x), Read -> Printf.fprintf oc "%d\tinw\t%s\t\t! %d\n" (pcincr()) (reg x) pos
  | NonTail(x), FRead -> Printf.fprintf oc "%d\tinf\t%s\t\t! %d\n" (pcincr()) (reg x) pos
  | NonTail(x), Write(y) -> Printf.fprintf oc "%d\toutb\t%s\t\t! %d\n" (pcincr()) (reg y) pos
  | NonTail(x), Add(y, V(z)) -> Printf.fprintf oc "%d\tadd\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos
  | NonTail(x), Add(y, C(z)) -> Printf.fprintf oc "%d\taddi\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg x) (reg y) z pos
  | NonTail(x), Sub(y, V(z)) -> Printf.fprintf oc "%d\tsub\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos
  | NonTail(x), Sub(y, C(z)) -> Printf.fprintf oc "%d\taddi\t%s, %s, -%d\t\t! %d\n" (pcincr()) (reg x) (reg y) z pos
  | NonTail(x), Div(y, V(z)) -> Printf.fprintf oc "%d\tdivu\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos
  | NonTail(x), Rem(y, z) -> Printf.fprintf oc "%d\tremu\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos
  | NonTail(x), Array(y, z) ->  if y = x then
                              (Printf.fprintf oc "%d\taddi\tx30, x3, 0\t\t! %d\n" (pcincr()) pos;
                               Printf.fprintf oc "%d\tbeq\t%s, x0, 20\t\t! %d\n" (pcincr()) (reg y) pos;
                               Printf.fprintf oc "%d\tsw\tx3, %s, 0\t\t! %d\n" (pcincr()) (reg z) pos;
                               Printf.fprintf oc "%d\taddi\tx3, x3, 4\t\t! %d\n" (pcincr()) pos;(*hp += 4*)
                               Printf.fprintf oc "%d\taddi\t%s, %s, -1\t\t! %d\n" (pcincr()) (reg y) (reg y)pos;
                               Printf.fprintf oc "%d\tjal\tx0, -16\t\t! %d\n" (pcincr()) pos;
                               Printf.fprintf oc "%d\taddi\t%s, x30, 0\t\t! %d\n" (pcincr()) (reg x) pos)
                               else
                              (Printf.fprintf oc "%d\taddi\tx30, x3, 0\t\t! %d\n" (pcincr()) pos;
                               Printf.fprintf oc "%d\tadd\tx31, x0, %s\t\t! %d\n" (pcincr()) (reg y) pos;
                               Printf.fprintf oc "%d\tbeq\tx31, x0, 20\t\t! %d\n" (pcincr()) pos;
                               Printf.fprintf oc "%d\tsw\tx3, %s, 0\t\t! %d\n" (pcincr()) (reg z) pos;
                               Printf.fprintf oc "%d\taddi\tx3, x3, 4\t\t! %d\n" (pcincr()) pos;(*hp += 4*)
                               Printf.fprintf oc "%d\taddi\tx31, x31, -1\t\t! %d\n" (pcincr()) pos;
                               Printf.fprintf oc "%d\tjal\tx0, -16\t\t! %d\n" (pcincr()) pos;
                               Printf.fprintf oc "%d\taddi\t%s, x30, 0\t\t! %d\n" (pcincr()) (reg x) pos)
  | NonTail(x), FArray(y, z) -> 
                               Printf.fprintf oc "%d\taddi\tx30, x3, 0\t\t! %d\n" (pcincr()) pos;
                               Printf.fprintf oc "%d\tadd\tx31, x0, %s\t\t! %d\n" (pcincr()) (reg y) pos;
                               Printf.fprintf oc "%d\tbeq\tx31, x0, 20\t\t! %d\n" (pcincr()) pos;
                               Printf.fprintf oc "%d\tfsw\tx3, %s, 0\t\t! %d\n" (pcincr()) (reg z) pos;
                               Printf.fprintf oc "%d\taddi\tx3, x3, 4\t\t! %d\n" (pcincr()) pos;
                               Printf.fprintf oc "%d\taddi\tx31, x31, -1\t\t! %d\n" (pcincr()) pos;
                               Printf.fprintf oc "%d\tjal\tx0, -16\t\t! %d\n" (pcincr()) pos;
                               Printf.fprintf oc "%d\taddi\t%s, x30, 0\t\t! %d\n" (pcincr()) (reg x) pos
  | NonTail(x), Slw(y, V(z)) -> Printf.fprintf oc "%d\tsll\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos(* TODO: RISC-V *)
  | NonTail(x), Slw(y, C(z)) -> Printf.fprintf oc "%d\tslli\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg x) (reg y) z pos (* TODO: RISC-V *)
  | NonTail(x), Sra(y, C(z)) -> Printf.fprintf oc "%d\tsrai\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg x) (reg y) z pos 
  | NonTail(x), Lwz(y, V(z)) -> 
      Printf.fprintf oc "%d\tadd\tx31, %s, %s\t\t! %d\n" (pcincr()) (reg y) (reg z) pos;
      Printf.fprintf oc "%d\tlw\t%s, x31, 0\t\t! %d\n" (pcincr()) (reg x)  pos
  | NonTail(x), Lwz(y, C(z)) -> 
    (if -2048 <= z && z < 2048 then
      Printf.fprintf oc "%d\tlw\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg x) (reg y) z pos
     else 
      (let u = upper z in
       let l = lower z in
       (Printf.fprintf oc "%d\tlui\tx31, %d\t\t! %d\n" (pcincr()) u pos;
        if l <> 0 then
          Printf.fprintf oc "%d\taddi\tx31, x31, %d\t\t! %d\n"(pcincr())  l pos);
          Printf.fprintf oc "%d\tadd\tx30, %s, x31\t\t! %d\n" (pcincr()) (reg y)  pos;
          Printf.fprintf oc "%d\tlw\t%s, x30, 0\t\t! %d\n" (pcincr()) (reg x) pos
))
  | NonTail(_), Stw(x, y, V(z)) -> 
      Printf.fprintf oc "%d\tadd\tx31, %s, %s\t\t! %d\n" (pcincr()) (reg y) (reg z) pos;
      Printf.fprintf oc "%d\tsw\tx31, %s, 0\t\t! %d\n" (pcincr()) (reg x) pos
  | NonTail(_), Stw(x, y, C(z)) -> 
      (if -2048 <= z && z < 2048 then
       Printf.fprintf oc "%d\tsw\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg y) (reg x) z pos
      else 
      (let u = upper z in
       let l = lower z in
       (Printf.fprintf oc "%d\tlui\tx31, %d\t\t! %d\n" (pcincr()) u pos;
        if l <> 0 then
          Printf.fprintf oc "%d\taddi\tx31, x31, %d\t\t! %d\n"(pcincr())  l pos);
          Printf.fprintf oc "%d\tadd\tx30, %s, x31\t\t! %d\n" (pcincr()) (reg y)  pos;
          Printf.fprintf oc "%d\tsw\tx30, %s, 0\t\t! %d\n" (pcincr()) (reg x) pos
  ))
  | NonTail(x), FMr(y) when x = y -> ()
  | NonTail(x), FMr(y) -> Printf.fprintf oc "%d\tfsgnj\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg y) pos
  | NonTail(x), FNeg(y) -> Printf.fprintf oc "%d\tfsgnjn\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg y) pos
  | NonTail(x), FAdd(y, z) -> Printf.fprintf oc "%d\tfadd\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos
  | NonTail(x), FSub(y, z) -> Printf.fprintf oc "%d\tfsub\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos
  | NonTail(x), FMul(y, z) -> Printf.fprintf oc "%d\tfmul\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos
  | NonTail(x), FDiv(y, z) -> Printf.fprintf oc "%d\tfdiv\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg x) (reg y) (reg z) pos
  | NonTail(x), Lfd(y, V(z)) -> 
      Printf.fprintf oc "%d\tadd\tx31, %s, %s\t\t! %d\n" (pcincr()) (reg y) (reg z) pos;
      Printf.fprintf oc "%d\tflw\t%s, x31, 0\t\t! %d\n" (pcincr()) (reg x)  pos
  | NonTail(x), Lfd(y, C(z)) -> 
  (if -2048 <= z && z < 2048 then
    Printf.fprintf oc "%d\tflw\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg x) (reg y) z pos
   else 
    (let u = upper z in
     let l = lower z in
     (Printf.fprintf oc "%d\tlui\tx31, %d\t\t! %d\n" (pcincr()) u pos;
      if l <> 0 then
        Printf.fprintf oc "%d\taddi\tx31, x31, %d\t\t! %d\n"(pcincr())  l pos);
        Printf.fprintf oc "%d\tadd\tx30, %s, x31\t\t! %d\n" (pcincr()) (reg y)  pos;
        Printf.fprintf oc "%d\tflw\t%s, x30, 0\t\t! %d\n" (pcincr()) (reg x) pos
))
  | NonTail(_), Stfd(x, y, V(z)) -> 
      Printf.fprintf oc "%d\tadd\tx31, %s, %s\t\t! %d\n" (pcincr()) (reg y) (reg z) pos;
      Printf.fprintf oc "%d\tfsw\tx31, %s, 0\t\t! %d\n" (pcincr()) (reg x) pos
  | NonTail(_), Stfd(x, y, C(z)) -> 
      (if -2048 <= z && z < 2048 then
       Printf.fprintf oc "%d\tfsw\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg y) (reg x) z pos
      else 
      (let u = upper z in
       let l = lower z in
       (Printf.fprintf oc "%d\tlui\tx31, %d\t\t! %d\n" (pcincr()) u pos;
        if l <> 0 then
          Printf.fprintf oc "%d\taddi\tx31, x31, %d\t\t! %d\n"(pcincr())  l pos);
          Printf.fprintf oc "%d\tadd\tx30, %s, x31\t\t! %d\n" (pcincr()) (reg y)  pos;
          Printf.fprintf oc "%d\tfsw\tx30, %s, 0\t\t! %d\n" (pcincr()) (reg x) pos
  ))
  | NonTail(_), Comment(s) -> Printf.fprintf oc "#\t%s\n" s
  (* 退避の仮想命令の実装 (caml2html: emit_save) *)
  | NonTail(_), Save(x, y) when List.mem x allregs && not (S.mem y !stackset) ->
      save y;
      Printf.fprintf oc "%d\tsw\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (reg x) (-(offset y)) pos
  | NonTail(_), Save(x, y) when List.mem x allfregs && not (S.mem y !stackset) ->
      savef y;
      Printf.fprintf oc "%d\tfsw\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (reg x) (-(offset y)) pos
  | NonTail(_), Save(x, y) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 (caml2html: emit_restore) *)
  | NonTail(x), Restore(y) when List.mem x allregs ->
      Printf.fprintf oc "%d\tlw\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg x) (reg reg_sp) (-(offset y)) pos
  | NonTail(x), Restore(y) ->
      assert (List.mem x allfregs);
      Printf.fprintf oc "%d\tflw\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg x) (reg reg_sp) (-(offset y)) pos
  (* 末尾だったら計算結果を第一レジスタにセットしてリターン (caml2html: emit_tailret) *)
  | Tail, (Nop | Stw _ | Stfd _ | Comment _ | Save _ | Write _ as exp) ->
      g' oc pos (NonTail(Id.gentmp Type.Unit), exp);
      Printf.fprintf oc "%d\tjalr\tx0, x1, 0\t\t! %d\n" (pcincr()) pos;
  | Tail, (Li _ | SetL _ | Mr _ | Neg _ | Add _ | Sub _ | Div _ | Rem _ | Slw _ | Sra _ | Lwz _ | FtoI _  | And _ | Or _  | Xor _ | AndI _ | FEq _ | FLT _ | Read | Array _  | FArray _ as exp) ->
      g' oc pos (NonTail(regs.(0)), exp);
      Printf.fprintf oc "%d\tjalr\tx0, x1, 0\t\t! %d\n" (pcincr()) pos;
  | Tail, (FLi _ | FMr _ | FNeg _ | FAdd _ | FSub _ | FMul _ | FDiv _ | Lfd _ | ItoF _ | FAbs _ | FSqrt _ | FFloor _  | FRead as exp) ->
      g' oc pos (NonTail(fregs.(0)), exp);
      Printf.fprintf oc "%d\tjalr\tx0, x1, 0\t\t! %d\n" (pcincr()) pos;
  | Tail, (Restore(x) as exp) ->
      (match locate x with
      | [i] -> g' oc pos (NonTail(regs.(0)), exp)
      | [i; j] when i + 1 = j -> g' oc pos (NonTail(fregs.(0)), exp)
      | _ -> assert false);
      Printf.fprintf oc "%d\tjalr\tx0, x1, 0\t\t! %d\n" (pcincr()) pos;
  | Tail, IfEq(x, V(y), e1, e2) ->
      g'_tail_if oc pos e1 e2 "beq" "bne" x y 
  | Tail, IfEq(x, C(y), e1, e2) ->
      Printf.fprintf oc "%d\taddi\t%s, x0, %d\t\t! %d\n" (pcincr()) (reg reg_tmp) y pos;
      g'_tail_if oc pos e1 e2 "beq" "bne" x reg_tmp
  | Tail, IfLE(x, V(y), e1, e2) ->
      g'_tail_if oc pos e1 e2 "bge" "blt" y x
  | Tail, IfLE(x, C(y), e1, e2) ->
      Printf.fprintf oc "%d\taddi\t%s, x0, %d\t\t! %d\n" (pcincr()) (reg reg_tmp) y pos;
      g'_tail_if oc pos e1 e2 "bge" "blt" reg_tmp x
  | Tail, IfGE(x, V(y), e1, e2) ->
      g'_tail_if oc pos e1 e2 "bge" "blt" x y
  | Tail, IfGE(x, C(y), e1, e2) ->
      Printf.fprintf oc "%d\taddi\t%s, x0, %d\t\t! %d\n" (pcincr()) (reg reg_tmp) y pos;
      g'_tail_if oc pos e1 e2 "bge" "blt" x reg_tmp
  | Tail, IfFEq(x, y, e1, e2) ->
      g'_tail_if oc pos e1 e2 "fbeq" "fbne" x y
  | Tail, IfFLE(x, y, e1, e2) ->
      g'_tail_if oc pos e1 e2 "fbge" "fblt" y x
  | Tail, IfZ(x, e1, e2) ->
      g'_tail_if oc pos e1 e2 "beq" "bne" x "%x0"
  | Tail, IfPos(x, e1, e2) ->
      g'_tail_if oc pos e1 e2 "bge" "blt" x "%x0"
  | Tail, IfNeg(x, e1, e2) ->
      g'_tail_if oc pos e1 e2 "bge" "blt" "%x0" x
  | NonTail(z), IfEq(x, V(y), e1, e2) ->
      g'_non_tail_if oc pos (NonTail(z)) e1 e2 "beq" "bne" x y
  | NonTail(z), IfEq(x, C(y), e1, e2) ->
      Printf.fprintf oc "%d\taddi\t%s, x0, %d\t\t! %d\n" (pcincr()) (reg reg_tmp) y pos;
      g'_non_tail_if oc pos (NonTail(z)) e1 e2 "beq" "bne" x reg_tmp
  | NonTail(z), IfLE(x, V(y), e1, e2) ->
      g'_non_tail_if oc pos (NonTail(z)) e1 e2 "bge" "blt" y x
  | NonTail(z), IfLE(x, C(y), e1, e2) ->
      Printf.fprintf oc "%d\taddi\t%s, x0, %d\t\t! %d\n" (pcincr()) (reg reg_tmp) y pos;
      g'_non_tail_if oc pos (NonTail(z)) e1 e2 "bge" "blt" reg_tmp x
  | NonTail(z), IfGE(x, V(y), e1, e2) ->
      g'_non_tail_if oc pos (NonTail(z)) e1 e2 "bge" "blt" x y
  | NonTail(z), IfGE(x, C(y), e1, e2) ->
      Printf.fprintf oc "%d\taddi\t%s, x0, y\t\t! %d\n" (pcincr()) (reg reg_tmp) pos;
      g'_non_tail_if oc pos (NonTail(z)) e1 e2 "bge" "blt" x reg_tmp
  | NonTail(z), IfFEq(x, y, e1, e2) ->
      g'_non_tail_if oc pos (NonTail(z)) e1 e2 "fbeq" "fbne" x y
  | NonTail(z), IfFLE(x, y, e1, e2) ->
      g'_non_tail_if oc pos (NonTail(z)) e1 e2 "fbge" "fblt" y x
  | NonTail(z), IfZ(x, e1, e2) ->
      g'_non_tail_if oc pos (NonTail(z)) e1 e2 "beq" "bne" x "%x0" 
  | NonTail(z), IfPos(x, e1, e2) ->
      g'_non_tail_if oc pos (NonTail(z)) e1 e2 "bge" "blt" x "%x0" 
  | NonTail(z), IfNeg(x, e1, e2) ->
      g'_non_tail_if oc pos (NonTail(z)) e1 e2 "bge" "blt" "%x0" x
  (* 関数呼び出しの仮想命令の実装 (caml2html: emit_call) *)
  | Tail, CallCls(x, ys, zs) -> (* 末尾呼び出し (caml2html: emit_tailcall) *)
      g'_args oc pos [(x, reg_cl)] ys zs;
      Printf.fprintf oc "%d\tlw\t%s, %s, 0\t\t! %d\n" (pcincr()) (reg reg_sw) (reg reg_cl) pos;
      Printf.fprintf oc "%d\tjalr\tx0, %s, 0\t\t! %d\n" (pcincr()) (reg reg_sw) pos;
  | Tail, CallDir(Id.L(x), ys, zs) -> (* 末尾呼び出し *)
      g'_args oc pos [] ys zs;
      (try
        Printf.fprintf oc "%d\tjal\tx0, %d\t\t! %d\n" (pcincr()) ((Hashtbl.find address_list x) - (!pc)) pos;
      with Not_found ->
        Printf.printf "LABEL %s NOT FOUND\n" x;
        Printf.fprintf oc "%d\tjal\tx0, NOT_FOUND\t\t! %d\n" (pcincr()) pos;
      )
  | NonTail(a), CallCls(x, ys, zs) ->
      g'_args oc pos [(x, reg_cl)] ys zs;
      let ss = stacksize () in
      Printf.fprintf oc "%d\tsw\t%s, x1, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (-(ss - 4)) pos;
      Printf.fprintf oc "%d\taddi\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (reg reg_sp) (-ss) pos;
      Printf.fprintf oc "%d\tlw\t%s, %s, 0\t\t! %d\n" (pcincr()) (reg reg_tmp) (reg reg_cl) pos;
      Printf.fprintf oc "%d\tjalr\tx1, %s, 0\t\t! %d\n" (pcincr()) (reg reg_tmp) pos;
      Printf.fprintf oc "%d\taddi\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (reg reg_sp) ss pos;
      Printf.fprintf oc "%d\tlw\tx1, %s, %d\t\t! %d\n" (pcincr())  (reg reg_sp) (-(ss - 4)) pos;
      if List.mem a allregs && a <> regs.(0) then
        Printf.fprintf oc "%d\taddi\t%s, %s, 0\t\t! %d\n" (pcincr()) (reg a) (reg regs.(0)) pos
      else if List.mem a allfregs && a <> fregs.(0) then
        Printf.fprintf oc "%d\tfsgnj\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg a) (reg fregs.(0)) (reg fregs.(0)) pos;
  | (NonTail(a), CallDir(Id.L(x), ys, zs)) ->
      g'_args oc pos [] ys zs;
      let ss = stacksize () in
      Printf.fprintf oc "%d\tsw\t%s, x1, %d\t\t! %d\n" (pcincr()) (reg reg_sp)  (-(ss - 4)) pos;
      Printf.fprintf oc "%d\taddi\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (reg reg_sp) (-ss) pos;
      (try
        Printf.fprintf oc "%d\tjal\tx1, %d\t\t! %d\n" (pcincr()) ((Hashtbl.find address_list x) - (!pc)) pos;
      with Not_found ->
        Printf.printf "LABEL %s NOT FOUND\n" x;
        Printf.fprintf oc "%d\tjal\tx1, NOT_FOUND\t\t! %d\n" (pcincr()) pos;
      );
      Printf.fprintf oc "%d\taddi\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (reg reg_sp) ss pos;
      Printf.fprintf oc "%d\tlw\tx1, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (-(ss - 4)) pos;
      if List.mem a allregs && a <> regs.(0) then
        Printf.fprintf oc "%d\taddi\t%s, %s, 0\t\t! %d\n" (pcincr()) (reg a) (reg regs.(0)) pos
      else if List.mem a allfregs && a <> fregs.(0) then
        Printf.fprintf oc "%d\tfsgnj\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg a) (reg fregs.(0)) (reg fregs.(0)) pos;
  | (NonTail(a), CallDir1(Id.L(x), ys, zs)) ->
      g'_args oc pos [] ys zs;
      let ss = stacksize () in
      Printf.fprintf oc "%d\tsw\t%s, x1, %d\t\t! %d\n" (pcincr()) (reg reg_sp)  (*(-(ss - 4))*) 0 pos;
      Printf.fprintf oc "%d\taddi\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (reg reg_sp) (-ss) pos;
      (try
        Printf.fprintf oc "%d\tjal\tx1, %d\t\t! %d\n" (pcincr()) ((Hashtbl.find address_list x) - (!pc)) pos;
      with Not_found ->
        Printf.printf "LABEL %s NOT FOUND\n" x;
        Printf.fprintf oc "%d\tjal\tx1, NOT_FOUND\t\t! %d\n" (pcincr()) pos;
      );
      (if !check = 0 then (check2 := 0;
      Printf.fprintf oc "%d\taddi\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (reg reg_sp) ss pos) else check2 := 1);
      (*Printf.fprintf oc "%d\tlw\tx1, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (-(ss - 4)) pos;*)
      if List.mem a allregs && a <> regs.(0) then
        Printf.fprintf oc "%d\taddi\t%s, %s, 0\t\t! %d\n" (pcincr()) (reg a) (reg regs.(0)) pos
      else if List.mem a allfregs && a <> fregs.(0) then
        Printf.fprintf oc "%d\tfsgnj\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg a) (reg fregs.(0)) (reg fregs.(0)) pos;
  | (NonTail(a), CallDir2(Id.L(x), ys, zs)) ->
      g'_args oc pos [] ys zs;
      let ss = stacksize () in
      (*Printf.fprintf oc "%d\tsw\t%s, x1, %d\t\t! %d\n" (pcincr()) (reg reg_sp)  (-(ss - 4)) pos;*)
      (if !check2 = 0 then 
      Printf.fprintf oc "%d\taddi\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (reg reg_sp) (-ss) pos else check2 := 1);
      (try
        Printf.fprintf oc "%d\tjal\tx1, %d\t\t! %d\n" (pcincr()) ((Hashtbl.find address_list x) - (!pc)) pos;
      with Not_found ->
        Printf.printf "LABEL %s NOT FOUND\n" x;
        Printf.fprintf oc "%d\tjal\tx1, NOT_FOUND\t\t! %d\n" (pcincr()) pos;
      );
      (if !check = 0 then (check2 := 0;
      Printf.fprintf oc "%d\taddi\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (reg reg_sp) ss pos) else check2 := 1);
      (*Printf.fprintf oc "%d\tlw\tx1, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (-(ss - 4)) pos;*)
      if List.mem a allregs && a <> regs.(0) then
        Printf.fprintf oc "%d\taddi\t%s, %s, 0\t\t! %d\n" (pcincr()) (reg a) (reg regs.(0)) pos
      else if List.mem a allfregs && a <> fregs.(0) then
        Printf.fprintf oc "%d\tfsgnj\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg a) (reg fregs.(0)) (reg fregs.(0)) pos;
    | (NonTail(a), CallDir3(Id.L(x), ys, zs)) ->
      g'_args oc pos [] ys zs;
      let ss = stacksize () in
     (* Printf.fprintf oc "%d\tsw\t%s, x1, %d\t\t! %d\n" (pcincr()) (reg reg_sp)  (-(ss - 4)) pos;*)
      if !check2 = 0 then 
      Printf.fprintf oc "%d\taddi\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (reg reg_sp) (-ss) pos;
      (try
        Printf.fprintf oc "%d\tjal\tx1, %d\t\t! %d\n" (pcincr()) ((Hashtbl.find address_list x) - (!pc)) pos;
      with Not_found ->
        Printf.printf "LABEL %s NOT FOUND\n" x;
        Printf.fprintf oc "%d\tjal\tx1, NOT_FOUND\t\t! %d\n" (pcincr()) pos;
      );
      Printf.fprintf oc "%d\taddi\t%s, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (reg reg_sp) ss pos;
      Printf.fprintf oc "%d\tlw\tx1, %s, %d\t\t! %d\n" (pcincr()) (reg reg_sp) (*(-(ss - 4))*)0 pos;
      if List.mem a allregs && a <> regs.(0) then
        Printf.fprintf oc "%d\taddi\t%s, %s, 0\t\t! %d\n" (pcincr()) (reg a) (reg regs.(0)) pos
      else if List.mem a allfregs && a <> fregs.(0) then
        Printf.fprintf oc "%d\tfsgnj\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg a) (reg fregs.(0)) (reg fregs.(0)) pos;
  | _ -> raise Not_found
and g'_tail_if oc pos e1 e2 b bn x y =
  let b_else = Id.genid (b ^ "_else") in
  (try
    Printf.fprintf oc "%d\t%s \t%s, %s, %d\t\t! %d\n" (pcincr()) bn (reg x) (reg y) ((Hashtbl.find address_list b_else) - (!pc)) pos;
  with Not_found ->
    Printf.printf "LABEL %s NOT FOUND!\n" b_else;
    Printf.fprintf oc "%d\t%s \t%s, %s, NOT_FOUND\t\t! %d\n" (pcincr()) bn (reg x) (reg y) pos;
  );
  let stackset_back = !stackset in
  g oc (Tail, e1);
  Printf.fprintf oc "# %s:\n" b_else;
  stackset := stackset_back;
  g oc (Tail, e2)
and g'_non_tail_if oc pos dest e1 e2 b bn x y=
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
  (try
    Printf.fprintf oc "%d\t%s\t%s, %s, %d\t\t! %d\n" (pcincr()) bn (reg x) (reg y) ((Hashtbl.find address_list b_else) - (!pc)) pos;
  with Not_found ->
    Printf.printf "LABEL %s NOT FOUND\n" b_else;
    Printf.fprintf oc "%d\t%s\t%s, %s, NOT FOUND\t\t! %d\n" (pcincr()) bn (reg x) (reg y) pos;
  );
  let stackset_back = !stackset in
  g oc (dest, e1);
  let stackset1 = !stackset in
  if not(f_nop dest e2) then
  ((try
    Printf.fprintf oc "%d\tjal\tx0, %d\t\t! %d\n" (pcincr()) ((Hashtbl.find address_list b_cont) - (!pc)) pos;
  with Not_found ->
    Printf.printf "LABEL %s NOT FOUND\n" b_cont;
    Printf.fprintf oc "%d\tjal\tx0, NOT_FOUND\t\t! %d\n" (pcincr()) pos;
  );)
  else ();
  Printf.fprintf oc "# %s:\n" b_else;
  stackset := stackset_back;
  g oc (dest, e2);
  Printf.fprintf oc "# %s:\n" b_cont;
  let stackset2 = !stackset in
  stackset := S.inter stackset1 stackset2
and g'_tail_fif oc pos e1 e2 b bn x y =
  let b_else = Id.genid (b ^ "_else") in
  (try
    Printf.fprintf oc "%d\t%s\tx31, %s, %s\t\t! %d\n" (pcincr()) b (reg x) (reg y)  pos;
    Printf.fprintf oc "%d\tbeq\tx31, x0, %d\t\t! %d\n" (pcincr()) ((Hashtbl.find address_list b_else) - (!pc)) pos;
  with Not_found ->
    Printf.printf "LABEL %s NOT FOUND!\n" b_else;
    Printf.fprintf oc "%d\t%s \t%s, %s, NOT_FOUND\t\t! %d\n" (pcincr()) bn (reg x) (reg y) pos;
  );
  let stackset_back = !stackset in
  g oc (Tail, e1);
  Printf.fprintf oc "# %s:\n" b_else;
  stackset := stackset_back;
  g oc (Tail, e2)
and g'_non_tail_fif oc pos dest e1 e2 b bn x y=
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
  if not(f_nop dest e1) then(
  (try
  Printf.fprintf oc "%d\t%s\tx31, %s, %s\t\t! %d\n" (pcincr()) b (reg x) (reg y)  pos;
  Printf.fprintf oc "%d\tbeq\tx31, x0, %d\t\t! %d\n" (pcincr()) ((Hashtbl.find address_list b_else) - (!pc)) pos;
  with Not_found ->
    Printf.printf "LABEL %s NOT FOUND\n" b_else;
    Printf.fprintf oc "%d\t%s\t%s, %s, NOT FOUND\t\t! %d\n" (pcincr()) bn (reg x) (reg y) pos;
  );
  let stackset_back = !stackset in
  g oc (dest, e1);
  let stackset1 = !stackset in
  if not(f_nop dest e2) then
  ((try
    Printf.fprintf oc "%d\tjal\tx0, %d\t\t! %d\n" (pcincr()) ((Hashtbl.find address_list b_cont) - (!pc)) pos; 
  with Not_found ->
    Printf.printf "LABEL %s NOT FOUND\n" b_cont;
    Printf.fprintf oc "%d\tjal\tx0, NOT_FOUND\t\t! %d\n" (pcincr()) pos;
  );) else ();
  Printf.fprintf oc "# %s:\n" b_else;
  stackset := stackset_back;
  g oc (dest, e2);
  Printf.fprintf oc "# %s:\n" b_cont;
  let stackset2 = !stackset in
  stackset := S.inter stackset1 stackset2)
  else
  (
  (try
  Printf.fprintf oc "%d\t%s\tx31, %s, %s\t\t! %d\n" (pcincr()) b (reg x) (reg y)  pos;
  Printf.fprintf oc "%d\tbne\tx31, x0, %d\t\t! %d\n" (pcincr()) ((Hashtbl.find address_list b_cont) - (!pc)) pos;
  with Not_found ->
    Printf.printf "LABEL %s NOT FOUND\n" b_else;
    Printf.fprintf oc "%d\t%s\t%s, %s, NOT FOUND\t\t! %d\n" (pcincr()) bn (reg x) (reg y) pos;
  );
  let stackset_back = !stackset in
  g oc (dest, e1);
  let stackset1 = !stackset in
  Printf.fprintf oc "# %s:\n" b_else;
  stackset := stackset_back;
  g oc (dest, e2);
  Printf.fprintf oc "# %s:\n" b_cont;
  let stackset2 = !stackset in
  stackset := S.inter stackset1 stackset2)
  
and g'_args oc pos x_reg_cl ys zs =
  let (i, yrs) =
    List.fold_left
      (fun (i, yrs) y -> (i + 1, (y, regs.(i)) :: yrs))
      (0, x_reg_cl)
      ys in
  List.iter
    (fun (y, r) -> Printf.fprintf oc "%d\taddi\t%s, %s, 0\t\t! %d\n" (pcincr()) (reg r) (reg y) pos)
    (shuffle reg_sw yrs);
  let (d, zfrs) =
    List.fold_left
      (fun (d, zfrs) z -> (d + 1, (z, fregs.(d)) :: zfrs))
      (0, [])
      zs in
  List.iter
    (fun (z, fr) -> Printf.fprintf oc "%d\tfsgnj\t%s, %s, %s\t\t! %d\n" (pcincr()) (reg fr) (reg z) (reg z) pos)
    (shuffle reg_fsw zfrs)

let rec k oc = function
    | dest, Ans(_, exp) -> k' oc (dest, exp)
    | dest, Let(_, (x, t), exp, e) ->
    if Peephole.occur2 e then check := 1 else check := 0;
        k' oc (NonTail(x), exp);
        k oc (dest, e)
  and k' oc = function
    | NonTail(_), Nop -> ()
    | NonTail(x), Li(n) ->
        let u = upper n in
        let l = lower n in
        if u = 0 then
          jpincr()
        else
          (jpincr();
          if l <> 0 then
            jpincr())
    | NonTail(x), FLi(d) ->
    let u = Int32.to_int(get_upper d) in
    let l = Int32.to_int(get_lower d) in
    if u = 0 && (l <> 0) then 
     (jpincr();jpincr())
     else if u = 0 then
     jpincr()
    else
       (jpincr();
       (if l <> 0 then
          jpincr();jpincr()))
    | NonTail(x), SetL(Id.L(y)) ->
        (*let s = load_label x y in
        Printf.fprintf oc "%s" s*)jpincr();jpincr()
    | NonTail(x), Mr(y) when x = y -> ()
    | NonTail(x), Mr(y) -> jpincr()
    | NonTail(x), And(y, z) -> jpincr()
    | NonTail(x), Or(y, z) -> jpincr()
    | NonTail(x), Xor(y, z) -> jpincr()
    | NonTail(x), AndI(y, z) -> jpincr()
    | NonTail(x), FAbs(y) -> jpincr()
    | NonTail(x), ItoF(y) -> jpincr()
    | NonTail(x), FtoI(y) -> jpincr()
    | NonTail(x), FSqrt(y) -> jpincr()
    | NonTail(x), FFloor(y) -> jpincr()
    | NonTail(x), FEq(y, z) -> jpincr()
    | NonTail(x), FLT(y, z) -> jpincr()
    | NonTail(x), Read -> jpincr()
    | NonTail(x), FRead -> jpincr()
    | NonTail(x), Write(y) -> jpincr()
    | NonTail(x), Neg(y) -> jpincr()
    | NonTail(x), Add(y, V(z)) -> jpincr()
    | NonTail(x), Add(y, C(z)) -> jpincr()
    | NonTail(x), Sub(y, V(z)) -> jpincr()
    | NonTail(x), Sub(y, C(z)) -> jpincr()
    | NonTail(x), Div(y, z) -> jpincr()
    | NonTail(x), Rem(y, z) -> jpincr()
    | NonTail(x), Array(y, z) -> if y = x then jpc := !jpc + 28 else jpc := !jpc + 32;
    | NonTail(x), FArray(y, z) -> jpc := !jpc + 32;
    | NonTail(x), Slw(y, V(z)) -> jpincr()
    | NonTail(x), Slw(y, C(z)) -> jpincr()
    | NonTail(x), Sra(y, C(z)) -> jpincr()
    | NonTail(x), Lwz(y, V(z)) -> jpincr();jpincr()
    | NonTail(x), Lwz(y, C(z)) -> 
    (if -2048 <= z && z < 2048 then
      jpincr()
      else 
      (let u = upper z in
      let l = lower z in
      (jpincr();
      if l <> 0 then
        jpincr());
       jpincr();
        jpincr()
      ))
    | NonTail(_), Stw(x, y, V(z)) -> jpincr();jpincr()
    | NonTail(_), Stw(x, y, C(z)) -> 
    (if -2048 <= z && z < 2048 then
      jpincr()
      else 
      (let u = upper z in
      let l = lower z in
      (jpincr();
      if l <> 0 then
        jpincr());
       jpincr();
        jpincr()
      ))
    | NonTail(x), FMr(y) when x = y -> ()
    | NonTail(x), FMr(y) -> jpincr()
    | NonTail(x), FNeg(y) -> jpincr()
    | NonTail(x), FAdd(y, z) -> jpincr()
    | NonTail(x), FSub(y, z) -> jpincr()
    | NonTail(x), FMul(y, z) -> jpincr()
    | NonTail(x), FDiv(y, z) -> jpincr()
    | NonTail(x), Lfd(y, V(z)) -> jpincr();jpincr()
    | NonTail(x), Lfd(y, C(z)) -> 
    (if -2048 <= z && z < 2048 then
      jpincr()
      else 
      (let u = upper z in
      let l = lower z in
      (jpincr();
      if l <> 0 then
        jpincr());
       jpincr();
        jpincr()
      ))
    | NonTail(_), Stfd(x, y, V(z)) -> jpincr();jpincr()
    | NonTail(_), Stfd(x, y, C(z)) -> 
    (if -2048 <= z && z < 2048 then
      jpincr()
      else 
      (let u = upper z in
      let l = lower z in
      (jpincr();
      if l <> 0 then
        jpincr());
       jpincr();
        jpincr()
      ))
    | NonTail(_), Comment(s) -> Printf.fprintf oc "#\t%s\n" s
    | NonTail(_), Save(x, y) when List.mem x allregs && not (S.mem y !stackset) ->
        save y;
        jpincr()
    | NonTail(_), Save(x, y) when List.mem x allfregs && not (S.mem y !stackset) ->
        savef y;
        jpincr()
    | NonTail(_), Save(x, y) -> assert (S.mem y !stackset); ()
    | NonTail(x), Restore(y) when List.mem x allregs ->
        jpincr()
    | NonTail(x), Restore(y) ->
        assert (List.mem x allfregs);
        jpincr()
    | Tail, (Nop | Stw _ | Stfd _ | Comment _ | Save _ | Write _ as exp) ->
        k' oc (NonTail(Id.gentmp Type.Unit), exp);
        jpincr()
    | Tail, (Li _ | SetL _ | Mr _ | Neg _ | Add _ | Sub _ | Div _ | Rem _ | Slw _ | Sra _ | Lwz _ | FtoI _ | FEq _ | FLT _ | And _ | Or _ | Xor _ | AndI _ | Read | Array _ | FArray _  as exp) ->
        k' oc (NonTail(regs.(0)), exp);
        jpincr()
    | Tail, (FLi _ | FMr _ | FNeg _ | FAdd _ | FSub _ | FMul _ | FDiv _ | Lfd _ | ItoF _ | FSqrt _  | FFloor _ | FAbs _ | FRead as exp) ->
        k' oc (NonTail(fregs.(0)), exp);
        jpincr()
    | Tail, (Restore(x) as exp) ->
        (match locate x with
        | [i] -> k' oc (NonTail(regs.(0)), exp)
        | [i; j] when i + 1 = j -> k' oc (NonTail(fregs.(0)), exp)
        | _ -> assert false);
        jpincr()
    | Tail, IfEq(x, V(y), e1, e2) ->
        k'_tail_if oc e1 e2 "beq" "bne" x y 
    | Tail, IfEq(x, C(y), e1, e2) ->
        jpincr();
        k'_tail_if oc e1 e2 "beq" "bne" x reg_tmp
    | Tail, IfLE(x, V(y), e1, e2) ->
        k'_tail_if oc e1 e2 "bge" "blt" y x
    | Tail, IfLE(x, C(y), e1, e2) ->
        jpincr();
        k'_tail_if oc e1 e2 "bge" "blt" reg_tmp x
    | Tail, IfGE(x, V(y), e1, e2) ->
        k'_tail_if oc e1 e2 "bge" "blt" x y
    | Tail, IfGE(x, C(y), e1, e2) ->
        jpincr();
        k'_tail_if oc e1 e2 "bge" "blt" x reg_tmp
    | Tail, IfFEq(x, y, e1, e2) ->
        k'_tail_if oc e1 e2 "fbeq" "fbne" x y
    | Tail, IfFLE(x, y, e1, e2) ->
        k'_tail_if oc e1 e2 "fbge" "fblt" y x
    | Tail, IfZ(x, e1, e2) ->
        k'_tail_if oc e1 e2 "beq" "bne" x "%x0"
    | Tail, IfPos(x, e1, e2) ->
        k'_tail_if oc e1 e2 "bge" "blt" x "%x0"
    | Tail, IfNeg(x, e1, e2) ->
        k'_tail_if oc e1 e2 "bge" "blt" "%x0" x
    | NonTail(z), IfEq(x, V(y), e1, e2) ->
        k'_non_tail_if oc (NonTail(z)) e1 e2 "beq" "bne" x y
    | NonTail(z), IfEq(x, C(y), e1, e2) ->
        jpincr();
        k'_non_tail_if oc (NonTail(z)) e1 e2 "beq" "bne" x reg_tmp
    | NonTail(z), IfLE(x, V(y), e1, e2) ->
        k'_non_tail_if oc (NonTail(z)) e1 e2 "bge" "blt" y x
    | NonTail(z), IfLE(x, C(y), e1, e2) ->
        jpincr();
        k'_non_tail_if oc (NonTail(z)) e1 e2 "bge" "blt" reg_tmp x
    | NonTail(z), IfGE(x, V(y), e1, e2) ->
        k'_non_tail_if oc (NonTail(z)) e1 e2 "bge" "blt" x y
    | NonTail(z), IfGE(x, C(y), e1, e2) ->
        jpincr();
        k'_non_tail_if oc (NonTail(z)) e1 e2 "bge" "blt" x reg_tmp
    | NonTail(z), IfFEq(x, y, e1, e2) ->
        k'_non_tail_if oc (NonTail(z)) e1 e2 "fbeq" "fbne" x y
    | NonTail(z), IfFLE(x, y, e1, e2) ->
        k'_non_tail_if oc (NonTail(z)) e1 e2 "fbge" "fblt" y x
    | NonTail(z), IfZ(x, e1, e2) ->
        k'_non_tail_if oc (NonTail(z)) e1 e2 "beq" "bne" x "%x0"
    | NonTail(z), IfPos(x, e1, e2) ->
        k'_non_tail_if oc (NonTail(z)) e1 e2 "bge" "blt" x "%x0"
    | NonTail(z), IfNeg(x, e1, e2) ->
        k'_non_tail_if oc (NonTail(z)) e1 e2 "bge" "blt" "%x0" x
    | Tail, CallCls(x, ys, zs) -> 
        k'_args oc [(x, reg_cl)] ys zs;
        jpincr();jpincr()
    | Tail, CallDir(Id.L(x), ys, zs) ->
        k'_args oc [] ys zs;
        jpincr()
    | NonTail(a), CallCls(x, ys, zs) ->
        k'_args oc [(x, reg_cl)] ys zs;
        let _ = stacksize () in
        jpc := !jpc + 24;
        if List.mem a allregs && a <> regs.(0) then
          jpincr()
        else if List.mem a allfregs && a <> fregs.(0) then
          jpincr()
    | (NonTail(a), CallDir(Id.L(x), ys, zs)) ->
        k'_args oc [] ys zs;
        let _ = stacksize () in
        jpc := !jpc + 20;
        if List.mem a allregs && a <> regs.(0) then
          jpincr()
        else if List.mem a allfregs && a <> fregs.(0) then
          jpincr()
    | (NonTail(a), CallDir1(Id.L(x), ys, zs)) ->
        k'_args oc [] ys zs;
        let _ = stacksize () in
        jpc := !jpc + 12;
        if !check = 0 then (check2 := 0;jpincr()) else check2 := 1;
        if List.mem a allregs && a <> regs.(0) then
          jpincr()
        else if List.mem a allfregs && a <> fregs.(0) then
          jpincr()
    | (NonTail(a), CallDir2(Id.L(x), ys, zs)) ->
        k'_args oc [] ys zs;
        let _ = stacksize () in
        if !check2 = 0 then jpincr() else ();
        jpc := !jpc + 4;
        if !check = 0 then (check2 := 0;jpincr()) else check2 := 1;
        if List.mem a allregs && a <> regs.(0) then
          jpincr()
        else if List.mem a allfregs && a <> fregs.(0) then
          jpincr()
    | (NonTail(a), CallDir3(Id.L(x), ys, zs)) ->
        k'_args oc [] ys zs;
        let _ = stacksize () in
        if !check2 = 0 then jpincr() else ();
        jpc := !jpc + 12;
        if List.mem a allregs && a <> regs.(0) then
          jpincr()
        else if List.mem a allfregs && a <> fregs.(0) then
          jpincr()
    | _ -> raise Not_found
    
  and k'_tail_if oc e1 e2 b bn x y =
    let b_else = Id.genid2 (b ^ "_else") in
    jpincr();
    let stackset_back = !stackset in
    k oc (Tail, e1);
    Hashtbl.add address_list b_else !jpc;
    Printf.printf "address_list に (%s, %d) を追加\n" b_else !jpc;
    stackset := stackset_back;
    k oc (Tail, e2)
  and k'_non_tail_if oc dest e1 e2 b bn x y=
    let b_else = Id.genid2 (b ^ "_else") in
    let b_cont = Id.genid2 (b ^ "_cont") in
    jpincr();
    let stackset_back = !stackset in
    k oc (dest, e1);
    let stackset1 = !stackset in
    if not(f_nop dest e2) then
    (jpincr();)
    else ();
    Hashtbl.add address_list b_else !jpc;
    Printf.printf "address_list に (%s, %d) を追加\n" b_else !jpc;
    stackset := stackset_back;
    k oc (dest, e2);
    Hashtbl.add address_list b_cont !jpc;
    Printf.printf "address_list に (%s, %d) を追加\n" b_cont !jpc;
    let stackset2 = !stackset in
    stackset := S.inter stackset1 stackset2
  and k'_tail_fif oc e1 e2 b bn x y =
    let b_else = Id.genid2 (b ^ "_else") in
    jpincr();jpincr();
    let stackset_back = !stackset in
    k oc (Tail, e1);
    Hashtbl.add address_list b_else !jpc;
    Printf.printf "faddress_list に (%s, %d) を追加\n" b_else !jpc;
    stackset := stackset_back;
    k oc (Tail, e2)
  and k'_non_tail_fif oc dest e1 e2 b bn x y=
    let b_else = Id.genid2 (b ^ "_else") in
    let b_cont = Id.genid2 (b ^ "_cont") in
    jpincr();jpincr();
    let stackset_back = !stackset in
    k oc (dest, e1);
    let stackset1 = !stackset in
    if not ((f_nop dest e1) || (f_nop dest e2)) then
    (jpincr();) else ();
    Hashtbl.add address_list b_else !jpc;
    Printf.printf "faddress_list に (%s, %d) を追加\n" b_else !jpc;
    stackset := stackset_back;
    k oc (dest, e2);
    Hashtbl.add address_list b_cont !jpc;
    Printf.printf "faddress_list に (%s, %d) を追加\n" b_cont !jpc;
    let stackset2 = !stackset in
    stackset := S.inter stackset1 stackset2
  and k'_args oc x_reg_cl ys zs =
    let (i, yrs) =
      List.fold_left
        (fun (i, yrs) y -> (i + 1, (y, regs.(i)) :: yrs))
        (0, x_reg_cl)
        ys in
    List.iter
      (fun (y, r) -> jpincr())
      (shuffle reg_sw yrs);
    let (d, zfrs) =
      List.fold_left
        (fun (d, zfrs) z -> (d + 1, (z, fregs.(d)) :: zfrs))
        (0, [])
        zs in
    List.iter
      (fun (z, fr) -> jpincr())
      (shuffle reg_fsw zfrs)
  
let temp_counter = ref 0

let h oc { name = Id.L(x); args = _; fargs = _; body = e; ret = _ } =
  Printf.fprintf oc "# %s:\n" x;
  stackset := S.empty;
  stackmap := ["dummy"];
  check := 0;
  check2 := 0;
  g oc (Tail, e)
 
let i oc { name = Id.L(x); args = _; fargs = _; body = e; ret = _ } =
  stackset := S.empty;
  stackmap := ["dummy"];
  Hashtbl.add address_list x !jpc; 
  Printf.printf "address_list に (%s, %d) を追加\n" x !jpc;
  Printf.printf "counter = %d\n" !counter;
  check := 0;
  check2 := 0;
  k oc (Tail, e)
 
let f oc (Prog(data, fundefs, e)) =
  Format.eprintf "generating assembly...@.";
  temp_counter := !counter;
  List.iter (fun fundef -> i oc fundef) fundefs;
  Printf.fprintf oc "# jump to main entry point\n";
  Printf.fprintf oc "0\taddi\tx2, x2, -8\n";
  Printf.fprintf oc "4\tjal\tx0, %d\n" ((!jpc)-4);
  check := 0;
  check2 := 0;
  k oc (NonTail("_R_0"), e);
  pc := 8;
  jpc := 8;

  counter := !temp_counter;
  List.iter (fun fundef -> h oc fundef) fundefs;
  Printf.fprintf oc "# main program starts\n";
  stackset := S.empty;
  stackmap := ["dummy"];

  check := 0;
  check2 := 0;
  g oc (NonTail("_R_0"), e);
  Printf.fprintf oc "# main program ends\n";