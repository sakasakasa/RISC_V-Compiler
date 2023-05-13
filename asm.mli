type id_or_imm = V of Id.t | C of int
type t =
  | Ans of int * exp
  | Let of int * (Id.t * Type.t) * exp * t
and exp =
  | Dummy
  | Nop
  | Li of int
  | FLi of float
  | SetL of Id.l
  | And of Id.t * Id.t
  | Or of Id.t * Id.t
  | Xor of Id.t * Id.t
  | AndI of Id.t * int
  | FAbs of Id.t 
  | ItoF of Id.t
  | FtoI of Id.t
  | FSqrt of Id.t
  | FFloor of Id.t
  | FEq of Id.t * Id.t
  | FLT of Id.t * Id.t
  | Read 
  | FRead 
  | Write of Id.t
  | Array of Id.t * Id.t
  | FArray of Id.t * Id.t
  | Mr of Id.t
  | Neg of Id.t
  | Add of Id.t * id_or_imm
  | Sub of Id.t * id_or_imm
  | Mul of Id.t * id_or_imm
  | Div of Id.t * id_or_imm
  | Rem of Id.t * Id.t
  | Slw of Id.t * id_or_imm
  | Sra of Id.t * id_or_imm
  | Lwz of Id.t * id_or_imm
  | Stw of Id.t * Id.t * id_or_imm
  | FMr of Id.t 
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | Lfd of Id.t * id_or_imm
  | Stfd of Id.t * Id.t * id_or_imm
  | Comment of string
  (* virtual instructions *)
  | IfEq of Id.t * id_or_imm * t * t
  | IfLE of Id.t * id_or_imm * t * t
  | IfGE of Id.t * id_or_imm * t * t
  | IfFEq of Id.t * Id.t * t * t
  | IfFLE of Id.t * Id.t * t * t
  | IfZ of Id.t * t * t
  | IfPos of Id.t * t * t
  | IfNeg of Id.t * t * t
  (* closure address, integer arguments, and float arguments *)
  | CallCls of Id.t * Id.t list * Id.t list
  | CallDir of Id.l * Id.t list * Id.t list
  | CallDir1 of Id.l * Id.t list * Id.t list
  | CallDir2 of Id.l * Id.t list * Id.t list
  | CallDir3 of Id.l * Id.t list * Id.t list
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of Id.t (* スタック変数から値を復元 *)
type fundef = { name : Id.l; args : Id.t list; fargs : Id.t list; body : t; ret : Type.t }
type prog = Prog of (Id.l * float) list * fundef list * t

val fletd : int * Id.t * exp * t -> t (* shorthand of Let for float *)
val seq : int * exp * t -> t (* shorthand of Let for unit *)

val regs : Id.t array
val fregs : Id.t array
val allregs : Id.t list
val allfregs : Id.t list
val reg_cl : Id.t
val reg_sw : Id.t
val reg_fsw : Id.t
val reg_hp : Id.t
val reg_sp : Id.t
val reg_tmp : Id.t
val is_reg : Id.t -> bool

val fv_exp : exp -> Id.t list
val fv : t -> Id.t list
val concat : int -> t -> Id.t * Type.t -> t -> t

val align : int -> int
