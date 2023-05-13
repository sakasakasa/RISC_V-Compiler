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
  | LetTuple of (Id.t * Type.t) list * t * t
  | Array of t * t
  | Get of t * t
  | Put of t * t * t
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

let rec print_syntax outchan t n  = match t with 
| Unit ->  print_space outchan n;Printf.fprintf outchan "%s" "UNIT\n"
| Bool(x) -> print_space outchan n;Printf.fprintf outchan "%s" ("BOOL  "^(string_of_bool(x))^"\n")
| Int(x) -> print_space outchan n;Printf.fprintf outchan "%s" ("INT  "^(string_of_int(x))^"\n")
| Float(x) -> print_space outchan n;Printf.fprintf outchan "%s" ("FLOAT  "^(string_of_float(x))^"\n")
| Not(_,x) -> print_space outchan n;Printf.fprintf outchan "%s" "NOT\n";print_syntax outchan x (n+2)
| Neg(_,x) -> print_space outchan n;Printf.fprintf outchan "%s" "NEG\n";print_syntax outchan x (n+2)
| And((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "AND\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| AndI((_,x),y) -> print_space outchan n;Printf.fprintf outchan "%s" "ANDI\n";print_syntax outchan x (n+2);Printf.fprintf outchan "%d\n" y 
| Or((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "OR\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| Xor((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "XOR\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| FEq((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "FEQ\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| FLT((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "FLT\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| FSqrt((_,x)) -> print_space outchan n;Printf.fprintf outchan "%s" "FSQRT\n";print_syntax outchan x (n+2)
| FFloor((_,x)) -> print_space outchan n;Printf.fprintf outchan "%s" "FFLOOR\n";print_syntax outchan x (n+2)
| FAbs((_,x)) -> print_space outchan n;Printf.fprintf outchan "%s" "FABS\n";print_syntax outchan x (n+2)
| Add((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "ADD\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| Sub((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "SUB\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| Mul((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "MUL\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| Div((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "DIV\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| Rem((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "REM\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| Read -> print_space outchan n;Printf.fprintf outchan "%s" "READ\n"
| FRead -> print_space outchan n;Printf.fprintf outchan "%s" "FREAD\n"
| Write((_,x)) -> print_space outchan n;Printf.fprintf outchan "%s" "WRITE\n";print_syntax outchan x (n+2)
| FNeg((_,x)) -> print_space outchan n;Printf.fprintf outchan "%s" "FNEG\n";print_syntax outchan x (n+2)
| FAdd((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "FADD\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| FSub((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "FSUB\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| FMul((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "FMUL\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| FDiv((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "FDIV\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| Eq((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "EQ\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| LE((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "LE\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| If((_,x),(_,y),(_,z)) -> print_space outchan n;Printf.fprintf outchan "%s" "IF\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2);print_syntax outchan z (n+2)
| Let((a,b),(_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "LET\n";print_idtype outchan (a,b) (n+2);print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| Var(x) -> print_space outchan n;Printf.fprintf outchan "%s" "VAR  ";Printf.fprintf outchan "%s" (x^"\n")
| ItoF((_,x)) -> print_space outchan n;Printf.fprintf outchan "%s" "ITOF\n";print_syntax outchan x (n+2)
| FtoI((_,x)) -> print_space outchan n;Printf.fprintf outchan "%s" "FTOI\n";print_syntax outchan x (n+2)
| LetRec(x,(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "LETREC\n";print_idtype outchan x.name (n+2);print_idlist outchan x.args (n+2);print_syntax outchan (snd(x.body)) (n+2);print_syntax outchan y (n+2)
| App((_,x),y) -> print_space outchan n;Printf.fprintf outchan "%s" "APP\n";print_syntax outchan x (n+2);print_syntax_list outchan y (n+2)
| Tuple(x) -> print_space outchan n;Printf.fprintf outchan "%s" "TUPLE\n";print_syntax_list outchan x (n+2)
| LetTuple(x,(_,y),(_,z)) -> print_space outchan n;Printf.fprintf outchan "%s" "LETTUPLE\n";print_idlist outchan x (n+2);print_syntax outchan y (n+2);print_syntax outchan z (n+2)
| Array((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "ARRAY\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| Get((_,x),(_,y)) -> print_space outchan n;Printf.fprintf outchan "%s" "Get\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2)
| Put((_,x),(_,y),(_,z)) -> print_space outchan n;Printf.fprintf outchan "%s" "PUT\n";print_syntax outchan x (n+2);print_syntax outchan y (n+2);print_syntax outchan z (n+2)
and 
print_syntax_list outchan t n = match t with
|[] -> ()
|(_,x)::xs -> print_syntax outchan x n;print_syntax_list outchan xs n
and
print_idtype outchan t n = match t with
|(a,b) -> Type.print_type outchan b n;Printf.fprintf outchan "  %s\n" a
and
print_idlist outchan t n = match t with
|[] -> ()
|x::xs -> print_idtype outchan x n;print_idlist outchan xs n
and
print_space outchan n = ()(*if n = 0 then () else (Printf.fprintf outchan  " %s" "";print_space outchan (n-1))*)