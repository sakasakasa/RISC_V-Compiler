type t = (* MinCamlの型を表現するデータ型 (caml2html: type_t) *)
  | Unit
  | Bool
  | Int
  | Float
  | Fun of t list * t (* arguments are uncurried *)
  | Tuple of t list
  | Array of t
  | Var of t option ref

let gentyp () = Var(ref None) (* 新しい型変数を作る *)

let rec print_type outchan t n = match t with
  | Unit -> (*print_space outchan n;*)Printf.fprintf outchan "%s" "UNIT"
  | Bool -> (*print_space outchan n;*)Printf.fprintf outchan "%s" "BOOL"
  | Int -> (*print_space outchan n;*)Printf.fprintf outchan "%s" "INT"
  | Float -> (*print_space outchan n;*)Printf.fprintf outchan "%s" "FLOAT"
  | Fun(x,y) -> (*print_space outchan n;*)Printf.fprintf outchan "%s" "FUN";print_type_list outchan x n;print_type outchan y n 
  | Tuple(x) -> (*print_space outchan n;*)Printf.fprintf outchan "%s" "TUPLE";print_type_list outchan x n
  | Array(x) -> (*print_space outchan n;*)Printf.fprintf outchan "%s" "ARRAY";print_type outchan x n
  | Var(x) -> (*print_space outchan n;*)Printf.fprintf outchan "%s" "VAR"
and 
  print_type_list outchan t n = match t with
  |[] -> ()
  |x::xs -> print_type outchan x n;print_type_list outchan xs n
and 
  print_space outchan n = if n = 0 then () else (Printf.fprintf outchan  " %s" "";print_space outchan (n-1))