open KNormal

let global_counter = ref 0 (* メモリ上のどこにあるか　*)
let globallist = ref [] (* 変数名と番地の対応　*)
let globals = ref [] (*globals.mlで定義されたarrayおよびtuple*)

let rec g env (pos, ebody) = match ebody with
| Let((x,t),(pos',e1),e2) -> (match e1 with
     | Int(i) -> g ((x,i)::env) e2
     | Array(y,z) -> 
         let n = (List.assoc y env) in 
         (global_counter := !global_counter + 4 * n;g env e2)
     | GlobalArray(y,z) -> 
         let n = (List.assoc y env) in 
         (globallist :=(x,!global_counter)::(!globallist);
         global_counter := !global_counter + 4 * n;
         globals := x::!globals;g env e2
         )
     | Tuple(es) ->
         let n = List.length es in 
         (global_counter := !global_counter + 4 * n;g env e2)
     | GlobalTuple(es) -> 
        let n = List.length es in 
        (globallist :=(x,!global_counter)::(!globallist);
        global_counter := !global_counter + 4 * n;
        globals := x::!globals;g env e2
        )
     | _ -> g env e2
     )
| _ -> ()

let rec print_global l = match l with
|[] -> ()
| (x,n)::xs -> print_global xs;(Printf.printf "%s=%d\n" x n)

let rec list_include a b (*aがbに含まれる*) = match a with
| [] -> true
| x::xs -> (List.mem x b) && (list_include xs b)

let f e = (g [] e);e