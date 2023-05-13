open Asm 

let rec g exp = match exp with (*ゼロレジスタを利用した覗き穴最適化*)
| Let(pos,(x',t'),Li(0),Ans(pos',IfEq(x,V(y),e1,e2))) when x' = y ->
   Ans(pos',IfEq("%x0",V(x),g e1, g e2))
| Let(pos,(x',t'),Li(0),Ans(pos',IfEq(x,V(y),e1,e2))) when x' = x ->
   Ans(pos',IfEq("%x0",V(y),g e1, g e2))
| Let(pos,(x',t'),IfEq(x,y,e1,e2),e) ->
  Let(pos,(x',t'),IfEq(x,y,g e1,g e2),g e)
| Let(pos,(x',t'),IfLE(x,y,e1,e2),e) ->
  Let(pos,(x',t'),IfLE(x,y,g e1,g e2),g e)
| Let(pos,(x',t'),IfGE(x,y,e1,e2),e) ->
  Let(pos,(x',t'),IfGE(x,y,g e1,g e2),g e)
| Let(pos,(x',t'),IfFEq(x,y,e1,e2),e) ->
  Let(pos,(x',t'),IfFEq(x,y,g e1,g e2),g e)
| Let(pos,(x',t'),IfFLE(x,y,e1,e2),e) ->
  Let(pos,(x',t'),IfFLE(x,y,g e1,g e2),g e)
| Let(pos,(x',t'),com, e) ->
   Let(pos,(x',t'),com,g e)
| _ -> exp

let rec occur e = (* 直後に関数呼び出しが起こるか *)
match e with
| Let(_,_,CallDir(_,_,_),_) -> true
| Let(_,_,IfEq(_,_,e1,e2),e3) -> occur e1 && occur e2
| Let(_,_,IfLE(_,_,e1,e2),e3) -> occur e1 && occur e2
| Let(_,_,IfGE(_,_,e1,e2),e3) -> occur e1 && occur e2
| Let(_,_,IfFEq(_,_,e1,e2),e3) -> occur e1 && occur e2
| Let(_,_,IfFLE(_,_,e1,e2),e3) -> occur e1 && occur e2
| Let(_,_,IfZ(_,e1,e2),e3) -> occur e1 && occur e2
| Let(_,_,IfPos(_,e1,e2),e3) -> occur e1 && occur e2
| Let(_,_,IfNeg(_,e1,e2),e3) -> occur e1 && occur e2
| Let(_,_,_,e1) -> occur e1 
| _ ->  false

let rec occur2 e = 
match e with
| Let(_,_,CallDir2(_,_,_),_) -> true
| Let(_,_,CallDir3(_,_,_),_) -> true
| Let(_,_,Save(_,_),_) -> false
| Let(_,_,Restore(_),_) -> false
| Let(_,_,IfEq(_,_,e1,e2),e3) -> false(*occur2 e1 && occur2 e2*)
| Let(_,_,IfLE(_,_,e1,e2),e3) -> false(*occur2 e1 && occur2 e2*)
| Let(_,_,IfGE(_,_,e1,e2),e3) -> false(*occur2 e1 && occur2 e2*)
| Let(_,_,IfFEq(_,_,e1,e2),e3) -> false(*occur2 e1 && occur2 e2*)
| Let(_,_,IfFLE(_,_,e1,e2),e3) -> false(*occur2 e1 && occur2 e2*)
| Let(_,_,IfZ(_,e1,e2),e3) -> false
| Let(_,_,IfPos(_,e1,e2),e3) -> false
| Let(_,_,IfNeg(_,e1,e2),e3) -> false
| Let(_,_,_,e1) -> occur2 e1 
| Ans(_,_) -> false
| _ -> assert false

let rec i exp flag = match (flag,exp) with (* リンクレジスタの保存に関する覗き穴最適化　*)
| (0,Let(pos,(x1,t1),CallDir(Id.L(x),ys,zs),e)) ->
   if occur e then
   Let(pos,(x1,t1),CallDir1(Id.L(x),ys,zs),(i e 1))
   else
   Let(pos,(x1,t1),CallDir(Id.L(x),ys,zs), (i e 0))
| (1,Let(pos,(x1,t1),CallDir(x,ys,zs),e)) ->
   if occur e then
   Let(pos,(x1,t1),CallDir2(x,ys,zs),(i e 1))
   else
   Let(pos,(x1,t1),CallDir3(x,ys,zs),(i e 0))
| (n,Let(pos,(x',t'),IfEq(x,y,e1,e2),e)) ->
    Let(pos,(x',t'),IfEq(x,y,i e1 n,i e2 n),i e 0)
| (n,Let(pos,(x',t'),IfLE(x,y,e1,e2),e)) ->
    Let(pos,(x',t'),IfLE(x,y,i e1 n,i e2 n),i e 0)
| (n,Let(pos,(x',t'),IfGE(x,y,e1,e2),e)) ->
    Let(pos,(x',t'),IfGE(x,y,i e1 n,i e2 n),i e 0)
| (n,Let(pos,(x',t'),IfFEq(x,y,e1,e2),e)) ->
    Let(pos,(x',t'),IfFEq(x,y,i e1 n,i e2 n),i e 0)
| (n,Let(pos,(x',t'),IfFLE(x,y,e1,e2),e)) ->
    Let(pos,(x',t'),IfFLE(x,y,i e1 n,i e2 n),i e 0)
| (n,Let(pos,(x',t'),IfZ(x,e1,e2),e)) ->
    Let(pos,(x',t'),IfZ(x,i e1 n,i e2 n),i e 0)
| (n,Let(pos,(x',t'),IfPos(x,e1,e2),e)) ->
    Let(pos,(x',t'),IfPos(x,i e1 n,i e2 n),i e 0)
| (n,Let(pos,(x',t'),IfNeg(x,e1,e2),e)) ->
    Let(pos,(x',t'),IfNeg(x,i e1 n,i e2 n),i e 0)
| (0,Let(pos,(x',t'),com, e)) ->
   Let(pos,(x',t'),com,i e 0)
| (1,Let(pos,(x',t'),com, e)) ->
   Let(pos,(x',t'),com,i e 1)
| (_,Ans(pos,IfEq(x,y,e1,e2))) -> 
   Ans(pos,IfEq(x,y, i e1 0,i e2 0))
| (_,Ans(pos,IfLE(x,y,e1,e2))) -> 
   Ans(pos,IfLE(x,y, i e1 0,i e2 0))
| (_,Ans(pos,IfGE(x,y,e1,e2))) -> 
   Ans(pos,IfGE(x,y, i e1 0,i e2 0))
| (_,Ans(pos,IfFEq(x,y,e1,e2))) -> 
   Ans(pos,IfFEq(x,y, i e1 0,i e2 0))
| (_,Ans(pos,IfFLE(x,y,e1,e2))) -> 
   Ans(pos,IfFLE(x,y, i e1 0,i e2 0))
| (_,Ans(pos,IfZ(x,e1,e2))) -> 
   Ans(pos,IfZ(x,i e1 0,i e2 0))
| (_,Ans(pos,IfPos(x,e1,e2))) -> 
   Ans(pos,IfPos(x,i e1 0,i e2 0))
| (_,Ans(pos,IfNeg(x,e1,e2))) -> 
   Ans(pos,IfNeg(x,i e1 0,i e2 0))
| (0,Ans(pos,CallDir(x,ys,zs))) ->
   Ans(pos,CallDir(x,ys,zs))
| (1,Ans(pos,CallDir(x,ys,zs))) ->
   Ans(pos,CallDir(x,ys,zs))
| (_,Ans(pos,e)) ->
   Ans(pos,e)
| _ -> exp


let h { name = l; args = xs; fargs = ys; body = e; ret = t } = 
{ name = l; args = xs; fargs = ys; body = i(g e) 0; ret = t }

let f (Prog(data, fundefs, e)) = 
  Prog(data,List.map h fundefs, i(g e) 0) 