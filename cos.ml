 let rec my_cos x = 
 let rec pi_div e x = 
    if (not (fless e 0.)) && fless e (3.1415926535*.2.) then e 
    else if (fless e 0.) && (not (fless x (-.e))) then  pi_div (e+.x) (x/.2.)
    else if fless 0. e && not (fless x e) then pi_div (e-.x/.2.) (x/.2.)
    else pi_div e (x*.2.) in
 let rec pi4div x = 
     if fless x (3.1415927/.2.) then (x,1.)
     else if fless x 3.1415927 then (3.1415927-.x,-.1.)
     else if fless x (3.1415927*.1.5) then (x-.3.1415927,-.1.)
     else (3.1415927*.2.-.x,1.) in 
 let rec tailor y = 
    let xx = y *. y in
    let t2 = xx /. 2. in
    let t4 = xx *. t2 /. 12. in
    let t6 = xx *. t4 /. 30. in
    let t8 = xx *. t6 /. 56. in
    let t10 = xx *. t8 /. 90. in
    let t12 = xx *. t10 /. 132. in
        1. -. t2 +. t4 -. t6 +. t8 -. t10 +. t12 in 
 let (a,b) = pi4div(pi_div x (3.1415926535 *. 2.)) in b  *. (tailor a) in let _ = my_cos 3. in ()