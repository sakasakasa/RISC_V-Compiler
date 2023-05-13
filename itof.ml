 let c = 
  let rec pi_div e x = 
       if 0. <= e && e < (3.1415926535*.2.) then e 
     else if 0. > e && -.e <= x then pi_div (e+.x) (x/.2.)
     else if 0. < e && e <= x then pi_div (e-.x/.2.) (x/.2.)
     else pi_div e (x*.2.) in
  let rec pi4div x = 
     if x < (3.1415926535/.2.) then (x,1.)  
     else if x < (3.1415926535) then (3.1415926535-.x ,-1.)
     else if x < (3.1415926535*.1.5) then (x-.3.1415926535,-1.)
     else ((3.1415926535*.2.)-.x,1.) in
  let rec tailor y = 
     let xx = y *. y in
     let t2 = xx /. 2. in
     let t4 = xx *. t2 /. 12. in
     let t6 = xx *. t4 /. 30. in
     let t8 = xx *. t6 /. 56. in
     let t10 = xx *. t8 /. 90. in
     let t12 = xx *. t10 /. 132. in
     1. -. t2 +. t4 -. t6 +. t8 -. t10 +. t12 in
  let (a,b) = pi4div(pi_div 1.2 (3.1415926535 *. 2.)) in
  b *. (tailor a) 