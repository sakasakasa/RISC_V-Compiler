let rec fib n =
  if n <= 1 then n else
  fib (n - 1) + fib (n - 2) in
let _ = fib 30 in ()
