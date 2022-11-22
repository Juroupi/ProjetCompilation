let fact n =
  let rec fact n res =
    if n <= 1 then
      res
    else
      fact (n - 1) (n * res)
  in fact n 1
in

fact 5