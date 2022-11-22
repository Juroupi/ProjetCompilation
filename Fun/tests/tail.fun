let rec pair n =
  if n = 0 then
    true
  else if n = 1 then
    false
  else
    pair (n - 2)
in

pair 10