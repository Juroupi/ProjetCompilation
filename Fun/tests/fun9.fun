let ajoute_sept x f =
    (f x) + 7
in

ajoute_sept 10 (fun x -> x + 5)