let z = 5 in

let ajoute_cinq x =
    x + z
in

let ajoute_sept x =
    (ajoute_cinq x) + 2
in

ajoute_sept 10