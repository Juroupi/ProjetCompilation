let f x =
    6 * x
in

let g x =
    3 * x
in

let tmp = f in
let f = g in
let g = tmp in

g (f 6) + tmp 1