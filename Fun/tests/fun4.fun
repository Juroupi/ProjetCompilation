let f x = 
    6 * x 
in

let g = f in
let h = g in
let h = g in
let g = h in

g 7