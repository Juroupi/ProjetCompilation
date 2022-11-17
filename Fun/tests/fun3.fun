let z = 567 in

let f = 
    fun x ->
        let w = 123 in
        fun y ->
            x + y + z + w
in

f 7 6