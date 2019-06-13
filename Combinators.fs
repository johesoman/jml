module Combinators



let flip f x y = f y x

let curry f x y = f (x, y)

let uncurry f (x, y) = f x y

let giveLeft x y = x

let giveRight x y = y

