module Log



let log x =
  printfn "%A" x;
  x



let logp x =
  printfn "%A" x
  ignore (System.Console.ReadLine())
  x



let logd x =
  printfn "%A" x
  ignore (System.Console.ReadLine())
  failwith "death"



let logWith f x = f x |> printfn "%s"; x


let logWithI (n : int) (f : _ -> string) (x : _) =
  printfn "%s%s" (String.replicate n " ") (f x)
  x


let logWithI2 (f : _ -> string) (x : _) = logWithI 2 f x
