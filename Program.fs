module Program



open Parser
open Extensions



type Repl =
  { state       : Eval.State
  ; whatToPrint : Eval.WhatToPrint
  }



module Repl =
  let init =
    { state       = Eval.State.empty
    ; whatToPrint = Eval.WhatToPrint.JustResult
    }



  let eval (s : string) (r : Repl) =
    match s with
    | ":show nothing"    -> {r with whatToPrint = Eval.WhatToPrint.Nothing}
    | ":show something"  -> {r with whatToPrint = Eval.WhatToPrint.JustResult}
    | ":show everything" -> {r with whatToPrint = Eval.WhatToPrint.AllSteps}

    | _ ->
        match Parser.parse s with
        | AST ast   -> {r with state = Eval.AST.eval r.whatToPrint r.state ast}
        | Error err -> printfn "%s" err; r



  let run (r : Repl) =
    let rec go (buffer : string []) (r : Repl) =
      match System.Console.ReadLine () with
      | s when String.endsWith ";;" s ->
          let ss =
            String.takeNOrLess (String.length s - 2) s
            |> String.filter ((<>) '\n')
            |> Array.snoc buffer

          match String.concat "" ss with
          |":quit" -> ()

          | ":clear" ->
              System.Console.Clear ()
              printf "\n> "
              go [||] r

          |  s ->
              let r2 = eval s r
              printf "\n> "
              go [||] r2

      | s ->
          printf "  "
          go (Array.snoc buffer s) r

    printf "\n> "
    go [||] r



[<EntryPoint>]
let main _ =
    printfn "++++++++++++++++++++++++++++++++++++++++++++++++++++++++"
    printfn "+                 Welcome to JML REPL!                 +"
    printfn "+ An interactive environment for Joel's Meta Language. +"
    printfn "++++++++++++++++++++++++++++++++++++++++++++++++++++++++"
    Repl.run Repl.init
    0



