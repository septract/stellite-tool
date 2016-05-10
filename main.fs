module Main

open System
open FParsec 

open Stellite.parser
open Stellite.translator 

[<EntryPoint>]
let main argv = 
    try match argv with 
            | [|filen|] ->
                let fg = freshGen () in  
                match parseFile filen (parseOptScript fg) with 
                    | Success(result,_,_) -> 
                        //printfn "Parse:\n %A" result 
                        let res = dispOptPredRelat 7 filen result 
                        //printfn "Predicates:" 
                        for l in res do printfn "%s" l
                        0
                    | Failure(errorMsg,_,_) -> eprintfn "Failure %s" errorMsg; 1 
            | _ -> eprintfn "One argument expected"; 1
    with 
    | :? System.IO.FileNotFoundException -> eprintfn "Couldn't find the specified file!"; 1 
