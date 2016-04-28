module Main

open System

open FParsec 
open FParsec.CharParsers

open Stellite.parser
open Stellite.translator 

//let testfile = "../../sample.stl"
//let maintest argv = 
//    let fg = freshGen () in  
//    match (parseFile fg) testfile with 
//    | Success(result,_,_) -> 
//        let res = dispExec result 
//        for l in res do printfn "%s" l
//        0 
//    | Failure(errorMsg,_,_) -> printfn "Failure %s" errorMsg; 1 

[<EntryPoint>]
let main argv = 
    try match argv with 
            | [|first|] ->
                let fg = freshGen () in  
                match parseFile first (parseOptScript fg) with 
                    | Success(result,_,_) -> 
                        printfn "Parse:\n %A" result 
                        let res = dispOptPredRelat result 
                        printfn "Predicates:" 
                        for l in res do printfn "%s" l
                        0 
                    | Failure(errorMsg,_,_) -> printfn "Failure %s" errorMsg; 1 
            | _ -> printfn "One argument expected"; 1
    with 
    | :? System.IO.FileNotFoundException -> printfn "Couldn't find the specified file!"; 1 
