module Main

open System
open FParsec 
open FParsec.CharParsers
open Stellite.parser

let parseFile name = 
    let stream, streamName = (IO.File.OpenRead(name) :> IO.Stream, name) in 
    runParserOnStream parseScript () streamName stream Text.Encoding.UTF8

[<EntryPoint>]
let main argv = 
    match argv with 
        | [|first|] -> 
            match parseFile first with 
                | Success(result,_,_) -> printfn "Success %A" result; 0 
                | Failure(errorMsg,_,_) -> printfn "Failure %s" errorMsg; 1 
        | _ -> 
            printfn "One argument expected" 
            1
           
