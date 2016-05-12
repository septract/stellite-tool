module Main

open System
open FParsec
open Argu 

open Stellite.parser
open Stellite.translator 

// Command-line arguments 
type CLIArguments =
    | File of string
    | Depth of int
with
    interface IArgParserTemplate with
        member s.Usage =
            match s with
            | File _ -> "Target file."
            | Depth _ -> "Search depth."

// Build the argument parser
let argparser = ArgumentParser.Create<CLIArguments>()
let argusage = argparser.Usage() 

// Make a fresh number generator 
let fg = freshGen () 

// Default search depth
let defaultdepth = 6

// Main function 
[<EntryPoint>]
let main argv = 
    try let argres = argparser.Parse(argv) in 
        let depth = argres.GetResult (<@ Depth @>, defaultValue = defaultdepth)
        let filen = argres.GetResult (<@ File @>) 
        match parseFile filen (parseOptScript fg) with 
        | Success(result,_,_) -> 
            // printfn "Parse:\n %A" result 
            let res = dispOptPredRelat depth filen result 
            for l in res do printfn "%s" l
            0
        | Failure(errorMsg,_,_) -> eprintfn "Parse failure %s" errorMsg; 1 
    with 
    | :? System.IO.FileNotFoundException -> eprintfn "Couldn't open the file"; 1 
    | :? System.ArgumentException -> 
             eprintf "Bad argument. Usage: %s" argusage
             1 
