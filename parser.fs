module Stellite.parser 

open System
open FParsec 

/// Creates a new fresh generator.
let freshGen () = ref 0

/// Takes a fresh number out of the generator.
/// This method is NOT thread-safe.
let getFresh fg =
    let result = !fg
    fg := !fg + 1
    result

/// Identifiers are strings
type Ident = string 

///// Boolean expressions
//type BExp = 
//    | Eq of Ident * Ident 
//    | Neq of Ident * Ident 

type Operation = 
    | Write of Ident * Ident
    | Read of Ident * Ident
    | ReadN of Ident
    | RMW of Ident * Ident * Ident
//    | Choice of Command * Command 
//    | Cond of BExp * List<Command>
    | AssumeEq of Ident * Ident
    | FenceSC  

type Command = 
    | ThrDecl of List<Ident>
    | GlobDecl of List<Ident>
    | ValDecl of List<Ident>
    | Op of int * Operation

/// Parse comment 
let com = skipString "//" .>> skipRestOfLine true

/// Parse a section separator 
let sepr = skipString "/**" .>> skipRestOfLine true

/// Parse whitespace
let ws = skipMany (com <|> spaces1) 

/// Parse a comma surrounded by whitespace
let wscomma = ws >>. skipString "," .>> ws 

/// Parse an end bracket
let parseEndBrac = (ws .>> skipString ")") 

/// Parse an identifier
let parseIdent = many1Chars2 (pchar '_' <|> asciiLetter)
                             (pchar '_' <|> asciiLetter <|> digit)
let parseIdentList = sepBy parseIdent wscomma

/// Parse declaration lists 
let parseGlobDecl = skipString "global " >>. ws >>. parseIdentList |>> GlobDecl 
let parseThrDecl = skipString "local" >>. ws >>. parseIdentList |>> ThrDecl 
let parseValDecl = skipString "val " >>. ws >>. parseIdentList |>> ValDecl 

/// Note parseWrite / parseRead / parseRMW all pass a fresh-name generator fg
/// This is a mutable counter which populates the identifier field of the action. 

/// Create a fresh name for the operation, and wrap in the Comamnd type
let makeOp c fg : Command = Op ((getFresh fg), c) 

/// Parse a write action 
let parseWrite fg = 
    between (skipString "write(" >>. ws) 
            parseEndBrac 
            (tuple2 parseIdent (wscomma >>. parseIdent))
    |>> fun (a,b) -> makeOp (Write (a, b)) fg 

/// Parse a read action
let parseRead fg = 
    between (skipString "read(" >>. ws) 
            parseEndBrac 
            (tuple2 parseIdent (wscomma >>. parseIdent))
    |>> fun (a,b) -> makeOp (Read (a,b)) fg 

/// Parse a readN action
let parseReadN fg = 
    between (skipString "readN(" >>. ws) 
            parseEndBrac 
            parseIdent
    |>> fun a -> makeOp (ReadN a) fg 

/// Parse a RMW action 
let parseRMW fg = 
    between (skipString "RMW(" >>. ws) 
            parseEndBrac 
            (tuple3 (parseIdent .>> wscomma) 
                    (parseIdent .>> wscomma) 
                    parseIdent) 
    |>> fun (a,b,c) -> makeOp (RMW (a,b,c)) fg 

(*
/// Parse an assume operation 
let parseAssume fg =
    between (skipString "assumeEq(" >>. ws)
            parseEndBrac 
            (tuple2 parseIdent (ws >>. skipString "," >>. ws >>. parseIdent) ) 
    |>> fun (a,b) -> AssumeEq (getFresh fg, (a,b))
*) 

/// Parse an SC fence operation 
let parseFenceSC fg = 
    (skipString "fenceSC" >>. ws)
    |>> fun _ -> makeOp FenceSC fg 

/// Parse the file name 
let parseName = skipString "/**" >>. ws >>. parseIdent .>> skipRestOfLine true 

/// Parse a single declaration / command terminated by a semicolon 
let parseDecl fg = (choice[ parseThrDecl
                            parseGlobDecl 
                            parseValDecl ]) .>> (ws .>> pstring ";" .>> ws) 

let parseCmd fg = (choice[ parseWrite fg
                           parseRead fg 
                           parseReadN fg 
                           //(parseRMW fg) 
                           // parseAssume fg 
                           parseFenceSC fg]) .>> (ws .>> pstring ";" .>> ws) 
 
/// Parse an optimisation script                                                  
let parseOptScript fg : Parser<String * List<Command> * List<Command> * List<Command>, unit> = 
    tuple4 (parseName .>> ws) 
           (many (parseDecl fg) .>> sepr .>> ws)
           (many (parseCmd fg) .>> sepr .>> ws)
           (many (parseCmd fg) .>> eof) 
(*
/// Parse a simple script 
let parseSimpScript fg : Parser<_, unit> = 
    tuple3 (parseName .>> ws) 
           (many (parseDecl fg) .>> sepr .>> ws)
           (many (parseCmd fg) .>> eof)
    |>> (fun (a,b,c) -> (a, (b @ c)))  
*) 

/// Parse a named file 
let parseFile name parser = 
    let stream, streamName = (IO.File.OpenRead(name) :> IO.Stream, name) in 
    runParserOnStream parser () streamName stream Text.Encoding.UTF8

 
