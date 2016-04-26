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

// TODO would be nice to separate actions by type 
type Command = 
    | LocDecl of List<Ident>
    | GlobDecl of List<Ident>
    | ValDecl of List<Ident>
    | Write of int * (Ident * Ident)
    | Read of int * (Ident * Ident)
    | RMW of int * (Ident * Ident * Ident * Ident)
//    | Choice of Command * Command 
//    | Cond of BExp * List<Command>
    | AssumeEq of Ident * Ident

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
let parseLocDecl = skipString "local" >>. ws >>. parseIdentList |>> LocDecl 
let parseValDecl = skipString "val " >>. ws >>. parseIdentList |>> ValDecl 

/// Note parseWrite / parseRead / parseRMW all pass a fresh-name generator
/// This is a mutable counter which populates the identifier field of the action. 

/// Parse a write action 
let parseWrite fg = 
    between (skipString "write(" >>. ws) 
            parseEndBrac 
            (tuple2 parseIdent (wscomma >>. parseIdent))
    |>> fun (a,b) -> Write (getFresh fg, (a, b)) 

/// Parse a read action
let parseRead fg = 
    between (skipString "read(" >>. ws) 
            parseEndBrac 
            (tuple2 parseIdent (wscomma >>. parseIdent))
    |>> fun (a,b) -> Read (getFresh fg, (a, b)) 

/// Parse a RMW action 
let parseRMW fg = 
    between (skipString "RMW(" >>. ws) 
            parseEndBrac 
            (tuple4 (parseIdent .>> wscomma) 
                    (parseIdent .>> wscomma) 
                    (parseIdent .>> wscomma) 
                    parseIdent) 
    |>> fun (a,b,c,d) -> RMW (getFresh fg, (a, b, c, d)) 

/// Parse an assume operation 
let parseAssume =
    between (skipString "assume(" >>. ws)
            parseEndBrac 
            (tuple2 parseIdent (ws >>. skipString "==" >>. ws >>. parseIdent) ) 
    |>> fun (a,b) -> AssumeEq (a,b)

/// Parse the file name 
let parseName = skipString "/**" >>. ws >>. parseIdent .>> skipRestOfLine true 

/// Parse a single command terminated by a semicolon 
let parseDecl fg =    (choice[ parseLocDecl
                               parseGlobDecl 
                               parseValDecl ]) .>> (ws .>> pstring ";" .>> ws) 

let parseCmd fg = (choice[ (parseWrite fg)
                           (parseRead fg) 
                           //(parseRMW fg) 
                           parseAssume ]) .>> (ws .>> pstring ";" .>> ws) 
 
/// Parse an optimisation script                                                  
let parseOptScript fg : Parser<_, unit> = 
    tuple4 parseName 
           (many (parseDecl fg) .>> sepr)
           (many (parseCmd fg) .>> sepr)
           (many (parseCmd fg) .>> eof) 

/// Parse a simple script 
let parseSimpScript fg : Parser<_, unit> = 
    tuple3 parseName 
           (many (parseDecl fg) .>> sepr)
           (many (parseCmd fg) .>> eof)
    |>> (fun (a,b,c) -> (a, (b @ c)))  


/// Parse a named file 
let parseFile name parser = 
    let stream, streamName = (IO.File.OpenRead(name) :> IO.Stream, name) in 
    runParserOnStream parser () streamName stream Text.Encoding.UTF8

 