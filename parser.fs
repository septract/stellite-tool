module Stellite.parser 

open System
open FParsec 

/// Hack to avoid warnings about type instantiation
type UserState = unit 
type Parser<'t> = Parser<'t, UserState>

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
    | RMW of int * (Ident * Ident * Ident) 
    | Choice of Command * Command 
//    | Cond of BExp * List<Command>
    | AssumeEq of Ident * Ident

/// Creates a new fresh generator.
let freshGen () = ref 0

/// Takes a fresh number out of the generator.
/// This method is NOT thread-safe.
let getFresh fg =
    let result = !fg
    fg := !fg + 1
    result

let com = skipString "//" .>> skipRestOfLine true

let ws = skipMany (com <|> spaces1) 

let wscomma = ws >>. skipString "," .>> ws 

let parseEndBrac = (ws .>> skipString ")") 

let parseIdent = many1Chars2 (pchar '_' <|> asciiLetter)
                          (pchar '_' <|> asciiLetter <|> digit)

let parseIdentList = sepBy parseIdent wscomma

let parseGlobDecl = skipString "global " >>. ws >>. parseIdentList |>> GlobDecl 

let parseLocDecl = skipString "local" >>. ws >>. parseIdentList |>> LocDecl 

let parseValDecl = skipString "val " >>. ws >>. parseIdentList |>> ValDecl 

let parseWrite fg = 
    between (skipString "write(" >>. ws) 
            parseEndBrac 
            (tuple2 parseIdent (wscomma >>. parseIdent))
    |>> fun (a,b) -> Write (getFresh fg, (a, b)) 

let parseRead fg = 
    between (skipString "read(" >>. ws) 
            parseEndBrac 
            (tuple2 parseIdent (wscomma >>. parseIdent))
    |>> fun (a,b) -> Read (getFresh fg, (a, b)) 

let parseRMW fg = 
    between (skipString "RMW(" >>. ws) 
            parseEndBrac 
            (tuple3 (parseIdent .>> wscomma) 
                    (parseIdent .>> wscomma) 
                    parseIdent) 
    |>> fun (a,b,c) -> RMW (getFresh fg, (a, b, c)) 

let parseAssume =
    between (skipString "assume(" >>. ws)
            parseEndBrac 
            (tuple2 parseIdent (ws >>. skipString "==" >>. ws >>. parseIdent) ) 
    |>> fun (a,b) -> AssumeEq (a,b)

let parseName = skipString "//" >>. ws >>. parseIdent .>> skipRestOfLine true 

let parseCommand fg = (choice[ parseLocDecl
                               parseGlobDecl 
                               parseValDecl
                               (parseWrite fg)
                               (parseRead fg) 
                               //(parseRMW fg) 
                               parseAssume ]) .>> (ws .>> pstring ";" .>> ws) 
                   
let parseScript fg : Parser<_> = 
    parseName .>>. many (parseCommand fg) .>> eof 