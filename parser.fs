module Stellite.parser 

open System
open FParsec 

/// Hack to avoid warnings about type instantiation
type UserState = unit 
type Parser<'t> = Parser<'t, UserState>

/// Identifiers are strings
type Ident = string 

/// Boolean expressions
type BExp = 
    | Eq of Ident * Ident 
    | Neq of Ident * Ident 

type Command = 
    | LocDecl of List<Ident>
    | GlobDecl of List<Ident>
    | ValDecl of List<Ident>
    | Write of Ident * Ident
    | Read of Ident * Ident
    | RMW of Ident * Ident * Ident
    | Choice of Command * Command 
    | Cond of BExp * List<Command>
    | Assert of BExp 

let com = skipString "//" .>> skipRestOfLine true

/// Parser for skipping zero or more whitespace characters.
let ws = spaces <|> com 
let wscom = ws >>. skipString "," .>> ws 

let parseVarname = many1Chars2 (pchar '_' <|> asciiLetter)
                          (pchar '_' <|> asciiLetter <|> digit)

let parseIdentList = sepBy parseVarname (ws .>> pstring "," .>> ws)

let parseGlobDecl = 
    skipString "global " >>. parseIdentList |>> GlobDecl 

let parseLocDecl = 
    skipString "local" >>. ws >>. parseIdentList |>> LocDecl 

let parseValDecl = 
    skipString "val " >>. ws >>. parseIdentList |>> ValDecl 

let parseEndBrac = (ws .>> skipString ")") 

let parseWrite = 
    between (skipString "write(" >>. ws) 
            parseEndBrac 
            (parseVarname .>>. (wscom >>. parseVarname))
    |>> Write

let parseRead = 
    between (skipString "read(" >>. ws) 
            parseEndBrac 
            (parseVarname .>>. (wscom >>. parseVarname))
    |>> Read

let parseRMW = 
    between (skipString "RMW(" >>. ws) 
            parseEndBrac 
            (tuple3 (parseVarname .>> wscom) 
                    (parseVarname .>> wscom) 
                    parseVarname) 
    |>> RMW 

let parseUnit = 
    ws >>. 
    choice[ parseLocDecl
            parseGlobDecl 
            parseValDecl
            parseWrite
            parseRead 
            parseRMW ] 
    .>> ws .>> pstring ";" .>> ws 

let parseScript : Parser<_> = ws >>. many parseUnit .>> eof 