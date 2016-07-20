module Stellite.translator 

open Stellite.parser

// TODO: refactor so actions are a different subtype? 

// Concat a list of strings with a fixed string in between
let rec intersperse i xs = 
    match xs with
    | [] -> ""  
    | [x] -> x 
    | x::y::ys -> x + i + intersperse i (y::ys)

/// Display the declared global variable names
let dispGlobDecl cmds = 
    List.map (function | GlobDecl vs -> vs 
                       | _ -> []) cmds 
    |> List.concat 

/// Display the declared local variable names
let dispThrDecl cmds = 
    List.map (function | ThrDecl vs -> vs 
                           | _ -> []) cmds 
    |> List.concat 

/// Display the declared values
let dispValDecl cmds = 
    List.map (function | ValDecl vs -> vs  
                       | _ -> []) cmds
    |> List.concat 

/// Display the variable names, then the value names
// TODO: should be possible to refactor these three into something more general
let dispAllDecl cmds =   
     (dispGlobDecl cmds |> intersperse ", ") + 
     ", " + 
     (dispThrDecl cmds |> intersperse ", ") // + ", " + dispValDecl cmds

/// Check whether a command is an action
let (|HasGloc|_|) = 
  function | Write (x,_) | Read (x,_) | ReadN x | RMW (x,_,_) -> Some x
           | _ -> None 

/// Check whether a command is an action
let (|HasLloc1|_|) = 
  function | Write (_,x) | Read (_,x) | RMW (_,x,_) -> Some x
           | _ -> None

/// Check whether a command is an assumeEq
let (|HasLloc2|_|) = 
  function | RMW (_,_,x) -> Some x
           | _ -> None

(*
let isFence = function | FenceSC _ -> true
                       | _ -> false 
*) 

(*
/// Get the identifier for an action 
let getActionId a = 
    match a with 
    | Write (i,_) | Read (i,_) | ReadN (i,_) | RMW (i,_) | AssumeEq (i,_) | FenceSC i -> i
    | _ -> failwith "getActionId: not a valid parameter!" 


/// Get the variable for an action 
let getActionGloc a = 
    match a with 
    | Write (_,(x,_)) | Read (_,(x,_)) | ReadN (_,x) -> x
    //| RMW (_,(x,_,_)) -> x
    | _ -> failwith "getActionGloc: not a valid parameter!" 

/// Get the local variable for an action 
let getActionlloc1 a = 
    match a with 
    | Write (_,(_,x)) | Read (_,(_,x)) | RMW (_,(_,x,_)) -> x
    //| RMW (_,(x,_,_)) -> x
    | _ -> failwith "getActionlloc1: not a valid parameter!" 

/// Get the local variable for an action 
let getActionlloc2 a = 
    match a with 
    | RMW (_,(_,_,x)) -> x
    | _ -> failwith "getActionlloc2: not a valid parameter!" 
*) 

/// Generate the name for the action. 
let actName (i,x) = "op" + string i

/// Get the correct set for the action. 
let actKind (i,c) = 
    match c with 
    | Write _ -> "Write"
    | Read _ -> "Read"
    | ReadN _ -> "ReadN" 
    | RMW _ -> "RMW" 
    | AssumeEq _ -> "AssmEq" 
    | FenceSC _ -> "FenceSC" 

/// Helper function to convert a sequence of names into an Alloy sequence definition. 
let rec seqDefn names : string = 
    match names with 
    | a :: b :: rest -> " + (" + string a + "->" + string b + ")" + seqDefn (b :: rest) 
    | _ -> "" 


(*********************************************************************
 *  Display functions  
 *********************************************************************) 

let dispSimpPredRelat ((name, cmds) : string * List<Command>) : List<string> =
    let allOps = List.choose (function Op (i,x) -> Some (i,x) | _ -> None) cmds 
    let glocOps = List.choose (fun (i,x) -> (match x with | HasGloc v -> Some (i,v) | _ -> None)) allOps 
    let lloc1Ops = List.choose (fun (i,x) -> (match x with | HasLloc1 v -> Some (i,v) | _ -> None)) allOps 
    let lloc2Ops = List.choose (fun (i,x) -> (match x with | HasLloc2 v -> Some (i,v) | _ -> None)) allOps in 
      [ "pred " + name ] @
      [ "         [ dom : set Action, kind : Action -> Kind," ] @
      [ "           gloc : Action -> Glob, lloc1, lloc2 : Action -> Thr, " ] @
      [ "           sb : Action -> Action, " + (dispGlobDecl cmds |> intersperse ", ") + " : Glob, " 
               + (dispThrDecl cmds |> intersperse ", ") + " : Thr ] { "] @
      [ "  sb in (dom -> dom)" ] @ 
      (if (List.length allOps > 0) then 
        [ "  some disj " + (List.map actName allOps |> intersperse ", ") + " : Action | "]
      else []) @ 
      [ "  { "] @ 
      [ "    dom = " + (List.fold (fun c a -> (actName a) + " + " + c) "" allOps) + "Call + Ret" ] @ 
      [ "    (Call -> Ret)" + (List.map actName allOps |> seqDefn) + " in sb" ] @ 
      (List.map (fun c -> "    " + (actName c) + ".gloc = " + (snd c)) glocOps) @ 
      (List.map (fun c -> "    " + (actName c) + ".lloc1 = " + (snd c)) lloc1Ops) @ 
      (List.map (fun c -> "    " + (actName c) + ".lloc2 = " + (snd c)) lloc2Ops) @ 
      (List.map (fun c -> "    " + (actName c) + " in kind." + (actKind c)) allOps) @ 
      [ "  }"] @  
      [ "}"] 

let dispHarnessPredRelat name decl = 
    [ "// Optimisation name: " + name ] @ 
    [ "pred optPred" ] @
    [ "     [ dom, dom' : set Action," ] @
    [ "       kind, kind' : Action -> Kind,"] @
    [ "       gloc, gloc' : Action -> Glob," ] @ 
    [ "       lloc1, lloc1' : Action -> Thr," ] @
    [ "       lloc2, lloc2' : Action -> Thr," ] @
    [ "       sb, sb' : Action -> Action ] {" ] @ 
    [ "  one Call & (dom + dom')" ] @ 
    [ "  one Ret & (dom + dom')" ] @ 
    [ "  preexecWF[dom, kind, gloc, lloc1, lloc2, sb]" ] @ 
    [ "  preexecWF[dom', kind', gloc', lloc1', lloc2', sb']" ] @ 
    [ "  some disj " + (dispGlobDecl decl |> intersperse ", ") + " : Glob, " + 
             "disj " + (dispThrDecl decl |> intersperse ", ") + " : Thr | {" ] @ 
    [ "    optLHS[dom - Extern, kind, gloc, lloc1, lloc2, sb, " + dispAllDecl decl + "]" ] @ 
    [ "    optRHS[dom' - Extern, kind', gloc', lloc1', lloc2', sb', " + dispAllDecl decl + "]" ] @ 
    [ "  }" ] @ 
    [ "}" ] 


let dispOptPredRelat (depth :int) (filen : string) ((name,decl,lhs,rhs) : string * List<Command> * List<Command> * List<Command>) 
                : List<string> = 
    [ "// Warning: automatically generated file - modifications will be overwritten!" ] @
    [ "// Generated by Stellite from " + filen ] @
    [ "module " + name ] @
    [ "open ../c11Relat" ] @ 
    [ "open ../histRelat" ] @ 
    [ "" ] @ 
    dispHarnessPredRelat name decl @
    [ "" ] @ 
    dispSimpPredRelat ("optLHS", (decl @ lhs)) @ 
    [ "" ] @ 
    dispSimpPredRelat ("optRHS", (decl @ rhs)) @ 
    [ "" ] @ 
    [ "check { histIncl } for " + string depth ] @
    [ " but"] @
    // Constrain the domain of global / local variables to exactly those in the opt definition
    [ "  exactly 1 Call, exactly 1 Ret," ] @ 
    [ "  exactly " + (dispGlobDecl decl |> List.length |> string) + " Glob," ] @
    [ "  exactly " + (dispThrDecl decl |> List.length |> string) + " Thr" ] 


