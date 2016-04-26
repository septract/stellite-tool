module Stellite.translator 

open Stellite.parser

// TODO: refactor so actions are a different subtype? 

// Concat a list of strings with a fixed string in between
let rec intersperse i xs = 
    match xs with
    | [] -> ""  
    | [x] -> x 
    | x::y::ys -> x + i + intersperse i (y::ys)

/// Display the declared variable names
let dispVarDecl cmds = 
    List.map (function | GlobDecl vs -> vs 
                           | _ -> []) cmds 
    |> List.concat |> intersperse ", "

/// Display the declared values
let dispValDecl cmds = 
    List.map (function | ValDecl vs -> vs  
                       | _ -> []) cmds
    |> List.concat |> intersperse ", "

/// Display the variable names, then the value names
// TODO: should be possible to refactor these three into something more general
let dispVarValDecl cmds = 
    (List.map (function | GlobDecl vs -> vs  
                        | _ -> []) cmds) 
    @ 
    (List.map (function | ValDecl vs -> vs  
                        | _ -> []) cmds) 
    |> List.concat |> intersperse ", "

/// Check whether a command is an action
let isAct = function | Write _ | Read _ | RMW _ -> true
                     | _ -> false 

/// Get the identifier for an action 
let getActionId a = 
    match a with 
    | Write (i,_) | Read (i,_) | RMW (i,_) -> i
    | _ -> failwith "getActionId: not an action!" 

/// Get the variable for an action 
let getActionLoc a = 
    match a with 
    | Write (_,(x,_)) | Read (_,(x,_)) -> x
    //| RMW (_,(x,_,_)) -> x
    | _ -> failwith "getActionLoc: not an action!" 

/// Generate the name for the action. 
let actName c = "op" + string (getActionId c)

/// Get the correct set for the action. 
let actKind c = 
    match c with 
    | Write _ -> "Write"
    | Read _ -> "Read" 
    | RMW _ -> "RMW" 
    | _ -> failwith "actKind: not an action!"

/// Generate equality assertions for read-write and read-value pairs. 
/// These represent the effect of local variables in the semantics
let genEqRW id id2 = "op" + string id + ".rval = op" + string id2 + ".wval" 
let genEqRV id vname = "op" + string id + ".rval = " + vname

/// Generate equality assertions in a program suffix. This stops propagating when 
/// we reach a read that assigns to the same local variable. 
let rec genEqLoc i l cmds = 
    match cmds with 
    | Write (i',(_,l')) :: cmds' when l = l' -> [genEqRW i i'] @ (genEqLoc i l cmds') 
    //| RMW (i', (_,l',l'',_)) :: cmds' -> 
    //  [genEqRMW i i'] @ (genEqLoc i l cmds') 
    | AssumeEq (l',v') :: cmds' when l' = l -> [genEqRV i v'] @ (genEqLoc i l cmds') 
    | Read (_, (_,l')) :: cmds' when l = l' -> [] 
    | _ :: cmds' -> genEqLoc i l cmds'  
    | [] -> [] 

/// Generate equality assertions arising from local variables. 
let rec genEqs cmds = 
    match cmds with 
    | Read (i,(_,l)) :: cmds' | RMW (i,(_,_,_,l)) :: cmds' -> 
        (genEqLoc i l cmds') @ (genEqs cmds') 
    | c :: cmds' -> genEqs cmds'
    | [] -> []  

/// Helper function to convert a sequence of names into an Alloy sequence definition. 
let rec seqDefn names : string = 
    match names with 
    | a :: b :: rest -> " + (" + string a + "->" + string b + ")" + seqDefn (b :: rest) 
    | _ -> "" 

// TODO: deal with the case where we don't declare any explicit values? 

let dispSimpPred ((name, cmds) : string * List<Command>) : List<string> =
    let acts = (List.filter isAct) cmds in
      [ "pred " + name ] @
      [ "         [ dom : set Action, sb : Action -> Action,"] @   
      [ "           " + dispVarDecl cmds + " : Loc, " + dispValDecl cmds + " : Val ] { "] @
      [ "  sb in (dom -> dom)" ] @ 
      [ "  some disj " + (List.map actName acts |> intersperse ", ") + " : Action | { "] @ 
      [ "    dom = " + (List.map actName acts |> intersperse " + ") + " + Call + Ret" ] @ 
      [ "    (none -> none)" + (List.map actName acts |> seqDefn) + " in sb" ] @ 
      (List.map (fun c -> "    " + (actName c) + ".loc = " + (getActionLoc c)) acts) @ 
      (List.map (fun c -> "    " + (actName c) + " in " + (actKind c)) acts) @ 
      (List.map ((+) "    ") (genEqs cmds)) @ 
      [ "  }"] @  
      [ "}"] 

let dispHarnessPred name decl = 
    [ "pred " + name ] @ 
    [ "     [ dom, dom' : set Action, sb, sb' : Action -> Action ] {" ] @ 
    [ "       some " + dispVarDecl decl + " : Glob & Atomic, " + dispValDecl decl + " : Val | {" ] @ 
    [ "    " + name + "LHS[dom - Extern, sb, " + dispVarValDecl decl + "]" ] @ 
    [ "    " + name + "RHS[dom' - Extern, sb', " + dispVarValDecl decl + "]" ] @ 
    [ "  }" ] @ 
    [ "}" ] 


let dispOptPred ((name,decl,lhs,rhs) : string * List<Command> * List<Command> * List<Command>) 
                : List<string> = 
    dispSimpPred (name+"LHS", (decl @ lhs)) @ 
    dispSimpPred (name+"RHS", (decl @ rhs)) @ 
    dispHarnessPred name decl 

//pred RaRelim [ dom, dom': Action, sb, sb' : Action -> Action] { 
//  some l : Glob & Atomic, v: Val | { 
//    read1[ dom - Extern, sb, l, v ] 
//    read2[ dom' - Extern, sb', l, v ] 
//  } 
//} 