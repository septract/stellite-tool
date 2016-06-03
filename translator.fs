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

    //(List.map (function | GlobDecl vs -> vs  
    //                    | _ -> []) cmds) 
    //@ 
    //(List.map (function | ValDecl vs -> vs  
    //                    | _ -> []) cmds) 
    //x |> List.concat |> intersperse ", "

/// Check whether a command is an action
let isAct = function | Write _ | Read _ | RMW _ -> true
                     | _ -> false 

/// Check whether a command is an assumeEq
let isAssm = function | AssumeEq _ -> true
                      | _ -> false 

let isFence = function | FenceSC _ -> true
                       | _ -> false 

/// Get the identifier for an action 
let getActionId a = 
    match a with 
    | Write (i,_) | Read (i,_) | RMW (i,_) | AssumeEq (i,_) | FenceSC i -> i
    | _ -> failwith "getActionId: not a valid parameter!" 

/// Get the variable for an action 
let getActionGloc a = 
    match a with 
    | Write (_,(x,_)) | Read (_,(x,_)) -> x
    //| RMW (_,(x,_,_)) -> x
    | _ -> failwith "getActionGloc: not a valid parameter!" 

/// Get the local variable for an action 
let getActionlloc1 a = 
    match a with 
    | Write (_,(_,x)) | Read (_,(_,x)) | AssumeEq (_,(x,_)) -> x
    //| RMW (_,(x,_,_)) -> x
    | _ -> failwith "getActionlloc1: not a valid parameter!" 

/// Get the local variable for an action 
let getActionlloc2 a = 
    match a with 
    | AssumeEq (_,(_,x)) -> x
    | _ -> failwith "getActionlloc2: not a valid parameter!" 

/// Generate the name for the action. 
let actName c = "op" + string (getActionId c)

/// Get the correct set for the action. 
let actKind c = 
    match c with 
    | Write _ -> "Write"
    | Read _ -> "Read" 
    //| RMW _ -> "RMW" 
    | AssumeEq _ -> "AssmEq" 
    | FenceSC _ -> "FenceSC" 
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
    // | AssumeEq (l',v') :: cmds' when l' = l -> [genEqRV i v'] @ (genEqLoc i l cmds') 
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


(*********************************************************************
 *   Predicates for the simpler C11 model
 *********************************************************************) 

(*
let dispSimpPredHO ((name, cmds) : string * List<Command>) : List<string> =
    let acts = (List.filter isAct) cmds in
      [ "pred " + name ] @
      [ "         [ dom : set Action, sb : Action -> Action,"] @   
      [ "           " + dispGlobDecl cmds + " : Loc, " + dispValDecl cmds + " : Val ] { "] @
      [ "  sb in (dom -> dom)" ] @ 
      [ "  some disj " + (List.map actName acts |> intersperse ", ") + " : Action | { "] @ 
      [ "    dom = " + (List.map actName acts |> intersperse " + ") + " + Call + Ret" ] @ 
      [ "    (none -> none)" + (List.map actName acts |> seqDefn) + " in sb" ] @ 
      (List.map (fun c -> "    " + (actName c) + ".loc = " + (getActionGloc c)) acts) @ 
      (List.map (fun c -> "    " + (actName c) + " in " + (actKind c)) acts) @ 
      (List.map ((+) "    ") (genEqs cmds)) @ 
      [ "  }"] @  
      [ "}"] 

let dispHarnessPredHO name decl = 
    [ "pred " + name ] @ 
    [ "     [ dom, dom' : set Action, sb, sb' : Action -> Action ] {" ] @ 
    [ "       some " + dispGlobDecl decl + " : Glob & Atomic, " + dispValDecl decl + " : Val | {" ] @ 
    [ "    " + name + "LHS[dom - Extern, sb, " + dispAllDecl decl + "]" ] @ 
    [ "    " + name + "RHS[dom' - Extern, sb', " + dispAllDecl decl + "]" ] @ 
    [ "  }" ] @ 
    [ "}" ] 


let dispOptPredHO ((name,decl,lhs,rhs) : string * List<Command> * List<Command> * List<Command>) 
                : List<string> = 
    dispSimpPredHO (name+"LHS", (decl @ lhs)) @ 
    dispSimpPredHO (name+"RHS", (decl @ rhs)) @ 
    dispHarnessPredHO name decl 
*)

(*********************************************************************
 *  Display functions for the more advanced, relational C11 model. 
 *********************************************************************) 

let dispSimpPredRelat ((name, cmds) : string * List<Command>) : List<string> =
    let acts = (List.filter isAct) cmds in
    let assms = (List.filter isAssm) cmds in 
    let fences = (List.filter isFence) cmds in 
    let allops = acts @ assms @ fences in 
      [ "pred " + name ] @
      [ "         [ dom : set Action, kind : Action -> Kind," ] @
      [ "           gloc : Action -> Glob, lloc1, lloc2 : Action -> Thr, " ] @
      [ "           sb : Action -> Action, " + (dispGlobDecl cmds |> intersperse ", ") + " : Glob, " 
               + (dispThrDecl cmds |> intersperse ", ") + " : Thr ] { "] @
      [ "  sb in (dom -> dom)" ] @ 
      (if (List.length allops > 0) then 
        [ "  some disj " + (List.map actName allops |> intersperse ", ") + " : Action | "]
      else []) @ 
      [ "  { "] @ 
      [ "    dom = " + (List.fold (fun c a -> (actName a) + " + " + c) "" allops) + "Call + Ret" ] @ 
      [ "    (Call -> Ret)" + (List.map actName allops |> seqDefn) + " in sb" ] @ 
      (List.map (fun c -> "    " + (actName c) + ".gloc = " + (getActionGloc c)) acts) @ 
      (List.map (fun c -> "    " + (actName c) + ".lloc1 = " + (getActionlloc1 c)) (acts @ assms)) @ 
      (List.map (fun c -> "    " + (actName c) + ".lloc2 = " + (getActionlloc2 c)) assms) @ 
      (List.map (fun c -> "    " + (actName c) + " in kind." + (actKind c)) allops) @ 
      //(List.map ((+) "    ") (genEqs cmds)) @ 
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


