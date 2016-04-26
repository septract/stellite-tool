module Stellite.translator 

open Stellite.parser

let rec intersperse i xs = 
    match xs with
    | [] -> ""  
    | [x] -> x 
    | x::y::ys -> x + i + intersperse i (y::ys)

// TODO: Should refactor these two into one fold :p 
let dispVarDecl cmds = 
    List.map (fun c -> match c with 
                       | GlobDecl vs -> vs  
                       | _ -> []) 
             cmds
    |> List.concat |> intersperse ", "   

let dispValDecl cmds = 
    List.map (fun c -> match c with 
                       | ValDecl vs -> vs  
                       | _ -> []) 
             cmds
    |> List.concat |> intersperse ", "   

let isAct x = 
    match x with 
    | Write _ | Read _ | RMW _ -> true
    | _ -> false 

//let countActions = 
//    List.fold (fun a x -> if (isAct x) then a+1 else a) 0 

let rec dispN (str : string) (i : int) : List<string> = 
    match i with 
    | 0 -> []  
    | _ -> dispN str (i-1) @ [str + (string i)] 

//let setLoc a i = 
//    match a with 
//    | Write (a,b) | Read (a,b) -> "op" + string i + ".loc = " + a 
//    | RMW (a,b,c) -> "ERROR"
//    | _ -> "ERROR" 

let getActions = 
    List.filter (fun c -> match c with 
                          | Write _ | Read _ | RMW _ -> true 
                          | _ -> false )               

let getActionId a = 
    match a with 
    | Write (i,_) | Read (i,_) | RMW (i,_) -> i
    | _ -> failwith "getActionId: not an action!" 

let getActionLoc a = 
    match a with 
    | Write (_,(x,_)) | Read (_,(x,_)) -> x
    | RMW (_,(x,_,_)) -> x
    | _ -> failwith "getActionLoc: not an action!" 

let actName c = "op" + string (getActionId c)

let actKind c = 
    match c with 
    | Write _ -> "Write"
    | Read _ -> "Read" 
    | RMW _ -> "RMW" 
    | _ -> failwith "actKind: not an action!"

let genEqRW id id2 = "op" + string id + ".rval = op" + string id2 + ".wval" 
let genEqRV id vname = "op" + string id + ".rval = " + vname

let rec genEqLoc i l cmds = 
    match cmds with 
    | Write (i',(_,l')) :: cmds' when l = l' -> [genEqRW i i'] @ (genEqLoc i l cmds') 
    | AssumeEq (l',v') :: cmds' when l' = l -> [genEqRV i v'] @ (genEqLoc i l cmds') 
    | Read (_, (_,l')) :: cmds' when l = l' -> [] 
    | _ :: cmds' -> genEqLoc i l cmds'  
    | [] -> [] 

let rec genEqs cmds = 
    match cmds with 
    | Read (i,(_,l)) :: cmds' -> (genEqLoc i l cmds') @ (genEqs cmds') 
    | c :: cmds' -> genEqs cmds'
    | [] -> []  

//let rec readDeps id var cmds : List<string> = 
//    match cmds with 
//    | Write (id2, (_,v2)) :: cmds2 -> 
//         (if (v2 = var) then [ genEqRW id id2 ] else [])  @ readDeps id var cmds2 
//    | Read (id2, (_,v2)) :: cmds2 -> 
//        if not (v2 = var) then readDeps id var cmds2 else [] 
//    | AssumeEq (loc,vl) :: cmds2 -> [] 
//    | _ -> [] 

let rec seqDefn names = 
    match names with 
    | a :: b :: rest -> ["(" + string a + "->" + string b + ")"] @ seqDefn (b :: rest) 
    | _ -> [] 

let dispExec ((name, cmds) : string * List<Command>) : List<string> =
    let acts = getActions cmds in
      [ "pred " + name + " [ dom : set Action, sb : Action -> Action,"] @   
      [ "           " + dispVarDecl cmds + " : Loc, " + dispValDecl cmds + " : Val ] { "] @
      [ "  sb in (dom -> dom)" ] @ 
      [ "  some disj " + (List.map actName acts |> intersperse ", ") + " : Action | { "] @ 
      [ "    dom = " + (List.map actName acts |> intersperse " + ") ] @ 
      [ "    sb = " + (List.map actName acts |> seqDefn |> intersperse " + ") ] @ 
      (List.map (fun c -> "    " + (actName c) + ".loc = " + (getActionLoc c)) acts) @ 
      (List.map (fun c -> "    " + (actName c) + " in " + (actKind c)) acts) @ 
      (List.map ((+) "    ") (genEqs cmds)) @ 
      [ "  }"] @  
      [ "}"] 
 