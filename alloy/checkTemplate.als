
/****************************************************/ 
/* Inclusion checking code.                         */ 
/* Template: ./alloy/checkTemplate.als              */ 
/****************************************************/ 

pred histIncl() { 
  all dom, dom' : set Action, 
      kind, kind' : Action -> Kind,
      gloc, gloc' : Action -> Glob,
      lloc1, lloc1' : Intern -> Thr, 
      lloc2, lloc2' : Intern -> Thr, 
      callmap, retmap : Thr -> Val, 
      wv, rv : Action -> Val, 
      sb, sb' : Action -> Action,
      hb, mo, rf, guar, deny : Action -> Action
    when { 
      no lloc2 + lloc2' 

      // Optimisation definition 
      optPred[dom, dom', kind, kind', gloc, gloc', lloc1, lloc1', lloc2, lloc2', ^sb, ^sb'] 

      // Enforce validity for LHS
      valid[dom, kind, gloc, lloc1, lloc2, callmap, retmap, wv, rv, ^hb, ^sb, mo, rf] 

      // Interfaces are the same
      Extern & dom = Extern & dom' 
      Extern <: gloc = Extern <: gloc' 
      Extern <: kind = Extern <: kind' 
   
      // Nonatomics disabled 
      // DRF[dom, kind, loc, wv, rv, ^hb, ^sb, mo, rf]

      guar = getguar[dom, ^hb] 
      deny = getdeny[dom, kind, gloc, wv, rv, ^hb, ^sb, mo, rf] 
 
      // Cut irrelevant executions. 
      cutR[dom, kind, gloc, wv, rv, ^hb, ^sb, mo, rf] 
      cutW[dom, kind, gloc, wv, rv, ^hb, ^sb, mo, rf] 

      // Sanity conditions 
      Action = dom + dom' 
      Loc = dom.(lloc1 + gloc) + dom'.(lloc1' + gloc') 

      // Make the relations nicer to display 
      is_core[hb] 
      is_core[sb] 
      is_core[sb'] 
  } | 
  some wvi, rvi : Intern -> Val, 
       mo', rf' : Action -> Action | { 
   let hb' = ^(sb' + rf'), 
       wv' = wvi + (Extern <: wv), 
       rv' = rvi + (Extern <: rv) | { 

      // Enforce validity for RHS 
      valid[dom', kind', gloc', lloc1', lloc2', callmap, retmap, wv', rv', ^hb', ^sb', mo', rf']

      // Atomics disabled 
      //DRF[dom', kind', loc', wv', rv', ^hb', sb', mo', rf']
 
      // Histories are related
      getguar[dom', ^hb'] in guar 
      getdeny[dom', kind', gloc', wv', rv', ^hb', ^sb', mo', rf'] in deny 
    } 
  }
} 

// check { histIncl } for 7


/****************************************************/ 
/* Debugging code.                                  */  
/* Generate LHS / RHS of the inclusion.             */ 
/****************************************************/ 

// pred histInclRun() { 
//   some dom, dom' : set Action, kind, kind' : Action -> Kind,
//        gloc, gloc', lloc, lloc' : Action -> Loc, 
//        callmap, retmap : Thr -> Val, 
//        wv, rv : Action -> Val, 
//        sb, sb' : Action -> Action,
//        hb, mo, rf, guar, deny : Action -> Action,
//        wvi, rvi : Intern -> Val, 
//        mo', rf' : Action -> Action | { 
//    let hb' = ^(sb' + rf'), 
//        wv' = wvi + (Extern <: wv), 
//        rv' = rvi + (Extern <: rv) | { 
//       // Optimisation definition 
//       optPred[dom, dom', kind, kind', gloc, gloc', lloc, lloc', ^sb, ^sb'] 
// 
//       valid[dom, kind, gloc, lloc, callmap, retmap, wv, rv, ^hb, ^sb, mo, rf] 
//      
//       // Nonatomics disabled 
//       // DRF[dom, kind, loc, wv, rv, ^hb, ^sb, mo, rf]
// 
//       guar = getguar[dom, ^hb] 
//       deny = getdeny[dom, kind, gloc, wv, rv, ^hb, ^sb, mo, rf] 
//  
//       // Cut irrelevant executions. 
//       cutR[dom, kind, gloc, wv, rv, ^hb, ^sb, mo, rf] 
//       cutW[dom, kind, gloc, wv, rv, ^hb, ^sb, mo, rf] 
// 
//       // Sanity conditions 
//       Action = dom + dom' 
//       Loc = dom.(lloc + gloc) + dom'.(lloc' + gloc') 
// 
//       // Make the relations nicer to display 
//       is_core[hb] 
//       is_core[sb] 
//       is_core[sb'] 
// 
//       // one Call & (dom + dom') 
//       // one Ret & (dom + dom') 
//       
//       // // Pre-execution structure
//       // preexecWF[dom, kind, gloc, lloc, sb] 
//       // preexecWF[dom', kind', gloc', lloc', ^sb'] 
// 
//       Extern & dom = Extern & dom' 
//       Extern <: gloc = Extern <: gloc' 
//       Extern <: kind = Extern <: kind' 
//       valid[dom', kind', gloc', lloc', callmap, retmap, wv', rv', ^hb', ^sb', mo', rf']
// 
//       // Atomics disabled 
//       //DRF[dom', kind', loc', wv', rv', ^hb', ^sb', mo', rf']
//  
//       getguar[dom', ^hb'] in guar 
//       getdeny[dom', kind', gloc', wv', rv', ^hb', ^sb', mo', rf'] in deny 
//     } 
//   }
// } 
// 
// pred histInclRunLHS() { 
//   some dom : set Action, kind : Action -> Kind,
//        gloc, lloc : Action -> Loc, 
//        callmap, retmap : Thr -> Val, 
//        wv, rv : Action -> Val, 
//        sb : Action -> Action,
//        hb, mo, rf, guar, deny : Action -> Action, 
//        x: Glob, l : Thr | { 
//       // Optimisation definition 
//       optLHS[dom - Extern, kind, gloc, lloc, ^sb, x, l] 
//       preexecWF[dom, kind, gloc, lloc, sb]  
//       one Call & dom 
//       one Ret & dom 
// 
//       valid[dom, kind, gloc, lloc, callmap, retmap, wv, rv, ^hb, ^sb, mo, rf] 
//      
//       // Nonatomics disabled 
//       // DRF[dom, kind, loc, wv, rv, ^hb, ^sb, mo, rf]
// 
//       guar = getguar[dom, ^hb] 
//       deny = getdeny[dom, kind, gloc, wv, rv, ^hb, ^sb, mo, rf] 
//  
//       // Cut irrelevant executions. 
//       cutR[dom, kind, gloc, wv, rv, ^hb, ^sb, mo, rf] 
//       cutW[dom, kind, gloc, wv, rv, ^hb, ^sb, mo, rf] 
// 
//       // Sanity conditions 
//       Action = dom 
//       Loc = dom.(lloc + gloc) 
// 
//       // Make the relations nicer to display 
//       is_core[hb] 
//       is_core[sb] 
//   }
// } 


//run { histInclRun } for 4
//run { histInclRunLHS } for 6 


