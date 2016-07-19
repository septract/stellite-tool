
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
      deny = getdeny[dom, kind, gloc, wv, rv, ^hb, ^sb, ^mo, rf] 
 
      // Cut irrelevant executions. 
      cutR[dom, kind, gloc, wv, rv, ^hb, ^sb, ^mo, rf] 
      cutW[dom, kind, gloc, wv, rv, ^hb, ^sb, ^mo, rf] 
      cutF[dom, kind, ^hb, ^sb, ^mo, rf] 

      // Sanity conditions 
      Action = dom + dom' 

      // Make the relations nicer to display 
      is_core[hb] 
      is_core[sb] 
      is_core[sb'] 
  } | 
  some wv', rv' : Action -> Val, 
       hb', mo', rf' : dom' -> dom' | { 
    (Extern <: wv) = (Extern <: wv') 
    (Extern <: rv) = (Extern <: rv') 

    // Enforce validity for RHS 
    valid[dom', kind', gloc', lloc1', lloc2', callmap, retmap, wv', rv', ^hb', ^sb', ^mo', rf']

    // Nonatomics disabled 
    //DRF[dom', kind', loc', wv', rv', ^hb', sb', mo', rf']
 
    // Histories are related
    getguar[dom', ^hb'] in guar 
    getdeny[dom', kind', gloc', wv', rv', ^hb', ^sb', mo', rf'] in deny 
  }
} 


/****************************************************/ 
/* Debugging code.                                  */  
/* Generate LHS / RHS of the inclusion.             */ 
/****************************************************/ 

pred histInclRun() { 
  some dom, dom' : set Action, 
      kind, kind' : Action -> Kind,
      gloc, gloc' : Action -> Glob,
      lloc1, lloc1' : Intern -> Thr, 
      lloc2, lloc2' : Intern -> Thr, 
      callmap, retmap : Thr -> Val, 
      wv, rv : Action -> Val, 
      sb, sb' : Action -> Action,
      hb, mo, rf, guar, deny : Action -> Action, 
      wv', rv' : Action -> Val, 
      hb', mo', rf' : dom' -> dom' | { 

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
    deny = getdeny[dom, kind, gloc, wv, rv, ^hb, ^sb, ^mo, rf] 
 
    // Cut irrelevant executions. 
    cutR[dom, kind, gloc, wv, rv, ^hb, ^sb, ^mo, rf] 
    cutW[dom, kind, gloc, wv, rv, ^hb, ^sb, ^mo, rf] 
    cutF[dom, kind, ^hb, ^sb, ^mo, rf] 

    // Sanity conditions 
    Action = dom + dom' 

    // Make the relations nicer to display 
    is_core[hb] 
    is_core[sb] 
    is_core[sb'] 

    (Extern <: wv) = (Extern <: wv') 
    (Extern <: rv) = (Extern <: rv') 

    // Enforce validity for RHS 
    valid[dom', kind', gloc', lloc1', lloc2', callmap, retmap, wv', rv', ^hb', ^sb', ^mo', rf']

    // Nonatomics disabled 
    //DRF[dom', kind', loc', wv', rv', ^hb', sb', mo', rf']
 
    // Histories are related
    getguar[dom', ^hb'] in guar 
    getdeny[dom', kind', gloc', wv', rv', ^hb', ^sb', mo', rf'] in deny 
    
  }
} 

/* 
pred histInclRunLHS() { 
  some dom : set Action, 
       kind : Action -> Kind,
       gloc, lloc1, lloc2 : Action -> Loc, 
       callmap, retmap : Thr -> Val, 
       wv, rv : Action -> Val, 
       sb : Action -> Action,
       hb, mo, rf, guar, deny : Action -> Action | { 
      // Optimisation definition 
      some x: Glob, l : Thr | { 
      optLHS[dom - Extern, kind, gloc, lloc1, lloc2, ^sb, x, l] 
      preexecWF[dom, kind, gloc, lloc1, lloc2, sb]  

      valid[dom, kind, gloc, lloc1, lloc2, callmap, retmap, wv, rv, ^hb, ^sb, mo, rf] 
     
      // Nonatomics disabled 
      // DRF[dom, kind, loc, wv, rv, ^hb, ^sb, mo, rf]

      guar = getguar[dom, ^hb] 
      deny = getdeny[dom, kind, gloc, wv, rv, ^hb, ^sb, mo, rf] 
 
      // Cut irrelevant executions. 
      cutR[dom, kind, gloc, wv, rv, ^hb, ^sb, mo, rf] 
      cutW[dom, kind, gloc, wv, rv, ^hb, ^sb, mo, rf] 

      // Sanity conditions 
      Action = dom 
      Loc = dom.(lloc1 + lloc2 + gloc) 

      // Make the relations nicer to display 
      is_core[hb] 
      is_core[sb] 
    } 
  }
} 

run { histInclRun } for 4
run { histInclRunLHS } for 6 but exactly 1 Call, 1 Ret
*/
