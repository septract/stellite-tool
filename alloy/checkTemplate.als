
/****************************************************/ 
/* Inclusion checking code.                         */ 
/* Template: stellite-tool/alloy/checkTemplate.als  */ 
/****************************************************/ 

pred histIncl() { 
  all dom, dom' : set Action, kind, kind' : Action -> Kind,
      gloc, gloc', lloc, lloc' : Action -> Loc, 
      callmap, retmap : Thr -> Val, 
      wv, rv : Action -> Val, 
      sb, sb' : Action -> Action,
      hb, mo, rf, guar, deny : Action -> Action
    when { 
      // Optimisation definition 
      optPredDef[dom, dom', kind, kind', gloc, gloc', lloc, lloc', sb, sb'] 

      valid[dom, kind, gloc, lloc, callmap, retmap, wv, rv, ^hb, sb, mo, rf] 
   
      // Nonatomics disabled 
      // DRF[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]

      guar = getguar[dom, ^hb] 
      deny = getdeny[dom, kind, gloc, wv, rv, ^hb, sb, mo, rf] 
 
      // Cut irrelevant executions. 
      cutR[dom, kind, gloc, wv, rv, ^hb, sb, mo, rf] 
      cutW[dom, kind, gloc, wv, rv, ^hb, sb, mo, rf] 

      // Sanity conditions 
      Action = dom + dom' 
      Loc = dom.(lloc + gloc) + dom'.(lloc' + gloc') 
      is_core[hb] 
      is_core[sb] 
      one Call & (dom + dom') 
      one Ret & (dom + dom') 
      
      // Pre-execution structure
      preexecWF[dom, kind, gloc, lloc, sb] 
      preexecWF[dom', kind', gloc', lloc', sb'] 

      Extern & dom = Extern & dom' 
      Extern <: gloc = Extern <: gloc' 
      Extern <: kind = Extern <: kind' 
  } | 
  some wvi, rvi : Intern -> Val, 
       mo', rf' : Action -> Action | { 
   let hb' = ^(sb' + rf'), 
       wv' = wvi + (Extern <: wv), 
       rv' = rvi + (Extern <: rv) | { 
      valid[dom', kind', gloc', lloc', callmap, retmap, wv', rv', ^hb', sb', mo', rf']

      // Atomics disabled 
      //DRF[dom', kind', loc', wv', rv', ^hb', sb', mo', rf']
 
      getguar[dom', ^hb'] in guar 
      getdeny[dom', kind', gloc', wv', rv', ^hb', sb', mo', rf'] in deny 
    } 
  }
} 

check { histIncl } for 7 


