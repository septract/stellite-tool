// Relational version of history

module histRelat
open c11Relat 

pred preexecWF [ dom : set Action, kind : Action -> Kind,
                 gloc, lloc : Action -> Loc, sb : Action -> Action ] { 
  // no kind.RMW

  SBwf[dom, kind, sb] 
  locWF[dom, kind, gloc, lloc] 

  // External actions are unordered in sb  
  no sb & ((Extern -> Action) + (Action -> Extern)) 

  // Internal actions are totally ordered in sb 
  all disj a1, a2 : (dom & Intern) | 
    a1 -> a2 in (^sb + ^(~sb))

  // Call / Return bracket internal actions
  all c : dom & Call, r : dom & Ret | { 
    (c -> r) in ^sb 
    all i : dom | 
      i in Intern iff (c -> i) + (i -> r) in ^sb
  } 
}

fun HBvsMO_d [ dom : set Action, kind : Action -> Kind,
               loc : Action -> Loc, wv, rv : Action -> Val, 
               hb, sb, mo, rf : Action -> Action ] 
                  : (Action -> Action) { 
  { u : (Extern + Ret), v : (Extern + Call) | 
    some disj w1, w2 : (dom <: loc.Atomic) | 
    { 
      (w2 -> w1) in mo
      (w1 -> u) + (v -> w2) in (iden + hb) 
    } 
  } 
} 

fun CoWR_d [ dom : set Action, kind : Action -> Kind,
             loc : Action -> Loc, wv, rv : Action -> Val, 
             hb, sb, mo, rf : Action -> Action ] 
                : (Action -> Action) { 
  { u : (Extern + Ret), v : (Extern + Call) |
    disj [u,v] and 
    some w1, w2 : kind.Write & (dom <: loc.Atomic), 
               r : kind.Read & (dom <: loc.Atomic)   | 
    { 
      disj [w1, w2, r] 
      (w1 -> r) in rf 
      (w1 -> w2) in mo
      (w2 -> u) in iden + hb 
      (v -> r) in iden + hb 
    } 
  } 
} 

fun HBacyc_d [ dom : set Action, kind : Action -> Kind,
               loc : Action -> Loc, wv, rv : Action -> Val, 
               hb, sb, mo, rf : Action -> Action ] 
                 : (Action -> Action) { 
  { u : (Extern + Ret), v : (Extern + Call) | 
    disj [u,v] 
   and 
    (v -> u) in hb 
  } 
} 

fun getguar[ dom : Action, hb : Action -> Action ] : Action -> Action { 
  hb & ((Extern -> Extern) + (Call -> Extern) +  (Extern -> Ret)) 
} 

fun getdeny[ dom : set Action, kind : Action -> Kind,
             loc : Action -> Loc, wv, rv : Action -> Val, 
             hb, sb, mo, rf : Action -> Action ] 
                 : Action -> Action { 
   // Note: removed Ret -> Call deny because it's already enforced by sb 
   (CoWR_d[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]
     + 
    HBvsMO_d[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]
     + 
    HBacyc_d[dom, kind, loc, wv, rv, ^hb, sb, mo, rf])
        - (Ret -> Call) 
} 

/*************************************************/ 
/* Cutting Predicates                            */ 
/*************************************************/

pred cutR[ dom : set Action, kind : Action -> Kind,
           loc : Action -> Loc, wv, rv : Action -> Val, 
           hb, sb, mo, rf : Action -> Action ] { 
  all r : Extern & kind.Read & loc.Atomic & dom | 
  some w : Intern & dom | { 
    (w -> r) in rf
    no (w.rf & Extern) - r
  } 
} 

fun vizAct[ dom : set Action, rf : Action -> Action ] : Action  { 
  // Internal actions 
  (dom & Intern) + 
  // External actions that are read or read from internal actions
  { a : dom & Extern | 
    some a' : dom & Intern | some ((a -> a') + (a' -> a)) & rf }
} 

pred cutW[ dom : set Action, kind : Action -> Kind,
            loc : Action -> Loc, wv, rv : Action -> Val, 
            hb, sb, mo, rf : Action -> Action ] { 
  all disj w, w' : Extern & dom | { 
    {(w.loc = w'.loc) and (no (w + w') & vizAct[dom, rf])} 
       implies 
    some w'' : vizAct[dom, rf] | 
       (w -> w'') + (w'' -> w') in mo
  } 
} 


//fun getinterf[ dom : set Action ] : set Action { 
//  dom & (Extern + Call + Ret) 
//} 

// // run hist_run_simp
// //   { some dom : set Action, hb, sb, mo, rf : Action -> Action | {
// //      valid[dom, ^hb, sb, mo, rf]
// //      // DRF[dom, ^hb, sb, mo, rf]  
// //  
// //      // Sanity conditions 
// //      dom = Action 
// //      Loc = dom.loc 
// //      is_core[hb] 
// //      is_core[sb] 
// //      //some Extern & Write
// //      //some Intern.loc & (Extern & Write).loc 
// // 
// //      some disj w0, w1, w2 : Write | { 
// //        w0 + w1 in Intern 
// //        w2 in Extern 
// //        one w0.loc + w1.loc + w2.loc 
// //        w0.loc in Atomic 
// //      } 
// // 
// //      one Call 
// //      one Ret
// //      preexecWF[ dom, sb ] 
// // 
// //      interesting_exec[dom, ^hb, sb, mo, rf] 
// // 
// //      some l : Glob & Atomic, v : Val | write2[ dom - Extern, sb, l, v] 
// //   } 
// // } for 5 



/*************************************************/ 
/* Tests                                         */ 
/*************************************************/


// run hist_run
//   { some dom : set Action, kind : Action -> Kind,
//              gloc, lloc : Action -> Loc, 
//              callmap, retmap : Thr -> Val, 
//              wv, rv : Action -> Val, 
//              hb, sb, mo, rf : Action -> Action,
//              guar, deny : Action -> Action | {
//      valid[dom, kind, gloc, lloc, callmap, retmap, wv, rv, ^hb, sb, mo, rf]
// 
//      // Non-atomics turned off. 
//      // DRF[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]  
// 
//      // prune boring contexts
//      cutR[dom, kind, gloc, wv, rv, ^hb, sb, mo, rf] 
//      cutW[dom, kind, gloc, wv, rv, ^hb, sb, mo, rf] 
//      //some Extern & Read
//      //some Intern.loc & (Extern & Read).loc 
//  
//      // Sanity conditions 
//      dom = Action 
//      Loc = dom.(lloc + gloc) 
//      is_core[hb] 
//      is_core[sb] 
// 
//      // History stuff
//      preexecWF[dom, kind, gloc, lloc, sb] 
//      one Call & dom 
//      one Ret & dom 
//      //some Extern & kind.Read
// 
//      some g : Glob & Atomic, t : Thr | 
//        read2[dom - Extern, kind, gloc, lloc, sb, g, t] 
// 
//      guar = getguar[dom, hb]
//      deny = getdeny[dom, kind, gloc, wv, rv, ^hb, sb, mo, rf] 
//   } 
// } for 8 but exactly 2 Extern 
//
// run hist_incl_run { 
//   some dom : set Action, hb, sb, mo, rf : Action -> Action, 
//       // guar, deny : Action -> Action, 
//       dom' : set Action, hb', sb', mo', rf' : Action -> Action, 
//       guar, guar', deny, deny' : Action -> Action 
//     when { 
//       interesting_exec[dom,^hb, sb, mo, rf] 
//       // some Extern & Write
// 
//       valid[dom, ^hb, sb, mo, rf] 
//       DRF[dom, ^hb, sb, mo, rf] 
//       is_core[hb] 
//       is_core[hb']
//       is_core[sb]
//       is_core[sb']
//        
//       preexecWF[dom, sb] 
//       preexecWF[dom', sb'] 
//  
//       // identical interfaces 
//       getinterf[dom] = getinterf[dom'] 
// 
//       // Sanity conditions 
//       Action = dom + dom' 
//       Loc = dom.loc + dom'.loc 
//       
//       // Shared call / return 
//       one Call & (dom + dom') 
//       one Ret & (dom + dom') 
//       
//       // Code definition 
//       some l : Loc, v : Val | { 
//         write2[ dom - Extern, sb, l, v] 
//         write1[ dom' - Extern, sb', l, v] 
//       } 
//     } | { 
//       valid[dom', ^hb', sb', mo', rf'] 
//       DRF[dom', ^hb', sb', mo', rf'] 
// 
//       guar = getguar[dom, hb]
//       guar' = getguar[dom', hb']
//       guar' in guar
// 
//       deny = getdeny[dom, hb, sb, mo, rf] 
//       deny' = getdeny[dom', hb', sb', mo', rf'] 
//       deny' in deny 
// 
//       some r1, r2 : Extern & Read, w : Extern & Write | 
//          disj[r1, r2, w]
//     } 
//   } for 7 but 1 Call, 1 Ret, 0 RMW
