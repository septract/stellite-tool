// Relational version of history, tests

module histRelat
open c11Relat 

pred preexecWF [ dom : set Action, kind : Action -> Kind,
                 gloc, lloc : Action -> Loc, sb : Action -> Action ] { 
  SBwf[dom, kind, sb] 
  locWF[dom, kind, gloc, lloc] 

//   // External actions act on global locations 
//   (dom & Extern).loc in Glob 

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
    some disj w1, w2 : (kind.Write & (dom <: loc.Atomic)) | 
    { 
      (w2 -> w1) in mo
      (w1 -> u) + (v -> w2) in iden + hb
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

// pred histWF [ dom : set Action, hb, sb, mo, rf : Action -> Action, 
//               interf : set Action, guar, deny : Action -> Action ] { 
//   no interf & Intern 
// 
//   // Guarantee is a projection of Call -> Ret and external hb
//   guar = hb & 
//       ((Extern -> Extern) + (Call -> Extern) +  (Extern -> Ret)) 
//   
//   // Deny is built from two kinds of shape 
//   deny = CoWR_d[dom, hb, sb, mo, rf] + 
//          HBvsMO_d[dom, hb, sb, mo, rf]
// }

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
  all r : Extern & kind.Read | some w : Intern & kind.Write | { 
    (w -> r) in rf
    no (w.rf & Extern) - r
  } 
} 

fun visible [ dom : set Action, rf : Action -> Action ] 
    : Action  { 
  // Internal actions 
  (dom & Intern) + 
  // External actions that are read or read from internal actions
  { a : dom & Extern | 
    some a' : dom & Intern | some ((a -> a') + (a' -> a)) & rf }
} 

pred cutW'[ dom : set Action, kind : Action -> Kind,
            loc : Action -> Loc, wv, rv : Action -> Val, 
            hb, sb, mo, rf : Action -> Action ] { 
  all disj w, w' : Extern & dom | { 
    {(w.loc = w'.loc) and (no (w + w') & visible[dom, hb, sb, mo, rf])} 
       implies 
    some w'' : visible[dom, rf] | 
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


run hist_run
  { some dom : set Action, kind : Action -> Kind,
             gloc, lloc : Action -> Loc, 
             callmap, retmap : Thr -> Val, 
             wv, rv : Action -> Val, 
             hb, sb, mo, rf : Action -> Action,
             guar, deny : Action -> Action | {
     valid[dom, kind, gloc, lloc, callmap, retmap, wv, rv, ^hb, sb, mo, rf]

     // Non-atomics turned off. 
     // DRF[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]  

     // prune boring contexts
     cutR[dom, kind, gloc, wv, rv, ^hb, sb, mo, rf] 
     cutW'[dom, kind, gloc, wv, rv, ^hb, sb, mo, rf] 
     //some Extern & Read
     //some Intern.loc & (Extern & Read).loc 
 
     // Sanity conditions 
     dom = Action 
     Loc = dom.(lloc + gloc) 
     is_core[hb] 
     is_core[sb] 

     // History stuff
     preexecWF[dom, kind, gloc, lloc, sb] 
     one Call & dom 
     one Ret & dom 
     //some Extern & kind.Read

     some g : Glob & Atomic, t : Thr | 
       read2[dom - Extern, kind, gloc, lloc, sb, g, t] 

     guar = getguar[dom, hb]
     deny = getdeny[dom, kind, gloc, wv, rv, ^hb, sb, mo, rf] 
  } 
} for 8 

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


check hist_incl { 
  all dom, dom' : set Action, kind, kind' : Action -> Kind,
      gloc, gloc', lloc, lloc' : Action -> Loc, 
      callmap, retmap : Thr -> Val, 
      wv, rv : Action -> Val, 
      sb, sb' : Action -> Action,
      hb, mo, rf, guar, deny : Action -> Action
    when { 
      valid[dom, kind, gloc, lloc, callmap, retmap, wv, rv, ^hb, sb, mo, rf] 
   
      // Nonatomics disabled 
      // DRF[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]

      guar = getguar[dom, ^hb] 
      deny = getdeny[dom, kind, gloc, wv, rv, ^hb, sb, mo, rf] 
 
      // Cut boring executions. 
      cutR[dom, kind, gloc, wv, rv, ^hb, sb, mo, rf] 
      cutW'[dom, kind, gloc, wv, rv, ^hb, sb, mo, rf] 

      // Sanity conditions 
      Action = dom + dom' 
      Loc = dom.(lloc + gloc) + dom'.(lloc' + gloc') 
      is_core[hb] 
      is_core[sb] 
      one Call // & (dom + dom') 
      one Ret // & (dom + dom') 
      
      // Optimisation definition 
      RaRintro[dom, dom', kind, kind', gloc, gloc', lloc, lloc', sb, sb'] 

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
} for 6


/*************************************************/ 
/* Optimizations                                 */ 
/*************************************************/

// Should be sound 
pred Req [ dom, dom': Action, 
             kind, kind' : Action -> Kind, 
             gloc, gloc' : Action -> Glob, 
             lloc, lloc' : Action -> Thr, 
             sb, sb' : Action -> Action] { 
  some g : Glob & Atomic, t : Thr | { 
    read1[ dom - Extern, kind, gloc, lloc, sb, g, t ] 
    read1[ dom' - Extern, kind', gloc', lloc', sb', g, t ] 
  } 
} 

// Should be sound 
pred RaRintro [ dom, dom': Action, 
                kind, kind' : Action -> Kind, 
                gloc, gloc' : Action -> Glob, 
                lloc, lloc' : Action -> Thr, 
                sb, sb' : Action -> Action] { 
  some g : Glob & Atomic, t : Thr | { 
    read2[ dom - Extern, kind, gloc, lloc, sb, g, t ] 
    read1[ dom' - Extern, kind', gloc', lloc', sb', g, t ] 
  } 
} 

// // // Should be sound 
// // pred RaRelim [ dom, dom': Action, sb, sb' : Action -> Action] { 
// //   some l : Glob & Atomic, v: Val | { 
// //     read1[ dom - Extern, sb, l, v ] 
// //     read2[ dom' - Extern, sb', l, v ] 
// //   } 
// // } 
// // 
// // // Should be sound 
// // pred WaWelim [ dom, dom' : Action, sb, sb' : Action -> Action] { 
// //   some l : Glob & Atomic, v, v': Val | { 
// //     write1[ dom - Extern, sb, l, v']
// //     write2[ dom' - Extern, sb', l, v, v']
// //   } 
// // } 
// // 
// // // Should be unsound 
// // pred WaWelim2 [ dom, dom' : Action, sb, sb' : Action -> Action] { 
// //   some l : Glob & Atomic, v, v': Val | { 
// //     write1[ dom - Extern, sb, l, v]
// //     write2[ dom' - Extern, sb', l, v, v'] // NOTE: removed 2nd val.
// //   } 
// // } 
// // 
// // // Should be unsound 
// // pred WaWintro [ dom, dom' : Action, sb, sb' : Action -> Action] { 
// //   some l : Glob & Atomic, v, v': Val | { 
// //     write2[ dom - Extern, sb, l, v, v']
// //     write1[ dom' - Extern, sb', l, v]
// //   } 
// // } 
// // 
// // // Should be unsound 
// // pred WaRintro [ dom, dom' : Action, sb, sb' : Action -> Action] { 
// //   some l : Glob & Atomic, v: Val | { 
// //     read1write1[ dom - Extern, sb, l, v]
// //     read1[ dom' - Extern, sb', l, v]
// //   } 
// // } 
// // 
// // // Should be unsound 
// // pred WaRelim [ dom, dom' : Action, sb, sb' : Action -> Action] { 
// //   some l : Glob & Atomic, v: Val | { 
// //     read1[ dom - Extern, sb, l, v]
// //     read1write1[ dom' - Extern, sb', l, v]
// //   } 
// // } 
// // 
// // // Should be sound 
// // pred RaWelim [ dom, dom' : Action, sb, sb' : Action -> Action] { 
// //   some l : Glob & Atomic, v: Val | { 
// //     write1[ dom - Extern, sb, l, v]
// //     write1read1[ dom' - Extern, sb', l, v]
// //   } 
// // } 
// // 
// // // Should be unsound 
// // pred WRswap [ dom, dom' : Action, sb, sb' : Action -> Action] { 
// //   some l : Glob & Atomic, v: Val | { 
// //     read1write1[ dom - Extern, sb, l, v]
// //     write1read1[ dom' - Extern, sb', l, v]
// //   } 
// // } 
// // 
// // // Should be unsound 
// // pred RWswap [ dom, dom' : Action, sb, sb' : Action -> Action] { 
// //   some l : Glob & Atomic, v: Val | { 
// //     write1read1[ dom - Extern, sb, l, v]
// //     read1write1[ dom' - Extern, sb', l, v]
// //   } 
// // } 

/*************************************************/ 
/* Code fragments                                */ 
/*************************************************/


pred read1[ dom : set Action, kind : Action -> Kind,
            gloc : Action -> Glob, lloc : Action -> Thr, 
            sb : Action -> Action, g : Glob, t : Thr ] { 
  some r1 : kind.Read | { 
    r1.gloc = g 
    r1.lloc = t 
    dom = r1 + Call + Ret 
    sb in (dom -> dom) 
  } 
} 

pred read2[ dom : set Action, kind : Action -> Kind,
            gloc : Action -> Loc, lloc : Action -> Thr, 
            sb : Action -> Action, g : Glob, t : Thr ] { 
  some disj r1, r2 : kind.Read | { 
    r1.gloc + r2.gloc = g 
    r1.lloc + r2.lloc = t 
    dom = r1 + r2 + Call + Ret 
    r1 -> r2 in sb 
    sb in (dom -> dom) 
  } 
} 

// pred write1[ dom : set Action, kind : Action -> Kind,
//              loc : Action -> Loc, wv, rv : Action -> Val,  
//              sb : Action -> Action, l : Loc, v : Val ] { 
//   some r1 : kind.Write | { 
//     r1.loc = l 
//     r1.wv = v 
//     dom = r1 + Call + Ret 
//     sb in (dom -> dom) 
//   } 
// } 
// 
// pred write1read1 [ dom : set Action, kind : Action -> Kind,
//                    loc : Action -> Loc, wv, rv : Action -> Val, 
//                    sb : Action -> Action, l : Loc, v : Val ] { 
//   some disj r1 : kind.Read, r2 : kind.Write | { 
//     r1.loc + r2.loc = l 
//     r1.rv + r2.wv = v 
//     dom = r1 + r2 + Call + Ret 
//     r2 -> r1 in sb 
//     sb in (dom -> dom) 
//   } 
// } 
// 
// pred read1write1 [ dom : set Action, kind : Action -> Kind,
//                    loc : Action -> Loc, wv, rv : Action -> Val, 
//                    sb : Action -> Action, l : Loc, v : Val ] { 
//   some disj r1 : kind.Read, r2 : kind.Write | { 
//     r1.loc + r2.loc = l 
//     r1.rv + r2.wv = v 
//     dom = r1 + r2 + Call + Ret 
//     r1 -> r2 in sb 
//     sb in (dom -> dom) 
//   } 
// } 
// 
// pred write2[ dom : set Action, kind : Action -> Kind,
//              loc : Action -> Loc, wv, rv : Action -> Val,  
//              sb : Action -> Action, l : Loc, v, v' : Val ] { 
//   some disj r1, r2 : kind.Write | { 
//     r1.loc + r2.loc = l 
//     r1.wv = v 
//     r2.wv = v' 
//     dom = r1 + r2 + Call + Ret 
//     r1 -> r2 in sb 
//     sb in (dom -> dom) 
//   } 
// } 
// 
// pred skip [ dom : set Action, sb : Action -> Action ] { 
//   dom = Call + Ret
//   sb in (dom -> dom) 
// } 
// 
// // /* 
// // 
// // pred WW_code [ e : Execution ] { 
// //   some disj w1, w2 : Write | { 
// //     (e.act & Intern) = w1 + w2
// //     (w1 -> w2) in e.sb
// //     one w1.loc + w2.loc 
// //     w1.loc in Atomic & Glob 
// //   } 
// // } 
// // 
// // */
