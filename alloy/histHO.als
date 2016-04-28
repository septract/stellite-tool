module histHO
open c11HO 

sig Intern, Extern in Action {} 
sig Glob, Thr in Loc {} 

fact { 
  disj[ Glob, Thr ] 
  Glob + Thr = Loc 

  disj[ Intern, Extern, Call, Ret ] 
  Intern + Extern + Call + Ret = Action 
 
  //disj[ Call.loc, Ret.loc, (Intern+Extern).loc ]
} 

pred preexecWF [ dom : set Action, sb: Action -> Action ] { 
  SBwf[dom, sb] 

  // External actions act on global locations 
  (dom & Extern).loc in Glob 

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

fun HBvsMO_d [ dom : set Action, hb, sb, mo, rf : Action -> Action ] 
      : (Action -> Action) { 
  { u : (Extern + Ret), v : (Extern + Call) | 
    some disj w1, w2 : ((Write + RMW) & (dom <: loc.Atomic)) | 
    { 
      (w2 -> w1) in mo
      (w1 -> u) + (v -> w2) in iden + hb
    } 
  } 
} 

fun CoWR_d [ dom : set Action, hb, sb, mo, rf : Action -> Action ] 
      : (Action -> Action) { 
  { u : (Extern + Ret), v : (Extern + Call) |
    disj [u,v] and 
    some w1, w2 : (Write + RMW) & (dom <: loc.Atomic), 
               r : (Read + RMW) & (dom <: loc.Atomic)   | 
    { 
      disj [w1, w2, r] 
      (w1 -> r) in rf 
      (w1 -> w2) in mo
      (w2 -> u) in iden + hb 
      (v -> r) in iden + hb 
    } 
  } 
} 

fun HBacyc_d [ dom : set Action, hb, sb, mo, rf : Action -> Action ] 
        : (Action -> Action) { 
  { u : (Extern + Ret), v : (Extern + Call) | 
    disj [u,v] and 
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

fun getdeny[ dom : set Action, hb, sb, mo, rf : Action -> Action ] 
              : Action -> Action { 

   // Note: remove Ret -> Call deny because it's already enforced by sb 
   (CoWR_d[dom, hb, sb, mo, rf]
     + 
    HBvsMO_d[dom, hb, sb, mo, rf]
     + 
    HBacyc_d[dom, hb, sb, mo, rf])
        - (Ret -> Call) 
} 

fun getinterf[ dom : set Action ] : set Action { 
  dom & (Extern + Call + Ret) 
} 

// run hist_run_simp
//   { some dom : set Action, hb, sb, mo, rf : Action -> Action | {
//      valid[dom, ^hb, sb, mo, rf]
//      // DRF[dom, ^hb, sb, mo, rf]  
//  
//      // Sanity conditions 
//      dom = Action 
//      Loc = dom.loc 
//      is_core[hb] 
//      is_core[sb] 
//      //some Extern & Write
//      //some Intern.loc & (Extern & Write).loc 
// 
//      some disj w0, w1, w2 : Write | { 
//        w0 + w1 in Intern 
//        w2 in Extern 
//        one w0.loc + w1.loc + w2.loc 
//        w0.loc in Atomic 
//      } 
// 
//      one Call 
//      one Ret
//      preexecWF[ dom, sb ] 
// 
//      interesting_exec[dom, ^hb, sb, mo, rf] 
// 
//      some l : Glob & Atomic, v : Val | write2[ dom - Extern, sb, l, v] 
//   } 
// } for 5 


run hist_run
  { some dom : set Action, hb, sb, mo, rf, guar, deny : Action -> Action | {
     valid[dom, ^hb, sb, mo, rf]
     DRF[dom, ^hb, sb, mo, rf]  

     // prune boring contexts
     //interesting_exec[dom,^hb, sb, mo, rf]
     cutR[dom,^hb, sb, mo, rf] 
     cutW'[dom, ^hb, sb, mo, rf] 
     //some Extern & Read
     //some Intern.loc & (Extern & Read).loc 
 
     // Sanity conditions 
     dom = Action 
     Loc = dom.loc 
     is_core[hb] 
     is_core[sb] 

     // History stuff
     preexecWF[dom, sb] 
     one Call & dom 
     one Ret & dom 

     some l : Glob & Atomic, v : Val | write1read1[dom - Extern, sb, l, v] 

     //some l : Glob & Atomic, v : Val | 
     //  some disj r1, r2 : Write | { 
     //    r1.loc + r2.loc = l 
     //    r1.wval + r2.wval = v 
     //    dom - Extern = r1 + r2 + Call + Ret 
     //    r1 -> r2 in sb 
     //    sb in (dom -> dom) 

     //    some disj r1', r2' : Extern & Read, w : Extern & Write | {
     //      r1.rf = r1'
     //      r2.rf = r2'
     //    } 
     //}

     //some disj r1', r2' : Extern & Read, w : Extern & Write | {
     //  (r1' -> w) + (w -> r2') in deny 
     //}

     guar = getguar[dom, hb]
     deny = getdeny[dom, hb, sb, mo, rf] 
  } 
} for 5 but 0 RMW, 2 Val 


// TODO: kicks out too many execs: see WaRelim
pred interesting_exec[ dom : set Action, hb, sb, mo, rf : Action -> Action ] { 
  all r : Read & Extern & dom | some rf.r
  //all a :  | { 
  //  some i : Intern | (a -> i) in rf or (i -> a) in rf 
  //} 
  all disj w1, w2 : Extern & Write & dom when w1.loc = w2.loc | { 
    some r,r' : Intern | (w1 -> r) + (w2 -> r') in rf 
    or 
    some w3 : Intern & Write | 
       (w1 -> w3) + (w3 -> w2) in mo 
       or
       (w2 -> w3) + (w3 -> w1) in mo 
  } 
  //no dom & RMW

//  all a : Extern & dom | 
//    some a' : Intern & dom | a.loc = a'.loc 
} 

pred cutR[ dom: set Action, hb, sb, mo, rf : Action -> Action ] { 
  all r : Extern & Read | some w : Intern & Write | { 
    (w -> r) in rf
    no (w.rf & Extern) - r
  } 
} 

fun visible [ dom : set Action, hb, sb, mo, rf : Action -> Action ] 
    : Action  { 
  { a : Action & dom | 
    a in Intern 
   or 
    some a' : Intern & dom | some ((a -> a') + (a' -> a)) & rf }
} 

pred cutW'[ dom : set Action, hb, sb, mo, rf : Action -> Action ] { 
  all disj w, w' : Extern & dom | { 
    {(w.loc != w'.loc) and (no w + w' & visible[dom, hb, sb, mo, rf])} 
       implies 
    some w'' : visible[dom, hb, sb, mo, rf] | 
       (w -> w'') + (w'' -> w') in mo
  } 
} 

run hist_incl_run { 
  some dom : set Action, hb, sb, mo, rf : Action -> Action, 
      // guar, deny : Action -> Action, 
      dom' : set Action, hb', sb', mo', rf' : Action -> Action, 
      guar, guar', deny, deny' : Action -> Action 
    when { 
      interesting_exec[dom,^hb, sb, mo, rf] 
      // some Extern & Write

      valid[dom, ^hb, sb, mo, rf] 
      DRF[dom, ^hb, sb, mo, rf] 
      is_core[hb] 
      is_core[hb']
      is_core[sb]
      is_core[sb']
       
      preexecWF[dom, sb] 
      preexecWF[dom', sb'] 
 
      // identical interfaces 
      getinterf[dom] = getinterf[dom'] 

      // Sanity conditions 
      Action = dom + dom' 
      Loc = dom.loc + dom'.loc 
      
      // Shared call / return 
      one Call & (dom + dom') 
      one Ret & (dom + dom') 
      
      // Code definition 
      some l : Loc, v : Val | { 
        write2[ dom - Extern, sb, l, v] 
        write1[ dom' - Extern, sb', l, v] 
      } 
    } | { 
      valid[dom', ^hb', sb', mo', rf'] 
      DRF[dom', ^hb', sb', mo', rf'] 

      guar = getguar[dom, hb]
      guar' = getguar[dom', hb']
      guar' in guar

      deny = getdeny[dom, hb, sb, mo, rf] 
      deny' = getdeny[dom', hb', sb', mo', rf'] 
      deny' in deny 

      some r1, r2 : Extern & Read, w : Extern & Write | 
         disj[r1, r2, w]
    } 
  } for 7 but 1 Call, 1 Ret, 0 RMW


check hist_incl { 
  all dom : set Action, hb, sb, mo, rf : Action -> Action, 
      guar, deny : Action -> Action, 
      dom' : set Action, sb' : Action -> Action 
    when { 
      valid[dom, ^hb, sb, mo, rf] 
      DRF[dom, ^hb, sb, mo, rf] 
      preexecWF[dom, sb] 
      preexecWF[dom', sb'] 

      getinterf[dom] = getinterf[dom'] 
      guar = getguar[dom, ^hb] 
      deny = getdeny[dom, ^hb, sb, mo, rf] 
 
      // Cut boring executions. 
      cutR[dom, ^hb, sb, mo, rf] 
      cutW'[dom, ^hb, sb, mo, rf] 

      // Sanity conditions 
      Action = dom + dom' 
      Loc = dom.loc + dom'.loc 
      one Call & (dom + dom') 
      one Ret & (dom + dom') 
      is_core[hb] 
      is_core[sb] 
      is_core[sb'] 
      
      // Optimisation definition 
      RRElim[dom, dom', sb, sb'] 
  } | 
  some hb', mo', rf' : Action -> Action | { 
      valid[dom', ^hb', sb', mo', rf'] 
      DRF[dom', ^hb', sb', mo', rf'] 
      getguar[dom', ^hb'] in guar 
      getdeny[dom', ^hb', sb', mo', rf'] in deny 
  }
} for 6 but 0 NonAtomic


/*************************************************/ 
/* Optimizations                                 */ 
/*************************************************/

// Should be sound 
pred RaRintro [ dom, dom': Action, sb, sb' : Action -> Action] { 
  some l : Glob & Atomic, v : Val | { 
    read2[ dom - Extern, sb, l, v ] 
    read1[ dom' - Extern, sb', l, v ] 
  } 
} 

// Should be sound 
pred RaRelim [ dom, dom': Action, sb, sb' : Action -> Action] { 
  some l : Glob & Atomic, v: Val | { 
    read1[ dom - Extern, sb, l, v ] 
    read2[ dom' - Extern, sb', l, v ] 
  } 
} 

// Should be sound 
pred WaWelim [ dom, dom' : Action, sb, sb' : Action -> Action] { 
  some l : Glob & Atomic, v, v': Val | { 
    write1[ dom - Extern, sb, l, v']
    write2[ dom' - Extern, sb', l, v, v']
  } 
} 

// Should be unsound 
pred WaWelim2 [ dom, dom' : Action, sb, sb' : Action -> Action] { 
  some l : Glob & Atomic, v, v': Val | { 
    write1[ dom - Extern, sb, l, v]
    write2[ dom' - Extern, sb', l, v, v'] // NOTE: removed 2nd val.
  } 
} 

// Should be unsound 
pred WaWintro [ dom, dom' : Action, sb, sb' : Action -> Action] { 
  some l : Glob & Atomic, v, v': Val | { 
    write2[ dom - Extern, sb, l, v, v']
    write1[ dom' - Extern, sb', l, v]
  } 
} 

// Should be unsound 
pred WaRintro [ dom, dom' : Action, sb, sb' : Action -> Action] { 
  some l : Glob & Atomic, v: Val | { 
    read1write1[ dom - Extern, sb, l, v]
    read1[ dom' - Extern, sb', l, v]
  } 
} 

// Should be unsound 
pred WaRelim [ dom, dom' : Action, sb, sb' : Action -> Action] { 
  some l : Glob & Atomic, v: Val | { 
    read1[ dom - Extern, sb, l, v]
    read1write1[ dom' - Extern, sb', l, v]
  } 
} 

// Should be sound 
pred RaWelim [ dom, dom' : Action, sb, sb' : Action -> Action] { 
  some l : Glob & Atomic, v: Val | { 
    write1[ dom - Extern, sb, l, v]
    write1read1[ dom' - Extern, sb', l, v]
  } 
} 

// Should be unsound 
pred WRswap [ dom, dom' : Action, sb, sb' : Action -> Action] { 
  some l : Glob & Atomic, v: Val | { 
    read1write1[ dom - Extern, sb, l, v]
    write1read1[ dom' - Extern, sb', l, v]
  } 
} 

// Should be unsound 
pred RWswap [ dom, dom' : Action, sb, sb' : Action -> Action] { 
  some l : Glob & Atomic, v: Val | { 
    write1read1[ dom - Extern, sb, l, v]
    read1write1[ dom' - Extern, sb', l, v]
  } 
} 

/*************************************************/ 
/* Code fragments                                */ 
/*************************************************/


pred read1[ dom : set Action, sb : Action -> Action, l : Loc, v : Val ] { 
  some r1 : Read | { 
    r1.loc = l 
    r1.rval = v 
    dom = r1 + Call + Ret 
    sb in (dom -> dom) 
  } 
} 

pred read2[ dom : set Action, sb : Action -> Action, l : Loc, v : Val ] { 
  some disj r1, r2 : Read | { 
    r1.loc + r2.loc = l 
    r1.rval + r2.rval = v 
    dom = r1 + r2 + Call + Ret 
    r1 -> r2 in sb 
    sb in (dom -> dom) 
  } 
} 

pred write1[ dom : set Action, sb : Action -> Action, 
             l : Loc, v : Val ] { 
  some r1 : Write | { 
    r1.loc = l 
    r1.wval = v 
    dom = r1 + Call + Ret 
    sb in (dom -> dom) 
  } 
} 

pred write1read1 [ dom : set Action, sb : Action -> Action, 
             l : Loc, v : Val ] { 
  some disj r1 : Read, r2 : Write | { 
    r1.loc + r2.loc = l 
    r1.rval + r2.wval = v 
    dom = r1 + r2 + Call + Ret 
    r2 -> r1 in sb 
    sb in (dom -> dom) 
  } 
} 

pred read1write1 [ dom : set Action, sb : Action -> Action, 
             l : Loc, v : Val ] { 
  some disj r1 : Read, r2 : Write | { 
    r1.loc + r2.loc = l 
    r1.rval + r2.wval = v 
    dom = r1 + r2 + Call + Ret 
    r1 -> r2 in sb 
    sb in (dom -> dom) 
  } 
} 

pred write2[ dom : set Action, sb : Action -> Action, 
             l : Loc, v, v' : Val ] { 
  some disj r1, r2 : Write | { 
    r1.loc + r2.loc = l 
    r1.wval = v 
    r2.wval = v' 
    dom = r1 + r2 + Call + Ret 
    r1 -> r2 in sb 
    sb in (dom -> dom) 
  } 
} 

pred skip [ dom : set Action, sb : Action -> Action ] { 
  dom = Call + Ret
  sb in (dom -> dom) 
} 

/* 

pred WW_code [ e : Execution ] { 
  some disj w1, w2 : Write | { 
    (e.act & Intern) = w1 + w2
    (w1 -> w2) in e.sb
    one w1.loc + w2.loc 
    w1.loc in Atomic & Glob 
  } 
} 

*/


/*************************************************/ 
/* Generated code                                */ 
/*************************************************/

pred SampleOptLHS
         [ dom : set Action, sb : Action -> Action,
           x, y : Loc, v, v2 : Val ] { 
  sb in (dom -> dom)
  some disj op0, op1, op2, op3 : Action | { 
    dom = op0 + op1 + op2 + op3
    sb = (op0->op1) + (op1->op2) + (op2->op3)
    op0.loc = x
    op1.loc = x
    op2.loc = y
    op3.loc = y
    op0 in Write
    op1 in Read
    op2 in Write
    op3 in Read
    op1.rval = op2.wval
    op1.rval = v
  }
}
pred SampleOptRHS
         [ dom : set Action, sb : Action -> Action,
           x, y : Loc, v, v2 : Val ] { 
  sb in (dom -> dom)
  some disj op4, op5 : Action | { 
    dom = op4 + op5
    sb = (op4->op5)
    op4.loc = x
    op5.loc = y
    op4 in Read
    op5 in Write
    op4.rval = op5.wval
    op4.rval = v
  }
}
pred SampleOpt
     [ dom, dom' : set Action, sb, sb' : Action -> Action ] {
  some x, y : Loc, v, v2 : Val | {
    SampleOptLHS[dom, sb, x, y, v, v2]
    SampleOptRHS[dom', sb', x, y, v, v2]
  }
}

pred RRElimLHS
         [ dom : set Action, sb : Action -> Action,
           x : Loc, v : Val ] { 
  sb in (dom -> dom)
  some disj op0 : Action | { 
    dom = op0 + Call + Ret
    (none -> none) in sb
    op0.loc = x
    op0 in Read
    op0.rval = v
  }
}
pred RRElimRHS
         [ dom : set Action, sb : Action -> Action,
           x : Loc, v : Val ] { 
  sb in (dom -> dom)
  some disj op1, op2 : Action | { 
    dom = op1 + op2 + Call + Ret
    (none -> none) + (op1->op2) in sb
    op1.loc = x
    op2.loc = x
    op1 in Read
    op2 in Read
    op1.rval = v
  }
}
pred RRElim
     [ dom, dom' : set Action, sb, sb' : Action -> Action ] {
       some x : Glob & Atomic, v : Val | {
    RRElimLHS[dom - Extern, sb, x, v]
    RRElimRHS[dom' - Extern, sb', x, v]
  }
}
