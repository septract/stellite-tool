// Optimisations

module optPred
open c11Relat 

/*************************************************/ 
/* Optimizations                                 */ 
/*************************************************/

// Should be sound 
pred optPredDef [ dom, dom': Action, 
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

// Should be unsound 
pred RtoWrepl [ dom, dom': Action, 
                kind, kind' : Action -> Kind, 
                gloc, gloc' : Action -> Glob, 
                lloc, lloc' : Action -> Thr, 
                sb, sb' : Action -> Action] { 
  some g : Glob & Atomic, t : Thr | { 
    write1[ dom - Extern, kind, gloc, lloc, sb, g, t ] 
    read1[ dom' - Extern, kind', gloc', lloc', sb', g, t ] 
  } 
} 

// Should be unsound 
pred WtoRrepl [ dom, dom': Action, 
                kind, kind' : Action -> Kind, 
                gloc, gloc' : Action -> Glob, 
                lloc, lloc' : Action -> Thr, 
                sb, sb' : Action -> Action] { 
  some g : Glob & Atomic, t : Thr | { 
    read1[ dom - Extern, kind, gloc, lloc, sb, g, t ] 
    write1[ dom' - Extern, kind', gloc', lloc', sb', g, t ] 
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

pred write1[ dom : set Action, kind : Action -> Kind,
            gloc : Action -> Glob, lloc : Action -> Thr, 
            sb : Action -> Action, g : Glob, t : Thr ] { 
  some w1 : kind.Write | { 
    w1.gloc = g 
    w1.lloc = t 
    dom = w1 + Call + Ret 
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


// Generated code: 

pred RReqTestLHS
         [ dom : set Action, kind : Action -> Kind,
           gloc : Action -> Glob, lloc : Action -> Thr, 
           sb : Action -> Action, x : Glob, l : Thr ] { 
  sb in (dom -> dom)
  some disj op0 : Action | { 
    dom = op0 + Call + Ret
    (none -> none) in sb
    op0.gloc = x
    op0.lloc = l
    op0 in kind.Read
  }
}
pred RReqTestRHS
         [ dom : set Action, kind : Action -> Kind,
           gloc : Action -> Glob, lloc : Action -> Thr, 
           sb : Action -> Action, x : Glob, l : Thr ] { 
  sb in (dom -> dom)
  some disj op1, op2 : Action | { 
    dom = op1 + op2 + Call + Ret
    (none -> none) + (op1->op2) in sb
    op1.gloc = x
    op2.gloc = x
    op1.lloc = l
    op2.lloc = l
    op1 in kind.Read
    op2 in kind.Read
  }
}
pred RReqTest
     [ dom, dom' : set Action,
       kind, kind' : Action -> Kind,
       gloc, gloc' : Action -> Glob,
       lloc, lloc' : Action -> Thr,
       sb, sb' : Action -> Action ] {
  some x : Glob, l : Thr | {
    RReqTestLHS[dom - Extern, kind, gloc, lloc, sb, x, l]
    RReqTestRHS[dom' - Extern, kind', gloc', lloc', sb', x, l]
  }
}
