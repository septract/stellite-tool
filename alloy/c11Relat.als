module c11Relat
// open util/relation

// TODO: Get rid of spesh, restrict Call / Ret to a singleton

// Disable non-atomics entirely
fact { 
  no NonAtomic 
} 

// Locations can be local or global 
abstract sig Loc {} 
sig Glob, Thr extends Loc {} 

// Furthermore locations can be atomic or nonatomic 
sig Atomic, NonAtomic in Glob {} 
fact { 
  Atomic + NonAtomic = Glob 
  disj [ Atomic, NonAtomic ] 
} 

sig Val {} 
one sig Init in Val {} // Magic initialisation value

// Actions kinds corresponding to different memory actions
abstract sig Kind {} 
one sig Read, Write, RMW, AssmEq, Spesh extends Kind {} 

// Actions 
abstract sig Action {} 
sig Intern, Extern, Call, Ret extends Action {} 

// Locations are associated with actions correctly 
pred locWF[ dom : set Action, 
            kind : Action -> Kind, 
            gloc : Action -> Glob, 
            lloc1, lloc2 : Intern -> Thr ] { 
    kind in dom -> one Kind 
    gloc in (dom - (Call + Ret)) -> lone Glob
    lloc1 in dom -> lone Thr
    lloc2 in dom -> lone Thr

    all a : dom | { 
      a in (Call + Ret) iff kind[a] in Spesh

      // All reads and writes access global locations
      a in kind.(Read + Write + RMW)  iff  one a.gloc

      // Reads and writes acces one local variable 
      a in kind.(Read + Write) & Intern  implies  { 
        one a.lloc1 and no a.lloc2
      } 

      // Assume and RMW access two local variables
      a in kind.(AssmEq + RMW) & Intern  implies  { 
        one a.lloc1 and one a.lloc2
      } 
    } 
} 

// Values are associated with actions correctly 
pred valWF[ dom : set Action,
            kind : Action -> Kind, 
            wv, rv : Action -> Val ] { 
    wv in (dom - (Call + Ret)) -> lone Val
    rv in (dom - (Call + Ret)) -> lone Val

    // Writes have a written value, reads have a read value, RMW have both
    all a : dom - (Call + Ret) | { 
      kind[a] in Write iff { 
        one a.wv
        no a.rv
      } 
      kind[a] in Read iff { 
        one a.rv
        no a.wv
      } 
      kind[a] in RMW iff { 
        one a.rv
        one a.wv
      } 
      // TODO: add case for no r/w?  
    } 
} 

// No transitive edges in the relation 
pred is_core [ r : Action -> Action ] { 
  all a,b,c: Action | 
    (a -> b) + (b -> c) in ^r  implies  not (a -> c) in r 
} 

// SB is acyclic 
pred SBwf [ dom : set Action, 
            kind : Action -> Kind,
            sb: Action -> Action ] {
  no iden & ^sb     
} 

// HB is acyclic 
pred HBacyc [ dom : set Action, kind : Action -> Kind,
              loc : Action -> Loc, wv, rv : Action -> Val, 
              hb, sb, mo, rf : Action -> Action ] { 
  no iden & ^hb 
} 

// Find the last value written for a given local variable and action
fun lastval [ dom : set Action, 
              kind : Action -> Kind, 
              lloc : Action -> Loc, 
              callmap : Thr -> Val, 
              rv : Action -> Val, 
              sb : Action -> Action, 
              curr : Action, 
              currloc : Loc ] : set Val { 
  { v : Val | 
    some r : dom & kind.Read | { 
      r.rv = v 
      r -> curr in ^sb 
      r.lloc = currloc 
      no r' : dom & kind.Read | { 
        (r -> r') + (r' -> curr) in ^sb 
        r'.lloc = currloc  
      } 
    } 
  } 
    + 
  { v : Val | {
      v = (currloc).callmap 
      (Call -> curr) in ^sb 
      no r' : dom & kind.Read | { 
        (Call -> r') + (r' -> curr) in ^sb 
        r'.lloc = currloc  
      }  
    } 
  } 
} 

// Write the value given at the call to the same local variable.
// TODO: handle internal RMW  
pred RFwfLocal [ dom : set Action, 
                kind : Action -> Kind, 
                gloc : Action -> Loc, 
                lloc1, lloc2 : Action -> Loc, 
                callmap, retmap : Thr -> Val, 
                wv, rv : Action -> Val, 
                hb, sb, mo, rf : Action -> Action ] { 
  callmap in Thr -> one Val 
  retmap in Thr -> one Val 

  all a : dom & kind.AssmEq | { 
    lastval[dom, kind, lloc1, callmap, rv, sb, a, a.lloc1] = 
      lastval[dom, kind, lloc1, callmap, rv, sb, a, a.lloc2] 
  } 

  // Writes take the correct local var value 
  all w : dom & kind.Write | {
    w.wv = lastval[dom, kind, lloc1, callmap, rv, sb, w, w.lloc1] 
  } 

  // The retmap takes the correct values. 
  all t : Thr | { 
    t.retmap = lastval[dom, kind, lloc1, callmap, rv, sb, Ret, t] 
  } 
} 

// RF is well-formed 
pred RFwf [ dom : set Action, 
            kind : Action -> Kind,
            loc : Action -> Loc, 
            wv, rv : Action -> Val, 
            hb, sb, mo, rf : Action -> Action ] { 
  // Read from at most one write 
  rf in kind.(Write + RMW) lone -> kind.(Read + RMW) 

  // Irreflexive 
  no iden & rf 

  all r : dom & kind.(Read + RMW) | { 
    // Read from the same location written 
    (rf.r).loc in r.loc 

    // Value taken from origin write
    // TODO: decide whether to allow assignments to Init
    some rf.r implies r.rv = (rf.r).wv // and not r.rval in Init
    no rf.r implies r.rv in Init 

    // Allow initialisation reads, but force actions to 
    // read from an explicit write if any is hb-available 
    (some (hb + mo).r & (kind.(Write + RMW) <: loc).(r.loc) ) 
          implies (some rf.r) 
  } 
} 

// Define hb by combining rf and hb over atomics 
pred HBdef [ dom : set Action, 
             kind : Action -> Kind,
             loc : Action -> Loc, 
             wv, rv : Action -> Val, 
             hb, sb, mo, rf : Action -> Action ] {
  let aact = (dom <: loc).Atomic | 
  let sw = rf & (aact -> aact) | 
  hb = ^(sw + sb)
} 

// Coherence order is respected
// Note: this also covers the AtomRMW rule. 
pred CoWR [ dom : set Action, kind : Action -> Kind,
            loc : Action -> Loc, wv, rv : Action -> Val, 
            hb, sb, mo, rf : Action -> Action ] {
  all r : dom & kind.(Read + RMW), w1 : rf.r | 
    not { (w1 -> r) in mo.(hb + mo) } 
} 

// Modification order is well-formed
pred MOwf [ dom : set Action, kind : Action -> Kind,
            loc : Action -> Loc, wv, rv : Action -> Val, 
            hb, sb, mo, rf : Action -> Action ] { 
  mo = ^mo     // transitive
  no iden & mo  // irreflexive 
  mo in kind.(Write + RMW) -> kind.(Write + RMW)
  
  // per-location total on atomics
  all disj w1, w2 : kind.(Write + RMW) | 
     (w1 -> w2) in mo + ~mo iff 
       (w1.loc = w2.loc) and w1 + w2 in (dom <: loc.Atomic)
 } 
 
// HB and MO do not contradict one another
pred HBvsMO [ dom : set Action, kind : Action -> Kind,
              loc : Action -> Loc, wv, rv : Action -> Val, 
              hb, sb, mo, rf : Action -> Action ] { 
  no hb & ~mo 
} 

// // Stronger version of this axiom: rule out cycles, not loops
// pred HBMOacyc [ e : Execution ] { 
//   no iden & ^(e.hb + e.mo) 
// } 

// Reads-from edges for NAs all follow hb 
pred RFNonAtomic [ dom : set Action,  
                   kind : Action -> Kind,
                   loc : Action -> Loc, 
                   wv, rv : Action -> Val, 
                   hb, sb, mo, rf : Action -> Action ] { 
  let NA_reads = (dom <: loc).NonAtomic & kind.Read | 
     (rf :> NA_reads) in hb 
} 

// Test whether the execution is DRF 
pred DRF [ dom : set Action, 
           kind : Action -> Kind,
           loc : Action -> Loc, 
           wv, rv : Action -> Val, 
           hb, sb, mo, rf : Action -> Action ] { 
  all l : NonAtomic | 
  all disj w, a : (dom <: loc).l | 
    (w in kind.Write) 
    and 
    (a in kind.(Write + Read)) 
    implies 
    (w -> a) in (hb + ~hb) 
} 

// Combine the different predicates into execution validity 
pred valid [ dom : set Action, 
             kind : Action -> Kind,
             gloc : Action -> Glob, 
             lloc1, lloc2: Action -> Thr, 
             callmap, retmap : Thr -> Val, 
             wv, rv : Action -> Val, 
             hb, sb, mo, rf : Action -> Action ] {
  // Sanity conditions
  hb + sb + mo + rf in (dom -> dom) 

  // Pre-execution structure 
  locWF[dom, kind, gloc, lloc1, lloc2]  
  valWF[dom, kind, wv, rv]
  SBwf[dom, kind, sb]

  // Local variable handling 
  RFwfLocal[dom, kind, gloc, lloc1, lloc2, callmap, retmap, wv, rv, hb, sb, mo, rf] 

  // Axioms 
  HBacyc[dom, kind, gloc, wv, rv, hb, sb, mo, rf] 
  RFwf[dom, kind, gloc, wv, rv, hb, sb, mo, rf] 
  HBdef[dom, kind, gloc, wv, rv, hb, sb, mo, rf] 
  CoWR[dom, kind, gloc, wv, rv, hb, sb, mo, rf] 
  MOwf[dom, kind, gloc, wv, rv, hb, sb, mo, rf] 
  HBvsMO[dom, kind, gloc, wv, rv, hb, sb, mo, rf] 
  RFNonAtomic[dom, kind, gloc, wv, rv, hb, sb, mo, rf] 
} 

// The execution is sequential, i.e. sb is total
pred sequential [ dom : set Action, sb : Action -> Action ] { 
  all disj a1, a2 : dom |   a1 -> a2 in ^sb + ^(~sb)
} 


/*************************************************/ 
/* Tests                                         */ 
/*************************************************/ 

// run valid_run
//   { some dom : set Action, kind : Action -> Kind,
//                gloc, lloc : Action -> Loc, 
//                callmap, retmap : Thr -> Val, 
//                wv, rv : Action -> Val, 
//                hb, sb, mo, rf : Action -> Action | {
//      valid[dom, kind, gloc, lloc, callmap, retmap, wv, rv, ^hb, sb, mo, rf]
//      dom = Action 
//      Loc = dom.(gloc + lloc)
//      is_core[hb] 
//      is_core[sb] 
//      no Call + Ret
//   } 
// } for 6 but exactly 2 Thr, 0 Extern
// 
//  
// run seq_run
//   { some dom : set Action, kind : Action -> Kind,
//                gloc, lloc : Action -> Loc, 
//                callmap, retmap : Thr -> Val, 
//                wv, rv : Action -> Val, 
//                hb, sb, mo, rf : Action -> Action | {
//      valid[dom, kind, gloc, lloc, callmap, retmap, wv, rv, ^hb, sb, mo, rf]
//      dom = Action 
//      Loc = dom.(gloc + lloc) 
//      is_core[hb] 
//      is_core[sb] 
//      // check sequential 
//      sequential[dom, sb]  
//      no Call + Ret
//   } 
// } for 6
//  

// // Executions with no non-atomics are automatically DRF 
// check atomic_DRF 
//   { all dom : set Action, kind : Action -> Kind,
//                loc : Action -> Loc, wv, rv : Action -> Val, 
//                hb, sb, mo, rf : Action -> Action |
//     valid[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]  
//        implies DRF[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
//   }
//   for 30
//   but 0 NonAtomic 
// 
// // Sequential executions are automatically DRF 
// check seq_DRF 
//   { all dom : set Action, kind : Action -> Kind,
//               loc : Action -> Loc, wv, rv : Action -> Val, 
//               hb, sb, mo, rf : Action -> Action |
//     valid[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
//       and sequential[dom, sb] 
//     implies DRF[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
//   } 
//   for 10
// 
// run litmus_SB 
//   { some dom : set Action, kind : Action -> Kind,
//          loc : Action -> Loc, wv, rv : Action -> Val, 
//          hb, sb, mo, rf : Action -> Action | {
//       valid[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]
//       DRF[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
//       dom = Action 
//       Loc = dom.loc 
//       is_core[hb] 
//       is_core[sb] 
//       // litmus test 
//       code_SB[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
//     }
//   } 
//   for 6 
//   but 0 NonAtomic, 2 Val 
// 
// run litmus_IRIW 
//   { some dom : set Action, kind : Action -> Kind,
//          loc : Action -> Loc, wv, rv : Action -> Val, 
//          hb, sb, mo, rf : Action -> Action | {
//       valid[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]
//       DRF[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
//       dom = Action 
//       Loc = dom.loc 
//       is_core[hb] 
//       is_core[sb] 
//       // litmus test 
//       code_IRIW[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
//     }
//   } 
//   for 10
//   but 0 NonAtomic, 2 Val 
// 
// /*************************************************/ 
// /* Litmus test code                              */ 
// /*************************************************/ 
// 
// // SB litmus test without initialisation
// pred code_SB [ dom : set Action, kind : Action -> Kind,
//                loc : Action -> Loc, wv, rv : Action -> Val, 
//                hb, sb, mo, rf : Action -> Action ] { 
//   some disj wx, wy : kind.Write |  
//   some disj rx, ry : kind.Read |  { 
//     dom = (wx + wy + rx + ry)
//     (wx -> ry) + (wy -> rx) in sb // allow stronger sb  
//     one wx.loc + rx.loc 
//     one wy.loc + ry.loc 
//     no wx.loc & wy.loc
//     no rf // read from initialisation 
//   } 
// } 
// 
// // Comment from JPW - alloy simplifies rel = ((a->b) + (c->d)... 
// // Refactor this code? 
// 
// pred code_IRIW [ dom : set Action, kind : Action -> Kind,
//                  loc : Action -> Loc, wv, rv : Action -> Val, 
//                  hb, sb, mo, rf : Action -> Action ] { 
//   some disj wx, wy : kind.Write | 
//   some disj r1x, r2x, r1y, r2y : kind.Read | { 
//     dom = wx + wy + r1x + r2x + r1y + r2y 
//     rf = ((wx -> r1x) + (wy -> r2y)) 
//     ((r1x -> r1y) + (r2y -> r2x)) in sb
//     one wx.loc + r1x.loc + r2x.loc 
//     one wy.loc + r1y.loc + r2y.loc 
//     no wx.loc & wy.loc 
//   } 
// } 
// 
