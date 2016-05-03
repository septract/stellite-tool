module c11Relat

// TODO: refactor Call / Ret into Hist module?

abstract sig Loc {} 
sig Atomic, NonAtomic extends Loc {} 
sig Glob, Thr in Loc {} 

sig Val {} 
one sig Init in Val {} 

abstract sig Kind {} 
one sig Read, Write, Spesh extends Kind {} 

// Took out RMW for the moment. 
// RMW

sig Action {} 
sig Intern, Extern, Call, Ret extends Action {} 

fact { 
  disj[ Glob, Thr ] 
  Glob + Thr = Loc 
  Intern + Extern + Call + Ret = Action 
} 

// Values associated with actions correctly 
pred valWF[ dom : set Action, kind : Action -> Kind, 
            gloc : Action -> Glob, lloc : Action -> Thr, 
            wv, rv : Action -> Val ] { 
    kind in dom -> one Kind 
    wv in dom -> lone Val
    rv in dom -> lone Val
    gloc in dom -> lone Glob
    lloc in dom -> lone Thr

    all a : dom | { 
      kind[a] in Spesh iff a in (Call + Ret) 

      kind[a] in Read + Write implies { 
        one a.gloc 
        lone lloc 
      } 

      kind[a] in Write iff one a.wv
      kind[a] in Read iff one a.rv
    } 

    // No RMW over atomic locations
    // no (kind.RMW).loc & NonAtomic
} 

run valWF for 7

// No transitive edges in the relation 
pred is_core [ r : Action -> Action ] { 
  all a,b,c: Action | 
    (a -> b) + (b -> c) in ^r  implies  not (a -> c) in r 
} 

// Pre-execution structure 
pred SBwf [ dom : set Action, kind : Action -> Kind,
            loc : Action -> Loc, wv, rv : Action -> Val, 
            sb: Action -> Action ] {
  // Acyclic 
  no iden & ^sb     

  // Can't write initialisation value
  no (dom & kind.Write).wv & Init 
} 

pred HBacyc [ dom : set Action, kind : Action -> Kind,
              loc : Action -> Loc, wv, rv : Action -> Val, 
              hb, sb, mo, rf : Action -> Action ] { 
  no iden & ^hb 
} 

// Write the value of the preceding read accessing the same 
// local variable. 
pred RFwfLoc [ dom : set Action, kind : Action -> Kind, 
               gloc : Action -> Loc, lloc : Action -> Loc, 
               wv, rv : Action -> Val, 
               hb, sb, mo, rf : Action -> Action ] { 
 
} 

// Write the value given at the call to the same local variable.
pred RFwfLoc [ dom : set Action, kind : Action -> Kind, 
                gloc : Action -> Loc, lloc : Action -> Loc, 
                wv, rv : Action -> Val, 
                callval : Thr -> Val, retval : Thr -> Val, 
                hb, sb, mo, rf : Action -> Action ] { 
  all w : dom & kind.Write | { 
    all r : dom & kind.Read | { 
      r -> w in ^sb 
      r.lloc = w.lloc 
      no r' : dom & kind.Read | { 
        (r -> r') + (r' -> w) in ^sb 
        r'.lloc = w.lloc 
      }  
    } implies r.rv = w.wv
  and 
    { Call -> w in ^sb 
      no r' : dom & kind.Read | { 
        (Call -> r') + (r' -> w) in ^sb 
        r'.lloc = w.lloc 
      }  
    } implies w.wv = (w.lloc).callval
  } 
} 

pred RFwf [ dom : set Action, kind : Action -> Kind,
            loc : Action -> Loc, wv, rv : Action -> Val, 
            hb, sb, mo, rf : Action -> Action ] { 
  // Read from at most one write 
  rf in kind.Write lone -> kind.Read 

  // Irreflexive 
  no iden & rf 

  all r : (dom & kind.Read) | { 
    // Read from the same location written 
    (rf.r).loc in r.loc 

    // Value taken from origin write
    // NOTE: can't be init value (does this matter?) 
    some rf.r implies r.rv = (rf.r).wv // and not r.rval in Init
    no rf.r implies r.rv in Init 

    // Allow initialisation reads, but force actions to 
    // read from an explicit write if any is hb-available 
    ( (some (hb + mo).r & (kind.Write <: loc).(r.loc) ) 
          implies (some rf.r) ) 
  } 
} 

pred HBdef [ dom : set Action, kind : Action -> Kind,
             loc : Action -> Loc, wv, rv : Action -> Val, 
             hb, sb, mo, rf : Action -> Action ] {
  let aact = (dom <: loc).Atomic | 
  let sw = rf & (aact -> aact) | 
  hb = ^(sw + sb)
} 

// Note: this also covers the AtomRMW rule. 
pred CoWR [ dom : set Action, kind : Action -> Kind,
            loc : Action -> Loc, wv, rv : Action -> Val, 
            hb, sb, mo, rf : Action -> Action ] {
  all r : dom & kind.Read, w1 : rf.r | 
    not { (w1 -> r) in mo.(hb + mo) } 
} 

pred MOwf [ dom : set Action, kind : Action -> Kind,
            loc : Action -> Loc, wv, rv : Action -> Val, 
            hb, sb, mo, rf : Action -> Action ] { 
  mo = ^mo     // transitive
  no iden & mo  // irreflexive 
  mo in kind.Write -> kind.Write
  
   // per-location total on atomics
   { all disj w1, w2 : kind.Write | 
     (w1 -> w2) in mo + ~mo iff 
       (w1.loc = w2.loc) and w1 + w2 in (dom <: loc.Atomic) } 
 } 
 
pred HBvsMO [ dom : set Action, kind : Action -> Kind,
              loc : Action -> Loc, wv, rv : Action -> Val, 
              hb, sb, mo, rf : Action -> Action ] { 
  no hb & ~mo 
} 

// // Stronger version of this axiom: rule out cycles, not loops
// pred HBMOacyc [ e : Execution ] { 
//   no iden & ^(e.hb + e.mo) 
// } 

pred RFNonAtomic [ dom : set Action, kind : Action -> Kind,
                   loc : Action -> Loc, wv, rv : Action -> Val, 
                   hb, sb, mo, rf : Action -> Action ] { 
  let NA_reads = (dom <: loc).NonAtomic & kind.Read | 
     rf :> NA_reads in hb 
} 

pred DRF [ dom : set Action, kind : Action -> Kind,
           loc : Action -> Loc, wv, rv : Action -> Val, 
           hb, sb, mo, rf : Action -> Action ] { 
  all l : NonAtomic | 
  all disj w, a : (dom <: loc).l | 
    (w in kind.Write) 
    and 
    (a in kind.(Write + Read)) 
    implies 
    (w -> a) in (hb + ~hb) 
} 


pred valid [ dom : set Action, kind : Action -> Kind,
             loc : Action -> Loc, wv, rv : Action -> Val, 
             hb, sb, mo, rf : Action -> Action ] {
  // Sanity conditions
  hb + sb + mo + rf in (dom -> dom) 

  // Pre-execution structure 
  valWF[dom, kind, loc, (none -> none), wv, rv]
  SBwf[dom, kind, loc, wv, rv, sb] 

  // Axioms 
  HBacyc[dom, kind, loc, wv, rv, hb, sb, mo, rf] 
  RFwf[dom, kind, loc, wv, rv, hb, sb, mo, rf] 
  HBdef[dom, kind, loc, wv, rv, hb, sb, mo, rf] 
  CoWR[dom, kind, loc, wv, rv, hb, sb, mo, rf] 
  MOwf[dom, kind, loc, wv, rv, hb, sb, mo, rf] 
  HBvsMO[dom, kind, loc, wv, rv, hb, sb, mo, rf] 
  RFNonAtomic[dom, kind, loc, wv, rv, hb, sb, mo, rf] 
} 

pred sequential [ dom : set Action, sb : Action -> Action ] { 
  all disj a1, a2 : dom |   a1 -> a2 in ^sb + ^(~sb)
} 


/*************************************************/ 
/* Tests                                         */ 
/*************************************************/ 

run valid_run
  { some dom : set Action, kind : Action -> Kind,
               loc : Action -> Loc, wv, rv : Action -> Val, 
               hb, sb, mo, rf : Action -> Action | {
     valid[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]
     //DRF[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]  
     dom = Action 
     Loc = dom.loc 
     is_core[hb] 
     is_core[sb] 
     some Call
  } 
} for 6 but 0 NonAtomic 

 
run seq_run
  { some dom : set Action, kind : Action -> Kind,
               loc : Action -> Loc, wv, rv : Action -> Val, 
               hb, sb, mo, rf : Action -> Action | {
     valid[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]
     dom = Action 
     Loc = dom.loc 
     is_core[hb] 
     is_core[sb] 
     // check sequential 
     sequential[dom, sb]  
     some Call 
  } 
} for 6
 

// Executions with no non-atomics are automatically DRF 
check atomic_DRF 
  { all dom : set Action, kind : Action -> Kind,
               loc : Action -> Loc, wv, rv : Action -> Val, 
               hb, sb, mo, rf : Action -> Action |
    valid[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]  
       implies DRF[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
  }
  for 30
  but 0 NonAtomic 

// Sequential executions are automatically DRF 
check seq_DRF 
  { all dom : set Action, kind : Action -> Kind,
              loc : Action -> Loc, wv, rv : Action -> Val, 
              hb, sb, mo, rf : Action -> Action |
    valid[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
      and sequential[dom, sb] 
    implies DRF[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
  } 
  for 10

run litmus_SB 
  { some dom : set Action, kind : Action -> Kind,
         loc : Action -> Loc, wv, rv : Action -> Val, 
         hb, sb, mo, rf : Action -> Action | {
      valid[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]
      DRF[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
      dom = Action 
      Loc = dom.loc 
      is_core[hb] 
      is_core[sb] 
      // litmus test 
      code_SB[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
    }
  } 
  for 6 
  but 0 NonAtomic, 2 Val 

run litmus_IRIW 
  { some dom : set Action, kind : Action -> Kind,
         loc : Action -> Loc, wv, rv : Action -> Val, 
         hb, sb, mo, rf : Action -> Action | {
      valid[dom, kind, loc, wv, rv, ^hb, sb, mo, rf]
      DRF[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
      dom = Action 
      Loc = dom.loc 
      is_core[hb] 
      is_core[sb] 
      // litmus test 
      code_IRIW[dom, kind, loc, wv, rv, ^hb, sb, mo, rf] 
    }
  } 
  for 10
  but 0 NonAtomic, 2 Val 

/*************************************************/ 
/* Litmus test code                              */ 
/*************************************************/ 

// SB litmus test without initialisation
pred code_SB [ dom : set Action, kind : Action -> Kind,
               loc : Action -> Loc, wv, rv : Action -> Val, 
               hb, sb, mo, rf : Action -> Action ] { 
  some disj wx, wy : kind.Write |  
  some disj rx, ry : kind.Read |  { 
    dom = (wx + wy + rx + ry)
    (wx -> ry) + (wy -> rx) in sb // allow stronger sb  
    one wx.loc + rx.loc 
    one wy.loc + ry.loc 
    no wx.loc & wy.loc
    no rf // read from initialisation 
  } 
} 

// Comment from JPW - alloy simplifies rel = ((a->b) + (c->d)... 
// Refactor this code? 

pred code_IRIW [ dom : set Action, kind : Action -> Kind,
                 loc : Action -> Loc, wv, rv : Action -> Val, 
                 hb, sb, mo, rf : Action -> Action ] { 
  some disj wx, wy : kind.Write | 
  some disj r1x, r2x, r1y, r2y : kind.Read | { 
    dom = wx + wy + r1x + r2x + r1y + r2y 
    rf = ((wx -> r1x) + (wy -> r2y)) 
    ((r1x -> r1y) + (r2y -> r2x)) in sb
    one wx.loc + r1x.loc + r2x.loc 
    one wy.loc + r1y.loc + r2y.loc 
    no wx.loc & wy.loc 
  } 
} 
