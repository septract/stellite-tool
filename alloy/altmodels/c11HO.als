module c11HO

abstract sig Loc {} 

sig Atomic, NonAtomic extends Loc {} 

sig Val {} 
one sig Init in Val {} 

abstract sig Action { loc : lone Loc, rval, wval : lone Val } 
sig Read, Write, RMW, Call, Ret extends Action {} 

// Values associated with actions correctly 
fact { 
  all w : Read + Write + RMW | one w.loc 
  all w : Write | no w.rval 
  all w' : Write + RMW | one w'.wval 
  all r : Read | no r.wval 
  all r' : Read + RMW | one r'.rval 
  all c : Call + Ret | no c.loc + c.rval + c.wval 
} 

// No RMW over atomic locations
fact { 
  no RMW.loc & NonAtomic
} 

// No transitive edges in the relation 
pred is_core [ r : Action -> Action ] { 
  all a,b,c: Action | 
    (a -> b) + (b -> c) in ^r  implies  not (a -> c) in r 
} 

// Pre-execution structure 
pred SBwf [ dom : set Action, sb: Action -> Action ] {
  //sb = ^sb          // transitively closed 
  no iden & ^sb     // acyclic 
  no (dom & (Write + RMW)).wval & Init // Can't write initialisation value
} 

pred HBacyc [ dom : set Action, hb, sb, mo, rf : Action -> Action ] {
  no iden & ^hb 
} 

pred RFwf [ dom : set Action, hb, sb, mo, rf : Action -> Action ] { 
  // Read from at most one write 
  rf in (Write + RMW) lone -> (Read + RMW) 

  // Irreflexive 
  no iden & rf 

  all r : (dom & (Read+RMW)) | 
  { 
    // Read from the same location written 
    (rf.r).loc in r.loc 

    // Value taken from origin write
    // NOTE: can't be init value (does this matter?) 
    some rf.r implies r.rval = (rf.r).wval // and not r.rval in Init
    no rf.r implies r.rval in Init 

    // Allow silent initialisation reads, but force actions to 
    // read from an explicit write if any is hb-available 
    ( (some (hb + mo).r & ((Write+RMW) <: loc).(r.loc) ) 
          implies (some rf.r) ) 
  } 
} 

pred HBdef [ dom : set Action, hb, sb, mo, rf : Action -> Action ] {
  let aact = (dom <: loc).Atomic | 
  let sw = rf & (aact -> aact) | 
  hb = ^(sw + sb)
} 

// Note: this also covers the AtomRMW rule. 
pred CoWR [ dom : set Action, hb, sb, mo, rf : Action -> Action ] {
  all r : dom & (Read+RMW), w1 : rf.r | 
    not { (w1 -> r) in mo.(hb + mo) } 
} 

pred MOwf [ dom : set Action, hb, sb, mo, rf : Action -> Action ] { 
  mo = ^mo     // transitive
  no iden & mo  // irreflexive 
  mo in (Write + RMW) -> (Write + RMW)
  
  // per-location total on atomics
  { all disj w1, w2 : Write + RMW | 
    (w1 -> w2) in mo + ~mo iff 
      (w1.loc = w2.loc) and w1 + w2 in (dom <: loc.Atomic) } 
} 

pred HBvsMO [ dom : set Action, hb, sb, mo, rf : Action -> Action ] { 
  no hb & ~mo 
} 

// // Stronger version of this axiom: rule out cycles, not loops
// pred HBMOacyc [ e : Execution ] { 
//   no iden & ^(e.hb + e.mo) 
// } 

pred RFNonAtomic [ dom : set Action, hb, sb, mo, rf : Action -> Action ] { 
  let NA_reads = (dom <: loc).NonAtomic & (Read+RMW) | 
     rf :> NA_reads in hb 
} 

pred DRF [ dom : set Action, hb, sb, mo, rf : Action -> Action ] { 
  all l : NonAtomic | 
  all disj w, a : (dom <: loc).l | 
    (w in Write) implies 
    (w -> a) in (hb + ~hb) 
} 

pred valid [ dom : set Action, hb, sb, mo, rf : Action -> Action ] {
  hb + sb + mo + rf in (dom -> dom) 

  SBwf[dom, sb] 
  HBacyc[dom, hb, sb, mo, rf] 
  RFwf[dom, hb, sb, mo, rf] 
  HBdef[dom, hb, sb, mo, rf] 
  MOwf[dom, hb, sb, mo, rf] 
  CoWR[dom, hb, sb, mo, rf] 
  HBvsMO[dom, hb, sb, mo, rf] 
  // HBMOacyc[dom, hb, sb, mo, rf] 
  RFNonAtomic[dom, hb, sb, mo, rf] 
} 

pred sequential [ dom : set Action, hb, sb, mo, rf : Action -> Action ] { 
  all disj a1, a2 : dom | 
  a1 -> a2 in ^sb + ^(~sb)
} 

/*************************************************/ 
/* Tests                                         */ 
/*************************************************/ 

run valid_run
  { some dom : set Action, hb, sb, mo, rf : Action -> Action | {
     valid[dom, ^hb, sb, mo, rf]
     DRF[dom, ^hb, sb, mo, rf]  
     dom = Action 
     Loc = dom.loc 
     is_core[hb] 
     is_core[sb] 
     some rf 
  } 
} for 6 but exactly 1 Call, exactly 1 Ret

run seq_run
  { some dom : set Action, hb, sb, mo, rf : Action -> Action | {
     valid[dom, ^hb, sb, mo, rf]
     dom = Action 
     Loc = dom.loc 
     is_core[hb] 
     is_core[sb] 
     // check sequential 
     sequential[dom, ^hb, sb, mo, rf]  
  } 
} for 6 but exactly 2 Read, 0 NonAtomic

// Executions with no non-atomics are automatically DRF 
check atomic_DRF 
  { all dom : set Action, hb, sb, mo, rf : Action -> Action | 
    valid[dom, hb, sb, mo, rf]  
       implies DRF[dom, hb, sb, mo, rf] 
  }
  for 30
  but 0 NonAtomic 

// Sequential executions are automatically DRF 
check seq_DRF 
  { all dom : set Action, hb, sb, mo, rf : Action -> Action | 
    { valid[dom, hb, sb, mo, rf] 
      sequential[dom, hb, sb, mo, rf] 
     }
    implies DRF[dom, hb, sb, mo, rf] 
  } 
  for 4

run litmus_SB 
  { some dom : set Action, hb, sb, mo, rf : Action -> Action | {
      valid[dom, ^hb, sb, mo, rf]
      DRF[dom, ^hb, sb, mo, rf] 
      dom = Action 
      Loc = dom.loc 
      is_core[hb] 
      is_core[sb] 
      // litmus test 
      code_SB[dom, hb, sb, mo, rf] 
    }
  } 
  for 6 
  but 0 NonAtomic 

run litmus_IRIW 
  { some dom : set Action, hb, sb, mo, rf : Action -> Action | {
      valid[dom, ^hb, sb, mo, rf]
      DRF[dom, ^hb, sb, mo, rf] 
      dom = Action 
      Loc = dom.loc 
      is_core[hb] 
      is_core[sb] 
      // litmus test 
      code_IRIW[dom, hb, sb, mo, rf] 
    }
  } 
  for 6 
  but 0 NonAtomic 

run test_sample 
  { some dom : set Action, hb, sb, mo, rf : Action -> Action, 
         l1, l2 : Loc, v1, v2 : Val | {
      valid[dom, ^hb, sb, mo, rf]
      DRF[dom, ^hb, sb, mo, rf] 
      dom = Action 
      Loc = dom.loc 
      Val = v1 + v2 // need this?  
      is_core[hb] 
      is_core[sb] 
      // litmus test 
      Sample_opt[dom, sb, l1, l2, v1, v2] 
    }
  } 
  for 8 
  but 0 NonAtomic 

/*************************************************/ 
/* Litmus test code                              */ 
/*************************************************/ 

// SB litmus test without initialisation
pred code_SB [ dom : set Action, hb, sb, mo, rf : Action -> Action ] { 
  some disj wx, wy : Write |  
  some disj rx, ry : Read |  { 
    dom = (wx + wy + rx + ry)
    (wx -> ry) + (wy -> rx) in sb // allow stronger sb  
    one wx.loc + rx.loc 
    one wy.loc + ry.loc 
    no wx.loc & wy.loc
    no rf // read from initialisation 
  } 
} 
 
pred code_IRIW [ dom : set Action, hb, sb, mo, rf : Action -> Action ] { 
  some disj wx, wy : Write | 
  some disj r1x, r2x, r1y, r2y : Read | { 
    dom = wx + wy + r1x + r2x + r1y + r2y 
    rf = ((wx -> r1x) + (wy -> r2y)) 
    ((r1x -> r1y) + (r2y -> r2x)) in sb
    one wx.loc + r1x.loc + r2x.loc 
    one wy.loc + r1y.loc + r2y.loc 
    no wx.loc & wy.loc 
  } 
} 

pred Sample_opt [ dom : set Action, sb : Action -> Action,
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
  }
}


