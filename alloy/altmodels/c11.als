module c11

// TODO define a function hb_display which derives a temporary 
// relation -- avoids junk in the model. 

// TODO find out how to hide transitive edges without making
// everything confusing 

// TODO set of accessed locations in Execution? 

abstract sig Loc {} 
// As we don't have RLX or SC, only care about NA vs Atomic
sig Atomic, NonAtomic extends Loc {} 

abstract sig Action { loc : Loc } 
sig Read, Write, RMW extends Action {} 

sig Execution { 
  act: set Action, 
  hb: Action -> Action, 
  rf: Action lone -> Action, 
  sb: Action -> Action,  // note, non-transitive sb 
  mo: Action -> Action, 

  // display relations 
  hb_d: Action -> Action, 
  mo_d: Action -> Action, 
} 

// Domain restriction, because doing this in the sig is broken in HO Alloy*
fact { all e : Execution | 
    e.(hb + rf + sb + mo) in (e.act -> e.act) 
} 

// Well-formedness
fact { 
  Execution.act = Action  // Every action belongs to some execution 
  Execution.act.loc = Loc // Every location is accessed in some execution

  no RMW.loc & NonAtomic
  
  Execution.rf in (Write + RMW) -> (Read + RMW) 
  Execution.mo in (Write + RMW) -> (Write + RMW) 
} 

// Drop transitive edges 
fun detrans [r : (Action -> Action)] : (Action -> Action) { 
  { a,b : Action | 
     (a -> b) in r and no c : Action | (a -> c) + (c -> b) in r }
} 

// Display relations 
fact { 
 all e : Execution | 
  e.hb_d = detrans[e.hb]
 and 
  e.mo_d = detrans[e.mo]  
} 

// Pre-execution structure 
fact {
  all e : Execution | 
    e.sb = ^(e.sb) // transitively closed 
  and 
    no iden & ^(e.sb) // acyclic 
} 

pred HBacyc [ e : Execution ] {
  no iden & ^(e.hb) 
} 

pred RFwf [ e : Execution ] { 
  all r : (e.act & (Read+RMW)) | 
  { 
    (e.rf.r).loc in r.loc 
    // Note this obliges you to read from a non-init write if any 
    // is available 
    ( (some (e.hb + e.mo).r & ((Write+RMW) <: loc).(r.loc) ) 
          implies (some e.rf.r) ) 
  } 
} 

pred HBdef [ e : Execution ] {
  let aact = (e.act <: loc).Atomic | 
  let sw = e.rf & (aact -> aact) | 
  e.hb = ^(sw + e.sb)
} 

pred CoWR [ e : Execution ] {
  all r : e.act & (Read+RMW) | 
  all w1 : (e.rf).r | 
  // all w2 : (e.act & Write) - w1 | 
  not { (w1 -> r) in (e.mo).(e.hb + e.mo) } 
} 

pred MOwf [ e : Execution ] { 
   { e.mo = ^(e.mo) }    // transitive
  and 
   { no iden & (e.mo) }  // irreflexive 
  and                    // per-location total on atomics
   { all disj w1, w2 : ((Write + RMW)) | 
     (w1 -> w2) in (e.mo + ~(e.mo)) iff 
       (w1.loc = w2.loc) and w1 + w2 in (e.act <: loc.Atomic) } 
} 

pred HBvsMO [ e : Execution ] { 
  no e.hb & ~(e.mo) 
} 

// // Stronger version of this axiom: rule out cycles, not loops
// pred HBMOacyc [ e : Execution ] { 
//   no iden & ^(e.hb + e.mo) 
// } 

pred RFNonAtomic [ e : Execution ] { 
  let NA_reads = (e.act <: loc).NonAtomic & (Read+RMW) | 
  (e.rf) :> NA_reads in e.hb 
  // and 
  // all r : NA_reads | 
  //   let loc_writes = (e.act <: loc).(r.loc) & Write | 
  //   no (e.rf).r implies no (e.hb).r & loc_writes 
} 

pred DRF [ e : Execution ] { 
  all l : NonAtomic | 
  all disj w, a : (e.act <: loc).l | 
    (w in Write) implies 
    (w -> a) in (e.hb + ~(e.hb)) 
} 

pred valid [ e : Execution ] {
  HBacyc[e] 
  RFwf[e] 
  HBdef[e] 
  MOwf[e] 
  CoWR[e] 
  HBvsMO[e] 
  // HBMOacyc[e] 
  RFNonAtomic[e] 
} 

pred sequential [ e : Execution ] { 
  all disj a1, a2 : e.act | 
  a1 -> a2 in (^(e.sb) + ^(~(e.sb)))
} 

run { all e : Execution | valid[e] } 
  for 4 
  but exactly 1 Execution, exactly 2 RMW

// Executions with no non-atomics are automatically DRF 
check Atomic_DRF { all e : Execution | valid[e] implies DRF[e] }
  for 10
  but exactly 1 Execution, 0 NonAtomic 

check Sequential_DRF { all e : Execution | 
    valid[e] and sequential[e] implies DRF[e] } 
  for 8
  but exactly 1 Execution 

run Litmus_IRIW { all e : Execution | valid[e] and litm_IRIW[e] } 
  for 6 
  but exactly 1 Execution, 0 NonAtomic 

run Litmus_SB { all e : Execution | valid[e] and litm_SB[e] } 
  for 6 
  but exactly 1 Execution, 0 NonAtomic 


/*************************************************/ 
/* Litmus tests                                  */ 
/*************************************************/ 

// SB litmus test without initialisation
pred litm_SB [ e : Execution ] { 
  some disj wx, wy : Write |  
  some disj rx, ry : Read |  { 
    e.act = (wx + wy + rx + ry)
    (wx -> ry) + (wy -> rx) in e.sb // allow stronger sb  
    one wx.loc + rx.loc 
    one wy.loc + ry.loc 
    no wx.loc & wy.loc
    no e.rf // read from initialisation 
  } 
} 

// // SB litmus test with initialisation 
// pred litm_SB [ e : Execution ] { 
//   some disj ix, iy, wx, wy : Write |  
//   some disj rx, ry : Read |  { 
//     e.act = (ix + iy + wx + wy + rx + ry)
//     (ix -> iy) + (iy -> wx) + (iy -> wy) + (wx -> ry) + (wy -> rx) in e.sb
//     one ix.loc + wx.loc + rx.loc 
//     one iy.loc + wy.loc + ry.loc 
//     no ix.loc & iy.loc
//     e.rf = (ix -> rx) + (iy -> ry) 
//     e.act.loc in Atomic 
//   } 
// } 

pred litm_IRIW [ e : Execution ] { 
  some disj wx, wy : Write | 
  some disj r1x, r2x, r1y, r2y : Read | { 
    e.act = wx + wy + r1x + r2x + r1y + r2y 
    e.rf = ((wx -> r1x) + (wy -> r2y)) 
    ((r1x -> r1y) + (r2y -> r2x)) in e.sb
    one wx.loc + r1x.loc + r2x.loc 
    one wy.loc + r1y.loc + r2y.loc 
    no wx.loc & wy.loc 
  } 
} 

