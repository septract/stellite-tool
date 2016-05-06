module hist 

open c11

// TODO: handling of call / return is a bit wonky 

sig Intern, Extern, Call, Ret in Action {} 
sig Glob, Thr in Loc {} 

fact { 
  disj[ Glob, Thr ] 
  Glob + Thr = Loc 

  disj[ Intern, Extern, Call, Ret ] 
  Intern + Extern + Call + Ret = Action 
 
  disj[ Call.loc, Ret.loc, (Intern+Extern).loc ]

  Call + Ret in RMW 
} 

pred ExecWF [ e : Execution ] { 
  // Call and return are unique in an execution
  one Call & e.act 
  one Ret & e.act 

  // External actions act on global locations 
  (e.act & Extern).loc in Glob 

  // External actions are unordered in sb  
  no (e.sb) & ((Extern -> Action) + (Action -> Extern)) 

  // Internal actions are totally ordered in sb 
  all disj a1, a2 : (e.act & Intern) | 
    a1 -> a2 in (^(e.sb) + ^(~(e.sb)))

  // Call / Return bracket internal actions
  all c : e.act & Call, r : e.act & Ret | { 
    (c -> r) in ^(e.sb) 
    all i : e.act | 
      i in Intern iff (c -> i) + (i -> r) in ^(e.sb) 
  } 
}

sig History { 
  interf : set (Call + Ret + Extern), 
  guar : Action -> Action, 
  deny : Action -> Action,  
} 

// Domain restriction
fact { all h : History | 
  h.(guar + deny) in (h.interf -> h.interf) 
} 

fun HBvsMO_d [ e : Execution ] : (Action -> Action) { 
  { u : (Extern + Ret), v : (Extern + Call) | 
    some disj w1, w2 : ((Write + RMW) & (e.act <: loc.Atomic)) | 
    { 
      (w2 -> w1) in e.mo
      (w1 -> u) + (v -> w2) in iden + e.hb
    } 
  } 
} 

fun CoWR_d [ e : Execution ] : (Action -> Action) { 
  { u : (Extern + Ret), v : (Extern + Call) | 
    disj [u,v] and 
    some disj w1, w2 : (Write + RMW) & (e.act <: loc.Atomic), 
               r : (Read + RMW) & (e.act <: loc.Atomic)   | 
    { 
      disj [w1, w2, r] 
      (w1 -> r) in e.rf 
      (w1 -> w2) in e.hb
      (w2 -> u) in iden + e.hb 
      (v -> r) in iden + e.hb 
    } 
  } 
} 

// Remove denies that arise just from another single edge.
pred no_trivial_denies[ e: Execution, h : History ]  { 
  no h.deny & ( (Call -> Ret) + ~(e.mo) + ~(e.hb) ) 
} 

pred histWF [ e : Execution, h : History ]  { 
  h.interf = e.act & (Extern + Call + Ret)  

  // Guarantee is a projection of Call -> Ret and external hb
  h.guar = (e.hb & 
      ((Extern -> Extern) + (Call -> Extern) +  (Extern -> Ret))) 
  
  // Deny is built from two kinds of shape 
  h.deny = CoWR_d[e] + HBvsMO_d[e]
} 

pred hist_eq[ h, h' : History] { 
  { 
    h.interf = h'.interf
    h.guar = h'.guar
    h.deny = h'.deny 
  } 
} 

// sig PreExec { 
//   pact : set Intern,  
//    psb : pact lone -> lone pact,  
// } 

fun allHist [ pact : set Intern, psb : pact -> pact, i : set Action ] 
        : set History { 
  { h : History | 
    some e : Execution | { 
      valid[e] // needs modified validity axiom with i 
      ExecWF[e] 
      histWF[e,h]
      ^psb in e.sb 
      pact = e.act & Intern
      i = e.act - Intern 
      #pact = 2
    } 
  } 
}

run gen_hist { all h : History | some pact : set Intern, psb : Action -> Action, i : Action | 
    h in allHist[pact, psb, i] 
    and
    // all a,b : pact | (a->b) in (^(psb) + ^(~psb)) 
    // and 
    #Intern = 2 
  } 
for 6 but exactly 1 History, exactly 1 Execution

run any_hist { all e : Execution | some h : History | 
     valid[e] and ExecWF[e] and histWF[e, h] and no_trivial_denies[e, h] 
     and #h.guar = 1 and #h.deny = 1 and #Intern = 2
  } 
  for 8 but exactly 1 Execution, exactly 1 History, 2 RMW 

run WW_hist { some e : Execution, h : History | {  
    valid[e]
    ExecWF[e]
    histWF[e, h]
    // no_trivial_denies[e, h]  

    // Code definition: 
    WW_code[e]
  }  
} for 8 but exactly 1 Execution, exactly 1 History

// Check that guarantee can't be cyclic. 
check acyc_guar { all e : Execution | some h : History | 
    valid[e] and ExecWF[e] and histWF[e, h] implies (no iden & ^(h.guar)) } 
  for 2 but exactly 1 Execution, exactly 1 History, 0 RMW, 7 Action



/*************************************************/ 
/* Code fragments                                */ 
/*************************************************/

pred WW_code [ e : Execution ] { 
  some disj w1, w2 : Write | { 
    (e.act & Intern) = w1 + w2
    (w1 -> w2) in e.sb
    one w1.loc + w2.loc 
    w1.loc in Atomic & Glob 
  } 
} 
