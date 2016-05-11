// Relational version of history

module histRelat
open c11Relat 

pred preexecWF [ dom : set Action, 
                 kind : Action -> Kind,
                 gloc : Action -> Glob,  
                 lloc1, lloc2 : Action -> Thr, 
                 sb : Action -> Action ] { 
  SBwf[dom, kind, sb] 
  locWF[dom, kind, gloc, lloc1, lloc2] 

  lloc1 in Intern -> Thr 
  lloc2 in Intern -> Thr

  // Assumptions don't turn up in the environment 
  no kind.AssmEq & Extern 

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


