include "AsyncLCR.i.dfy"

module AsyncLCR_composed {
import opened Types
import P0 = AsyncLCR_0
import P1 = AsyncLCR_1
import P2 = AsyncLCR_2

datatype State = State( p0: P0.State
                      , p1: P1.State
                      , p2: P2.State)

predicate Initial(s: State) {
    P0.Initial(s.p0)
 && P1.Initial(s.p1)
 && P2.Initial(s.p2)
}

predicate Output(act: Action) {
    P0.Output(act)
 || P1.Output(act)
 || P2.Output(act)
}

predicate Input(act: Action) {
   ( P0.Input(act)
  || P1.Input(act)
  || P2.Input(act))
 && !Output(act)
}

predicate Internal(act: Action) {
    P0.Internal(act)
 || P1.Internal(act)
 || P2.Internal(act)
}

lemma Action_Set_Disjoint(act: Action)
    ensures !(Output(act) && Input(act))
         && !(Output(act) && Internal(act))
         && !(Internal(act) && Input(act))
{}

predicate External(act: Action) {
    Input(act) || Output(act)
}

predicate Signature(act: Action) {
    External(act) || Internal(act)
}

lemma Compatibility(act: Action)
    ensures !(P0.Output(act) && P1.Output(act))
         && !(P0.Internal(act) && P1.Signature(act))
         && !(P0.Signature(act) && P1.Internal(act))
    ensures !(P1.Output(act) && P2.Output(act))
         && !(P1.Internal(act) && P2.Signature(act))
         && !(P1.Signature(act) && P2.Internal(act))
    ensures !(P2.Output(act) && P0.Output(act))
         && !(P2.Internal(act) && P0.Signature(act))
         && !(P2.Signature(act) && P0.Internal(act))
{}

predicate Transition(s: State, act: Action, s': State) {
    (if P0.Signature(act)
     then P0.Transition(s.p0, act, s'.p0)
     else s'.p0 == s.p0)
 && (if P1.Signature(act)
     then P1.Transition(s.p1, act, s'.p1)
     else s'.p1 == s.p1)
 && (if P2.Signature(act)
     then P2.Transition(s.p2, act, s'.p2)
     else s'.p2 == s.p2)
}

lemma Input_Enabled(act: Action, s: State)
    requires Input(act)
    ensures  exists s': State :: Transition(s, act, s')
{
    var s': State :| Transition(s, act, s');
}

}
