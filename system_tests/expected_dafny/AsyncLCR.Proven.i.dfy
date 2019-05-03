module Types {
newtype Index = n: int | 0<=n<3
function incre(n: Index): Index
{ if n==2 then 0 else n+1 }
function decre(n: Index): Index
{ if n==0 then 2 else n-1 }

predicate between(lower: Index, i: Index, upper: Index)
    requires lower != i
    requires lower != upper
{
    if lower < upper then
        (lower < i <= upper)
    else
        (i > lower || i <= upper)
}


type UID = nat
datatype Status = UNKNOWN | CHOSEN | REPORTED

datatype Action = send_recv(src: Index, dst: Index, v: UID) | leader(id: Index)
function max(a: nat, b: nat, c: nat): nat
{ var tmp := if a >= b then a else b; if tmp >= c then tmp else c }

function i_max(u0: UID, u1: UID, u2: UID): Index
{
    if u0 == max(u0, u1, u2) then 0
    else if u1 == max(u0, u1, u2) then 1
    else assert u2 == max(u0, u1, u2); 2
}
}
module Sys {
import opened Types
datatype Parameter = Parameter(u0: UID, u1: UID, u2: UID)
predicate automaton_where(para: Parameter)
{ ((para.u0!=para.u1)&&(para.u1!=para.u2)&&(para.u2!=para.u0)) }

import P0 = AsyncLCR
import P1 = AsyncLCR
import P2 = AsyncLCR
datatype State = State(P0: P0.State, P1: P1.State, P2: P2.State)
predicate initially(s: State, para: Parameter) {
P0.initially(s.P0, P0.Parameter(0, para.u0))&&
P1.initially(s.P1, P1.Parameter(1, para.u1))&&
P2.initially(s.P2, P2.Parameter(2, para.u2))
}
predicate input(act: Action, para: Parameter) {
(
P0.input(act, P0.Parameter(0, para.u0))||
P1.input(act, P1.Parameter(1, para.u1))||
P2.input(act, P2.Parameter(2, para.u2))
)&& !output(act, para)
}
predicate output(act: Action, para: Parameter) {
P0.output(act, P0.Parameter(0, para.u0))||
P1.output(act, P1.Parameter(1, para.u1))||
P2.output(act, P2.Parameter(2, para.u2))
}
predicate internal(act: Action, para: Parameter) {
P0.internal(act, P0.Parameter(0, para.u0))||
P1.internal(act, P1.Parameter(1, para.u1))||
P2.internal(act, P2.Parameter(2, para.u2))
}
lemma compatibility_proof?(act: Action, para: Parameter)
requires automaton_where(para)
ensures !(P0.output(act, P0.Parameter(0, para.u0))&&P1.output(act, P1.Parameter(1, para.u1)))
ensures !(P0.internal(act, P0.Parameter(0, para.u0))&&P1.signature(act, P1.Parameter(1, para.u1)))
ensures !(P0.signature(act, P0.Parameter(0, para.u0))&&P1.internal(act, P1.Parameter(1, para.u1)))
ensures !(P0.output(act, P0.Parameter(0, para.u0))&&P2.output(act, P2.Parameter(2, para.u2)))
ensures !(P0.internal(act, P0.Parameter(0, para.u0))&&P2.signature(act, P2.Parameter(2, para.u2)))
ensures !(P0.signature(act, P0.Parameter(0, para.u0))&&P2.internal(act, P2.Parameter(2, para.u2)))
ensures !(P1.output(act, P1.Parameter(1, para.u1))&&P2.output(act, P2.Parameter(2, para.u2)))
ensures !(P1.internal(act, P1.Parameter(1, para.u1))&&P2.signature(act, P2.Parameter(2, para.u2)))
ensures !(P1.signature(act, P1.Parameter(1, para.u1))&&P2.internal(act, P2.Parameter(2, para.u2)))

{  }
predicate transitions(s: State, act: Action, s': State, para: Parameter) {
(if P0.signature(act, P0.Parameter(0, para.u0)) then P0.transitions(s.P0, act, s'.P0, P0.Parameter(0, para.u0)) else s'.P0==s.P0)&&
(if P1.signature(act, P1.Parameter(1, para.u1)) then P1.transitions(s.P1, act, s'.P1, P1.Parameter(1, para.u1)) else s'.P1==s.P1)&&
(if P2.signature(act, P2.Parameter(2, para.u2)) then P2.transitions(s.P2, act, s'.P2, P2.Parameter(2, para.u2)) else s'.P2==s.P2)
}

predicate invariant_of(s: State, para: Parameter)
{
((para.u0!=max(para.u0, para.u1, para.u2)) ==> (s.P0.status==UNKNOWN))&&
((para.u1!=max(para.u0, para.u1, para.u2)) ==> (s.P1.status==UNKNOWN))&&
((para.u2!=max(para.u0, para.u1, para.u2)) ==> (s.P2.status==UNKNOWN))&&
((0 != i_max(para.u0, para.u1, para.u2) && between(0, i_max(para.u0, para.u1, para.u2), 1)) ==> para.u0 !in s.P1.q)&&
((0 != i_max(para.u0, para.u1, para.u2) && between(0, i_max(para.u0, para.u1, para.u2), 2)) ==> para.u0 !in s.P2.q)&&
((1 != i_max(para.u0, para.u1, para.u2) && between(1, i_max(para.u0, para.u1, para.u2), 0)) ==> para.u1 !in s.P0.q)&&
((1 != i_max(para.u0, para.u1, para.u2) && between(1, i_max(para.u0, para.u1, para.u2), 2)) ==> para.u1 !in s.P2.q)&&
((2 != i_max(para.u0, para.u1, para.u2) && between(2, i_max(para.u0, para.u1, para.u2), 0)) ==> para.u2 !in s.P0.q)&&
((2 != i_max(para.u0, para.u1, para.u2) && between(2, i_max(para.u0, para.u1, para.u2), 1)) ==> para.u2 !in s.P1.q)
}
lemma bmc_proof?(s0: State, para: Parameter)
requires automaton_where(para)
requires initially(s0, para)
ensures invariant_of(s0, para)
{  }
lemma induction_proof?(s0: State, s1: State, a1: Action, para: Parameter)
requires automaton_where(para)
requires invariant_of(s0, para)
requires transitions(s0, a1, s1, para)
ensures invariant_of(s1, para)
{  }

lemma disjoint_actions_proof?(act: Action, para: Parameter)
requires automaton_where(para)
ensures !(input(act, para)&&internal(act, para))
ensures !(input(act, para)&&output(act, para))
ensures !(internal(act, para)&&output(act, para))
{  }

predicate signature(act: Action, para: Parameter)
{ input(act, para)||output(act, para)||internal(act, para) }

}

module AsyncLCR {
import opened Types
datatype Parameter = Parameter(i: Index, u: UID)
predicate automaton_where(para: Parameter)
{ true }

predicate input(act: Action, para: Parameter)
{ false||(act.send_recv?&&((act.src==decre(para.i))&&(act.dst==para.i))) }
predicate output(act: Action, para: Parameter)
{ false||(act.send_recv?&&((act.src==para.i)&&(act.dst==incre(para.i))))||(act.leader?&&(act.id==para.i)) }
predicate internal(act: Action, para: Parameter)
{ false }

datatype State = State(q: seq<UID>, status: Status)
predicate initially(s: State, para: Parameter)
{ ((s.q==[para.u])&&(s.status==UNKNOWN)) }

predicate pre'2_send_recv(s: State, act: Action, para: Parameter)
{ act.send_recv?&&output(act, para)&&((s.q!=[])&&(act.v==s.q[0])) }

function eff'2_send_recv(s: State, act: Action, para: Parameter): State
  requires pre'2_send_recv(s, act, para) {
var s: State := s.(q := s.q[1..]); s
}

predicate pre'3_send_recv(s: State, act: Action, para: Parameter)
{ act.send_recv?&&input(act, para) }

function eff'3_send_recv(s: State, act: Action, para: Parameter): State
  requires pre'3_send_recv(s, act, para) {
var s: State := if (act.v>para.u)
then var s: State := s.(q := (s.q+[act.v])); s
else var s: State := if (act.v==para.u)
then var s: State := s.(status := CHOSEN); s
else  s; s; s
}

predicate pre'4_leader(s: State, act: Action, para: Parameter)
{ act.leader?&&output(act, para)&&(s.status==CHOSEN) }

function eff'4_leader(s: State, act: Action, para: Parameter): State
  requires pre'4_leader(s, act, para) {
var s: State := s.(status := REPORTED); s
}

predicate transitions(s: State, act: Action, s': State, para: Parameter) {
(pre'2_send_recv(s, act, para) && eff'2_send_recv(s, act, para)== s')||
(pre'3_send_recv(s, act, para) && eff'3_send_recv(s, act, para)== s')||
(pre'4_leader(s, act, para) && eff'4_leader(s, act, para)== s')
}

lemma disjoint_actions_proof?(act: Action, para: Parameter)
requires automaton_where(para)
ensures !(input(act, para)&&internal(act, para))
ensures !(input(act, para)&&output(act, para))
ensures !(internal(act, para)&&output(act, para))
{  }

predicate signature(act: Action, para: Parameter)
{ input(act, para)||output(act, para)||internal(act, para) }

}

