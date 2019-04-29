module Types {
datatype Action = trans(i: int)
function max(a: nat, b: nat, c: nat): nat
{ var tmp := if a >= b then a else b; if tmp >= c then tmp else c }

}
/* Dijkstra's self-stabilizing algorithm on a ring */
module StableRing {
import opened Types
datatype Parameter = Parameter(N: int, K: int)
predicate automaton_where(para: Parameter)
{ (1<para.N<para.K) }

predicate input(act: Action, para: Parameter)
{ false }
predicate output(act: Action, para: Parameter)
{ false||(act.trans?&&(0<=act.i<para.N)) }
predicate internal(act: Action, para: Parameter)
{ false }

datatype State = State(x: seq<int>)
predicate initially(s: State, para: Parameter)
{ (( |s.x| ==para.N)&&(forall i::((0<=i<para.N) ==> (s.x[i]<=para.K)))) }

predicate pre'0_trans(s: State, act: Action, para: Parameter)
{ act.trans?&&output(act, para)&&((act.i==0)&&(s.x[act.i]==s.x[(para.N-1)])) }

function eff'0_trans(s: State, act: Action, para: Parameter): State
  requires pre'0_trans(s, act, para) {
var s: State := s.(x:=s.x[act.i := ((s.x[(para.N-1)]+1)%para.K)]); s
}

predicate pre'1_trans(s: State, act: Action, para: Parameter)
{ act.trans?&&output(act, para)&&((act.i!=0)&&(s.x[act.i]!=s.x[(act.i-1)])) }

function eff'1_trans(s: State, act: Action, para: Parameter): State
  requires pre'1_trans(s, act, para) {
var s: State := s.(x:=s.x[act.i := s.x[(act.i-1)]]); s
}

predicate transitions(s: State, act: Action, s': State, para: Parameter) {
(pre'0_trans(s, act, para) && eff'0_trans(s, act, para)== s')||
(pre'1_trans(s, act, para) && eff'1_trans(s, act, para)== s')
}

predicate invariant_of(s: State, para: Parameter)
{ (( |s.x| ==para.N)&&(forall i::((0<=i<para.N) ==> (s.x[i]<=para.K)))) }
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

