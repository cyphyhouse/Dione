module Types {
newtype Status = n: int | 0<=n<4
function incre(n: Status): Status
{ if n==3 then 0 else n+1 }
function decre(n: Status): Status
{ if n==0 then 3 else n-1 }


datatype Action = trans(i: int)
function max(a: nat, b: nat, c: nat): nat
{ var tmp := if a >= b then a else b; if tmp >= c then tmp else c }

}
/* Mutual Exclusion on a bi-directional array */
module StableArray {
import opened Types
datatype Parameter = Parameter(N: int)
predicate automaton_where(para: Parameter)
{ (2<=para.N) }

predicate input(act: Action, para: Parameter)
{ false }
predicate output(act: Action, para: Parameter)
{ false||(act.trans?&&(0<=act.i<para.N)) }
predicate internal(act: Action, para: Parameter)
{ false }

datatype State = State(s: seq<Status>)
predicate initially(s: State, para: Parameter)
{ (( |s.s| ==para.N)&&((s.s[0]==1)||(s.s[0]==3))&&((s.s[(para.N-1)]==0)||(s.s[(para.N-1)]==2))) }

predicate pre'1_trans(s: State, act: Action, para: Parameter)
{ act.trans?&&output(act, para)&&(((act.i==0)&&(s.s[(act.i+1)]==incre(s.s[act.i])))||((act.i==(para.N-1))&&(s.s[(act.i-1)]==incre(s.s[act.i])))) }

function eff'1_trans(s: State, act: Action, para: Parameter): State
  requires pre'1_trans(s, act, para) {
var s: State := s.(s:=s.s[act.i := incre(incre(s.s[act.i]))]); s
}

predicate pre'2_trans(s: State, act: Action, para: Parameter)
{ act.trans?&&output(act, para)&&((0<act.i<(para.N-1))&&(s.s[(act.i-1)]==incre(s.s[act.i]))) }

function eff'2_trans(s: State, act: Action, para: Parameter): State
  requires pre'2_trans(s, act, para) {
var s: State := s.(s:=s.s[act.i := s.s[(act.i-1)]]); s
}

predicate pre'3_trans(s: State, act: Action, para: Parameter)
{ act.trans?&&output(act, para)&&((0<act.i<(para.N-1))&&(s.s[(act.i+1)]==incre(s.s[act.i]))) }

function eff'3_trans(s: State, act: Action, para: Parameter): State
  requires pre'3_trans(s, act, para) {
var s: State := s.(s:=s.s[act.i := s.s[(act.i+1)]]); s
}

predicate transitions(s: State, act: Action, s': State, para: Parameter) {
(pre'1_trans(s, act, para) && eff'1_trans(s, act, para)== s')||
(pre'2_trans(s, act, para) && eff'2_trans(s, act, para)== s')||
(pre'3_trans(s, act, para) && eff'3_trans(s, act, para)== s')
}

predicate invariant_of(s: State, para: Parameter)
{ (( |s.s| ==para.N)&&((s.s[0]==1)||(s.s[0]==3))&&((s.s[(para.N-1)]==0)||(s.s[(para.N-1)]==2))) }
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

