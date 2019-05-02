module Types {
type Bit = bv1
newtype BitPos = n: int | (-1)<=n<11
function incre(n: BitPos): BitPos
{ if n==10 then (-1) else n+1 }
function decre(n: BitPos): BitPos
{ if n==(-1) then 10 else n-1 }


datatype NodeState = NodeState(arb: bv11, transmit: bool)

datatype Action = send(msgs: seq<Bit>) | recv(msg: Bit)
function max(a: nat, b: nat, c: nat): nat
{ var tmp := if a >= b then a else b; if tmp >= c then tmp else c }

}
/* CAN Bus arbitration protocol */
module Sys {
import opened Types
predicate automaton_where()
{ true }

import bus = Bus
import nseq = NodeSeq
datatype State = State(bus: bus.State, nseq: nseq.State)
predicate initially(s: State) {
bus.initially(s.bus)&&
nseq.initially(s.nseq)
}
predicate input(act: Action) {
(
bus.input(act)||
nseq.input(act)
)&& !output(act)
}
predicate output(act: Action) {
bus.output(act)||
nseq.output(act)
}
predicate internal(act: Action) {
bus.internal(act)||
nseq.internal(act)
}
lemma compatibility_proof?(act: Action)
ensures !(bus.output(act)&&nseq.output(act))
ensures !(bus.internal(act)&&nseq.signature(act))
ensures !(bus.signature(act)&&nseq.internal(act))

{  }
predicate transitions(s: State, act: Action, s': State) {
(if bus.signature(act) then bus.transitions(s.bus, act, s'.bus) else s'.bus==s.bus)&&
(if nseq.signature(act) then nseq.transitions(s.nseq, act, s'.nseq) else s'.nseq==s.nseq)
}

predicate invariant_of(s: State)
{ (( |s.nseq.nodes| >0)&&s.nseq.nodes[i_min(s.nseq.nodes)].transmit) }
lemma bmc_proof?(s0: State, s1: State, s2: State, s3: State, s4: State, s5: State, s6: State, s7: State, s8: State, s9: State, s10: State, s11: State, s12: State, s13: State, s14: State, s15: State, s16: State, s17: State, s18: State, s19: State, s20: State, s21: State, s22: State, s23: State, a1: Action, a2: Action, a3: Action, a4: Action, a5: Action, a6: Action, a7: Action, a8: Action, a9: Action, a10: Action, a11: Action, a12: Action, a13: Action, a14: Action, a15: Action, a16: Action, a17: Action, a18: Action, a19: Action, a20: Action, a21: Action, a22: Action, a23: Action)
requires initially(s0)
requires transitions(s0, a1, s1)
requires transitions(s1, a2, s2)
requires transitions(s2, a3, s3)
requires transitions(s3, a4, s4)
requires transitions(s4, a5, s5)
requires transitions(s5, a6, s6)
requires transitions(s6, a7, s7)
requires transitions(s7, a8, s8)
requires transitions(s8, a9, s9)
requires transitions(s9, a10, s10)
requires transitions(s10, a11, s11)
requires transitions(s11, a12, s12)
requires transitions(s12, a13, s13)
requires transitions(s13, a14, s14)
requires transitions(s14, a15, s15)
requires transitions(s15, a16, s16)
requires transitions(s16, a17, s17)
requires transitions(s17, a18, s18)
requires transitions(s18, a19, s19)
requires transitions(s19, a20, s20)
requires transitions(s20, a21, s21)
requires transitions(s21, a22, s22)
requires transitions(s22, a23, s23)
ensures invariant_of(s0)
ensures invariant_of(s1)
ensures invariant_of(s2)
ensures invariant_of(s3)
ensures invariant_of(s4)
ensures invariant_of(s5)
ensures invariant_of(s6)
ensures invariant_of(s7)
ensures invariant_of(s8)
ensures invariant_of(s9)
ensures invariant_of(s10)
ensures invariant_of(s11)
ensures invariant_of(s12)
ensures invariant_of(s13)
ensures invariant_of(s14)
ensures invariant_of(s15)
ensures invariant_of(s16)
ensures invariant_of(s17)
ensures invariant_of(s18)
ensures invariant_of(s19)
ensures invariant_of(s20)
ensures invariant_of(s21)
ensures invariant_of(s22)
ensures invariant_of(s23)
{  }
lemma induction_proof?(s0: State, s1: State, s2: State, s3: State, s4: State, s5: State, s6: State, s7: State, s8: State, s9: State, s10: State, s11: State, s12: State, s13: State, s14: State, s15: State, s16: State, s17: State, s18: State, s19: State, s20: State, s21: State, s22: State, s23: State, s24: State, a1: Action, a2: Action, a3: Action, a4: Action, a5: Action, a6: Action, a7: Action, a8: Action, a9: Action, a10: Action, a11: Action, a12: Action, a13: Action, a14: Action, a15: Action, a16: Action, a17: Action, a18: Action, a19: Action, a20: Action, a21: Action, a22: Action, a23: Action, a24: Action)
requires invariant_of(s0)
requires transitions(s0, a1, s1)
requires invariant_of(s1)
requires transitions(s1, a2, s2)
requires invariant_of(s2)
requires transitions(s2, a3, s3)
requires invariant_of(s3)
requires transitions(s3, a4, s4)
requires invariant_of(s4)
requires transitions(s4, a5, s5)
requires invariant_of(s5)
requires transitions(s5, a6, s6)
requires invariant_of(s6)
requires transitions(s6, a7, s7)
requires invariant_of(s7)
requires transitions(s7, a8, s8)
requires invariant_of(s8)
requires transitions(s8, a9, s9)
requires invariant_of(s9)
requires transitions(s9, a10, s10)
requires invariant_of(s10)
requires transitions(s10, a11, s11)
requires invariant_of(s11)
requires transitions(s11, a12, s12)
requires invariant_of(s12)
requires transitions(s12, a13, s13)
requires invariant_of(s13)
requires transitions(s13, a14, s14)
requires invariant_of(s14)
requires transitions(s14, a15, s15)
requires invariant_of(s15)
requires transitions(s15, a16, s16)
requires invariant_of(s16)
requires transitions(s16, a17, s17)
requires invariant_of(s17)
requires transitions(s17, a18, s18)
requires invariant_of(s18)
requires transitions(s18, a19, s19)
requires invariant_of(s19)
requires transitions(s19, a20, s20)
requires invariant_of(s20)
requires transitions(s20, a21, s21)
requires invariant_of(s21)
requires transitions(s21, a22, s22)
requires invariant_of(s22)
requires transitions(s22, a23, s23)
requires invariant_of(s23)
requires transitions(s23, a24, s24)
ensures invariant_of(s24)
{  }

lemma disjoint_actions_proof?(act: Action)
ensures !(input(act)&&internal(act))
ensures !(input(act)&&output(act))
ensures !(internal(act)&&output(act))
{  }

predicate signature(act: Action)
{ input(act)||output(act)||internal(act) }

}

module Bus {
import opened Types
predicate automaton_where()
{ true }

predicate input(act: Action)
{ false||(act.send?) }
predicate output(act: Action)
{ false||(act.recv?) }
predicate internal(act: Action)
{ false }

datatype State = State(bus: Bit)
predicate initially(s: State)
{ true }

predicate pre'2_send(s: State, act: Action)
{ act.send?&&input(act) }

function eff'2_send(s: State, act: Action): State
  requires pre'2_send(s, act) {
var s: State := if (forall i::((0<=i< |act.msgs| ) ==> (act.msgs[i]==1)))
then var s: State := s.(bus := 1); s
else var s: State := s.(bus := 0); s; s
}

predicate pre'3_recv(s: State, act: Action)
{ act.recv?&&output(act)&&(act.msg==s.bus) }

function eff'3_recv(s: State, act: Action): State
  requires pre'3_recv(s, act) {
var s: State := s; s
}

predicate transitions(s: State, act: Action, s': State) {
(pre'2_send(s, act) && eff'2_send(s, act)== s')||
(pre'3_recv(s, act) && eff'3_recv(s, act)== s')
}

lemma disjoint_actions_proof?(act: Action)
ensures !(input(act)&&internal(act))
ensures !(input(act)&&output(act))
ensures !(internal(act)&&output(act))
{  }

predicate signature(act: Action)
{ input(act)||output(act)||internal(act) }

}

module NodeSeq {
import opened Types
predicate automaton_where()
{ true }

predicate input(act: Action)
{ false||(act.recv?) }
predicate output(act: Action)
{ false||(act.send?) }
predicate internal(act: Action)
{ false }

datatype State = State(pos: BitPos, nodes: seq<NodeState>)
predicate initially(s: State)
{ ((s.pos==10)&&( |s.nodes| >0)&&(forall i::((0<=i< |s.nodes| ) ==> s.nodes[i].transmit))) }

predicate pre'4_send(s: State, act: Action)
{ act.send?&&output(act)&&(( |act.msgs| == |s.nodes| )&&(forall i::((0<=i< |s.nodes| ) ==> (act.msgs[i]==(if s.nodes[i].transmit then bv_extract(s.nodes[i].arb, s.pos) else 1))))) }

function eff'4_send(s: State, act: Action): State
  requires pre'4_send(s, act) {
var s: State := s; s
}

predicate pre'5_recv(s: State, act: Action)
{ act.recv?&&input(act) }

function eff'5_recv(s: State, act: Action): State
  requires pre'5_recv(s, act) {
var s: State := if (s.pos>=0)
then var s: State := s.(nodes := applyMapSeq(map n | n in s.nodes :: (if (n.transmit&&(act.msg!=bv_extract(n.arb, s.pos))) then NodeState(n.arb, false) else n), s.nodes));
var s: State := s.(pos := (s.pos-1)); s
else  s; s
}

predicate transitions(s: State, act: Action, s': State) {
(pre'4_send(s, act) && eff'4_send(s, act)== s')||
(pre'5_recv(s, act) && eff'5_recv(s, act)== s')
}

lemma disjoint_actions_proof?(act: Action)
ensures !(input(act)&&internal(act))
ensures !(input(act)&&output(act))
ensures !(internal(act)&&output(act))
{  }

predicate signature(act: Action)
{ input(act)||output(act)||internal(act) }

}

