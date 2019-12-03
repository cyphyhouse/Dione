module Types {
datatype MachineStatus = M_IDLE | M_WORK | M_DONE | M_BAD

datatype SharedStatus = READY | BUSY | DONE

datatype Action = m_done(i: nat) | drop(i: nat) | pick(i: nat) | m_selfloop(i: nat)
function max(a: nat, b: nat, c: nat): nat
{ var tmp := if a >= b then a else b; if tmp >= c then tmp else c }

}
module system {
import opened Types
import Robot = robot
import M0 = machine
import M1 = machine
import M2 = machine
datatype State = State(Robot: Robot.State, M0: M0.State, M1: M1.State, M2: M2.State)
predicate initially(s: State) {
Robot.initially(s.Robot)&&
M0.initially(s.M0, M0.Parameter(0))&&
M1.initially(s.M1, M1.Parameter(1))&&
M2.initially(s.M2, M2.Parameter(2))
}
predicate input(act: Action) {
(
Robot.input(act)||
M0.input(act, M0.Parameter(0))||
M1.input(act, M1.Parameter(1))||
M2.input(act, M2.Parameter(2))
)&& !output(act)
}
predicate output(act: Action) {
Robot.output(act)||
M0.output(act, M0.Parameter(0))||
M1.output(act, M1.Parameter(1))||
M2.output(act, M2.Parameter(2))
}
predicate internal(act: Action) {
Robot.internal(act)||
M0.internal(act, M0.Parameter(0))||
M1.internal(act, M1.Parameter(1))||
M2.internal(act, M2.Parameter(2))
}
lemma compatibility_proof?(act: Action)
ensures !(Robot.output(act)&&M0.output(act, M0.Parameter(0)))
ensures !(Robot.internal(act)&&M0.signature(act, M0.Parameter(0)))
ensures !(Robot.signature(act)&&M0.internal(act, M0.Parameter(0)))
ensures !(Robot.output(act)&&M1.output(act, M1.Parameter(1)))
ensures !(Robot.internal(act)&&M1.signature(act, M1.Parameter(1)))
ensures !(Robot.signature(act)&&M1.internal(act, M1.Parameter(1)))
ensures !(Robot.output(act)&&M2.output(act, M2.Parameter(2)))
ensures !(Robot.internal(act)&&M2.signature(act, M2.Parameter(2)))
ensures !(Robot.signature(act)&&M2.internal(act, M2.Parameter(2)))
ensures !(M0.output(act, M0.Parameter(0))&&M1.output(act, M1.Parameter(1)))
ensures !(M0.internal(act, M0.Parameter(0))&&M1.signature(act, M1.Parameter(1)))
ensures !(M0.signature(act, M0.Parameter(0))&&M1.internal(act, M1.Parameter(1)))
ensures !(M0.output(act, M0.Parameter(0))&&M2.output(act, M2.Parameter(2)))
ensures !(M0.internal(act, M0.Parameter(0))&&M2.signature(act, M2.Parameter(2)))
ensures !(M0.signature(act, M0.Parameter(0))&&M2.internal(act, M2.Parameter(2)))
ensures !(M1.output(act, M1.Parameter(1))&&M2.output(act, M2.Parameter(2)))
ensures !(M1.internal(act, M1.Parameter(1))&&M2.signature(act, M2.Parameter(2)))
ensures !(M1.signature(act, M1.Parameter(1))&&M2.internal(act, M2.Parameter(2)))

{  }
predicate transitions(s: State, act: Action, s': State) {
(if Robot.signature(act) then Robot.transitions(s.Robot, act, s'.Robot) else s'.Robot==s.Robot)&&
(if M0.signature(act, M0.Parameter(0)) then M0.transitions(s.M0, act, s'.M0, M0.Parameter(0)) else s'.M0==s.M0)&&
(if M1.signature(act, M1.Parameter(1)) then M1.transitions(s.M1, act, s'.M1, M1.Parameter(1)) else s'.M1==s.M1)&&
(if M2.signature(act, M2.Parameter(2)) then M2.transitions(s.M2, act, s'.M2, M2.Parameter(2)) else s'.M2==s.M2)
}

predicate invariant_of(s: State)
{ (((s.Robot.m0_status==READY) ==> (s.M0.status==M_IDLE))&&((s.Robot.m1_status==READY) ==> (s.M1.status==M_IDLE))&&((s.Robot.m2_status==READY) ==> (s.M2.status==M_IDLE))&&((s.Robot.m0_status==DONE) ==> (s.M0.status==M_DONE))&&((s.Robot.m1_status==DONE) ==> (s.M1.status==M_DONE))&&((s.Robot.m2_status==DONE) ==> (s.M2.status==M_DONE))&&(s.M0.status!=M_BAD)&&(s.M1.status!=M_BAD)&&(s.M2.status!=M_BAD)) }
lemma bmc_proof?(s0: State)
requires initially(s0)
ensures invariant_of(s0)
{  }
lemma induction_proof?(s0: State, s1: State, a1: Action)
requires invariant_of(s0)
requires transitions(s0, a1, s1)
ensures invariant_of(s1)
{  }

lemma disjoint_actions_proof?(act: Action)
ensures !(input(act)&&internal(act))
ensures !(input(act)&&output(act))
ensures !(internal(act)&&output(act))
{  }

predicate signature(act: Action)
{ input(act)||output(act)||internal(act) }

}

module robot {
import opened Types
predicate automaton_where()
{ true }

datatype State = State(m0_status: SharedStatus, m1_status: SharedStatus, m2_status: SharedStatus)
predicate initially(s: State)
{ ((s.m0_status==READY)&&(s.m1_status==READY)&&(s.m2_status==READY)) }

predicate input(act: Action)
{ false||(act.m_done?&&(0<=act.i<3)) }
predicate output(act: Action)
{ false||(act.drop?&&(0<=act.i<3))||(act.pick?&&(0<=act.i<3)) }
predicate internal(act: Action)
{ false }

predicate pre'2_m_done(s: State, act: Action)
{ act.m_done?&&input(act) }

function eff'2_m_done(s: State, act: Action): State
  requires pre'2_m_done(s, act) {
var s: State := if (act.i==0)
then var s: State := s.(m0_status := DONE); s
else  s;
var s: State := if (act.i==1)
then var s: State := s.(m1_status := DONE); s
else  s;
var s: State := if (act.i==2)
then var s: State := s.(m2_status := DONE); s
else  s; s
}

predicate pre'3_drop(s: State, act: Action)
{ act.drop?&&output(act)&&((act.i==0)&&(s.m0_status==READY)) }

function eff'3_drop(s: State, act: Action): State
  requires pre'3_drop(s, act) {
var s: State := s.(m0_status := BUSY); s
}

predicate pre'4_drop(s: State, act: Action)
{ act.drop?&&output(act)&&((act.i==1)&&(s.m1_status==READY)) }

function eff'4_drop(s: State, act: Action): State
  requires pre'4_drop(s, act) {
var s: State := s.(m1_status := BUSY); s
}

predicate pre'5_drop(s: State, act: Action)
{ act.drop?&&output(act)&&((act.i==2)&&(s.m2_status==READY)) }

function eff'5_drop(s: State, act: Action): State
  requires pre'5_drop(s, act) {
var s: State := s.(m2_status := BUSY); s
}

predicate pre'6_pick(s: State, act: Action)
{ act.pick?&&output(act)&&((act.i==0)&&(s.m0_status==DONE)) }

function eff'6_pick(s: State, act: Action): State
  requires pre'6_pick(s, act) {
var s: State := s.(m0_status := READY); s
}

predicate pre'7_pick(s: State, act: Action)
{ act.pick?&&output(act)&&((act.i==1)&&(s.m1_status==DONE)) }

function eff'7_pick(s: State, act: Action): State
  requires pre'7_pick(s, act) {
var s: State := s.(m1_status := READY); s
}

predicate pre'8_pick(s: State, act: Action)
{ act.pick?&&output(act)&&((act.i==2)&&(s.m2_status==DONE)) }

function eff'8_pick(s: State, act: Action): State
  requires pre'8_pick(s, act) {
var s: State := s.(m2_status := READY); s
}

predicate transitions(s: State, act: Action, s': State) {
(pre'2_m_done(s, act) && eff'2_m_done(s, act)== s')||
(pre'3_drop(s, act) && eff'3_drop(s, act)== s')||
(pre'4_drop(s, act) && eff'4_drop(s, act)== s')||
(pre'5_drop(s, act) && eff'5_drop(s, act)== s')||
(pre'6_pick(s, act) && eff'6_pick(s, act)== s')||
(pre'7_pick(s, act) && eff'7_pick(s, act)== s')||
(pre'8_pick(s, act) && eff'8_pick(s, act)== s')
}

lemma disjoint_actions_proof?(act: Action)
ensures !(input(act)&&internal(act))
ensures !(input(act)&&output(act))
ensures !(internal(act)&&output(act))
{  }

predicate signature(act: Action)
{ input(act)||output(act)||internal(act) }

}

module machine {
import opened Types
datatype Parameter = Parameter(machine_id: nat)
predicate automaton_where(para: Parameter)
{ true }

datatype State = State(status: MachineStatus)
predicate initially(s: State, para: Parameter)
{ (s.status==M_IDLE) }

predicate input(act: Action, para: Parameter)
{ false||(act.drop?&&(act.i==para.machine_id))||(act.pick?&&(act.i==para.machine_id)) }
predicate output(act: Action, para: Parameter)
{ false||(act.m_done?&&(act.i==para.machine_id)) }
predicate internal(act: Action, para: Parameter)
{ false||(act.m_selfloop?&&(act.i==para.machine_id)) }

predicate pre'9_m_selfloop(s: State, act: Action, para: Parameter)
{ act.m_selfloop?&&internal(act, para)&&true }

function eff'9_m_selfloop(s: State, act: Action, para: Parameter): State
  requires pre'9_m_selfloop(s, act, para) {
var s: State := s; s
}

predicate pre'10_m_done(s: State, act: Action, para: Parameter)
{ act.m_done?&&output(act, para)&&(s.status==M_WORK) }

function eff'10_m_done(s: State, act: Action, para: Parameter): State
  requires pre'10_m_done(s, act, para) {
var s: State := s.(status := M_DONE); s
}

predicate pre'11_drop(s: State, act: Action, para: Parameter)
{ act.drop?&&input(act, para) }

function eff'11_drop(s: State, act: Action, para: Parameter): State
  requires pre'11_drop(s, act, para) {
var s: State := if (s.status==M_IDLE)
then var s: State := s.(status := M_WORK); s
else var s: State := s.(status := M_BAD); s; s
}

predicate pre'12_pick(s: State, act: Action, para: Parameter)
{ act.pick?&&input(act, para) }

function eff'12_pick(s: State, act: Action, para: Parameter): State
  requires pre'12_pick(s, act, para) {
var s: State := if (s.status==M_DONE)
then var s: State := s.(status := M_IDLE); s
else var s: State := s.(status := M_BAD); s; s
}

predicate transitions(s: State, act: Action, s': State, para: Parameter) {
(pre'9_m_selfloop(s, act, para) && eff'9_m_selfloop(s, act, para)== s')||
(pre'10_m_done(s, act, para) && eff'10_m_done(s, act, para)== s')||
(pre'11_drop(s, act, para) && eff'11_drop(s, act, para)== s')||
(pre'12_pick(s, act, para) && eff'12_pick(s, act, para)== s')
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

