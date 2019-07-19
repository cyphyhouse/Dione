module Types {

const N: nat
newtype V = i:nat | i <= N
type E = (V, V)
type Round = nat
}

module Agent {

import opened Types

datatype Conf = Conf(r: Round)
}

module SyncSem {

import opened Types
import Agent

datatype Conf = Conf(a: (V -> Agent.Conf), r: Round)

predicate initial(s: Conf)
{
    forall i: V :: s.a(i).r == 0
 && s.r == 0
}

predicate pre_AllSend(s: Conf)
{
    forall i: V :: s.a(i).r == s.r
}

function eff_AllSend(s: Conf): Conf
    requires pre_AllSend(s)
{
    s.(r := s.r + 1)
}

predicate pre_AllRecv(s: Conf)
{
    forall i: V :: s.a(i).r + 1 == s.r
}

function eff_AllRecv(s: Conf): Conf
    requires pre_AllRecv(s)
    ensures var s' := eff_AllRecv(s);
        forall i: V :: s'.a(i).r == s.r
     && s'.r == s.r
{
    s.(a := ((i: V) => Agent.Conf(s.r)))
}

predicate transition(s: Conf, s': Conf)
{
    (pre_AllSend(s) && s'==eff_AllSend(s))
 || (pre_AllRecv(s) && s'==eff_AllRecv(s))
}

}

module GSyncSem {

import opened Types
import Agent

datatype Status = Init | Sent | Rcvd

datatype Conf = Conf(a: (V -> Agent.Conf), user: (V, Round) -> Status)

predicate initial(s: Conf)
{
    forall i: V :: s.a(i).r == 0
     && forall r: Round :: s.user(i, r) == (if r == 0 then Rcvd else Init)
}

predicate rel_iSend(s: Conf, s': Conf)
{
    exists i: V ::
        // preconditions
        forall j : V :: s.user(j, s.a(i).r) == Rcvd
     && s.user(i, s.a(i).r + 1) == Init
        // effect
     && s' == s.(user := ((v: V, r: Round) => if v == i && r == s.a(i).r + 1 then Sent else s.user(v, r)))
}

predicate rel_iRecv(s: Conf, s': Conf)
{
    exists i: V ::
        // preconditions
        forall j: V :: s.user(j, s.a(i).r + 1) != Init // >= Sent
     && s.user(i, s.a(i).r + 1) != Rcvd
        // effect
     && s' == s.(
            a := (v: V) => if v == i then Agent.Conf(s.a(i).r + 1) else s.a(v),
            user := ((v: V, r: Round) => if v == i && r == s.a(i).r + 1 then Rcvd else s.user(v, r)))
}

predicate transition(s: Conf, s': Conf)
{
    rel_iSend(s, s')
 || rel_iRecv(s, s')
}

}


module BisimProof {

import SyncSem
import GSyncSem

predicate bisim(ss: SyncSem.Conf, gs: GSyncSem.Conf)
{
    false
}

}
