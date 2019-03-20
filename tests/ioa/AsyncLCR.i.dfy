module Types {

newtype UID = u: nat | (u == 0 || u == 1 || u == 2)

datatype Status = unknown | chosen | reported

datatype Action = from0to1(v: UID) | from1to2(v:UID) | from2to0(v:UID)
                | leader_0 | leader_1 | leader_2
}

module AsyncLCR_0 {

import opened Types

datatype State = State(q: seq<UID>, status: Status)

predicate Input(act: Action) {
    act.from2to0?
}

predicate Output(act: Action) {
    act.from0to1?
 || act.leader_0?
}

predicate Internal(act: Action) {
    false
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

predicate Initial(s: State) {
    s.q == [u0]
 && s.status == unknown
}

predicate pre_from0to1(act: Action, s: State) {
    Output(act) && act.from0to1?
 && s.q != [] && act.v == s.q[0]
}

function  eff_from0to1(act: Action, s: State): State
    requires pre_from0to1(act, s)
{
    var s: State := s.(q := s.q[1..]); s
}

predicate pre_from2to0(act: Action, s: State) {
    Input(act) && act.from2to0?
}

function  eff_from2to0(act: Action, s: State): State
    requires pre_from2to0(act, s)
{
    if act.v > u0 then
        var s: State := s.(q := s.q + [act.v]); s
    else if act.v == u0 then
        var s: State := s.(status := chosen); s
    else s
}

predicate pre_leader_0(act: Action, s: State) {
    Output(act) && act.leader_0?
 && s.status == chosen
}

function  eff_leader_0(act: Action, s: State): State
    requires pre_leader_0(act, s)
{
    var s: State := s.(status := reported); s
}

predicate Transition(s: State, act: Action, s': State) {
    (pre_from0to1(act, s) && s' == eff_from0to1(act, s))
 || (pre_from2to0(act, s) && s' == eff_from2to0(act, s))
 || (pre_leader_0(act, s) && s' == eff_leader_0(act, s))
}

lemma Input_Enabled(act: Action, s: State)
    requires Input(act)
    ensures  exists s': State :: Transition(s, act, s')
{
    var s': State :| Transition(s, act, s');
}

}

module AsyncLCR_1 {

import opened Types

datatype State = State(q: seq<UID>, status: Status)

predicate Input(act: Action) {
    act.from0to1?
}

predicate Output(act: Action) {
    act.from1to2?
 || act.leader_1?
}

predicate Internal(act: Action) {
    false
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

predicate Initial(s: State) {
    s.q == [u1]
 && s.status == unknown
}

predicate pre_from1to2(act: Action, s: State) {
    Output(act) && act.from1to2?
 && s.q != [] && act.v == s.q[0]
}

function  eff_from1to2(act: Action, s: State): State
    requires pre_from1to2(act, s)
{
    var s: State := s.(q := s.q[1..]); s
}

predicate pre_from0to1(act: Action, s: State) {
    Input(act) && act.from0to1?
}

function  eff_from0to1(act: Action, s: State): State
    requires pre_from0to1(act, s)
{
    if act.v > u1 then
        var s: State := s.(q := s.q + [act.v]); s
    else if act.v == u1 then
        var s: State := s.(status := chosen); s
    else s
}

predicate pre_leader_1(act: Action, s: State) {
    Output(act) && act.leader_1?
 && s.status == chosen
}

function  eff_leader_1(act: Action, s: State): State
    requires pre_leader_1(act, s)
{
    var s: State := s.(status := reported); s
}

predicate Transition(s: State, act: Action, s': State) {
    (pre_from1to2(act, s) && s' == eff_from1to2(act, s))
 || (pre_from0to1(act, s) && s' == eff_from0to1(act, s))
 || (pre_leader_1(act, s) && s' == eff_leader_1(act, s))
}

lemma Input_Enabled(act: Action, s: State)
    requires Input(act)
    ensures  exists s': State :: Transition(s, act, s')
{
    var s': State :| Transition(s, act, s');
}

}

module AsyncLCR_2 {

import opened Types

datatype State = State(q: seq<UID>, status: Status)

predicate Input(act: Action) {
    act.from1to2?
}

predicate Output(act: Action) {
    act.from2to0?
 || act.leader_2?
}

predicate Internal(act: Action) {
    false
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

predicate Initial(s: State) {
    s.q == [u2]
 && s.status == unknown
}

predicate pre_from2to0(act: Action, s: State) {
    Output(act) && act.from2to0?
 && s.q != [] && act.v == s.q[0]
}

function  eff_from2to0(act: Action, s: State): State
    requires pre_from2to0(act, s)
{
    var s: State := s.(q := s.q[1..]); s
}

predicate pre_from1to2(act: Action, s: State) {
    Input(act) && act.from1to2?
}

function  eff_from1to2(act: Action, s: State): State
    requires pre_from1to2(act, s)
{
    if act.v > u2 then
        var s: State := s.(q := s.q + [act.v]); s
    else if act.v == u2 then
        var s: State := s.(status := chosen); s
    else s
}

predicate pre_leader_2(act: Action, s: State) {
    Output(act) && act.leader_2?
 && s.status == chosen
}

function  eff_leader_2(act: Action, s: State): State
    requires pre_leader_2(act, s)
{
    var s: State := s.(status := reported); s
}

predicate Transition(s: State, act: Action, s': State) {
    (pre_from2to0(act, s) && s' == eff_from2to0(act, s))
 || (pre_from1to2(act, s) && s' == eff_from1to2(act, s))
 || (pre_leader_2(act, s) && s' == eff_leader_2(act, s))
}

lemma Input_Enabled(act: Action, s: State)
    requires Input(act)
    ensures  exists s': State :: Transition(s, act, s')
{
    var s': State :| Transition(s, act, s');
}

}
