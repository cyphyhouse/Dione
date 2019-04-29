module Types {
datatype Action = trans(i: int)
function max(a: nat, b: nat, c: nat): nat
{ var tmp := if a >= b then a else b; if tmp >= c then tmp else c }

lemma same_value_proof?<T>(arr: seq<T>)
    requires forall i |(1<=i<|arr|) :: arr[i]==arr[i-1]
    ensures  forall i, j | (0<=i<|arr| && 0<=j<|arr|) :: arr[i]==arr[j]
{
    if |arr| <= 2
    { /* Base cases are proven by Dafny */ }
    else // |arr| > 2
    {
        assert arr[0] == arr[1];
        same_value_proof?(arr[1..]);
    }
}

lemma singleton_proof?<T>(x: set<T>, i: T)
   requires i in x
   ensures x - {i} == {} <==> |x - {i}| == 0
   ensures x - {i} == {} <==> |x| == 1
   ensures|x - {i}|== 0  <==> |x| == 1
{}
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
{
( |s.x| ==para.N)&&
(forall i::((0<=i<para.N) ==> (s.x[i]<=para.K)))&&
(var has_token := set i | 0<=i<para.N &&
    ((i==0 && s.x[i] == s.x[para.N-1]) || (i!=0 && s.x[i] != s.x[i-1]));
|has_token| == 1)
}

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
{
( |s.x| ==para.N)&&
(forall i::((0<=i<para.N) ==> (s.x[i]<=para.K)))&& 
(var has_token := set i | 0<=i<para.N &&
    ((i==0 && s.x[i] == s.x[para.N-1]) || (i!=0 && s.x[i] != s.x[i-1]));
|has_token| == 1)
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
{
    var s0_has_token := set i | 0<=i<para.N &&
        ((i==0 && s0.x[i] == s0.x[para.N-1]) || (i!=0 && s0.x[i] != s0.x[i-1]));
    assert a1.i in s0_has_token;
    singleton_proof?(s0_has_token, a1.i);
    assert s0_has_token == {a1.i};
    // Convert empty set to UNSAT constraint
    if i :| i!=a1.i && 0<=i<para.N &&
        ((i==0 && s0.x[i] == s0.x[para.N-1]) || (i!=0 && s0.x[i] != s0.x[i-1]))
    {
        assert i!=a1.i && i in s0_has_token; // Prove i does not exist
    }
    assert !(exists i :: i!=a1.i && 0<=i<para.N &&
        ((i==0 && s0.x[i] == s0.x[para.N-1]) || (i!=0 && s0.x[i] != s0.x[i-1])));

    var s1_has_token := set i | 0<=i<para.N &&
        ((i==0 && s1.x[i] == s1.x[para.N-1]) || (i!=0 && s1.x[i] != s1.x[i-1]));
    if a1.i == para.N - 1
    {
        same_value_proof?(s1.x);
        assert s1_has_token == {0};
    }
    else
    {
        // same_value_proof?(s1.x[0..(a1.i+1)]);
        // same_value_proof?(s1.x[(a1.i+1)..para.N]);
        // assert s1.x[a1.i] != s1.x[a1.i + 1];
        assert s1_has_token == {a1.i + 1};
    }
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

