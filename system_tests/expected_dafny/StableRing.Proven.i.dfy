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

lemma singleton_proof?<T>(s: set<T>, i: T)
   requires i in s
   ensures s - {i} == {} <==> |s - {i}| == 0
   ensures s - {i} == {} <==> |s| == 1
   ensures|s - {i}|== 0  <==> |s| == 1
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

datatype State = State(s: seq<int>)
predicate initially(s: State, para: Parameter)
{
( |s.s| ==para.N)&&
(forall i::((0<=i<para.N) ==> (0<=s.s[i]<para.K)))&&
(var has_token := set i | 0<=i<para.N &&
    ((i==0 && s.s[i] == s.s[para.N-1]) || (i!=0 && s.s[i] != s.s[i-1]));
|has_token| == 1)
}

predicate pre'0_trans(s: State, act: Action, para: Parameter)
{ act.trans?&&output(act, para)&&((act.i==0)&&(s.s[act.i]==s.s[(para.N-1)])) }

function eff'0_trans(s: State, act: Action, para: Parameter): State
  requires pre'0_trans(s, act, para) {
var s: State := s.(s:=s.s[act.i := ((s.s[(para.N-1)]+1)%para.K)]); s
}

predicate pre'1_trans(s: State, act: Action, para: Parameter)
{ act.trans?&&output(act, para)&&((act.i!=0)&&(s.s[act.i]!=s.s[(act.i-1)])) }

function eff'1_trans(s: State, act: Action, para: Parameter): State
  requires pre'1_trans(s, act, para) {
var s: State := s.(s:=s.s[act.i := s.s[(act.i-1)]]); s
}

predicate transitions(s: State, act: Action, s': State, para: Parameter) {
(pre'0_trans(s, act, para) && eff'0_trans(s, act, para)== s')||
(pre'1_trans(s, act, para) && eff'1_trans(s, act, para)== s')
}

predicate invariant_of(s: State, para: Parameter)
{
( |s.s| ==para.N)&&
(forall i::((0<=i<para.N) ==> (0<=s.s[i]<para.K)))&&
(var has_token := set i | 0<=i<para.N &&
    ((i==0 && s.s[i] == s.s[para.N-1]) || (i!=0 && s.s[i] != s.s[i-1]));
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
//ensures invariant_of(s1, para)
{
    var s0_has_token := set i | 0<=i<para.N &&
        ((i==0 && s0.s[i] == s0.s[para.N-1]) || (i!=0 && s0.s[i] != s0.s[i-1]));
    assert a1.i in s0_has_token;
    singleton_proof?(s0_has_token, a1.i);
    assert s0_has_token == {a1.i};
    // Convert empty set to UNSAT constraint
    if i :| i!=a1.i && 0<=i<para.N &&
        ((i==0 && s0.s[i] == s0.s[para.N-1]) || (i!=0 && s0.s[i] != s0.s[i-1]))
    {
        assert i!=a1.i && i in s0_has_token; // Prove i does not exist
    }
    assert !(exists i :: i!=a1.i && 0<=i<para.N &&
        ((i==0 && s0.s[i] == s0.s[para.N-1]) || (i!=0 && s0.s[i] != s0.s[i-1])));

    var s1_has_token := set i | 0<=i<para.N &&
        ((i==0 && s1.s[i] == s1.s[para.N-1]) || (i!=0 && s1.s[i] != s1.s[i-1]));
    if a1.i == para.N - 1
    {
        same_value_proof?(s1.s);
        assert s1.s[0] == s1.s[para.N-1];
        assert s1_has_token == {0};
    }
    else
    {
        same_value_proof?(s1.s[0..(a1.i+1)]);
        same_value_proof?(s1.s[(a1.i+1)..para.N]);
        assert s1.s[a1.i] != s1.s[a1.i+1];
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

