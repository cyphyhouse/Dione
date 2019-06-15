=========
Semantics
=========


Program/Automaton Definition Semantics
--------------------------------------

Assuming a given network topology, G = (V, E) where V = {1, ..., n} and
E ⊆ V × V for simplicity.
We can easily treat V and E as data types.

Given a specific node ``i`` ∈ V, the automaton definition will be parsed into ``C_i``
with the message generation function ``msg_gen`` and the transition function ``trans``.

There should be standard rules to construct ``msg_gen`` and ``trans``,
but we skipped it for now.


Some issues not addressed:

+ Initial States
+ Automaton Parameters

.. code-block::

                 ... TODO ...
    ---------------------------------------- AutDef
    (AutDef, ⊥, ∅, 0) --> (., {C_i}, ∅, 0)

    C_i: MsgGen × Transition × State × ℕ
    C_i = (msg_gen, trans, s, r)

    type State = Var -> Val
    type MsgGen = State -> V -> Msg
    type Transition = State -> MsgsWSrc -> State
    type MsgsWSrc = Map[V, Msg]


Synchronous Network Semantics
-----------------------------

Synchronous semantics simply repeats the three rules, Send, Env, and Recv, in order.
The system is deterministic and will never stop.

.. code-block::

    ----------------------------------------- Init
    (., {C_i}, ∅) --> ("all send", {C_i}, ∅)


    tagged_msgs = { (i, dst, m) | m = C_i.msg_gen(C_i.s, dst) }
                                                      for all i
    ----------------------------------------------------------- Send
      ("all send", {C_i}, ∅) --> ("env", {C_i}, tagged_msgs)


        msgs' = drop/duplicate/fake msgs
    --------------------------------------------------- Env
    ("env", {C_i}, msgs) --> ("all recv", {C_i}, msgs')


      msgs_to_i = { src |-> m | (src, i, m) ∈ tagged_msgs },
         C_i'.s = C_i.trans(C_i.s, msgs_to_i),
         C_i'.r = C_i.r + 1
    ------------------------------------------------------------ Recv
    ("all recv", {C_i}, tagged_msgs) --> ("all send", {C_i'}, ∅)


Asynchronous Network with Synchronizer Semantics
------------------------------------------------

.. todo::
    Asynchronous semantics with Synchronizer

.. code-block::

    ------------------------------------- Init
    (., {C_i}, ∅) --> ("all send", {C_i}, ∅)



    ----------------------------------------
    ("all send", {C_i}, ∅) --> ()


    ----------------------------------------
    (recv, ) --> (send, tr.append("recv"))



Specifying Network Topology
---------------------------

We can also provide syntax for specifying network topology before automaton definition

.. code-block::

                 ... TODO...
    ---------------------------------------------- GraphDef
    (GraphDef AutDef, ., .) --> (AutDef, G, .)