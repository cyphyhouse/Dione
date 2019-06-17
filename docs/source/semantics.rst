=========
Semantics
=========


Program/Automaton Definition Semantics
--------------------------------------

Assuming a given network topology, G = (V, E) where V = {1, ..., n} and
E ⊆ V × V for simplicity.
We can easily treat V and E as data types.

Given a specific node ``i`` ∈ V, the automaton definition will be instantiated into
an agent configuration ``C_i``
with the message generation function ``msg_gen`` and the transition function ``trans``.
Also ``s`` should store the current state for the agent.
``r`` represents what the agent thinks the current round is.

There should be standard rules to construct ``msg_gen`` and ``trans``,
but we skipped it for now.

Some issues not addressed:

+ Initial States
+ Automaton Parameters

.. code-block::

                 ... TODO ...
    ---------------------------------------- AutDef
    (AutDef, ⊥, ∅) --> ("", {C_i}, ∅)

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

Notice that in ``AllRecv`` rule, ``msgs_to_i`` is computed and used in ``trans``
right away to avoid storing it in a local variable for each agent.
Another option is to store it locally so that we can cleanly separate receiving
and internal transition.

.. code-block::

    ----------------------------------------- Init
    ("", {C_i}, ∅) --> ("all send", {C_i}, ∅)


    tagged_msgs : Map[V × V, Msg]
    tagged_msgs = { (i, dst) -> m | m = C_i.msg_gen(C_i.s, dst) }
                                                      for all i
    ----------------------------------------------------------- AllSend
      ("all send", {C_i}, ∅) --> ("env", {C_i}, tagged_msgs)


        msgs' = drop/duplicate/fake msgs
    --------------------------------------------------- Env
    ("env", {C_i}, msgs) --> ("all recv", {C_i}, msgs')


      msgs_to_i = { src -> m | ((src, i) -> m) ∈ tagged_msgs },
         C_i'.s = C_i.trans(C_i.s, msgs_to_i),
         C_i'.r = C_i.r + 1
    ------------------------------------------------------------ AllRecv
    ("all recv", {C_i}, tagged_msgs) --> ("all send", {C_i'}, ∅)


Asynchronous Network Semantics
------------------------------

.. todo::

    How to allow both send and receive as the next action


.. code-block::

            m = C_i.msg_gen(C_i.s, dst)
    ------------------------------------------- Init
    ("", {C_i}, ∅) --> ("send i dst", {C_i}, ∅)


                       m = C_i.msg_gen(C_i.s, dst),
           msgs'[i, dst] = msgs[i, dst].append(m)
    ----------------------------------------------------- Send
    ("send i dst", {C_i}, msgs) --> ("env", {C_i}, msgs')


               msgs[src, i] is not empty,
    ----------------------------------------------------- Env
    ("env", {C_i}, msgs) --> ("recv src i", {C_i}, msgs)


           msgs[src, i] != empty,
           msgs'[src, i] = msgs[src, i].pop()
    ----------------------------------------------------- Recv
    ("recv src i", {C_i}, msgs) --> ("env", {C_i}, msgs')


Asynchronous Network with Global Synchronizer
---------------------------------------------

With global synchronizer, one

.. code-block::

    ------------------------------------- Init
    ("", {C_i}, ∅) --> ("send", {C_i}, ∅)



    ----------------------------------------
    ("send", {C_i}, ∅) --> ("")


    ----------------------------------------
    ("all recv", ) --> ("all send", )


Specifying Network Topology
---------------------------

We can also provide syntax for specifying network topology before automaton definition

.. code-block::

                 ... TODO...
    ---------------------------------------------- GraphDef
    (GraphDef AutDef, ., .) --> (AutDef, G, .)
