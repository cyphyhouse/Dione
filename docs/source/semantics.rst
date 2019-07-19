=========
Semantics
=========

Network Topology
****************

Assuming a given network topology, G = (V, E) where V = {1, ..., n} and
E ⊆ V × V for simplicity.
We can easily treat V and E as data types.

Specifying Network Topology
---------------------------

.. todo::

    We can also provide syntax for specifying network topology before automaton definition

.. code-block::

                 ... TODO...
    ---------------------------------------------- GraphDef
    (GraphDef AutDef, ., .) --> (AutDef, G, .)


Synchronous Model
*****************

Synchronous Algorithm Semantics
-------------------------------

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
    (AutDef, ⊥, ∅, R=0) --> ("", {C_i}, ∅, R=0)

    # Agent Configuration
    C_i : MsgGen × Transition × State × ℕ
    C_i = (msg_gen, trans, s, r)

    type State = Var -> Val
    type MsgGen = State -> V -> Msg
    type Transition = State -> MsgsWSrc -> State
    type MsgsWSrc = Map[V, Msg]


Synchronous Network Semantics
-----------------------------

Synchronous semantics simply repeats the two rules, ``AllSend`` and ``AllRecv``, in order.
The system is deterministic and will never stop.

In ``AllSendToAll`` rule, ``all_msgs`` only holds at most one message for now.
One can modified the rule to model channels with message loss.

Notice that in ``AllRecvFromAll`` rule, ``all_msgs`` are cleaned after delivered.
Also ``msgs_to_i`` is computed and used in ``trans``
right away to avoid storing it in a local variable for each agent.
Another option is to store it locally so that we can cleanly separate receiving
and internal transition.

.. code-block::

    # System Configuration
    conf : (V -> AgentConf) × Map[V × V, Msg] × ℕ
    conf = ({C_i}, msgs, R)

    ∀ i ∈ V,
        C_i.r = R
      ∧ ∀ dst ∈ V,
            msgs = { (i, dst) -> m | m = C_i.msg_gen(C_i.s, dst) }
    -------------------------------------------------------------- AllSendToAll
              ({C_i}, ∅, R) --> ({C_i}, msgs, R+1)


    ∀ src ∈ V, i ∈ V,
        msgs_to_i = { src -> m | ((src, i) -> m) ∈ msgs }
      ∧ C_i'.s = C_i.trans(C_i.s, msgs_to_i),
      ∧ C_i'.r = R
    ----------------------------------------------------- AllRecvFromAll
           ({C_i}, msgs, R) --> ({C_i'}, ∅, R)


Asynchronous Model
******************

Asynchronous Network with Global Synchronizer
---------------------------------------------

With global synchronizer, one

.. code-block::

    # System Configuration
    conf : (V -> AgentConf) × (V × V × ℕ -> Msg) × (V × ℕ -> Bool) × (V × ℕ -> bool)
    conf = ({C_i}, tray, user_sent, user_rcvd)

    ∃ i ∈ V,
        ∀ j ∈ V, user_rcvd(j, C_i.r) = true    # User automaton
      ∧ user_sent(i, C_i.r + 1) = false                # User automaton
      ∧ user_sent' = user_sent[(i, C_i.r + 1) := true]
      ∧ ∀ dst ∈ V,
            # TODO constraints for stroing messages to tray
    --------------------------------------------------------------- iSendToAll
    ({C_i}, tray, user_sent, user_rcvd)
    --> ({C_i}, tray', user_sent', user_rcvd)



    ∃ i ∈ V,
        ∀ j ∈ V, user_sent(j, C_i.r + 1) = true
      ∧ user_rcvd(i, C_i.r + 1) = false
      ∧ user_rcvd' = user_rcvd[(i, C_i.r + 1) := true]
      ∧ C_i'.r = C_i.r + 1
      ∧ ∀ dst ∈ V,
            # TODO constraints to deliver messages
    ----------------------------------------------- iRecvFromAll
    ({C_i}, tray, user_sent, user_rcvd)
    --> ({C_i'}, tray, user_sent, user_rcvd')

.. todo::

    Note that user_sent(i, r) = false ∧ user_rcvd(i, r) = true is an invalid
    configuration.
    We might want to merge them into one variable with three states.

Asynchronous Network Semantics
------------------------------

It seems interpreting a synchronous algorithm with asynchronous network
does not make much sense.
We can only define an arbitrary message delivery model and a memory model
for updating states with transition function.

Since transition function ``C_i.trans`` takes all messages delivered to
``i`` as arguments, we can choose

There are several options for ``Recv`` rule regarding
how many messages are delivered at the same time.

1. Deliver one message from one ``src`` node a time.
   More precisely, only pop the top of the ``(src, i)`` queue.

2. Deliver the oldest message to ``i`` for each source agent.
   More precisely, pop all the top of the ``(_, i)`` queue,
   and aggregate them.

3. Deliver all messages in queue sent to ``i`` (Weird)

The ``Recv`` rule below is specifying option 2.
It is obvious that the messages expected by agent ``i``
for transition may have not been sent yet,
and therefore executing the algorithm will have different behavior.

.. todo::

    Finish the semantic rules

.. code-block::

    # System Configuration
    conf : {AgentConf_i} × Map[V × V, Queue[Msg]]
    conf = ({C_i}, msgs)


                 m = C_i.msg_gen(C_i.s, dst),
     msgs'[i, dst] = msgs[i, dst].append(m)
    ---------------------------------------- Send
        ({C_i}, msgs) --> ({C_i}, msgs')


    msgs_to_i = { src -> m | msgs[src, i] != ∅ &&
                             m = msgs[src, i].top() },
       C_i'.s = C_i.trans(C_i.s, msgs_to_i),
    msgs'[src, i] = msgs[src, i].pop()
    -------------------------------------------------- Recv
            ({C_i}, msgs) --> ({C_i'}, msgs')
