Ideas
=====

Simplify Simulation for Parameterized Systems
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Technical Contributions
-----------------------

+ Given traces from testing/simulation of large systems


Theoretical Contributions
-------------------------

Apply existing small model properties to some classes of Safety/Liveness
properties φ in a specification language, e.g., LTL or Signal Temporal Logic.

Assume the system A(ṗ) takes parameters ṗ, we need to argue that model checking
A(ṗ) ⊧ φ(ṗ) is equi-satisfiable in proving in First Order Logic.
That is, for any assignment σ satisfies the symbolic representation Â(ṗ),
σ also satisfies the FOL translation of φ.

We restrict the interpretation of ṗ and σ within a (combined) SMT theory T
where only equality over ṗ and linear order (special case of difference logic)
for index of σ.
Each alphabet can be a pair of a state and an action.


Equivalently::

    ∀ṗ∀σ. (Valid(ṗ) ∧ Traces(ṗ)(σ) ∧ Â(ṗ)(σ)) → φ(ṗ)(σ) is T-valid ⇔
    Valid(ṗ) ∧ Traces(ṗ)(σ) ∧ Â(ṗ)(σ)) ∧ ¬φ(ṗ)(σ) is T-UNSAT

We therefore need to inspect the body of Valid, Traces, Â, and φ to determine if
the formula has finite model property.

Given symbolic representation of initial states Θ and transition relation δ
Â(ṗ) can be expanded as::

    θ(ṗ)(σ[0].state) ∧ ∀i.δ(σ[i].state, σ[i+1].act, σ[i+1].state)

Θ and δ cannot contain alternating quantifiers.





Verification with Synchronizer models
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

+ Provide two semantics for the same (restricted) IOA language

  * Execution on synchronous network environment
  * Execution with synchronizers on asynchronous network environment

+ Prove simulation(?) between asynchronous implementation and
  synchronous algorithm wrapped with synchronizers


Theoretical Contributions
-------------------------

Given a user defined **synchronous IOA**, A_pgm, and network topology, G,
we provide two semantics

S_sync = A_pgm || B_sync(G)
S_async = A_pgm || H(G) || B_async(G)

where H is the synchronizer

Theorem. ∀ A_pgm, S_sync ~ S_async


Technical Contributions
-----------------------

Tool support for

1. Constraint on A_pgm to be applied with synchronizers

2. Invariant checking for S_sync


Applications
------------

Maybe we can claim that, under our framework,

1. Users can model a synchronous algorithm, SynAlg, and prove against synchronous network
   as well as synchronizer over reliable asynchronous network

2. Provide a golden reference for comparing with the asynchronous version, AsynAlg

   + We can provide tests or assertions for AsynAlg based on (SynAlg || Synchronizer)

3. Perhaps we can provide proof if AsynAlg is designed according to SynAlg

   + Simulation proof: (SynAlg || Synchronizer) ~ AsynAlg
   + Prove ∀ fair trace t1 in Tr(AsynAlg),
     ∃ fair trace t2 in Tr(AsynAlg)

     * t2 is a reordering of t1 preserving Happens-Before partial order
     * t2 in Tr(SynAlg || Synchronizer)


Evaluation Subjects
-------------------

+ Both synchronous and asynchronous LCR algorithms

+ Self-stabilizing Mutual Exclusions

  * Ring, Bidirectional Array (Synchronized version)
  * Do we need asynchronous versions of the algorithms?


Weak Synchrony Assumptions
--------------------------

+ Should we consider extending our framework to support modeling for weakly synchronous
  network?
+ Prof. Elaine Shi's recent paper
  "Synchronous, with a Chance of Partition Tolerance"

