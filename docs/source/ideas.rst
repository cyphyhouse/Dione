Ideas
=====

Verification with Synchronizer models
-------------------------------------

+ Provide two semantics for the same (restricted) IOA language

    - Execution on synchronous network environment
    - Execution with synchronizers on asynchronous network environment

+ Prove simulation(?) between asynchronous implementation and
  synchronous algorithm wrapped with synchronizers


Contributions
-------------

Maybe we can claim that, under our framework,

1. Users can model a synchronous algorithm, SynAlg,
   and prove against synchronous network as well as synchronizer over asynchronous

2. Provide a golden reference for comparing with the asynchronous version, AsynAlg

   + We can provide tests or assertions for AsynAlg based on (SynAlg || Synchronizer)

3. Perhaps we can provide proof if AsynAlg is designed according to SynAlg
   (SynAlg || Synchronizer) ~ AsynAlg

   + Simulation proof
   + Prove ∀ fair trace t1 in Tr(AsynAlg),
     ∃ fair trace t2 in Tr(AsynAlg)

     - t2 is a reordering of t1 preserving Happens-Before partial order
     - t2 in Tr(SynAlg || Synchronizer)


Evaluation Subjects
-------------------

+ Both synchronous and asynchronous LCR algorithms

+ Self-stabilizing Mutual Exclusions

    - Ring, Bidirectional Array (Synchronized version)
    - Do we need asynchronous versions of the algorithm?

