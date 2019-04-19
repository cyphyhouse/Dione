"""Dijkstra's token ring self-stabilizing system"""

@automaton
def StablizingTokenRing(N: int, K: int):
    where = 1 < N < K

    class signature:
        @internal
        def trans(i: int): where = 0 <= i < N

    class states:
        x: Seq[int]
    initially = len(x) == N and forall(i, implies(0<=i<N, x[i] <= K))

    class transitions:
        @internal
        @pre(i == 0 and x[i] == x[N-1])
        def trans(i):
            x[i] = (x[N-1] + 1) % K

        @internal
        @pre(i != 0 and x[i] != x[i-1])
        def trans(i):
            x[i] = x[i-1]

    invariant_of = len(x) == N and \
        forall(i, implies(0<=i<N, x[i] <= K))
