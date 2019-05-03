""" Dijkstra's self-stabilizing algorithm on a ring """

@automaton
def StableRing(N: int, K: int):
    where = 1 < N < K

    class signature:
        @output
        def trans(i: int): where = 0 <= i < N

    class states:
        s: Seq[int]
    initially = len(s) == N and forall(i, implies(0<=i<N, 0<=s[i]<K))

    class transitions:
        @output
        @pre(i == 0 and s[i] == s[N-1])
        def trans(i):
            s[i] = (s[N-1] + 1) % K

        @output
        @pre(i != 0 and s[i] != s[i-1])
        def trans(i):
            s[i] = s[i-1]

    invariant_of = len(s) == N and \
        forall(i, implies(0<=i<N, 0<=s[i]<K))
