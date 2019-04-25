""" Mutual Exclusion on a Bidirection Array """

Status: type = IntRange(0, 4)

@automaton
def FourState(N: int):
    where= 2 <= N

    class signature:
        @internal
        def trans(i: int): where=0 <= i < N

    class states:
        s: Seq[Status]
    initially = len(s) == N and (s[0] == 1 or s[0] == 3) and (s[N-1] == 0 or s[N-1] == 2)

    class transitions:
        @internal
        @pre((i == 0 and s[i+1] == incre(s[i])) or (i == N-1 and s[i-1] == incre(s[i])))
        def trans(i):
            s[i] = incre(incre(s[i]))

        @internal
        @pre(0 < i < N-1 and s[i-1] == incre(s[i]))
        def trans(i):
            s[i] = s[i-1]

        @internal
        @pre(0 < i < N-1 and s[i+1] == incre(s[i]))
        def trans(i):
            s[i] = s[i+1]

    invariant_of = len(s) == N and (s[0] == 1 or s[0] == 3) and (s[N-1] == 0 or s[N-1] == 2)
