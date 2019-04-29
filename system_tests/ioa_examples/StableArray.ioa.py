""" Mutual Exclusion on a bi-directional array """

Status: type = IntRange[0:4]

@automaton
def StableArray(N: int):
    where= 2 <= N

    class signature:
        @output
        def trans(i: int): where=0 <= i < N

    class states:
        s: Seq[Status]
    initially = len(s) == N and (s[0] == 1 or s[0] == 3) and (s[N-1] == 0 or s[N-1] == 2)

    class transitions:
        @output
        @pre((i == 0 and s[i+1] == incre(s[i])) or (i == N-1 and s[i-1] == incre(s[i])))
        def trans(i):
            s[i] = incre(incre(s[i]))

        @output
        @pre(0 < i < N-1 and s[i-1] == incre(s[i]))
        def trans(i):
            s[i] = s[i-1]

        @output
        @pre(0 < i < N-1 and s[i+1] == incre(s[i]))
        def trans(i):
            s[i] = s[i+1]

    invariant_of = len(s) == N and (s[0] == 1 or s[0] == 3) and (s[N-1] == 0 or s[N-1] == 2)
