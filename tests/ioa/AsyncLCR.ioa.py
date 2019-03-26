UID = IntEnum(0, 1, 2)
Status = Enum(UNKNOWN, CHOSEN, REPORTED)

@composition
class Sys:
    def parameters(u0: UID, u1: UID, u2: UID):
        where = (u0 != u1 and u1 != u2 and u2 != u0)

    def components():
        P0 = AsyncLCR0(u0)
        P1 = AsyncLCR1(u1)
        P2 = AsyncLCR2(u2)

    invariant = (
            implies(u0 != max(u0, u1, u2), P0.status == Status.UNKNOWN) and
            implies(u1 != max(u0, u1, u2), P1.status == Status.UNKNOWN) and
            implies(u2 != max(u0, u1, u2), P2.status == Status.UNKNOWN)
    )

@automaton
class AsyncLCR0:
    def parameters(u0: UID): pass

    class signature:
        @output
        def from0to1(v: UID): where = True
        @input
        def from2to0(v: UID): pass
        @output
        def leader_0(): pass

    def states(
        q: Seq[UID] = [u0],
        status: Status = Status.UNKNOWN
    ): initially = True

    class transitions:

        @output
        @pre(q != [] and v == q[0])
        def eff_from0to1(v):
            q = q[1:]

        @input
        def from2to0(v):
            if v > u0:
                q = q + [v]
            elif v == u0:
                status = Status.CHOSEN

        @output
        @pre(status == Status.CHOSEN)
        def leader_0():
            status = Status.REPORTED
