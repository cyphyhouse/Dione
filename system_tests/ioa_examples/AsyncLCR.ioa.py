Index: type = IntRange[0:3]
UID: type = Nat
Status: type = Enum[UNKNOWN, CHOSEN, REPORTED]

@composition
def Sys(u0: UID, u1: UID, u2: UID):
    where = (u0 != u1 and u1 != u2 and u2 != u0)

    class components:
        P0: AsyncLCR(0, u0)
        P1: AsyncLCR(1, u1)
        P2: AsyncLCR(2, u2)

    invariant_of = (
            implies(u0 != max(u0, u1, u2), P0.status == UNKNOWN) and
            implies(u1 != max(u0, u1, u2), P1.status == UNKNOWN) and
            implies(u2 != max(u0, u1, u2), P2.status == UNKNOWN)
    )

@automaton
def AsyncLCR(i: Index, u: UID):
    where = True

    class signature:
        @output
        def send_recv(src: Index, dst: Index, v: UID):
            where = src == i and dst == incre(i)
        @input
        def send_recv(src: Index, dst: Index, v: UID):
            where = src == decre(i) and dst == i
        @output
        def leader(id: Index):
            where = id == i

    class states:
        q: Seq[UID]
        status: Status
    initially = q == [u] and status == UNKNOWN

    class transitions:
        @output
        @pre(q != [] and v == q[0])
        def send_recv(src, dst, v):
            q = q[1:]

        @input
        def send_recv(src ,dst, v):
            if v > u:
                q = q + [v]
            elif v == u:
                status = CHOSEN

        @output
        @pre(status == CHOSEN)
        def leader(id):
            status = REPORTED
