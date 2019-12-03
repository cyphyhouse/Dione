MachineStatus: type = Enum[M_IDLE,  # M_DOWN,
                           M_WORK, M_DONE, M_BAD]
SharedStatus: type = Enum[READY, BUSY, DONE]

@composition
def system():
    class components:
        Robot : robot()
        M0 : machine(0)
        M1 : machine(1)
        M2 : machine(2)

    invariant_of = implies((Robot.m0_status == READY), M0.status == M_IDLE) \
                and implies((Robot.m1_status == READY), M1.status == M_IDLE) \
                and implies((Robot.m2_status == READY), M2.status == M_IDLE) \
                and implies((Robot.m0_status == DONE), M0.status == M_DONE) \
                and implies((Robot.m1_status == DONE), M1.status == M_DONE) \
                and implies((Robot.m2_status == DONE), M2.status == M_DONE) \
                and M0.status != M_BAD \
                and M1.status != M_BAD \
                and M2.status != M_BAD

@automaton
def robot():
    where = True

    class states:
        m0_status: SharedStatus
        m1_status: SharedStatus
        m2_status: SharedStatus

    initially = m0_status == READY and \
                m1_status == READY and \
                m2_status == READY

    class signature:
        @input
        def m_done(i: Nat):
            where = 0 <= i < 3

        @output
        def drop(i: Nat):
            where = 0 <= i < 3
        @output
        def pick(i: Nat):
            where = 0 <= i < 3

    class transitions:
        @input
        def m_done(i):
            if i == 0:
                m0_status = DONE
            if i == 1:
                m1_status = DONE
            if i == 2:
                m2_status = DONE

        @output
        @pre(i == 0 and m0_status == READY)
        def drop(i):
            m0_status = BUSY
        @output
        @pre(i == 1 and m1_status == READY)
        def drop(i):
            m1_status = BUSY
        @output
        @pre(i == 2 and m2_status == READY)
        def drop(i):
            m2_status = BUSY

        @output
        @pre(i == 0 and m0_status == DONE)
        def pick(i):
            m0_status = READY
        @output
        @pre(i == 1 and m1_status == DONE)
        def pick(i):
            m1_status = READY
        @output
        @pre(i == 2 and m2_status == DONE)
        def pick(i):
            m2_status = READY


@automaton
def machine(machine_id: Nat):
    where = True

    class states:
        status: MachineStatus
    initially = (status == M_IDLE)

    class signature:
        @internal
        def m_selfloop(i: Nat):
            where = (i == machine_id)
        @output
        def m_done(i: Nat):
            where = (i == machine_id)

        @input
        def drop(i: Nat):
            where = (i == machine_id)
        @input
        def pick(i: Nat):
            where = (i == machine_id)

    class transitions:
        @internal
        @pre(True)
        def m_selfloop(i):
            pass

        @output
        @pre(status == M_WORK)
        def m_done(i):
            status = M_DONE

        @input
        def drop(i):
            if status == M_IDLE:
                status = M_WORK
            else:
                status = M_BAD

        @input
        def pick(i):
            if status == M_DONE:
                status = M_IDLE
            else:
                status = M_BAD
