""" CAN Bus arbitration protocol """

Bit: type = bv1
BitPos: type = IntRange[-1:11]
NodeState: type = NamedTuple[arb: bv11, transmit: Bool]

@composition
def Sys():
    where = True

    class components:
        bus: Bus()
        nseq: NodeSeq()

    invariant_of = len(nseq.nodes)>0 and \
                   nseq.nodes[i_min(nseq.nodes)].transmit

@automaton
def Bus():
    where = True

    class signature:
        @input
        def send(msgs: Seq[Bit]): pass
        @output
        def recv(msg: Bit): pass

    class states:
        bus: Bit
    initially = True

    class transitions:
        @input
        def send(msgs):
            if forall(i, implies(0 <= i < len(msgs), msgs[i] == 1)):
                bus = 1
            else:
                bus = 0
        @output
        @pre(msg == bus)
        def recv(msg):
            pass

@automaton
def NodeSeq():
    where = True

    class signature:
        @output
        def send(msgs: Seq[Bit]):
            pass

        @input
        def recv(msg: Bit):
            pass

    class states:
        pos: BitPos
        nodes: Seq[NodeState]
    initially = pos==10 and len(nodes) > 0 and \
                forall(i, implies(0<=i<len(nodes), nodes[i].transmit))

    class transitions:
        @output
        @pre(len(msgs) == len(nodes) and
             forall(i, implies(0<=i<len(nodes),
                    msgs[i]==(bv_extract(nodes[i].arb, pos) if nodes[i].transmit
                    else 1))))
        def send(msgs):
            pass

        @input
        def recv(msg):
            if pos >= 0:
                nodes = [NodeState(n.arb, False) if n.transmit and msg != bv_extract(n.arb, pos) else n
                    for n in nodes]
                pos = pos - 1
