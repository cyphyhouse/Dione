from enum import Enum, auto

class AutoName(Enum):
    def _generate_next_value_(self, start, count, last_values):
        return self

class IOA(AutoName):

    def __str__(self):
        return str(self.value)

    PRIM_AUTOMATON = "automaton"
    COMPONENT = auto()
    COMPONENT_LIST = "components"
    COMPOSITION = "composition"
    EFFECT = "eff"
    FORMAL_ACT = auto()
    INVARIANT = "invariant"
    IOA_SPEC = auto()
    PARAMETERS = "parameters"
    PRECONDITION = "pre"
    SIGNATURE = "signature"
    SIMULATION = "simulation"
    STATEMENT = "statement"
    STATES = "states"
    STMT_PASS = auto()
    TRAJECTORIES = "trajectories"
    TRANSITION_LIST = "transitions"
    TRANSITION = auto()
    TYPE_DEF = auto()
    WHERE = "where"


class IOAScope:
    """ Keep track of current scope using a stack while comparable with IOA
        value """
    def __init__(self):
        self.__stack = []

    def __eq__(self, other: IOA) -> bool:
        assert self.__stack
        return self.__stack[-1] == other

    @property
    def value(self):
        assert self.__stack
        return self.__stack[-1].value

    def enter(self, ioa_construct):
        # TODO check if the scope always goes to lower level
        self.__stack.append(ioa_construct)

    def exit(self):
        self.__stack.pop()


class IOAScopeHandler:
    """ Make sure the scope is correctly set and reset via `with` statement"""
    def __init__(self, scope, ioa_construct):
        self.__scope = scope
        self.__ioa = ioa_construct

    def __enter__(self):
        self.__scope.enter(self.__ioa)

    def __exit__(self, type, value, traceback):
        self.__scope.exit()
