from enum import Enum, auto


class IOA(Enum):
    AUTOMATON_DEF = auto()
    AUTOMATON = "automaton"
    COMPONENTS = "components"
    COMPOSITION = "composition"
    EFFECT = "eff"
    INVARIANT = "invariant"
    MODULE = "module"
    PARAMETERS = "parameters"
    PRECONDITION = "pre"
    SIGNATURE = "signature"
    SIMULATION = "simulation"
    TRANSITIONS = "transitions"
    TYPE_DEF = auto()
    WHERE = "where"


class IOAScope:
    """ Keep track of current scope using a stack while comparable with IOA
        value """
    def __init__(self):
        self.__stack = [IOA.MODULE]

    def __eq__(self, other: IOA) -> bool:
        assert self.__stack
        return self.__stack[-1] == IOA

    @property
    def value(self):
        assert self.__stack
        return self.__stack[-1].value

    def enter(self, ioa_struct):
        # TODO check if the scope always goes to lower level
        self.__stack.append(ioa_struct)

    def exit(self):
        self.__stack.pop()


class IOAScopeHandler:
    """ Make sure the scope is correctly set and reset via `with` statement"""
    def __init__(self, scope, ioa_struct):
        self.__scope = scope
        self.__ioa = ioa_struct

    def __enter__(self):
        self.__scope.enter(self.__ioa)

    def __exit__(self, type, value, traceback):
        self.__scope.exit()
