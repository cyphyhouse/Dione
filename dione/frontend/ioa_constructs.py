from enum import Enum, auto, unique


class AutoName(Enum):
    def _generate_next_value_(self, start, count, last_values) -> str:
        assert isinstance(self, str)
        region_sep = "_REGION_INTERNAL"
        if self != region_sep and \
                ("$" + region_sep.lower()) not in last_values:
            # reserved words
            return self.lower()
        # else: # internal structs
        return "$" + self.lower()


@unique
class IOA(AutoName):
    def __str__(self):
        return str(self.value)

    @classmethod
    def get(cls, key, default):
        try:
            return cls[key.upper()]
        except KeyError:
            return default

    # region reserved words
    AUTOMATON = auto()
    COMPONENTS = auto()
    COMPOSITION = auto()
    EFF = auto()
    ELSE = auto()
    FOR = auto()
    HIDDEN = auto()
    IF = auto()
    INITIALLY = auto()
    INPUT = auto()
    INTERNAL = auto()
    INVARIANT_OF = auto()
    OUTPUT = auto()
    PASS = auto()
    PRE = auto()
    SIGNATURE = auto()
    SIMULATION = auto()
    STATES = auto()
    TRAJECTORIES = auto()
    TRANSITIONS = auto()
    TYPE = auto()
    WHERE = auto()
    # endregion
    _REGION_INTERNAL = auto()
    # region internal syntax constructs. This must be after __REGION_INTERNAL
    ASSIGN = auto()
    AUTOMATON_INSTANCE = auto()
    DECL_COMPONENT = auto()
    DECL_VAR = auto()
    FORMAL_ACT = auto()
    FORMAL_PARA_LIST = auto()
    FORMAL_PARA = auto()
    ACTUAL_PARA_LIST = auto()
    ACTUAL_PARA = auto()
    IDENTIFIER = auto()
    IOA_SPEC = auto()
    SHORTHAND = auto()
    TRANSITION = auto()
    TYPE_DEF = auto()
    # endregion


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
