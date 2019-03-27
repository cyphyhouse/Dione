from enum import Enum, auto


class AutoName(Enum):
    def _generate_next_value_(self, start, count, last_values):
        assert isinstance(self, str)
        return self.lower()


class IOA(AutoName):

    def __str__(self):
        return str(self.value)

    @classmethod
    def get(cls, key, default):
        try:
            return cls[key.upper()]
        except KeyError:
            return default

    # reserved words
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
    INVARIANT = auto()
    OUTPUT = auto()
    PASS = auto()
    PRE = auto()
    SIGNATURE = auto()
    SIMULATION = auto()
    STATES = auto()
    TRAJECTORIES = auto()
    TRANSITIONS = auto()
    WHERE = auto()
    # internal syntax constructs
    ASSIGN = "$assign"
    DECL_COMPONENT = "$decl_component"
    DECL_VAR = "$decl_decl_var"
    FORMAL_ACT = "$formal_act"
    IDENTIFIER = "$identifier"
    IOA_SPEC = "$ioa_spec"
    SHORTHAND = "$shorthand"
    TRANSITION = "$transition"
    TYPE_DEF = "$type_def"


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
