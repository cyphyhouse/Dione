"""Syntax Checker to check if a given Python AST can be interpreted as a Koord AST"""

import ast
from enum import Enum, auto


class IOA(Enum):
    AUTOMATON_DEF = auto()
    AUTOMATON = "automaton"
    COMPOSITION = "composition"
    INVARIANT = "invariant"
    MODULE = "module"
    PARAMETERS = "parameters"
    SIGNATURE = "signature"
    SIMULATION = "simulation"
    TRANSITIONS = "transitions"
    TYPE_DEF = auto()
    WHERE = "where"


class IOAScope(Enum):
    MODULE = 0
    COMPONENTS = "component"
    AUTOMATON = "automaton"
    STATES = "states"
    EFFECT = "effect"


class IOAAstChecker(ast.NodeVisitor):
    def __init__(self):
        self.__scope = IOAScope.MODULE

    def visit_Module(self, node):
        for stmt in node.body:
            ioa_struct = self.visit(stmt)
            if ioa_struct not in \
                    [IOA.AUTOMATON_DEF, IOA.SIMULATION, IOA.TYPE_DEF]:
                # FIXME more precise error message
                raise ValueError(
                    "IOA Syntax Error: unexpected " + str(ioa_struct) + " at " + self.__scope.value + " level")
        return IOA.MODULE

    def visit_Assign(self, node):
        if len(node.targets) > 1:
            # FIXME allow multiple assignment?
            raise ValueError("Multiple assignment is not supported.")

        if self.__scope is IOAScope.MODULE:
            return self.visit_TypeDef(node)
        if self.__scope is IOAScope.AUTOMATON:
            if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                lhs = self.visit(node.targets[0])
                if lhs is IOA.INVARIANT.value:
                    return self.visit_Invariant(lhs, node.value)
        # TODO parameters and actions
                # if lhs is IOA.WHERE.value:
                #    return self.visit_Where(lhs, node.value)
        if self.__scope is IOAScope.COMPONENTS:
            return self.visit_AssignComponent(node)
        if self.__scope is IOAScope.EFFECT:
            return self.visit_AssignInEff(node)

        # else: # FIXME more precise error message
        raise ValueError("Unexpected assignment when specifying " + self.__scope.value)

    def visit_ClassDef(self, node):
        if self.__scope is IOAScope.MODULE:
            deco_list = [self.visit(d) for d in node.decorator_list]
            if IOA.AUTOMATON.value in deco_list or \
                    IOA.COMPOSITION.value in deco_list:
                return self.visit_AutomatonDef(node)
            # else: # FIXME more precise error message
            raise ValueError("Wrong decorators" + str(deco_list))
        # TODO cases on other class

    def visit_FunctionDef(self, node):
        # TODO
        pass

    def visit_Name(self, node):
        return node.id

    # IOA specific language constructs
    def visit_AutomatonDef(self, node):
        self.__scope = IOAScope.AUTOMATON  # Set scope
        for stmt in node.body:
            ioa_struct = self.visit(stmt)
            # TODO check if the body of automaton contains exactly one of each construct
            if False:
                # FIXME more precise error message
                raise ValueError("IOA Syntax Error")
        self.__scope = IOAScope.MODULE  # Reset scope
        return IOA.AUTOMATON_DEF

    def visit_TypeDef(self, node):
        assert len(node.targets) == 1
        if not isinstance(node.targets[0], ast.Name):
            # TODO allow defining generic type?
            raise ValueError("Left-hand side is not an identifier for type definition")

        lhs = self.visit(node.targets[0])
        # TODO Collect Type Information for lhs
        return IOA.TYPE_DEF

    def visit_Where(self, lhs_str, rhs_node):
        assert lhs_str is IOA.WHERE.value
        # TODO Check where clause is bool
        return IOA.WHERE

    def visit_Invariant(self, lhs_str, rhs_node):
        assert lhs_str is IOA.INVARIANT.value
        # TODO Check Invariant is bool
        return IOA.INVARIANT
