""" Syntax Checker to check if a given Python AST can be interpreted as
    Input/Output Automata
"""

import ast

from src.frontend.ioa_constructs import IOA, IOAScope, IOAScopeHandler


class IOAAstChecker(ast.NodeVisitor):
    def __init__(self):
        self.__scope = IOAScope()

    def visit_Assign(self, node):
        assert node.targets
        if len(node.targets) > 1:
            # FIXME allow multiple assignment?
            raise ValueError("Multiple assignment is currently not supported.")

        if self.__scope == IOA.IOA_SPEC:
            return self.visit_TypeDef(node)
        if self.__scope == IOA.PRIM_AUTOMATON or \
            self.__scope == IOA.COMPOSITION:
            if isinstance(node.targets[0], ast.Name):
                lhs = self.visit(node.targets[0])
                if IOA(lhs) == IOA.INVARIANT:
                    return self.visit_Invariant(lhs, node.value)
        if self.__scope == IOA.PARAMETERS or \
            self.__scope == IOA.FORMAL_ACT:
            if isinstance(node.targets[0], ast.Name):
                lhs = self.visit(node.targets[0])
                if IOA(lhs) == IOA.WHERE:
                    return self.visit_Where(lhs, node.value)
        if self.__scope == IOA.COMPONENT_LIST:
            return self.visit_Component(node)
        if self.__scope == IOA.EFFECT:
            return self.visit_AssignInEff(node)
        # else:
        raise ValueError("Unexpected assignment when specifying " +
            self.__scope.value)

    def visit_ClassDef(self, class_def):
        if self.__scope == IOA.IOA_SPEC:
            return self.visit_AutomatonDef(class_def)
        if self.__scope == IOA.PRIM_AUTOMATON:
            if IOA(class_def.name) == IOA.SIGNATURE:
                return self.visit_Signature(class_def)
            if IOA(class_def.name) == IOA.TRANSITION_LIST:
                return self.visit_TransitionList(class_def)
            if IOA(class_def.name) == IOA.TRAJECTORIES:
                return self.visit_Trajectories(class_def)
        # else:
        raise ValueError("Unexpected class \"" + class_def.name +
             "\" when specifying " + self.__scope.value)

    def visit_FunctionDef(self, func_def):
        if self.__scope == IOA.IOA_SPEC:
            if func_def.name == str(IOA.SIMULATION):
                return self.visit_Simulation(func_def)
        if self.__scope == IOA.PRIM_AUTOMATON:
            if func_def.name == str(IOA.PARAMETERS):
                return self.visit_Parameters(func_def)
            if func_def.name == str(IOA.STATES):
                return self.visit_States(func_def)
        if self.__scope == IOA.COMPOSITION:
            if func_def.name == str(IOA.PARAMETERS):
                return self.visit_Parameters(func_def)
            if func_def.name == str(IOA.COMPONENT_LIST):
                return self.visit_ComponentList(func_def)
        if self.__scope == IOA.SIGNATURE:
            return self.visit_FormalAction(func_def)
        if self.__scope == IOA.TRANSITION_LIST:
            return self.visit_Transition(func_def)
        # else:
        raise ValueError("Unexpected function \"" + func_def.name +
            "\" when specifying " + self.__scope.value)

    def visit_Module(self, mod):
        return self.visit_IOASpec(mod)

    def visit_Name(self, node):
        return node.id

    # IOA specific language constructs
    def visit_IOASpec(self, spec):
        expected = [IOA.AUTOMATON_DEF, IOA.SIMULATION, IOA.TYPE_DEF]

        for stmt in spec.body:
            ioa_construct = self.visit(stmt)
            if ioa_construct not in expected:
                # FIXME more precise error message
                raise ValueError(
                    "Unexpected \"" + str(ioa_construct) + "\" at " +
                        self.__scope.value + " level")
        return IOA.IOA_SPEC

    def visit_AutomatonDef(self, node):
        deco_list = [self.visit(d) for d in node.decorator_list]
        # If both @compostion and @automaton are present,
        # try composition first
        if str(IOA.COMPOSITION) in deco_list and \
                self.visit_Composition(node):
            return IOA.AUTOMATON_DEF
        if str(IOA.PRIM_AUTOMATON) in deco_list and \
                self.visit_PrimitiveAutomaton(node):
            return IOA.AUTOMATON_DEF
        # else:
        raise ValueError("Wrong decorators " + str(deco_list))

    def visit_PrimitiveAutomaton(self, node):
        expected = [IOA.PARAMETERS, IOA.SIGNATURE, IOA.STATES,
            IOA.TRANSITION_LIST, IOA.TRAJECTORIES, IOA.INVARIANT]

        with IOAScopeHandler(self.__scope, IOA.PRIM_AUTOMATON):
            for stmt in node.body:
                ioa_construct = self.visit(stmt)
                if not isinstance(ioa_construct, IOA):
                     # FIXME more precise error message
                    raise ValueError("Unexpected Python \"" + str(stmt) +
                        "\" when specifying " + self.__scope.value)
                if ioa_construct not in expected:
                    # FIXME more precise error message
                    raise ValueError("Unexpected \"" + str(ioa_construct) +
                        "\" when specifying " + self.__scope.value)
        # TODO check if the body contains exactly one of each construct
        return IOA.PRIM_AUTOMATON

    def visit_Composition(self, node):
        expected = [IOA.PARAMETERS, IOA.COMPONENT_LIST, IOA.INVARIANT]

        with IOAScopeHandler(self.__scope, IOA.COMPOSITION):
            for stmt in node.body:
                ioa_construct = self.visit(stmt)
                if not isinstance(ioa_construct, IOA):
                    # FIXME more precise error message
                    raise ValueError("Unexpected Python \"" + str(stmt) +
                        "\" when specifying " + self.__scope.value)
                if ioa_construct not in expected:
                    # FIXME more precise error message
                    raise ValueError("Unexpected \"" + str(ioa_construct) +
                        "\" when specifying " + self.__scope.value)
        # TODO check if the body contains exactly one of each construct
        return IOA.COMPOSITION

    def visit_ComponentList(self, node):
        # TODO
        return IOA.COMPONENT_LIST

    def visit_Component(self, stmt):
        # TODO
        return IOA.COMPONENT

    def visit_FormalAction(self, node):
        # TODO
        return IOA.FORMAL_ACT

    def visit_Invariant(self, lhs_str, rhs_node):
        assert IOA(lhs_str) == IOA.INVARIANT

        with IOAScopeHandler(self.__scope, IOA.INVARIANT):
            # TODO Check Invariant is bool
            pass
        return IOA.INVARIANT

    def visit_Parameters(self, node):
        # TODO
        return IOA.PARAMETERS

    def visit_Signature(self, node):
        # TODO
        return IOA.SIGNATURE

    def visit_Simulation(self, node):
        # TODO
        return IOA.SIMULATION

    def visit_States(self, node):
        # TODO
        return IOA.STATES

    def visit_Trajectories(self, node):
        # TODO
        return IOA.TRAJECTORIES

    def visit_TransitionList(self, node):
        # TODO
        return IOA.TRANSITION_LIST

    def visit_Transition(self, node):
        # TODO
        return IOA.TRANSITION

    def visit_TypeDef(self, node):
        assert len(node.targets) == 1
        if not isinstance(node.targets[0], ast.Name):
            # TODO allow defining generic type?
            raise ValueError("Left-hand side is not an identifier for type definition")

        with IOAScopeHandler(self.__scope, IOA.TYPE_DEF):
            lhs = self.visit(node.targets[0])
            # TODO Collect Type Information for lhs
        return IOA.TYPE_DEF

    def visit_Where(self, lhs_str, rhs_node):
        assert IOA(lhs_str) == IOA.WHERE
        # TODO Check where clause is bool
        return IOA.WHERE

    def visit_AssignInEff(self, stmt):
        # TODO
        return IOA.STATEMENT
