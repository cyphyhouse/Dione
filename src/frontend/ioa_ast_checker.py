""" Syntax Checker to check if a given Python AST can be interpreted as
    Input/Output Automata
"""

import ast

from src.frontend.ioa_constructs import IOA, IOAScope, IOAScopeHandler


class IOAAstChecker(ast.NodeVisitor):
    def __init__(self):
        self.__scope = IOAScope()

    def visit_AnnAssign(self, node):
        """ Variable annotated with type hints and followed by an optional assigned value. """
        if not isinstance(node.target, ast.Name):
            # TODO Allow subscription expressions (e.g., sequence, map, etc.) or member access
            raise NotImplementedError("Left-hand side must be an identifier for now.")

        lhs = self.visit(node.target)
        assert isinstance(lhs, IOA)
        if self.__scope == IOA.STATES:
            return self.visit_DeclStateVar(lhs, node.annotation, node.value)
        if self.__scope == IOA.COMPONENTS:
            return self.visit_Component(lhs, node.annotation, node.value)

        # else:
        raise ValueError("Unexpected variable with type hints \"" + node.target.id +
                         "\" when specifying " + self.__scope.value)

    def visit_Assign(self, node):
        """ Assignment without type hints """
        assert node.targets
        if len(node.targets) > 1:
            # TODO allow multiple assignment?
            raise NotImplementedError("Multiple assignment is currently not supported.")
        if not isinstance(node.targets[0], ast.Name):
            # TODO Allow subscription expressions (e.g., sequence, map, etc.) or member access
            raise NotImplementedError("Left-hand side must be an identifier for now.")

        lhs = self.visit(node.targets[0])
        assert isinstance(lhs, IOA)
        if self.__scope == IOA.IOA_SPEC:
            return self.visit_TypeDef(lhs, node.value)
        if self.__scope == IOA.AUTOMATON:
            if lhs == IOA.INITIALLY:
                return self.visit_Initially(lhs, node.value)
            if lhs == IOA.INVARIANT:
                return self.visit_Invariant(lhs, node.value)
            if lhs == IOA.WHERE:
                return self.visit_Where(lhs, node.value)
        if self.__scope == IOA.COMPOSITION:
            if lhs == IOA.INVARIANT:
                return self.visit_Invariant(lhs, node.value)
            if lhs == IOA.WHERE:
                return self.visit_Where(lhs, node.value)
        if self.__scope == IOA.FORMAL_ACT:
            if lhs == IOA.WHERE:
                return self.visit_Where(lhs, node.value)
        if self.__scope == IOA.EFF:
            return self.visit_StmtAssign(lhs, node.value)

        # else:
        if self.__scope == IOA.STATES:
            raise ValueError("Type of \"" + lhs.value +
                             "\" is required for specifying " + self.__scope.value)
        raise ValueError("Unexpected assignment to \"" + lhs.value +
                         "\" when specifying " + self.__scope.value)

    def visit_Call(self, call):
        if self.__scope == IOA.TYPE_DEF:
            return self.visit_Shorthand(call)
        if self.__scope == IOA.TRANSITION:
            return self.visit_Precondition(call)
        if self.__scope == IOA.EFF:
            raise NotImplementedError("Function call is not supported in eff yet")
        if self.__scope == IOA.DECL_COMPONENT:
            return

        # else:
        if isinstance(call.func, ast.Name):
            func = call.func.id
        else:
            func = str(call.func)
        raise ValueError("Unexpected call to \"" + func +
                         "\" when specifying " + self.__scope.value)

    def visit_ClassDef(self, class_def):
        if self.__scope == IOA.AUTOMATON:
            if class_def.name == str(IOA.SIGNATURE):
                return self.visit_Signature(class_def)
            if class_def.name == str(IOA.STATES):
                return self.visit_States(class_def)
            if class_def.name == str(IOA.TRANSITIONS):
                return self.visit_TransitionList(class_def)
            if class_def.name == str(IOA.TRAJECTORIES):
                return self.visit_Trajectories(class_def)
        if self.__scope == IOA.COMPOSITION:
            if class_def.name == str(IOA.COMPONENTS):
                return self.visit_ComponentList(class_def)
            if class_def.name == str(IOA.HIDDEN):
                return self.visit_Hidden(class_def)
        # else:
        raise ValueError("Unexpected class \"" + class_def.name +
                         "\" when specifying " + self.__scope.value)

    def visit_FunctionDef(self, func_def):
        if not func_def.decorator_list:
            raise ValueError("A decorator is expected for function \"" +
                             func_def.name + "\" when specifying " +
                             self.__scope.value)

        if self.__scope == IOA.IOA_SPEC:
            if len(func_def.decorator_list) > 1:
                raise ValueError("Only one decorator is expected for \"" +
                                 func_def.name + "\"")
            deco = self.visit_decorator(func_def.decorator_list[0])
            # If both @composition and @automaton are present,
            # try composition first
            if deco == IOA.COMPOSITION:
                return self.visit_Composition(func_def)
            if deco == IOA.AUTOMATON:
                return self.visit_PrimitiveAutomaton(func_def)
            if deco == IOA.SIMULATION:
                return self.visit_Simulation(func_def)
        if self.__scope == IOA.SIGNATURE:
            return self.visit_FormalAction(func_def)
        if self.__scope == IOA.TRANSITIONS:
            return self.visit_Transition(func_def)
        # else:
        raise ValueError("Unexpected function \"" + func_def.name +
                         "\" when specifying " + self.__scope.value)

    def visit_Module(self, mod):
        return self.visit_IOASpec(mod)

    def visit_Name(self, name):
        ioa = IOA.get(name.id, None)
        if ioa:  # Check if this is a reserved word
            return ioa
        # else:
        return IOA.IDENTIFIER

    def visit_Pass(self, stmt_pass):
        # TODO Do we have to differentiate pass statements appearing under different constructs
        return IOA.PASS

    def visit_arguments(self, arguments):
        if arguments.vararg or arguments.kwonlyargs or \
                arguments.kw_defaults or arguments.kwarg or \
                arguments.defaults:
            # TODO more precise error message
            raise ValueError("Unexpected arguments")
        return [self.visit(arg) for arg in arguments.args]

    def visit_arg(self, arg):
        # TODO also return type hint
        type_hint = self.visit(arg.annotation)
        return arg.arg

    # Util functions
    def visit_decorator(self, deco):
        """ Visit decorators """
        assert isinstance(deco, ast.expr)
        val = self.visit(deco)
        if isinstance(deco, ast.Name) or \
                isinstance(deco, ast.Call):
            return val
        # else:
        if not val:
            raise ValueError("Unexpected decorator \"" + str(deco) +
                             "\" when specifying " + self.__scope.value)
        raise ValueError("Unexpected decorator \"" + str(val) +
                         "\" when specifying " + self.__scope.value)

    def __check_list(self, ls, eq_one=None, geq_one=None,
                     leq_one=None, one_of=None, optional=None):
        # Avoid mutable default arguments
        if eq_one is None:
            eq_one = []
        if geq_one is None:
            geq_one = []
        if leq_one is None:
            leq_one = []
        if one_of is None:
            one_of = []
        if optional is None:
            optional = []

        for ioa_construct in ls:
            if not isinstance(ioa_construct, IOA):
                raise ValueError("Unexpected return value \"" + str(ioa_construct) +
                                 "\" when specifying " + self.__scope.value)
            if ioa_construct not in (eq_one + geq_one + leq_one + one_of + optional):
                raise ValueError("Unexpected \"" + str(ioa_construct) +
                                 "\" when specifying " + self.__scope.value)
        # TODO check if the body contains exactly one of each construct in eq_one
        # TODO check if the body contains at least one of each construct in geq_one
        # TODO check if the body contains at most one of each construct in leq_one
        # TODO check if the body contains exactly one from constructs in one_of

    # IOA specific language constructs
    def visit_IOASpec(self, spec):
        assert isinstance(spec, ast.Module)

        with IOAScopeHandler(self.__scope, IOA.IOA_SPEC):
            ioa_list = map(self.visit, spec.body)
            self.__check_list(ioa_list,
                              optional=[IOA.AUTOMATON, IOA.COMPOSITION,
                                        IOA.SIMULATION, IOA.TYPE_DEF])
        return IOA.IOA_SPEC

    def visit_PrimitiveAutomaton(self, prim):
        assert isinstance(prim, ast.FunctionDef)

        with IOAScopeHandler(self.__scope, IOA.AUTOMATON):
            parameters = self.visit(prim.args)
            ioa_list = map(self.visit, prim.body)
            self.__check_list(ioa_list,
                              eq_one=[IOA.SIGNATURE, IOA.STATES,
                                      IOA.TRANSITIONS],
                              leq_one=[IOA.WHERE, IOA.INITIALLY, IOA.TRAJECTORIES],
                              optional=[IOA.INVARIANT])
        return IOA.AUTOMATON

    def visit_Composition(self, comp):
        assert isinstance(comp, ast.FunctionDef)

        with IOAScopeHandler(self.__scope, IOA.COMPOSITION):
            parameters = self.visit(comp.args)
            ioa_list = map(self.visit, comp.body)
            self.__check_list(ioa_list,
                              eq_one=[IOA.COMPONENTS],
                              leq_one=[IOA.WHERE],
                              optional=[IOA.INVARIANT])
        return IOA.COMPOSITION

    def visit_ComponentList(self, comp_list):
        assert isinstance(comp_list, ast.ClassDef)

        with IOAScopeHandler(self.__scope, IOA.COMPONENTS):
            ioa_list = map(self.visit, comp_list.body)
            self.__check_list(ioa_list,
                              geq_one=[IOA.DECL_COMPONENT],
                              leq_one=[IOA.HIDDEN])
        return IOA.COMPONENTS

    def visit_Component(self, lhs, typ, rhs):
        assert lhs == IOA.IDENTIFIER
        assert isinstance(typ, ast.expr)
        assert rhs is None
        # TODO
        with IOAScopeHandler(self.__scope, IOA.DECL_COMPONENT):
            self.visit(typ)

        return IOA.DECL_COMPONENT

    def visit_DeclStateVar(self, lhs, typ, rhs):
        assert lhs == IOA.IDENTIFIER
        assert isinstance(typ, ast.expr)
        assert rhs is None or isinstance(rhs, ast.expr)
        # TODO
        with IOAScopeHandler(self.__scope, IOA.DECL_VAR):
            self.visit(typ)
            if rhs:
                self.visit(rhs)
        return IOA.DECL_VAR

    def visit_FormalAction(self, act):
        assert isinstance(act, ast.FunctionDef)

        with IOAScopeHandler(self.__scope, IOA.FORMAL_ACT):
            parameters = self.visit(act.args)
            ioa_list = map(self.visit, act.body)
            self.__check_list(ioa_list,
                              leq_one=[IOA.WHERE],
                              optional=[IOA.PASS])
        # TODO
        return IOA.FORMAL_ACT

    def visit_Hidden(self, node):
        # TODO
        raise NotImplementedError("Hidden actions are not supported yet")
        return IOA.HIDDEN

    def visit_Initially(self, lhs, rhs_node):
        assert lhs == IOA.INITIALLY
        # TODO Check initial condition is bool
        return IOA.INITIALLY

    def visit_Invariant(self, lhs, rhs_node):
        assert lhs == IOA.INVARIANT
        # TODO Check invariant is bool
        return IOA.INVARIANT

    def visit_Precondition(self, pre):
        assert isinstance(pre, ast.expr)
        # TODO
        return IOA.PRE

    def visit_Shorthand(self, typ):
        """ Shorthand is to build new types via enumeration, tuple, or union.
            See IOA manual Sect. 23
        """
        assert isinstance(typ, ast.Call)
        # TODO
        return IOA.SHORTHAND

    def visit_Signature(self, sig):
        assert isinstance(sig, ast.ClassDef)
        with IOAScopeHandler(self.__scope, IOA.SIGNATURE):
            ioa_list = map(self.visit, sig.body)
            self.__check_list(ioa_list,
                              geq_one=[IOA.FORMAL_ACT])
        return IOA.SIGNATURE

    def visit_Simulation(self, node):
        # TODO
        return IOA.SIMULATION

    def visit_States(self, states):
        assert isinstance(states, ast.ClassDef)
        # TODO
        return IOA.STATES

    def visit_Trajectories(self, node):
        # TODO
        raise NotImplementedError("Trajectories are not supported now.")
        return IOA.TRAJECTORIES

    def visit_TransitionList(self, tran_list):
        assert isinstance(tran_list, ast.ClassDef)
        with IOAScopeHandler(self.__scope, IOA.TRANSITIONS):
            ioa_list = map(self.visit, tran_list.body)
            self.__check_list(ioa_list,
                              geq_one=[IOA.TRANSITION])
        return IOA.TRANSITIONS

    def visit_Transition(self, tran):
        assert isinstance(tran, ast.FunctionDef)
        with IOAScopeHandler(self.__scope, IOA.TRANSITION):
            ioa_list = map(self.visit_decorator, tran.decorator_list)
            self.__check_list(ioa_list,
                              one_of=[IOA.INPUT, IOA.OUTPUT, IOA.INTERNAL])
            parameters = self.visit(tran.args)
            ioa_list = map(self.visit, tran.body)
            self.__check_list(ioa_list,
                              optional=[IOA.ASSIGN, IOA.IF,
                                        IOA.FOR, IOA.PASS])
        # TODO
        return IOA.TRANSITION

    def visit_TypeDef(self, lhs, rhs):
        assert lhs == IOA.IDENTIFIER
        assert isinstance(rhs, ast.expr)
        with IOAScopeHandler(self.__scope, IOA.TYPE_DEF):
            # TODO Collect Type Information from rhs
            self.visit(rhs)
        return IOA.TYPE_DEF

    def visit_Where(self, lhs, rhs):
        assert lhs == IOA.WHERE
        assert isinstance(rhs, ast.expr)
        with IOAScopeHandler(self.__scope, IOA.WHERE):
            # TODO Check where clause is bool
            self.visit(rhs)
        return IOA.WHERE

    def visit_StmtAssign(self, lhs, rhs):
        assert isinstance(lhs, str)
        assert isinstance(rhs, ast.expr)
        with IOAScopeHandler(self.__scope, IOA.ASSIGN):
            # TODO
            self.visit(rhs)
        return IOA.ASSIGN
