""" AST visitor to traverse only the language constructs used for Input/Output
    Automata in a given Python AST
"""

import ast
from src.frontend.ioa_constructs import IOA, IOAScope, IOAScopeHandler


class IOAAstVisitor(ast.NodeVisitor):
    def __init__(self):
        self.__scope = IOAScope()

    # Util functions
    def _get_scope(self):
        return self.__scope

    @staticmethod
    def _get_decorator_name(deco):
        if isinstance(deco, ast.Name):
            return deco.id
        if isinstance(deco, ast.Call) and isinstance(deco.func, ast.Name):
            return deco.func.id
        raise ValueError("Unexpect expression as a decorator")

    # Python language constructs
    def visit_AnnAssign(self, node):
        """ Variable annotated with type hints and followed by an optional assigned value. """
        if not isinstance(node.target, ast.Name):
            # TODO Allow subscription expressions (e.g., sequence, map, etc.) or member access
            raise NotImplementedError("Left-hand side must be an identifier for now.")

        if self.__scope == IOA.STATES:
            with IOAScopeHandler(self.__scope, IOA.DECL_VAR):
                return self.visit_DeclStateVar(node.target, node.annotation, node.value)
        if self.__scope == IOA.COMPONENTS:
            with IOAScopeHandler(self.__scope, IOA.DECL_COMPONENT):
                return self.visit_DeclComponent(node.target, node.annotation, node.value)
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

        lhs_str = node.targets[0].id
        if self.__scope == IOA.IOA_SPEC:
            with IOAScopeHandler(self.__scope, IOA.TYPE_DEF):
                return self.visit_TypeDef(node.targets[0], node.value)
        if self.__scope == IOA.AUTOMATON:
            if lhs_str == str(IOA.INITIALLY):
                with IOAScopeHandler(self.__scope, IOA.INITIALLY):
                    return self.visit_Initially(node.value)
            if lhs_str == str(IOA.INVARIANT):
                with IOAScopeHandler(self.__scope, IOA.INVARIANT):
                    return self.visit_Invariant(node.value)
            if lhs_str == str(IOA.WHERE):
                with IOAScopeHandler(self.__scope, IOA.WHERE):
                    return self.visit_Where(node.value)
        if self.__scope == IOA.COMPOSITION:
            if lhs_str == str(IOA.INVARIANT):
                with IOAScopeHandler(self.__scope, IOA.INVARIANT):
                    return self.visit_Invariant(node.value)
            if lhs_str == str(IOA.WHERE):
                with IOAScopeHandler(self.__scope, IOA.WHERE):
                    return self.visit_Where(node.value)
        if self.__scope == IOA.FORMAL_ACT:
            if lhs_str == str(IOA.WHERE):
                with IOAScopeHandler(self.__scope, IOA.WHERE):
                    return self.visit_Where(node.value)
        if self.__scope == IOA.EFF:
            return self.visit_StmtAssign(node.targets[0], node.value)
        # else:
        if self.__scope == IOA.STATES:
            raise ValueError("Type of \"" + lhs_str.value +
                             "\" is required for specifying " + self.__scope.value)
        raise ValueError("Unexpected assignment to \"" + lhs_str.value +
                         "\" when specifying " + self.__scope.value)

    def visit_Call(self, call):
        if self.__scope == IOA.TYPE_DEF:
            with IOAScopeHandler(self.__scope, IOA.SHORTHAND):
                return self.visit_Shorthand(call)
        if self.__scope == IOA.TRANSITION:
            if isinstance(call.func, ast.Name) and call.func.id == str(IOA.PRE):
                assert call.args and len(call.args) == 1
                with IOAScopeHandler(self.__scope, IOA.PRE):
                    return self.visit_Precondition(call.args[0])
        if self.__scope == IOA.EFF:
            raise NotImplementedError("Function call is not supported in eff yet")
        if self.__scope == IOA.DECL_COMPONENT:
            with IOAScopeHandler(self.__scope, IOA.AUTOMATON_INSTANCE):
                return self.visit_AutomatonInstance(call)
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
                with IOAScopeHandler(self.__scope, IOA.SIGNATURE):
                    return self.visit_Signature(class_def)
            if class_def.name == str(IOA.STATES):
                with IOAScopeHandler(self.__scope, IOA.STATES):
                    return self.visit_States(class_def)
            if class_def.name == str(IOA.TRANSITIONS):
                with IOAScopeHandler(self.__scope, IOA.TRANSITIONS):
                    return self.visit_TransitionList(class_def)
            if class_def.name == str(IOA.TRAJECTORIES):
                with IOAScopeHandler(self.__scope, IOA.TRAJECTORIES):
                    return self.visit_Trajectories(class_def)
        if self.__scope == IOA.COMPOSITION:
            if class_def.name == str(IOA.COMPONENTS):
                with IOAScopeHandler(self.__scope, IOA.COMPONENTS):
                    return self.visit_ComponentList(class_def)
            if class_def.name == str(IOA.HIDDEN):
                with IOAScopeHandler(self.__scope, IOA.HIDDEN):
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
            deco = self._get_decorator_name(func_def.decorator_list[0])
            if deco == str(IOA.COMPOSITION):
                with IOAScopeHandler(self.__scope, IOA.COMPOSITION):
                    return self.visit_Composition(func_def)
            if deco == str(IOA.AUTOMATON):
                with IOAScopeHandler(self.__scope, IOA.AUTOMATON):
                    return self.visit_PrimitiveAutomaton(func_def)
            if deco == str(IOA.SIMULATION):
                with IOAScopeHandler(self.__scope, IOA.SIMULATION):
                    return self.visit_Simulation(func_def)
            # else:
            raise ValueError("Unexpected decorator \"" + deco +
                             "\" for \"" + func_def.name + "\"")
        if self.__scope == IOA.SIGNATURE:
            with IOAScopeHandler(self.__scope, IOA.FORMAL_ACT):
                return self.visit_FormalAction(func_def)
        if self.__scope == IOA.TRANSITIONS:
            with IOAScopeHandler(self.__scope, IOA.TRANSITION):
                return self.visit_Transition(func_def)
        # else:
        raise ValueError("Unexpected function \"" + func_def.name +
                         "\" when specifying " + self.__scope.value)

    def visit_Module(self, mod):
        with IOAScopeHandler(self.__scope, IOA.IOA_SPEC):
            return self.visit_IOASpec(mod)

    def visit_Name(self, name):
        # Check if name is a not reserved word
        if not IOA.get(name.id, None):
            return self.visit_Identifier(name)
        # else:
        raise ValueError("Reserved word \"" + name.id + "\" is used as an identifier")

    def visit_arguments(self, arguments):
        if arguments.vararg or arguments.kwonlyargs or \
                arguments.kw_defaults or arguments.kwarg or \
                arguments.defaults:
            # FIXME more precise error message
            raise ValueError("Unexpected formal parameter specification for "
                             + str(self.__scope))
        with IOAScopeHandler(self.__scope, IOA.FORMAL_PARA_LIST):
            return self.visit_FormalParameters(arguments.args)

    def visit_arg(self, arg):
        if self.__scope == IOA.FORMAL_PARA_LIST:
            with IOAScopeHandler(self.__scope, IOA.FORMAL_PARA):
                return self.visit_FormalPara(arg)
        if self.__scope == IOA.ACTUAL_PARA_LIST:
            with IOAScopeHandler(self.__scope, IOA.ACTUAL_PARA):
                return self.visit_ActualPara(arg)
        raise AssertionError("Should be unreachable")  # FIXME error message

    def visit_list(self, ls):
        if self.__scope == IOA.AUTOMATON or self.__scope == IOA.COMPOSITION or \
                self.__scope == IOA.FORMAL_ACT:
            with IOAScopeHandler(self.__scope, IOA.FORMAL_PARA_LIST):
                return self.visit_FormalParameters(ls)
        if self.__scope == IOA.TRANSITION:
            assert all(isinstance(s, ast.stmt) for s in ls)
            with IOAScopeHandler(self.__scope, IOA.EFF):
                return self.visit_Effect(ls)
        # else:
        raise ValueError("Unexpected list " + str(ls) +
                         " when specifying " + self.__scope.value)

    # IOA specific language constructs
    def visit_IOASpec(self, spec):
        pass

    def visit_PrimitiveAutomaton(self, prim):
        pass

    def visit_AutomatonInstance(self, aut_inst):
        pass

    def visit_Composition(self, comp):
        pass

    def visit_ComponentList(self, comp_list):
        pass

    def visit_DeclStateVar(self, lhs, typ, rhs):
        pass

    def visit_DeclComponent(self, lhs, typ, rhs):
        pass

    def visit_Effect(self, stmt_list):
        pass

    def visit_FormalAction(self, act):
        pass

    def visit_FormalParameters(self, para_list):
        pass

    def visit_FormalPara(self, para):
        pass

    def visit_ActualParameters(self, para_list):
        pass

    def visit_ActualPara(self, para):
        pass

    def visit_Hidden(self, node):
        raise NotImplementedError("Hidden actions are not supported yet")

    def visit_Identifier(self, name):
        pass

    def visit_Signature(self, sig):
        pass

    def visit_Simulation(self, node):
        raise NotImplementedError("Simulations are not supported yet.")

    def visit_States(self, states):
        pass

    def visit_Trajectories(self, node):
        raise NotImplementedError("Trajectories are not supported now.")

    def visit_TransitionList(self, tran_list):
        pass

    def visit_Transition(self, tran):
        pass

    def visit_TypeDef(self, lhs, rhs):
        pass

    def visit_Initially(self, cond):
        pass

    def visit_Invariant(self, cond):
        pass

    def visit_Precondition(self, cond):
        pass

    def visit_Where(self, cond):
        pass

    def visit_StmtAssign(self, lhs, rhs):
        pass

    def visit_For(self, stmt):
        raise NotImplementedError("For-loops are not supported now.")

    def visit_If(self, stmt):
        pass

    def visit_Pass(self, stmt):
        pass

    def visit_Shorthand(self, typ):
        """ Shorthand is to build new types via enumeration, tuple, or union.
            See IOA manual Section 23
        """
        pass
