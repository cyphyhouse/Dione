""" AST visitor to traverse only the language constructs used for Input/Output
    Automata in a given Python AST
"""

import abc
import ast

from dione.frontend.ioa_constructs import IOA, IOAScope, IOAScopeHandler
from dione.frontend.ioa_ast_visitor_interface import IOAAstVisitorInterface


# TODO Decide in each visit function whether we give user AST root node itself
#  OR only the necessary subtrees that are used for IOA.
#  For example, visit_Signature only need the body and doesn't need
#  decorator_list and others

class DioneAstVisitor(IOAAstVisitorInterface, ast.NodeVisitor, abc.ABC):
    def __init__(self):
        self._scope = IOAScope()

    # region Top level Python AST node types
    def visit_Module(self, mod):
        """ Visit parsed AST from ast.parse in 'exec' mode """
        with IOAScopeHandler(self._scope, IOA.IOA_SPEC):
            return self.visit_ioa_spec(mod)

    def visit_Interactive(self, node):
        """ Visit parsed AST from ast.parse in 'single' mode
            This is can be used to test a single statement in eff
        """
        with IOAScopeHandler(self._scope, IOA.EFF):
            return self.visit(node.body)

    def visit_Expression(self, node):
        """ Visit parsed AST from ast.parse in 'single' mode
            This is can be used to test a single expression in eff
        """
        with IOAScopeHandler(self._scope, IOA.EFF):
            return self.visit(node.body)

    # endregion

    # region Python statements
    def visit_AnnAssign(self, node):
        """ Variable annotated with type hints and followed by an optional assigned value. """
        if not isinstance(node.target, ast.Name):
            # TODO Allow subscription expressions (e.g., sequence, map, etc.) or member access
            raise NotImplementedError("Left-hand side must be an identifier for now.")

        if self._scope == IOA.IOA_SPEC:
            if isinstance(node.annotation, ast.Name) and node.annotation.id == str(IOA.TYPE):
                assert node.value
                with IOAScopeHandler(self._scope, IOA.TYPE_DEF):
                    return self.visit_ioa_type_def(node.target, node.value)
        if self._scope == IOA.STATES:
            if not isinstance(node.target, ast.Name):
                raise ValueError("Left-hand side must be an identifier for declaring state variables.")
            with IOAScopeHandler(self._scope, IOA.DECL_VAR):
                return self.visit_ioa_decl_state_var(node.target, node.annotation, node.value)
        if self._scope == IOA.COMPONENTS:
            with IOAScopeHandler(self._scope, IOA.DECL_COMPONENT):
                return self.visit_ioa_decl_component(node.target, node.annotation, node.value)
        # else:
        raise ValueError("Unexpected typed variable\"" + node.target.id +
                         "\" when specifying " + self._scope.value)

    def visit_Assign(self, node):
        """ Assignment without type hints """
        assert node.targets
        if len(node.targets) > 1:
            # TODO allow multiple assignment?
            raise NotImplementedError("Multiple assignment is not supported yet.")
        if self._scope == IOA.EFF:
            return self.visit_ioa_stmt_assign(node.targets[0], node.value)

        if not isinstance(node.targets[0], ast.Name):
            raise NotImplementedError(
                "Left-hand side must be an identifier except in eff block.")
        lhs_str = node.targets[0].id
        if self._scope == IOA.AUTOMATON:
            if lhs_str == str(IOA.INITIALLY):
                with IOAScopeHandler(self._scope, IOA.INITIALLY):
                    return self.visit_ioa_initially(node.value)
            if lhs_str == str(IOA.INVARIANT_OF):
                with IOAScopeHandler(self._scope, IOA.INVARIANT_OF):
                    return self.visit_ioa_invariant(node.value)
            if lhs_str == str(IOA.WHERE):
                with IOAScopeHandler(self._scope, IOA.WHERE):
                    return self.visit_ioa_automaton_where(node.value)
        if self._scope == IOA.COMPOSITION:
            if lhs_str == str(IOA.INVARIANT_OF):
                with IOAScopeHandler(self._scope, IOA.INVARIANT_OF):
                    return self.visit_ioa_invariant(node.value)
            if lhs_str == str(IOA.WHERE):
                with IOAScopeHandler(self._scope, IOA.WHERE):
                    return self.visit_ioa_automaton_where(node.value)
        if self._scope == IOA.FORMAL_ACT:
            if lhs_str == str(IOA.WHERE):
                with IOAScopeHandler(self._scope, IOA.WHERE):
                    return self.visit_ioa_action_where(node.value)
        # else:
        if self._scope == IOA.STATES:
            raise ValueError("Type of \"" + lhs_str +
                             "\" is required for specifying " + self._scope.value)
        raise ValueError("Unexpected assignment to \"" + lhs_str +
                         "\" when specifying " + self._scope.value)

    def visit_Call(self, call):
        if self._scope == IOA.TRANSITION:
            if isinstance(call.func, ast.Name) and call.func.id == str(IOA.PRE):
                assert call.args and len(call.args) == 1
                with IOAScopeHandler(self._scope, IOA.PRE):
                    return self.visit_ioa_precondition(call.args[0])
        if self._scope == IOA.DECL_COMPONENT:
            with IOAScopeHandler(self._scope, IOA.AUTOMATON_INSTANCE):
                return self.visit_ioa_automaton_instance(call)
        if self._scope == IOA.EFF or \
                self._scope == IOA.PRE or \
                self._scope == IOA.INITIALLY or \
                self._scope == IOA.INVARIANT_OF or \
                self._scope == IOA.WHERE:
            return self.visit_ioa_external_call(call)
        # else:
        if isinstance(call.func, ast.Name):
            func = call.func.id
        else:
            func = str(call.func)
        raise ValueError("Unexpected call to \"" + func +
                         "\" when specifying " + self._scope.value)

    def visit_ClassDef(self, class_def):
        if self._scope == IOA.AUTOMATON:
            if class_def.name == str(IOA.SIGNATURE):
                with IOAScopeHandler(self._scope, IOA.SIGNATURE):
                    return self.visit_ioa_signature(class_def)
            if class_def.name == str(IOA.STATES):
                with IOAScopeHandler(self._scope, IOA.STATES):
                    return self.visit_ioa_states(class_def)
            if class_def.name == str(IOA.TRANSITIONS):
                with IOAScopeHandler(self._scope, IOA.TRANSITIONS):
                    return self.visit_ioa_transition_list(class_def)
            if class_def.name == str(IOA.TRAJECTORIES):
                with IOAScopeHandler(self._scope, IOA.TRAJECTORIES):
                    return self.visit_ioa_trajectories(class_def)
        if self._scope == IOA.COMPOSITION:
            if class_def.name == str(IOA.COMPONENTS):
                with IOAScopeHandler(self._scope, IOA.COMPONENTS):
                    return self.visit_ioa_component_list(class_def)
            if class_def.name == str(IOA.HIDDEN):
                with IOAScopeHandler(self._scope, IOA.HIDDEN):
                    return self.visit_ioa_hidden(class_def)
        # else:
        raise ValueError("Unexpected class \"" + class_def.name +
                         "\" when specifying " + self._scope.value)

    def visit_For(self, stmt):
        return self.visit_ioa_stmt_for(stmt)

    def visit_FunctionDef(self, func_def):
        if not func_def.decorator_list:
            raise ValueError("A decorator is expected for function \"" +
                             func_def.name + "\" when specifying " +
                             self._scope.value)

        if self._scope == IOA.IOA_SPEC:
            if len(func_def.decorator_list) > 1:
                raise ValueError("Only one decorator is expected for \"" +
                                 func_def.name + "\"")
            assert isinstance(func_def.decorator_list[0], ast.Name)
            deco = func_def.decorator_list[0].id
            if deco == str(IOA.COMPOSITION):
                with IOAScopeHandler(self._scope, IOA.COMPOSITION):
                    return self.visit_ioa_composite_automaton(func_def)
            if deco == str(IOA.AUTOMATON):
                with IOAScopeHandler(self._scope, IOA.AUTOMATON):
                    return self.visit_ioa_primitive_automaton(func_def)
            if deco == str(IOA.SIMULATION):
                with IOAScopeHandler(self._scope, IOA.SIMULATION):
                    return self.visit_ioa_simulation(func_def)
            # else:
            raise ValueError("Unexpected decorator \"" + deco +
                             "\" for \"" + func_def.name + "\"")
        if self._scope == IOA.SIGNATURE:
            with IOAScopeHandler(self._scope, IOA.FORMAL_ACT):
                return self.visit_ioa_formal_action(func_def)
        if self._scope == IOA.TRANSITIONS:
            with IOAScopeHandler(self._scope, IOA.TRANSITION):
                return self.visit_ioa_transition(func_def)
        # else:
        raise ValueError("Unexpected function \"" + func_def.name +
                         "\" when specifying " + self._scope.value)

    def visit_If(self, stmt):
        return self.visit_ioa_stmt_if(stmt)

    def visit_Expr(self, stmt):
        """ Expression as a statement"""
        return self.visit(stmt.value)

    def visit_Pass(self, stmt):
        return self.visit_ioa_stmt_pass(stmt)
    # endregion

    # region Python expressions
    def visit_Name(self, name):
        construct = IOA.get(name.id, None)
        # Check if name is a not reserved word
        if not construct:
            return self.visit_ioa_identifier(name)
        # name.id is a reserved word
        if self._scope == IOA.FORMAL_ACT or \
                self._scope == IOA.TRANSITION:
            if construct in [IOA.INPUT, IOA.INTERNAL, IOA.OUTPUT]:
                return self.visit_ioa_action_type(construct)
            raise ValueError("Unexpected action type \"" + name.id + "\"")
        # else:
        raise ValueError("Reserved word \"" + name.id + "\" is used as an identifier")

    def visit_Subscript(self, exp):
        if self._scope == IOA.TYPE_DEF:
            with IOAScopeHandler(self._scope, IOA.SHORTHAND):
                return self.visit_ioa_shorthand(exp)
        if self._scope in \
                [IOA.TYPE_DEF, IOA.FORMAL_PARA, IOA.DECL_VAR]:
            assert not isinstance(exp.ctx, ast.Store) \
                and not isinstance(exp.ctx, ast.AugStore)
            return self.visit_TypeHint(exp)
        # else:
        return self.visit_Select(exp)

    def visit_TypeHint(self, exp):
        pass

    def visit_Select(self, exp):
        pass

    def visit_comprehension(self, comprehension):
        pass

    def visit_arguments(self, arguments):
        if arguments.vararg or arguments.kwonlyargs or \
                arguments.kw_defaults or arguments.kwarg or \
                arguments.defaults:
            # FIXME more precise error message
            raise ValueError("Unexpected formal parameter specification for "
                             + str(self._scope))
        with IOAScopeHandler(self._scope, IOA.FORMAL_PARA_LIST):
            return self.visit_ioa_formal_para_list(arguments.args)

    def visit_arg(self, arg):
        if self._scope == IOA.FORMAL_PARA_LIST:
            with IOAScopeHandler(self._scope, IOA.FORMAL_PARA):
                return self.visit_ioa_formal_para(arg)
        if self._scope == IOA.ACTUAL_PARA_LIST:
            with IOAScopeHandler(self._scope, IOA.ACTUAL_PARA):
                return self.visit_ioa_actual_para(arg)
        raise AssertionError("Should be unreachable")  # FIXME error message

    def visit_list(self, ls):
        # FIXME It may be really confusing, but only the body of eff or a block,
        #  that is, a list of stmts, is handled by this function.
        #  Other lists currently have to be handled
        #  explicitly when implementing each visit function.
        if self._scope == IOA.TRANSITION or \
                self._scope == IOA.EFF:
            assert all(isinstance(s, ast.stmt) for s in ls)
            with IOAScopeHandler(self._scope, IOA.EFF):
                return self.visit_ioa_effect(ls)
        # else:
        raise ValueError("Unexpected list " + str(ls) +
                         " when specifying " + self._scope.value)
    # endregion
