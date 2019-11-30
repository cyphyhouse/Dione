""" AST visitor to traverse only the language constructs used for Input/Output
    Automata in a given Python AST
    This is for the simplified language Dio
"""

import abc
import ast
from typing import List

from dione.frontend.ioa_ast_visitor_interface import IOAAstVisitorInterface
from dione.frontend.ioa_constructs import IOA, IOAScope, IOAScopeHandler


class DioAstVisitor(IOAAstVisitorInterface, ast.NodeVisitor, abc.ABC):
    def __init__(self):
        self._scope = IOAScope()

    def _get_decorator_names(self, deco_list: List[ast.expr]) -> List[str]:
        ret = []
        for deco in deco_list:
            if isinstance(deco, ast.Name):
                ret.append(deco.id)
            elif isinstance(deco, ast.Call) and isinstance(deco.func, ast.Name):
                ret.append(deco.func.id)
            else:
                raise ValueError("Unexpected decorator \"" + str(deco) +
                                 "\" when specifying " + self._scope.value)
        return ret

    # region Top level Python AST node types
    def visit_Module(self, mod: ast.Module):
        """ Visit parsed AST from ast.parse in 'exec' mode """
        with IOAScopeHandler(self._scope, IOA.IOA_SPEC):
            return self.visit_ioa_spec(mod)

    def visit_Interactive(self, node: ast.Interactive):
        """ Visit parsed AST from ast.parse in 'single' mode
            This is can be used to test a single statement in eff
        """
        with IOAScopeHandler(self._scope, IOA.EFF):
            return self.visit(node.body)

    def visit_Expression(self, node: ast.Expression):
        """ Visit parsed AST from ast.parse in 'single' mode
            This is can be used to test a single expression in eff
        """
        with IOAScopeHandler(self._scope, IOA.EFF):
            return self.visit(node.body)

    def visit_Suite(self, node: ast.Suite):
        raise NotImplementedError
    # endregion

    # region Python statements
    def visit_FunctionDef(self, func_def: ast.FunctionDef):
        """ Function Definitions are used to specify automata or actions"""
        if not func_def.decorator_list:
            raise ValueError("A decorator is expected for function \"" +
                             func_def.name + "\" when specifying " +
                             self._scope.value)
        deco_name_list = self._get_decorator_names(func_def.decorator_list)
        if self._scope == IOA.IOA_SPEC:
            deco_name_set = set(IOA.get(d, None) for d in deco_name_list)
            ioa_scope_set = deco_name_set & {IOA.COMPOSITION, IOA.AUTOMATON, IOA.SIMULATION}
            if len(ioa_scope_set) != 1:
                raise ValueError("Conflicting decorators in \"" + str(deco_name_list) +
                                 "\" for \"" + func_def.name + "\"")
            # else:
            ioa_scope = ioa_scope_set.pop()
            with IOAScopeHandler(self._scope, ioa_scope):
                if ioa_scope == IOA.COMPOSITION:
                    return self.visit_ioa_composite_automaton(func_def)
                if ioa_scope == IOA.AUTOMATON:
                    return self.visit_ioa_primitive_automaton(func_def)
                if ioa_scope == IOA.SIMULATION:
                    return self.visit_ioa_simulation(func_def)
        if self._scope == IOA.SIGNATURE:
            with IOAScopeHandler(self._scope, IOA.FORMAL_ACT):
                return self.visit_ioa_formal_action(func_def)
        if self._scope == IOA.TRANSITIONS:
            with IOAScopeHandler(self._scope, IOA.TRANSITION):
                return self.visit_ioa_transition(func_def)
        # else:
        raise ValueError("Unexpected function \"" + func_def.name +
                         "\" when specifying " + self._scope.value)

    def visit_Assign(self, node: ast.Assign):
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
        # else:
        if self._scope == IOA.STATES:
            raise ValueError("Type of \"" + lhs_str +
                             "\" is required for specifying " + self._scope.value)
        raise ValueError("Unexpected assignment to \"" + lhs_str +
                         "\" when specifying " + self._scope.value)

    # endregion
