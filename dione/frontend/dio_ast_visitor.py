""" AST visitor to traverse only the language constructs used for Input/Output
    Automata in a given Python AST
    This is for the simplified language Dio
"""

import abc
import ast
from dione.frontend.ioa_ast_visitor_interface import IOAAstVisitorInterface
from dione.frontend.ioa_constructs import IOA, IOAScope, IOAScopeHandler


class DioAstVisitor(IOAAstVisitorInterface, ast.NodeVisitor, abc.ABC):
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
