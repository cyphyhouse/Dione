import ast
import symtable
import unittest

from src.frontend.ioa_constructs import IOA, IOAScopeHandler
from src.frontend.translator_dafny import _ToDafnyVisitor

_test_ioa = """
@automaton
def TestAut(N: int):
    class signature:
        @internal
        def trans(i: int): pass

    class states:
        arr: Seq[int]
"""


class Test_ToDafnyVisitor(unittest.TestCase):
    def setUp(self) -> None:
        """ Setup the symbol table for Dafny Visitor
            Notice that no transition are provided
        """
        sym_tab = symtable.symtable(_test_ioa, "<unknown>", 'exec')
        self._dfy_visitor = _ToDafnyVisitor(sym_tab, 1)

    def test_visit_Subscript(self):
        # Use single mode to test statements in an eff
        tree = ast.parse("arr[i] = 0", mode='single')
        print(self._dfy_visitor.visit(tree))


if __name__ == '__main__':
    unittest.main()
