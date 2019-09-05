import ast
import symtable
import unittest

from dione.frontend.ioa_constructs import IOA, IOAScopeHandler
from dione.frontend.translator_dafny import _IOANamespace, _ToDafnyVisitor

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
        ns = _IOANamespace(sym_tab)
        self._dfy_visitor = _ToDafnyVisitor(ns, 1)
        self._dfy_visitor._current_namespace.enter_automaton("TestAut")
        self._dfy_visitor._current_namespace.enter_transition("trans")

    def tearDown(self) -> None:
        self._dfy_visitor._current_namespace.exit()
        self._dfy_visitor._current_namespace.exit()

    def test_visit_Subscript(self):
        # Use single mode to test statements in an eff
        tree = ast.parse("arr[i] = arr[i-1] + 1", mode='single')
        self.assertEqual(self._dfy_visitor.visit(tree),
                         "var s: State := s.(arr:=s.arr[act.i := (s.arr[(act.i-1)]+1)]); s")

    def test_visit_Quantifier(self):
        # Use eval mode to test expressions in an eff
        tree = ast.parse("forall([i, j], 0 <= i < j < len(arr))", mode='eval')
        print(self._dfy_visitor.visit(tree))


if __name__ == '__main__':
    unittest.main()
