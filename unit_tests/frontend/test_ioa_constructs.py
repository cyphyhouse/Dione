import unittest

from dione.frontend.ioa_constructs import IOA, IOAScope, IOAScopeHandler


class TestIOA(unittest.TestCase):
    def test_auto_generate_value(self):
        is_internal = False
        for ioa in IOA:
            if ioa == IOA._REGION_INTERNAL:
                is_internal = True

            expected = ("$" if is_internal else "") + ioa.name.lower()
            self.assertEqual(expected, ioa.value)


class TestIOAScope(unittest.TestCase):
    # TODO
    pass


class TestIOAScopeHandler(unittest.TestCase):
    # TODO
    pass


if __name__ == '__main__':
    unittest.main()
