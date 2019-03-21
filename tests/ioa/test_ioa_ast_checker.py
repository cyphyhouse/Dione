import ast

from src.frontend.ioa_ast_checker import IOAAstChecker

f = open("tests/ioa/AsyncLCR.ioa.py").read()
tree = ast.parse(f)
IOAAstChecker().visit(tree)
