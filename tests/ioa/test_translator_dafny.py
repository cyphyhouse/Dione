import ast

from src.frontend.translator_dafny import TranslatorDafny

f = open("tests/ioa/AsyncLCR.ioa.py").read()
tree = ast.parse(f)
print(TranslatorDafny().visit(tree))