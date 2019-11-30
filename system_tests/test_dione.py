import ast

from dione.frontend.dione_ast_checker import DioneAstChecker
from dione.frontend.translator_dafny import TranslatorDafny

with open("system_tests/ioa_examples/AsyncLCR.ioa.py") as file:
    tree = ast.parse(file.read())
    DioneAstChecker().visit(tree)

    file.seek(0)
    translator = TranslatorDafny(file)
    print(translator.get_dafny_code())
