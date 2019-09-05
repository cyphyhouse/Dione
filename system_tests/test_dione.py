import ast

from dione.frontend.ioa_ast_checker import IOAAstChecker
from dione.frontend.translator_dafny import TranslatorDafny

with open("system_tests/ioa_examples/AsyncLCR.ioa.py") as file:
    tree = ast.parse(file.read())
    IOAAstChecker().visit(tree)

    file.seek(0)
    translator = TranslatorDafny(file)
    print(translator.get_dafny_code())
