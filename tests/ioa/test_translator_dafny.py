from src.frontend.translator_dafny import TranslatorDafny

with open("tests/ioa/AsyncLCR.ioa.py") as file:
    translator = TranslatorDafny(file)
    print(translator.get_dafny_code())
