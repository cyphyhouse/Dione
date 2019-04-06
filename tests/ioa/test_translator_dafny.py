from src.frontend.translator_dafny import TranslatorDafny

translator = TranslatorDafny("tests/ioa/AsyncLCR.ioa.py")
print(translator.get_dafny_code())
