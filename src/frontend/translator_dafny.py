""" Translator from IOA to Dafny proof assistant """
import ast
from typing import List, Optional

from src.frontend.ioa_ast_visitor import IOAAstVisitor


class TranslatorDafny(IOAAstVisitor):
    def __init__(self):
        super().__init__()
        self.__parameters = ""

    def __automaton_module(self, aut: ast.FunctionDef) -> str:
        ret = "module " + aut.name + " {\n"

        self.__parameters = self.visit(aut.args)
        if self.__parameters:
            ret += "datatype Parameter = Parameter(" + self.__parameters + ")\n"

        for stmt in aut.body:
            ret += self.visit(stmt) + "\n"

        ret += "}\n"
        return ret

    def visit_BoolOp(self, exp) -> str:
        op_str = self.visit(exp.op)
        return "(" + op_str.join(map(self.visit, exp.values)) + ")"

    def visit_BinOp(self, exp) -> str:
        return "(" + \
               self.visit(exp.left) + \
               self.visit(exp.op) + \
               self.visit(exp.right) + \
               ")"

    def visit_UnaryOp(self, exp) -> str:
        return "(" + self.visit(exp.op) + self.visit(exp.operand) + ")"

    def visit_Lambda(self, exp):
        raise NotImplementedError("\"lambda\" expression is not supported yet")

    def visit_IfExp(self, exp):
        raise NotImplementedError("ITE expression is not supported yet")

    def visit_Dict(self, exp):
        raise NotImplementedError("Dictionary expression is not supported yet")

    def visit_Set(self, exp):
        raise NotImplementedError("Finite set expression is not supported yet")

    def visit_ListComp(self, exp):
        raise NotImplementedError("List comprehension expression is not supported yet")

    def visit_SetComp(self, exp):
        raise NotImplementedError("Set comprehension expression is not supported yet")

    def visit_DictComp(self, exp):
        raise NotImplementedError("Dictionary comprehension expression is not supported yet")

    def visit_GeneratorExp(self, exp):
        raise RuntimeError("Generator expression will not be supported")

    def visit_Await(self, exp):
        raise RuntimeError("\"await\" expression will not be supported")

    def visit_Yield(self, exp):
        raise RuntimeError("\"yield\" expression will not be supported")

    def visit_YieldFrom(self, exp):
        raise RuntimeError("\"yield from\" expression will not be supported")

    def visit_Compare(self, exp) -> str:
        ret = "(" + self.visit(exp.left)
        for o, e in zip(exp.ops, exp.comparators):
            ret += self.visit(o) + self.visit(e)
        ret += ")"
        return ret

    def visit_Call(self, exp):
        return super().visit_Call(exp)

    def visit_Num(self, exp):
        raise NotImplementedError

    def visit_Str(self, exp):
        raise NotImplementedError

    def visit_FormattedValue(self, exp):
        raise NotImplementedError

    def visit_JoinedStr(self, exp):
        raise NotImplementedError

    def visit_Bytes(self, exp):
        raise NotImplementedError

    def visit_NameConstant(self, exp):
        raise NotImplementedError

    def visit_Ellipsis(self, exp):
        raise NotImplementedError

    def visit_Constant(self, exp):
        raise NotImplementedError

    def visit_Attribute(self, exp):
        # TODO
        return "ATTR_EXP"

    def visit_Subscript(self, exp) -> str:
        # TODO
        return "SUBSCRIPT_EXP"

    def visit_Starred(self, exp):
        raise NotImplementedError

    def visit_Name(self, exp):
        return super().visit_Name(exp)

    def visit_List(self, exp) -> str:
        return "[" + ", ".join(map(self.visit, exp.elts)) + "]"

    def visit_Tuple(self, exp):
        raise NotImplementedError

    def visit_Slice(self, slc):
        raise NotImplementedError

    def visit_ExtSlice(self, slc):
        raise NotImplementedError

    def visit_Index(self, slc):
        raise NotImplementedError

    def visit_And(self, _) -> str:
        return "&&"

    def visit_Or(self, _) -> str:
        return "||"

    def visit_Add(self, _) -> str:
        return "+"

    def visit_Sub(self, _) -> str:
        return "-"

    def visit_Mult(self, _) -> str:
        return "*"

    def visit_MatMult(self, _):
        raise RuntimeError("Matrix multiplication will not be supported")

    def visit_Div(self, _) -> str:
        return "/"

    def visit_Mod(self, _) -> str:
        return "%"

    def visit_Pow(self, _):
        raise RuntimeError("Exponentiation will not be supported")

    def visit_LShift(self, _) -> str:
        return "<<"

    def visit_RShift(self, _) -> str:
        return ">>"

    def visit_BitOr(self, _) -> str:
        return "|"

    def visit_BitXor(self, _) -> str:
        return "^"

    def visit_BitAnd(self, _) -> str:
        return "&"

    def visit_FloorDiv(self, _):
        raise RuntimeError("Floor division will not be supported")

    def visit_Invert(self, _) -> str:
        """ Bitwise invert"""
        import warnings
        warnings.warn("Bitwise invert is only applicable to bit-vectors in Dafny", RuntimeWarning)
        return "!"

    def visit_Not(self, _) -> str:
        return "!"

    def visit_UAdd(self, _) -> str:
        import warnings
        warnings.warn("Unary plus sign is ignored", RuntimeWarning)
        return ""

    def visit_USub(self, _) -> str:
        return "-"

    def visit_Eq(self, _) -> str:
        return "=="

    def visit_NotEq(self, _) -> str:
        return "!="

    def visit_Lt(self, _) -> str:
        return "<"

    def visit_LtE(self, _) -> str:
        return "<="

    def visit_Gt(self, _) -> str:
        return ">"

    def visit_GtE(self, _) -> str:
        return ">="

    def visit_Is(self, _) -> str:
        raise RuntimeError("\"is\" operator will not be supported")

    def visit_IsNot(self, _) -> str:
        raise RuntimeError("\"is not\" operator will not be supported")

    def visit_In(self, _) -> str:
        return "in"

    def visit_NotIn(self, _) -> str:
        return "!in"

    # IOA specific language constructs
    def visit_IOASpec(self, spec: ast.Module) -> str:
        ret = ""
        for stmt in spec.body:
            ret += self.visit(stmt)
        # TODO
        return ret

    def visit_TypeDef(self, lhs: ast.expr, rhs: ast.expr) -> str:
        # TODO
        return ""

    def visit_Composition(self, comp: ast.FunctionDef) -> str:
        return self.__automaton_module(comp)

    def visit_ComponentList(self, comp_list: ast.ClassDef):
        # TODO
        return ""

    def visit_PrimitiveAutomaton(self, prim: ast.FunctionDef) -> str:
        return self.__automaton_module(prim)

    def visit_FormalParameters(self, para_list: List[ast.arg]) -> str:
        # TODO
        return ", ".join(map(self.visit, para_list))

    def visit_FormalPara(self, para: ast.arg) -> str:
        assert para.annotation
        return para.arg + ": " + self.visit(para.annotation)

    def visit_Signature(self, sig: ast.ClassDef) -> str:
        # TODO Collect actions for creating the global set of actions
        return ""

    def visit_States(self, states: ast.ClassDef) -> str:
        ret = "datatype State = State("
        ret += ", ".join(map(self.visit, states.body))
        ret += ")"
        return ret

    def visit_DeclStateVar(self, lhs: ast.expr, typ: ast.expr,
                           rhs: Optional[ast.expr]) -> str:
        assert isinstance(lhs, ast.Name)
        # AST should have been preprocessed so that initial values are
        # specified via initially predicate
        assert rhs is None  # TODO error message

        return lhs.id + ": " + self.visit(typ)

    def visit_TransitionList(self, tran_list: ast.ClassDef) -> str:
        # TODO
        return ""

    def visit_Initially(self, cond: ast.expr) -> str:
        add_para = ", para: Parameter" if self.__parameters else ""
        return "predicate Initial(s: State" + add_para + ") { " + \
               self.visit(cond) + \
               " }\n"

    def visit_Invariant(self, cond: ast.expr) -> str:
        add_para = ", para: Parameter" if self.__parameters else ""
        return "predicate Invariant(s: State" + add_para + ") { " + \
               self.visit(cond) + \
               " }\n"

    def visit_Where(self, cond: ast.expr) -> str:
        # TODO
        return ""

    def visit_Identifier(self, name: str) -> str:
        # TODO Are there more built-in types to translate?
        return {"Char": "char",
                "Int": "int",
                "Nat": "nat",
                "Real": "real",
                "Seq": "seq",
                "Map": "map",
                "Set": "set",
                "Mset": "multiset",
                }.get(name, name)

    def visit_ExternalCall(self, call: ast.Call) -> str:
        assert not call.keywords
        dafny_op = {"forall": "forall",
                    "exists": "exists",
                    "implies": "==>",
                    "explies": "<==",
                    "disjoint": "!!",
                    }
        # TODO use built-in operators
        return self.visit(call.func) + "(" + \
               ", ".join(map(self.visit, call.args)) + ")"
