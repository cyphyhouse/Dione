""" Translator from IOA to Dafny proof assistant """
import ast
from typing import List, Optional

from src.frontend.ioa_ast_visitor import IOAAstVisitor
from src.frontend.ioa_constructs import IOA


class TranslatorDafny(IOAAstVisitor):
    def __init__(self):
        super().__init__()
        self.__parameters = None

    def __automaton_module(self, aut: ast.FunctionDef) -> str:
        ret = "module " + aut.name + " {\n"

        self.__parameters = self.visit(aut.args)
        ret += self.__parameters

        for stmt in aut.body:
            ret += self.visit(stmt) + "\n"

        ret += "}\n"
        return ret

    def __func_signature(self, construct, name=None):
        if construct not in [
                IOA.EFF, IOA.PRE, IOA.TRANSITIONS,
                IOA.INPUT, IOA.OUTPUT, IOA.INTERNAL,
                IOA.INITIALLY, IOA.INVARIANT_OF]:
            raise RuntimeError("Unexpected IOA construct")
        if not name:
            if construct in [IOA.PRE, IOA.EFF]:
                raise RuntimeError("Function name is required for precondition or effect")
            # else:
            name = str(construct)

        ret = ""
        if construct in [IOA.EFF]:
            ret += "function"
        else:
            ret += "predicate"
        ret += " " + name + "("
        if construct in \
                [IOA.EFF, IOA.PRE,
                 IOA.INPUT, IOA.OUTPUT, IOA.INTERNAL,
                 IOA.TRANSITIONS]:
            ret += "act: Action,"
        ret += "s: State"
        if construct == IOA.TRANSITIONS:
            ret += ", s': State"
        if self.__parameters:
            ret += ", para: Parameter"
        ret += ")"
        if construct in [IOA.EFF]:
            ret += ": State"
        return ret

    def __func_call(self, construct, name=None):
        if construct not in [
                IOA.EFF, IOA.PRE, IOA.TRANSITIONS,
                IOA.INPUT, IOA.OUTPUT, IOA.INTERNAL,
                IOA.INITIALLY, IOA.INVARIANT_OF]:
            raise RuntimeError("Unexpected IOA construct")
        if not name:
            if construct in [IOA.PRE, IOA.EFF]:
                raise RuntimeError("Function name is required for precondition or effect")
            # else:
            name = str(construct)

        ret = name + "("
        if construct in \
                [IOA.EFF, IOA.PRE,
                 IOA.INPUT, IOA.OUTPUT, IOA.INTERNAL,
                 IOA.TRANSITIONS]:
            ret += "act, "
        ret += "s"
        if construct == IOA.TRANSITIONS:
            ret += ", s'"
        if self.__parameters:
            ret += ", para"
        ret += ")"

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
        return str(exp.n)

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
        # Special case: printing 3.__abs__() is a syntax error,
        # so if t.value is an integer literal then we need to parenthesize it
        # to get (3).__abs__().
        if isinstance(exp.value, ast.Num) and isinstance(exp.value.n, int):
            ret = "(" + self.visit(exp.value) + ")"
        else:
            ret = self.visit(exp.value)
        ret += "." + exp.attr
        return ret

    def visit_Subscript(self, exp) -> str:
        # TODO Should use angle brackets for parametrized type in Dafny
        return self.visit(exp.value) + "[" + self.visit(exp.slice) + "]"

    def visit_Starred(self, exp):
        raise NotImplementedError

    def visit_Name(self, exp):
        return super().visit_Name(exp)

    def visit_List(self, exp) -> str:
        return "[" + ", ".join(map(self.visit, exp.elts)) + "]"

    def visit_Tuple(self, exp):
        raise NotImplementedError

    def visit_Slice(self, slc):
        ret = ""
        if slc.lower:
            ret += self.visit(slc.lower)
        ret += ".."
        if slc.upper:
            ret += self.visit(slc.lower)
        if slc.step:
            raise RuntimeError(
                "Dafny does not support step size in taking sub-sequences")
        return ret

    def visit_ExtSlice(self, slc):
        raise NotImplementedError

    def visit_Index(self, slc):
        return self.visit(slc.value)

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
        # TODO Group type definitions together
        return ret

    def visit_TypeDef(self, lhs: ast.expr, rhs: ast.expr) -> str:
        # TODO
        return ""

    def visit_Composition(self, comp: ast.FunctionDef) -> str:
        return self.__automaton_module(comp)

    def visit_ComponentList(self, comp_list: ast.ClassDef) -> str:
        # TODO how to define states and assign parameter values
        states = "datatype State = State()"
        return "\n".join(map(self.visit, comp_list.body)) + '\n' + states

    def visit_DeclComponent(self, lhs: ast.expr, typ: ast.expr,
                            rhs: Optional[ast.expr]) -> str:
        if not isinstance(lhs, ast.Name):
            raise NotImplementedError("Declaring a sequence of automata is not supported yet")
        name = self.visit(lhs)
        module = self.visit(typ)
        assert rhs is None
        return "import " + name + " = " + module

    def visit_AutomatonInstance(self, aut_inst: ast.Call) -> str:
        assert isinstance(aut_inst.func, ast.Name)
        # TODO how to return actual parameters for each component automaton
        return self.visit(aut_inst.func)

    def visit_PrimitiveAutomaton(self, prim: ast.FunctionDef) -> str:
        return self.__automaton_module(prim)

    def visit_FormalParameters(self, para_list: List[ast.arg]) -> str:
        if para_list:
            return "datatype Parameter = Parameter(" + \
                   ", ".join(map(self.visit, para_list)) + ")\n"
        # else:
        return ""

    def visit_FormalPara(self, para: ast.arg) -> str:
        assert para.annotation
        return para.arg + ": " + self.visit(para.annotation)

    def visit_Signature(self, sig: ast.ClassDef) -> str:
        # TODO Collect actions for creating the global set of actions
        for stmt in sig.body:
            self.visit(stmt)
        return ""

    def visit_FormalAction(self, act: ast.FunctionDef) -> str:
        # TODO
        list(map(self.visit, act.decorator_list))
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
        tran_rel = self.__func_signature(IOA.TRANSITIONS) + \
                   "{\n" + "RELATION_BODY" + "\n}\n"

        return "\n".join(map(self.visit, tran_list.body)) + "\n" + tran_rel

    def visit_Transition(self, tran: ast.FunctionDef) -> str:
        pred_pre = self.__func_signature(IOA.PRE, "pre_" + tran.name) + \
                   "{" + "act." + tran.name + "?&&" + \
                   "&&".join(map(self.visit, tran.decorator_list)) + "}\n"
        func_eff = self.__func_signature(IOA.EFF, "eff_" + tran.name) + \
                   "{\n" + self.visit(tran.body) + "\n}\n"
        return pred_pre + func_eff

    def visit_ActionType(self, act_typ: IOA) -> str:
        if self._get_scope() == IOA.FORMAL_ACT:
            return act_typ
        if self._get_scope() == IOA.TRANSITION:
            return self.__func_call(act_typ)

    def visit_Precondition(self, cond: ast.expr) -> str:
        return self.visit(cond)

    def visit_Effect(self, stmt_list: List[ast.stmt]) -> str:
        def __enclose(stmt) -> str:
            stmt_str = self.visit(stmt)
            return "var s: State := " + stmt_str + ";"

        return "\n".join(map(__enclose, stmt_list)) + " s"

    def visit_Initially(self, cond: ast.expr) -> str:
        return self.__func_signature(IOA.INITIALLY) + \
               "{ " + self.visit(cond) + " }\n"

    def visit_Invariant(self, cond: ast.expr) -> str:
        return self.__func_signature(IOA.INVARIANT_OF) + \
               "{ " + self.visit(cond) + " }\n"

    def visit_Where(self, cond: ast.expr) -> str:
        # TODO how to specify "where" constraint
        self.visit(cond)
        return ""

    def visit_StmtAssign(self, lhs: ast.expr, rhs: ast.expr) -> str:
        # TODO handle rhs differently to get state and parameter variables accordingly
        return "s.(" + \
               self.visit(lhs) + " := " + self.visit(rhs) + \
               ")"

    def visit_StmtIf(self, stmt: ast.If) -> str:
        return "if " + self.visit(stmt.test) + "\n" + \
               "then " + self.visit(stmt.body) + "\n" + \
               "else " + self.visit(stmt.orelse)

    def visit_StmtPass(self, stmt: ast.Pass) -> str:
        return "s"  # return the same state

    def visit_Identifier(self, name: str) -> str:
        # TODO Are there more built-in types to translate?
        # TODO Automatically access variables from s, act, para
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
