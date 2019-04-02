""" Translator from IOA to Dafny proof assistant """
import ast
from typing import List, Optional, Tuple

from src.frontend.ioa_ast_visitor import IOAAstVisitor
from src.frontend.ioa_constructs import IOA


class TranslatorDafny(IOAAstVisitor):
    def __init__(self):
        super().__init__()
        self.__parameters = None
        self.__global_signature = {}

    def __automaton_module(self, aut: ast.FunctionDef) -> str:
        ret = "module " + aut.name + " {\n"

        ret += "import opened Types\n"  # Import type definitions

        self.__parameters = self.visit(aut.args)
        if self.__parameters:
            ret += "datatype Parameter = Parameter(" + \
                   self.__parameters + ")\n"

        for stmt in aut.body:
            # TODO Deal with where constraints
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
        if construct in [IOA.INPUT, IOA.OUTPUT, IOA.INTERNAL]:
            ret += "act: Action"
        elif construct in [IOA.INITIALLY, IOA.INVARIANT_OF]:
            ret += "s: State"
        elif construct in [IOA.EFF, IOA.PRE]:
            ret += "act: Action, s: State"
        else:
            assert construct == IOA.TRANSITIONS
            ret += "s: State, act: Action, s': State"
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
        if construct in [IOA.INPUT, IOA.OUTPUT, IOA.INTERNAL]:
            ret += "act"
        elif construct in [IOA.INITIALLY, IOA.INVARIANT_OF]:
            ret += "s"
        elif construct in [IOA.EFF, IOA.PRE]:
            ret += "act, s"
        else:
            assert construct == IOA.TRANSITIONS
            ret += "s, act, s'"
        if self.__parameters:
            ret += ", para"
        ret += ")"
        if construct in [IOA.EFF]:
            ret += " == s'"
        return ret

    # region Python expression visitors
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

    def visit_NameConstant(self, exp) -> str:
        if exp.value is True:
            return "true"
        if exp.value is False:
            return "false"
        # else:
        raise RuntimeError("Unsupported Python constant" + str(exp.value))

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
        # FIXME We can also do this case split in IOAAstVisitor, for example,
        #  call visit_GenericType() or visit_ExprSubscript() based on cases
        if self._get_scope() in \
                [IOA.TYPE_DEF, IOA.FORMAL_PARA, IOA.DECL_VAR]:
            # Angle brackets are used for parametrized type in Dafny
            return self.visit(exp.value) + "<" + self.visit(exp.slice) + ">"
        # else:
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

    # endregion

    # region IOA specific language constructs visitors
    def visit_IOASpec(self, spec: ast.Module) -> str:
        ret = ""
        for stmt in spec.body:
            ret += self.visit(stmt) + "\n"
        # TODO Group type definitions together and create a module for types

        return ret

    def visit_TypeDef(self, lhs: ast.expr, rhs: ast.expr) -> str:
        assert isinstance(lhs, ast.Name)
        return "type " + self.visit(lhs) + " = " + "TYPE_CONSTRUCTOR"  # TODO  self.visit(rhs)

    def visit_Composition(self, comp: ast.FunctionDef) -> str:
        return self.__automaton_module(comp)

    def visit_ComponentList(self, comp_list: ast.ClassDef) -> str:
        # TODO define states and assign parameter values
        states = "datatype State = State(" + "TODO_STATES" + ")"
        # TODO define transitions
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
            return ", ".join(map(self.visit, para_list))
        # else:
        return ""

    def visit_FormalPara(self, para: ast.arg) -> str:
        assert para.annotation
        return para.arg + ": " + self.visit(para.annotation)

    def visit_Signature(self, sig: ast.ClassDef) -> str:
        # FIXME This assumes a different return type than str
        act_iter = map(self.visit, sig.body)
        # Collect actions for creating the global set of actions
        for name, (sig, _, _) in act_iter:
            if self.__global_signature.get(name, sig) != sig:
                raise RuntimeError("Signature of action \"" + name + "\" doesn't match")
            self.__global_signature[name] = sig
        # Construct input, output, and internal predicates
        pred_dict = {"input": "false",
                     "output": "false",
                     "internal": "false"}
        for name, (sig, typ, where) in act_iter:
            pred = "act." + name + "?"
            if where:
                pred += "&&" + where
            pred_dict[typ] += "||(" + pred + ")"
        ret = ""
        for typ, pred_body in pred_dict.items():
            ret += self.__func_signature(IOA.get(typ, None)) + \
                "{" + pred_body + "}\n"
        return ret

    def visit_FormalAction(self, act: ast.FunctionDef) \
            -> Tuple[str, Tuple[str, str, str]]:
        assert len(act.decorator_list) == 1
        act_typ = self.visit(act.decorator_list[0])
        act_sig = act.name + "(" + self.visit(act.args) + ")"
        assert len(act.body) == 1
        act_where = self.visit(act.body[0])
        # FIXME If possible, return a string like other functions
        return act.name, (act_sig, act_typ, act_where)

    def visit_States(self, states: ast.ClassDef) -> str:
        ret = "datatype State = State("
        ret += ", ".join(map(self.visit, states.body))
        ret += ")"
        return ret

    def visit_DeclStateVar(self, lhs: ast.expr, typ: ast.expr,
                           rhs: Optional[ast.expr]) -> str:
        assert isinstance(lhs, ast.Name)
        # FIXME This assumes that AST should have been preprocessed so that
        #  initial values are specified only via initially predicate
        assert rhs is None  # TODO error message

        return lhs.id + ": " + self.visit(typ)

    def visit_TransitionList(self, tran_list: ast.ClassDef) -> str:
        # TODO different names to allow multiple (pre, eff) for the same action
        def _gen_name(act):
            return "pre_" + act, "eff_" + act

        # FIXME This assumes a different return type than str
        tran_iter = map(self.visit, tran_list.body)
        ret = ""
        tran_rel_body = "false"
        for name, (pre_body, eff_body) in tran_iter:
            pre_name, eff_name = _gen_name(name)
            ret += self.__func_signature(IOA.PRE, pre_name) + \
                "{" + pre_body + "}\n"
            ret += self.__func_signature(IOA.EFF, eff_name) + \
                "{\n" + eff_body + "\n}\n"
            tran_rel_body += "\n || (" + \
                self.__func_call(IOA.PRE, pre_name) + " && " + \
                self.__func_call(IOA.EFF, eff_name) + ")"

        ret += self.__func_signature(IOA.TRANSITIONS) + \
            "{\n" + tran_rel_body + "\n}\n"
        return ret

    def visit_Transition(self, tran: ast.FunctionDef) -> Tuple[str, Tuple[str, str]]:
        assert tran.decorator_list  # At least one decorator
        pre_body = "act." + tran.name + "?&&" + \
                   "&&".join(map(self.visit, tran.decorator_list))
        eff_body = self.visit(tran.body)
        # FIXME If possible, return a string like other functions
        return tran.name, (pre_body, eff_body)

    def visit_ActionType(self, act_typ: IOA) -> str:
        if self._get_scope() == IOA.FORMAL_ACT:
            return str(act_typ)
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
        return self.visit(cond)

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
        if self._get_scope() == IOA.EFF:
            return "s"  # return the same state
        # else:
        return ""

    def visit_Identifier(self, name: str) -> str:
        # TODO Automatically access variables from s, act, para
        return {"Char": "char",
                "Int": "int",
                "Nat": "nat",
                "Real": "real",
                "Seq": "seq",
                "Map": "map",
                "Set": "set",
                "Mset": "multiset",
                # Are there more built-in types to translate?
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

    # endregion
