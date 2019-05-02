""" Translator from IOA to Dafny proof assistant """
import ast
from collections import namedtuple
import io
import symtable
from typing import List, Optional, Tuple

from src.frontend.ioa_ast_visitor import IOAAstVisitor
from src.frontend.ioa_constructs import IOA


class TranslatorDafny:
    def __init__(self, ioa_file: io.StringIO, k=1):
        if k <= 0:
            raise ValueError("Steps for invariant proof must be positive.")

        self.__ioa_file = ioa_file
        self.__dfy_code = None
        self.__k_steps = k

    def get_dafny_code(self) -> str:
        if self.__dfy_code:
            return self.__dfy_code

        ioa_code = self.__ioa_file.read()
        # TODO is there a better way to make sure the ioa_code
        #  is the same across all passes?
        prelude = ""  # TODO ""include \"Prelude.s.dfy\"\n"
        tree = ast.parse(ioa_code)
        sym_tab = symtable.symtable(ioa_code, self.__ioa_file.name, 'exec')
        ns = _IOANamespace(sym_tab)
        dfy_code = _ToDafnyVisitor(ns, self.__k_steps).visit(tree)
        self.__dfy_code = prelude + dfy_code
        return self.__dfy_code


class _IOANamespace:
    ioa2dfy = {"Bool": "bool",
               "Char": "char",
               "Int": "int",
               "Nat": "nat",
               "Real": "real",
               "Seq": "seq",
               "Map": "map",
               "Set": "set",
               "Mset": "multiset",
               # Python typing module
               "Sequence": "seq",
               "Mapping": "map",
               "Counter": "multiset",
               # Some hacking
               "disjoint": "disjoint",
               "max": "max",
               "range": "range",
               "incre": "incre",
               "decre": "decre",
               "bv_extract": "bv_extract",
               "i_min": "i_min",
               # Are there more built-in types to translate?
               }

    AutNamespace = namedtuple('AutNamespace', ['parameters', 'states',
                                               'act_formals', 'local_vars'])

    def __init__(self, sym_tab: symtable.SymbolTable):
        # FIXME Use another visitor to initialize namespaces
        #  This namespace may include not declared types and miss errors
        assert sym_tab.get_type() == "module"
        self.__ns_stack = []
        self.__system = \
            set(self.ioa2dfy.keys()) \
            | set(sym_tab.get_identifiers()) | set([e.value for e in IOA])

        self.__automaton = {}
        self.__act_formals = {}
        for aut_sym in sym_tab.get_children():
            # Collect automaton parameters
            assert isinstance(aut_sym, symtable.Function)
            aut_name = aut_sym.get_name()
            assert self.__system.isdisjoint(set(aut_sym.get_parameters()))
            parameters = set(aut_sym.get_parameters())

            # Collect state variables
            if str(IOA.STATES) in aut_sym.get_identifiers():
                states_sym = aut_sym.lookup(str(IOA.STATES)).get_namespace()
            elif str(IOA.COMPONENTS) in aut_sym.get_identifiers():
                states_sym = aut_sym.lookup(str(IOA.COMPONENTS)).get_namespace()
            elif False:  # TODO support simulation relations
                pass
            else:
                raise RuntimeError("Cannot find either states or components")
            states = \
                set(states_sym.get_identifiers()) \
                - parameters - self.__system
            self.__automaton[aut_name] = (parameters, states)

            if str(IOA.SIGNATURE) not in aut_sym.get_identifiers():
                continue
            # Collect all parameterized actions
            sig_sym = aut_sym.lookup(str(IOA.SIGNATURE)).get_namespace()
            for act_sym in sig_sym.get_children():
                assert isinstance(act_sym, symtable.Function)
                act_name = act_sym.get_name()
                assert set(act_sym.get_parameters()).isdisjoint(self.__system)
                assert set(act_sym.get_parameters()).isdisjoint(parameters)

                if not self.__act_formals.get(act_name, None):
                    self.__act_formals[act_name] = set(act_sym.get_parameters())
                assert self.__act_formals[act_name] == set(act_sym.get_parameters())

    def __push(self, curr_ns):
        self.__ns_stack.append(curr_ns)

    def enter_automaton(self, aut_name: str):
        parameters, states = self.__automaton[aut_name]
        new_ns = self.AutNamespace(parameters, states, set(), set())
        self.__push(new_ns)

    def enter_formal_action(self, act_name: str):
        assert self.__ns_stack
        curr_ns = self.__ns_stack[-1]
        act_formals = self.__act_formals[act_name]
        new_ns = self.AutNamespace(curr_ns.parameters,
                                   set(),  # states should not be used to declare actions
                                   act_formals, set())
        self.__push(new_ns)

    def enter_transition(self, act_name: str):
        assert self.__ns_stack
        curr_ns = self.__ns_stack[-1]
        act_formals = self.__act_formals[act_name]
        new_ns = self.AutNamespace(curr_ns.parameters,
                                   curr_ns.states,
                                   act_formals, set())
        self.__push(new_ns)

    def enter_quantification(self, var_list: List[str]):
        assert var_list
        assert self.__ns_stack
        curr_ns = self.__ns_stack[-1]
        new_local_vars = curr_ns.local_vars.copy() | set(var_list)
        new_ns = self.AutNamespace(curr_ns.parameters,
                                   curr_ns.states,
                                   curr_ns.act_formals,
                                   new_local_vars)
        self.__push(new_ns)

    def exit(self):
        assert self.__ns_stack
        self.__ns_stack.pop()

    def add_namespace(self, identifier: str) -> str:
        if self.__ns_stack:
            curr_ns = self.__ns_stack[-1]
            parameters, states, act_formals, local_vars = curr_ns
            if identifier in local_vars:
                return identifier
            if identifier in act_formals:
                return "act." + identifier
            if identifier in states:
                return "s." + identifier
            if identifier in parameters:
                return "para." + identifier
        # else:
        if identifier in self.__system:
            return self.ioa2dfy.get(identifier, identifier)
        raise RuntimeError("Unexpected identifier \"" + identifier + "\"")


class _ToDafnyVisitor(IOAAstVisitor):
    def __init__(self, ns: _IOANamespace, k: int):
        assert k > 0
        super().__init__()
        self.__k_steps = k
        self.__parameters = None
        self.__global_signature = {}
        self._current_namespace = ns
        self.__tmp_id_count = 0

    def __automaton_module(self, aut: ast.FunctionDef) -> str:
        body_list = ["import opened Types"]  # Import type definitions

        self.__parameters = self.visit(aut.args)
        if self.__parameters:
            body_list.append(
                "datatype Parameter = Parameter(" + self.__parameters + ")")

        for stmt in aut.body:
            # TODO Deal with where constraints over automaton parameters
            body_list.append(self.visit(stmt))

        body_list.append(self.__lemma_disjoint_actions())
        body_list.append(
            self.__func_name_args(IOA.SIGNATURE) +
            self.__body_block(
                self.__func_name_args(IOA.INPUT, type_hint=False) + "||" +
                self.__func_name_args(IOA.OUTPUT, type_hint=False) + "||" +
                self.__func_name_args(IOA.INTERNAL, type_hint=False),
                True)
        )
        return "module " + aut.name + self.__body_block("\n".join(body_list))

    def __func_name_args(
            self, construct, name=None, type_hint=True,
            curr_s="s", act="act", next_s="s'", para="para"
    ):
        if construct not in [
                IOA.WHERE,
                IOA.EFF, IOA.PRE, IOA.TRANSITIONS,
                IOA.INPUT, IOA.OUTPUT, IOA.INTERNAL, IOA.SIGNATURE,
                IOA.INITIALLY, IOA.INVARIANT_OF]:
            raise RuntimeError("Unexpected IOA construct")
        if not name:
            if construct in [IOA.PRE, IOA.EFF]:
                raise RuntimeError("Function name is required for precondition or effect")
            elif construct == IOA.WHERE:  # Avoid Dafny keyword "where"
                name = "automaton_where"
            else:
                name = str(construct)

        arg_list = []
        if construct in [IOA.EFF, IOA.PRE,
                         IOA.INITIALLY, IOA.INVARIANT_OF,
                         IOA.TRANSITIONS]:
            arg_list.append(curr_s + (": State" if type_hint else ""))
        if construct in [IOA.EFF, IOA.PRE,
                         IOA.INPUT, IOA.OUTPUT, IOA.INTERNAL, IOA.SIGNATURE,
                         IOA.TRANSITIONS]:
            arg_list.append(act + (": Action" if type_hint else ""))
        if construct in [IOA.TRANSITIONS]:
            arg_list.append(next_s + (": State" if type_hint else ""))
        if self.__parameters:
            arg_list.append(para + (": Parameter" if type_hint else ""))

        func_name_args = name + "(" + ", ".join(arg_list) + ")"
        if not type_hint:
            if construct in [IOA.EFF]:
                return func_name_args + "== s'"
            # else:
            return func_name_args
        if construct in [IOA.EFF]:
            return "function " + func_name_args + ": State"
        # else:
        return "predicate " + func_name_args

    @staticmethod
    def __body_block(body: str, one_line=False) -> str:
        if one_line:
            return "\n{ " + body + " }\n"
        else:
            return " {\n" + body + "\n}\n"

    def __lemma_disjoint_actions(self) -> str:
        arg_list = ["act: Action"]
        if self.__parameters:
            arg_list.append("para: Parameter")

        ret_list = ["lemma disjoint_actions_proof?(" + ", ".join(arg_list) + ")"]
        if self.__parameters:  # FIXME What if `where` clause is not specified
            ret_list.append("requires " +
                            self.__func_name_args(IOA.WHERE, type_hint=False))

        ret_list += [
            "ensures !(" +
            self.__func_name_args(IOA.INPUT, type_hint=False) + "&&" +
            self.__func_name_args(IOA.INTERNAL, type_hint=False) + ")",
            "ensures !(" +
            self.__func_name_args(IOA.INPUT, type_hint=False) + "&&" +
            self.__func_name_args(IOA.OUTPUT, type_hint=False) + ")",
            "ensures !(" +
            self.__func_name_args(IOA.INTERNAL, type_hint=False) + "&&" +
            self.__func_name_args(IOA.OUTPUT, type_hint=False) + ")",
        ]
        return "\n".join(ret_list) + self.__body_block("", True)

    def __lemma_bmc(self) -> str:
        k = self.__k_steps
        arg_list = \
            ["s"+str(i) + ": State" for i in range(0, k)] + \
            ["a"+str(i) + ": Action" for i in range(1, k)]
        if self.__parameters:
            arg_list.append("para: Parameter")

        ret_list = ["lemma bmc_proof?(" + ", ".join(arg_list) + ")"]
        if self.__parameters:  # FIXME What if `where` clause is not specified
            ret_list.append("requires " +
                            self.__func_name_args(IOA.WHERE, type_hint=False))
        ret_list.append(
            "requires " +
            self.__func_name_args(IOA.INITIALLY, type_hint=False, curr_s="s0")
        )
        ret_list += [
            "requires " +
            self.__func_name_args(
                IOA.TRANSITIONS, type_hint=False,
                curr_s="s"+str(i), act="a"+str(i+1), next_s="s"+str(i+1))
            for i in range(0, k-1)
        ] + [
            "ensures " +
            self.__func_name_args(
                IOA.INVARIANT_OF, type_hint=False, curr_s="s" + str(i))
            for i in range(0, k)
        ]
        return "\n".join(ret_list) + self.__body_block("", True)

    def __lemma_induction(self) -> str:
        k = self.__k_steps
        arg_list = \
            ["s"+str(i) + ": State" for i in range(0, k+1)] + \
            ["a"+str(i) + ": Action" for i in range(1, k+1)]
        if self.__parameters:
            arg_list.append("para: Parameter")

        ret_list = ["lemma induction_proof?(" + ", ".join(arg_list) + ")"]
        if self.__parameters:  # FIXME What if `where` clause is not specified
            ret_list.append("requires " +
                            self.__func_name_args(IOA.WHERE, type_hint=False))
        ret_list += [
            "requires " +
            self.__func_name_args(
                IOA.INVARIANT_OF, type_hint=False, curr_s="s" + str(i)) + '\n'
            "requires " +
            self.__func_name_args(
                IOA.TRANSITIONS, type_hint=False,
                curr_s="s"+str(i), act="a"+str(i+1), next_s="s"+str(i+1))
            for i in range(0, k)
        ]
        ret_list.append(
            "ensures " +
            self.__func_name_args(
                IOA.INVARIANT_OF, type_hint=False, curr_s="s" + str(k))
        )
        return "\n".join(ret_list) + self.__body_block("", True)


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

    def visit_IfExp(self, exp: ast.IfExp) -> str:
        return "(if " + self.visit(exp.test) + \
               " then " + self.visit(exp.body) + \
               " else " + self.visit(exp.orelse) + ")"

    def visit_Dict(self, exp):
        raise NotImplementedError("Dictionary expression is not supported yet")

    def visit_Set(self, exp):
        raise NotImplementedError("Finite set expression is not supported yet")

    def visit_ListComp(self, exp: ast.ListComp) -> str:
        # FIXME maybe we can visit generators
        assert exp.generators
        assert len(exp.generators) == 1  # TODO support multiple generators
        for gen in exp.generators:
            assert isinstance(gen.target, ast.Name)  # TODO support multiple bounded variables
            assert not gen.ifs  # TODO support filters
            var = self.visit(gen.target)
            sequence = self.visit(gen.iter)

        # Set namespace
        bounded_vars = [var]
        self._current_namespace.enter_quantification(bounded_vars)

        mapped = self.visit(exp.elt)

        # Reset namespace
        self._current_namespace.exit()

        return "applyMapSeq(map " + var + " | " + var + " in " + sequence + " :: " + \
               mapped + ", " + sequence + ")"
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

    def visit_Call(self, exp) -> str:
        return super().visit_Call(exp)

    def visit_Num(self, exp) -> str:
        return str(exp.n)

    def visit_Str(self, exp) -> str:
        if self._get_scope() == IOA.IOA_SPEC:
            return "/*" + exp.s + "*/"
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

    def visit_Attribute(self, exp) -> str:
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
        return super().visit_Subscript(exp)

    def visit_Select(self, exp):
        if isinstance(exp.ctx, ast.Store) or \
                isinstance(exp.ctx, ast.AugStore):
            assert isinstance(exp.value, ast.Name)
            raise RuntimeError(
                "Subscript expression as L-value should've been handled by"
                "visit_StmtAssign")
        # else:
        return self.visit(exp.value) + "[" + self.visit(exp.slice) + "]"

    def visit_TypeHint(self, exp) -> str:
        typ_cons = self.visit(exp.value)
        assert typ_cons in ['seq', 'set', 'map', 'multiset']
        # Angle brackets are used for generic type in Dafny
        return typ_cons + "<" + self.visit(exp.slice) + ">"

    def visit_Starred(self, exp):
        raise NotImplementedError

    def visit_Name(self, exp):
        return super().visit_Name(exp)

    def visit_List(self, exp) -> str:
        return "[" + ", ".join(map(self.visit, exp.elts)) + "]"

    def visit_Tuple(self, exp) -> str:
        return "(" + ", ".join(map(self.visit, exp.elts)) + ")"

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
        assert all(map(lambda d: d.lower and d.upper and not d.step, slc.dims))
        return ', '.join([self.visit(d.lower) + ": " + self.visit(d.upper) for d in slc.dims])

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
        return " in "

    def visit_NotIn(self, _) -> str:
        return " !in "

    # endregion

    # region IOA specific language constructs visitors
    def visit_IOASpec(self, spec: ast.Module) -> str:
        stmt_list = list(map(self.visit, spec.body))

        type_def_list, rem_list = [], []
        for s in stmt_list:
            # FIXME using prefix of returned string feels unsafe
            if any(s.startswith(ty) for ty in ["type", "newtype", "datatype"]):
                type_def_list.append(s)
            else:
                rem_list.append(s)

        # TODO Group type definitions together and create a module for types
        action_type = "datatype Action = " + \
            " | ".join(self.__global_signature.values())

        type_def_list += [
            action_type,
            "function max(a: nat, b: nat, c: nat): nat\n"
            "{ var tmp := if a >= b then a else b; if tmp >= c then tmp else c }\n"
        ]

        mod_types = "module Types" + \
            self.__body_block("\n".join(type_def_list))

        return mod_types + "\n".join(rem_list)

    def visit_TypeDef(self, lhs: ast.expr, rhs: ast.expr) -> str:
        assert isinstance(lhs, ast.Name)
        typ_name = self.visit(lhs)
        typ_rhs = self.visit(rhs)

        # FIXME hacky way to rename type
        if "shorthand'" in typ_rhs:
            return typ_rhs.replace("shorthand'", typ_name)
        return "type " + typ_name + " = " + typ_rhs

    def visit_Shorthand(self, typ: ast.Subscript) -> str:
        assert isinstance(typ.value, ast.Name)

        cons = self.visit(typ.value)
        name = "shorthand'"
        self.__tmp_id_count += 1
        if cons == "Enum":
            assert isinstance(typ.slice, ast.Index)
            assert isinstance(typ.slice.value, ast.Tuple)
            assert all(isinstance(e, ast.Name) for e in typ.slice.value.elts)
            arg_iter = map(self.visit, typ.slice.value.elts)
            shorthand = "datatype " + name + " = " + " | ".join(arg_iter)
        elif cons == "IntEnum":
            assert isinstance(typ.slice, ast.Index)
            assert isinstance(typ.slice.value, ast.Tuple)
            assert all(isinstance(e, ast.Num) for e in typ.slice.value.elts)
            arg_iter = map(self.visit, typ.slice.value.elts)
            shorthand = "newtype " + name + " = n: int | " + "||".join(map(lambda v: "n==" + v, arg_iter))
        elif cons == "IntRange":
            assert isinstance(typ.slice, ast.Slice)
            assert typ.slice.upper and typ.slice.lower and not typ.slice.step
            upper = self.visit(typ.slice.upper)
            lower = self.visit(typ.slice.lower)
            shorthand = "newtype " + name + " = n: int | " + lower + "<=n<" + upper + "\n"
            # TODO move these functions to a prelude file
            shorthand += \
                "function incre(n: " + name + "): " + name + \
                self.__body_block(
                    "if n==" + str(ast.literal_eval(upper)-1) +
                    " then " + lower + " else n+1",
                    one_line=True
                )
            shorthand += \
                "function decre(n: " + name + "): " + name + \
                self.__body_block(
                    "if n==" + lower +
                    " then " + str(ast.literal_eval(upper)-1) + " else n-1",
                    one_line=True
                )
        elif cons == 'NamedTuple':
            arg_list = self.visit(typ.slice)
            shorthand = "datatype " + name + " = " + name + "(" + arg_list + ")"
        else:
            raise ValueError("Unexpected shorthand type constructor \"" + cons + "\"")

        return shorthand + '\n'

    def visit_Composition(self, comp: ast.FunctionDef) -> str:
        # Set namespace for the given automaton
        self._current_namespace.enter_automaton(comp.name)

        result = self.__automaton_module(comp)
        # Reset namespace
        self._current_namespace.exit()
        return result

    def visit_AutomatonWhere(self, cond: ast.expr):
        return self.__func_name_args(IOA.WHERE) + \
               self.__body_block(self.visit(cond), True)

    def visit_ComponentList(self, comps: ast.ClassDef) -> str:
        # FIXME This assumes self.visit returns a different type than str
        #  This prevents, for example, a pass statement
        comp_list = list(map(self.visit, comps.body))

        import_comps = ""
        for comp_tag, comp_def, comp_actual in comp_list:
            import_comps += "import " + comp_tag + " = " + comp_def + "\n"

        state_typ = "datatype State = State(" + \
            ", ".join(map(lambda c: c[0] + ": " + c[0] + ".State", comp_list)) + ")\n"

        def call_comp_func(ioa):
            def __call(c):
                # FIXME the order of state and action arguments must match
                #  the order in __func_name_args, try to merge the two functions
                actual = []
                if ioa in [IOA.INITIALLY, IOA.INVARIANT_OF, IOA.TRANSITIONS]:
                    actual.append("s." + c[0])
                if ioa in [IOA.INPUT, IOA.OUTPUT, IOA.INTERNAL, IOA.SIGNATURE,
                           IOA.TRANSITIONS]:
                    actual.append("act")
                if ioa == IOA.TRANSITIONS:
                    actual.append("s'." + c[0])
                if c[2]:
                    actual.append(c[0] + ".Parameter(" + c[2] + ")")
                return c[0] + "." + str(ioa) + "(" + ", ".join(actual) + ")"
            return __call
        # Define initially predicate
        initially = self.__func_name_args(IOA.INITIALLY) + \
                    self.__body_block(
                "&&\n".join(map(call_comp_func(IOA.INITIALLY), comp_list))
            )
        # Define input predicate
        inp = self.__func_name_args(IOA.INPUT) + \
              self.__body_block(
                "(\n" + "||\n".join(map(call_comp_func(IOA.INPUT), comp_list)) +
                "\n)&& !" + self.__func_name_args(IOA.OUTPUT, type_hint=False)
                )
        # Define output predicate
        # FIXME support hidden actions
        outp = self.__func_name_args(IOA.OUTPUT) + \
               self.__body_block(
                "||\n".join(map(call_comp_func(IOA.OUTPUT), comp_list))
                )
        # Define internal predicate
        # FIXME support hidden actions
        internal = self.__func_name_args(IOA.INTERNAL) + \
                   self.__body_block(
                "||\n".join(map(call_comp_func(IOA.INTERNAL), comp_list))
            )

        # Define compatibility lemma
        arg_list = ["act: Action"]
        if self.__parameters:
            arg_list.append("para: Parameter")
        compatible = ["lemma compatibility_proof?(" + ", ".join(arg_list) + ")"]
        if self.__parameters:  # FIXME What if `where` clause is not specified
            compatible.append("requires " +
                              self.__func_name_args(IOA.WHERE, type_hint=False))
        compatible += [
            "ensures !(" + call_comp_func(IOA.OUTPUT)(comp_list[i]) + "&&" +
                           call_comp_func(IOA.OUTPUT)(comp_list[j]) + ")\n" +
            "ensures !(" + call_comp_func(IOA.INTERNAL)(comp_list[i]) + "&&" +
                           call_comp_func(IOA.SIGNATURE)(comp_list[j]) + ")\n" +
            "ensures !(" + call_comp_func(IOA.SIGNATURE)(comp_list[i]) + "&&" +
                           call_comp_func(IOA.INTERNAL)(comp_list[j]) + ")"
            for i in range(len(comp_list)) for j in range(i + 1, len(comp_list))
        ]
        compatible.append(self.__body_block("", True))
        compatible = '\n'.join(compatible)

        # Define transitions
        def check_sig(c):
            return "(if " + call_comp_func(IOA.SIGNATURE)(c) + \
                " then " + call_comp_func(IOA.TRANSITIONS)(c) + \
                " else s'." + c[0] + "==" + "s." + c[0] + ")"
        transitions = self.__func_name_args(IOA.TRANSITIONS) + \
                      self.__body_block("&&\n".join(map(check_sig, comp_list)))
        return import_comps + state_typ + initially + \
            inp + outp + internal + compatible + transitions

    def visit_DeclComponent(self, lhs: ast.expr, typ: ast.expr,
                            rhs: Optional[ast.expr]) -> Tuple[str, str, str]:
        if not isinstance(lhs, ast.Name):
            raise NotImplementedError("Declaring a sequence of automata is not supported yet")
        comp_tag = self.visit(lhs)
        # FIXME This assumes a different return type than str
        assert isinstance(typ, ast.Call)
        comp_def, comp_actual = self.visit(typ)
        assert rhs is None
        # FIXME If possible, return a string like other functions
        return comp_tag, comp_def, comp_actual

    def visit_AutomatonInstance(self, aut_inst: ast.Call) -> Tuple[str, str]:
        assert isinstance(aut_inst.func, ast.Name)
        # FIXME If possible, return a string like other functions
        return self.visit(aut_inst.func), ", ".join(map(self.visit, aut_inst.args))

    def visit_PrimitiveAutomaton(self, prim: ast.FunctionDef) -> str:
        # Set namespace for the given automaton
        self._current_namespace.enter_automaton(prim.name)

        result = self.__automaton_module(prim)
        # Reset namespace
        self._current_namespace.exit()
        return result

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
        act_list = list(map(self.visit, sig.body))
        # Collect actions for creating the global set of actions
        for name, (sig, _, _) in act_list:
            stored_sig = self.__global_signature.get(name, None)
            if not stored_sig:
                self.__global_signature[name] = sig
            elif stored_sig != sig:
                raise RuntimeError("Signature of action \"" + name + "\" doesn't match")
        # Construct input, output, and internal predicates
        pred_dict = {"input": "false",
                     "output": "false",
                     "internal": "false"}
        for name, (_, typ, where) in act_list:
            pred = "act." + name + "?"
            if where:
                pred += "&&" + where
            pred_dict[typ] += "||(" + pred + ")"
        ret = ""
        for typ, pred_body in pred_dict.items():
            ret += self.__func_name_args(IOA.get(typ, None)) + \
                   self.__body_block(pred_body, True)
        return ret

    def visit_FormalAction(self, act: ast.FunctionDef) \
            -> Tuple[str, Tuple[str, str, str]]:
        # Set namespace
        self._current_namespace.enter_formal_action(act.name)

        assert len(act.decorator_list) == 1
        act_typ = self.visit(act.decorator_list[0])
        act_sig = act.name + "(" + self.visit(act.args) + ")"
        assert len(act.body) == 1
        act_where = self.visit(act.body[0])
        # FIXME If possible, return a string like other functions
        result = act.name, (act_sig, act_typ, act_where)
        # Reset namespace
        self._current_namespace.exit()
        return result

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
            suffix = "'" + str(self.__tmp_id_count) + "_" + act
            self.__tmp_id_count += 1
            return "pre" + suffix, "eff" + suffix

        # FIXME This assumes a different return type than str
        tran_iter = map(self.visit, tran_list.body)
        ret_list = []
        tran_rel_list = []
        for name, (pre_body, eff_body) in tran_iter:
            pre_name, eff_name = _gen_name(name)
            ret_list.append(self.__func_name_args(IOA.PRE, pre_name) +
                            self.__body_block(pre_body, True))
            ret_list.append(self.__func_name_args(IOA.EFF, eff_name))
            ret_list.append(
                "  requires " + self.__func_name_args(IOA.PRE, pre_name, type_hint=False) +
                self.__body_block(eff_body))
            tran_rel_list.append(
                "(" + self.__func_name_args(IOA.PRE, pre_name, type_hint=False) + " && " +
                self.__func_name_args(IOA.EFF, eff_name, type_hint=False) + ")")

        ret_list.append(self.__func_name_args(IOA.TRANSITIONS) +
                        self.__body_block("||\n".join(tran_rel_list)))
        return "\n".join(ret_list)

    def visit_Transition(self, tran: ast.FunctionDef) -> Tuple[str, Tuple[str, str]]:
        # Set namespace
        self._current_namespace.enter_transition(tran.name)

        assert tran.decorator_list  # At least one decorator
        pre_body = "act." + tran.name + "?&&" + \
                   "&&".join(map(self.visit, tran.decorator_list))
        eff_body = self.visit(tran.body)
        # FIXME If possible, return a string like other functions
        result = tran.name, (pre_body, eff_body)

        # Reset namespace
        self._current_namespace.exit()
        return result

    def visit_ActionType(self, act_typ: IOA) -> str:
        if self._get_scope() == IOA.FORMAL_ACT:
            return str(act_typ)
        if self._get_scope() == IOA.TRANSITION:
            return self.__func_name_args(act_typ, type_hint=False)

    def visit_Precondition(self, cond: ast.expr) -> str:
        return self.visit(cond)

    def visit_Effect(self, stmt_list: List[ast.stmt]) -> str:
        def __enclose(stmt) -> str:
            stmt_str = self.visit(stmt)
            return "var s: State := " + stmt_str + ";"

        return "\n".join(map(__enclose, stmt_list)) + " s"

    def visit_Initially(self, cond: ast.expr) -> str:
        return self.__func_name_args(IOA.INITIALLY) + \
               self.__body_block(self.visit(cond), True)

    def visit_Invariant(self, cond: ast.expr) -> str:
        inv_pred = self.__func_name_args(IOA.INVARIANT_OF) + \
            self.__body_block(self.visit(cond), True)
        inv_lemma_bmc = self.__lemma_bmc()
        inv_lemma_ind = self.__lemma_induction()
        return inv_pred + inv_lemma_bmc + inv_lemma_ind

    def visit_ActionWhere(self, cond: ast.expr) -> str:
        return self.visit(cond)

    def visit_StmtAssign(self, lhs: ast.expr, rhs: ast.expr) -> str:
        assert lhs.ctx and isinstance(lhs.ctx, ast.Store)
        # TODO deal with assignment to sequence elements
        if isinstance(lhs, ast.Name):
            return "s.(" + \
                self.visit(lhs) + " := " + self.visit(rhs) + ")"
        if isinstance(lhs, ast.Subscript):
            assert isinstance(lhs.ctx, ast.Store) or \
                isinstance(lhs.ctx, ast.AugStore)
            assert isinstance(lhs.value, ast.Name)
            return "s.(" + lhs.value.id + ":=" + self.visit(lhs.value) + "[" + \
                self.visit(lhs.slice) + " := " + self.visit(rhs) + "])"
        raise NotImplementedError

    def visit_StmtIf(self, stmt: ast.If) -> str:
        return "if " + self.visit(stmt.test) + "\n" + \
               "then " + self.visit(stmt.body) + "\n" + \
               "else " + self.visit(stmt.orelse)

    def visit_StmtPass(self, stmt: ast.Pass) -> str:
        if self._get_scope() == IOA.EFF:
            return "s"  # return the same state
        # else:
        return ""

    def visit_Identifier(self, name: ast.Name) -> str:
        # FIXME We can also do this case split in IOAAstVisitor, for example,
        #  call visit_LValue() or visit_RValue() based on cases
        # A parameter declaration or L-values in an assignment
        if isinstance(name.ctx, ast.Param) or \
                isinstance(name.ctx, ast.Store) or \
                isinstance(name.ctx, ast.AugStore):
            return name.id
        # else:  # R-value in assignment or type annotations
        return self._current_namespace.add_namespace(name.id)

    def visit_ExternalCall(self, call: ast.Call) -> str:
        assert not call.keywords
        if isinstance(call.func, ast.Name):
            if call.func.id == "len":
                assert len(call.args) == 1
                return " |" + self.visit(call.args[0]) + "| "
            if call.func.id == "implies":
                assert len(call.args) == 2
                return "(" + self.visit(call.args[0]) + " ==> " + \
                       self.visit(call.args[1]) + ")"
            if call.func.id in ["forall", "exists"]:
                assert len(call.args) == 2
                return self.__quantification(call.func.id,
                                             call.args[0], call.args[1])
        # else:
        return self.visit(call.func) + "(" + \
            ", ".join(map(self.visit, call.args)) + ")"

    def __quantification(self, quantifier: str,
                         domain: ast.Expr, expr: ast.Expr) -> str:
        if isinstance(domain, ast.Name):
            # single variable
            bounded_vars = [domain.id]
        elif isinstance(domain, ast.List):
            assert all(map(lambda e: isinstance(e, ast.Name), domain.elts))
            bounded_vars = [e.id for e in domain.elts]
        else:
            # TODO we could support other formats for the domain.
            #  E.g., (x in int), (0 <= x < len(arr)), etc.
            raise RuntimeError("Domain for quantification is ill-formed")

        # Set namespace
        self._current_namespace.enter_quantification(bounded_vars)

        result = "(" + quantifier + " " + ", ".join(bounded_vars) + "::" + self.visit(expr) + ")"

        # Reset namespace
        self._current_namespace.exit()
        return result

    # endregion
