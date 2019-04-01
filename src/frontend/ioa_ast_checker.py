""" Syntax Checker to check if a given Python AST can be interpreted as
    Input/Output Automata
"""

import ast

from src.frontend.ioa_constructs import IOA
from src.frontend.ioa_ast_visitor import IOAAstVisitor


class IOAAstChecker(IOAAstVisitor):
    def __init__(self):
        super().__init__()

    def __check_list(self, ioa_iter, eq_one=None, geq_one=None,
                     leq_one=None, one_of=None, optional=None):
        # Avoid mutable default arguments
        if eq_one is None:
            eq_one = []
        if geq_one is None:
            geq_one = []
        if leq_one is None:
            leq_one = []
        if one_of is None:
            one_of = []
        if optional is None:
            optional = []

        for ioa_construct in ioa_iter:
            if not isinstance(ioa_construct, IOA):
                raise ValueError("Unexpected return value \"" + str(ioa_construct) +
                                 "\" when specifying " + self._get_scope().value)
            if ioa_construct not in (eq_one + geq_one + leq_one + one_of + optional):
                raise ValueError("Unexpected \"" + str(ioa_construct) +
                                 "\" when specifying " + self._get_scope().value)
        # TODO check if the body contains exactly one of each construct in eq_one
        # TODO check if the body contains at least one of each construct in geq_one
        # TODO check if the body contains at most one of each construct in leq_one
        # TODO check if the body contains exactly one from constructs in one_of

    # IOA specific language constructs
    def visit_IOASpec(self, spec):
        assert isinstance(spec, ast.Module)

        ioa_iter = map(self.visit, spec.body)
        self.__check_list(ioa_iter,
                          optional=[IOA.AUTOMATON, IOA.COMPOSITION,
                                    IOA.SIMULATION, IOA.TYPE_DEF])
        return IOA.IOA_SPEC

    def visit_PrimitiveAutomaton(self, prim):
        assert isinstance(prim, ast.FunctionDef)

        parameters = self.visit(prim.args)
        assert parameters == IOA.FORMAL_PARA_LIST  # TODO error message
        ioa_iter = map(self.visit, prim.body)
        self.__check_list(ioa_iter,
                          eq_one=[IOA.SIGNATURE, IOA.STATES,
                                  IOA.TRANSITIONS],
                          leq_one=[IOA.WHERE, IOA.INITIALLY, IOA.TRAJECTORIES],
                          optional=[IOA.INVARIANT_OF])
        return IOA.AUTOMATON

    def visit_AutomatonInstance(self, aut_inst):
        assert isinstance(aut_inst, ast.Call)
        # TODO
        return IOA.AUTOMATON_INSTANCE

    def visit_Composition(self, comp):
        assert isinstance(comp, ast.FunctionDef)

        parameters = self.visit(comp.args)
        assert parameters == IOA.FORMAL_PARA_LIST  # TODO error message
        ioa_iter = map(self.visit, comp.body)
        self.__check_list(ioa_iter,
                          eq_one=[IOA.COMPONENTS],
                          leq_one=[IOA.WHERE],
                          optional=[IOA.INVARIANT_OF])
        return IOA.COMPOSITION

    def visit_ComponentList(self, comp_list):
        assert isinstance(comp_list, ast.ClassDef)

        ioa_iter = map(self.visit, comp_list.body)
        self.__check_list(ioa_iter,
                          geq_one=[IOA.DECL_COMPONENT],
                          leq_one=[IOA.HIDDEN])
        return IOA.COMPONENTS

    def visit_DeclComponent(self, lhs, typ, rhs):
        if not isinstance(lhs, ast.Name):
            raise NotImplementedError("Declaring a sequence of automata is not supported yet")
        assert isinstance(typ, ast.expr)
        assert rhs is None

        ioa_construct = self.visit(typ)
        if ioa_construct != IOA.AUTOMATON_INSTANCE:
            raise ValueError("Unexpected \"" + str(ioa_construct) +
                             "\" when specifying " + self._get_scope().value)
        return IOA.DECL_COMPONENT

    def visit_DeclStateVar(self, lhs, typ, rhs):
        assert isinstance(lhs, ast.Name)
        assert isinstance(typ, ast.expr)
        assert rhs is None or isinstance(rhs, ast.expr)
        # TODO
        self.visit(typ)
        if rhs:
            self.visit(rhs)
        return IOA.DECL_VAR

    def visit_Effect(self, stmt_list):
        ioa_iter = map(self.visit, stmt_list)
        self.__check_list(ioa_iter,
                          optional=[IOA.ASSIGN, IOA.IF,
                                    IOA.FOR, IOA.PASS])
        return IOA.EFF

    def visit_FormalAction(self, act):
        assert isinstance(act, ast.FunctionDef)

        parameters = self.visit(act.args)
        assert parameters == IOA.FORMAL_PARA_LIST  # TODO error message
        ioa_iter = map(self.visit, act.body)
        self.__check_list(ioa_iter,
                          leq_one=[IOA.WHERE],
                          optional=[IOA.PASS])
        return IOA.FORMAL_ACT

    def visit_FormalParameters(self, para_list):
        assert isinstance(para_list, list)
        assert all(isinstance(p, ast.arg) for p in para_list)

        ioa_iter = map(self.visit, para_list)
        self.__check_list(ioa_iter,
                          optional=[IOA.FORMAL_PARA])
        return IOA.FORMAL_PARA_LIST

    def visit_FormalPara(self, para):
        assert isinstance(para, ast.arg)
        # TODO Check parameters are typed
        return IOA.FORMAL_PARA

    def visit_ActualParameters(self, para_list):
        assert isinstance(para_list, list)
        assert all(isinstance(p, ast.arg) for p in para_list)

        ioa_iter = map(self.visit, para_list)
        self.__check_list(ioa_iter,
                          optional=[IOA.ACTUAL_PARA])
        return IOA.ACTUAL_PARA_LIST

    def visit_ActualPara(self, para):
        assert isinstance(para, ast.arg)
        # TODO
        return IOA.ACTUAL_PARA

    def visit_Initially(self, cond):
        assert isinstance(cond, ast.expr)
        # TODO Check initial condition is bool
        return IOA.INITIALLY

    def visit_Invariant(self, cond):
        assert isinstance(cond, ast.expr)
        # TODO Check invariant is bool
        return IOA.INVARIANT_OF

    def visit_Precondition(self, cond):
        assert isinstance(cond, ast.expr)
        # TODO Check precondition is bool
        return IOA.PRE

    def visit_Signature(self, sig):
        assert isinstance(sig, ast.ClassDef)

        ioa_iter = map(self.visit, sig.body)
        self.__check_list(ioa_iter,
                          geq_one=[IOA.FORMAL_ACT])
        return IOA.SIGNATURE

    def visit_States(self, states):
        assert isinstance(states, ast.ClassDef)
        # TODO
        return IOA.STATES

    def visit_TransitionList(self, tran_list):
        assert isinstance(tran_list, ast.ClassDef)

        ioa_iter = map(self.visit, tran_list.body)
        self.__check_list(ioa_iter,
                          geq_one=[IOA.TRANSITION])
        return IOA.TRANSITIONS

    def visit_Transition(self, tran):
        assert isinstance(tran, ast.FunctionDef)
        ioa_iter = map(self.visit, tran.decorator_list)
        self.__check_list(ioa_iter,
                          leq_one=[IOA.PRE],
                          one_of=[IOA.INPUT, IOA.OUTPUT, IOA.INTERNAL])
        parameters = self.visit(tran.args)
        assert parameters == IOA.FORMAL_PARA_LIST  # TODO error message
        effect = self.visit(tran.body)
        if effect != IOA.EFF:
            raise ValueError("Unexpected \"" + str(effect) +
                             "\" when specifying " + self._get_scope().value)
        return IOA.TRANSITION

    def visit_ActionType(self, act_typ):
        assert isinstance(act_typ, IOA)
        assert act_typ in [IOA.INPUT, IOA.INTERNAL, IOA.OUTPUT]
        return act_typ

    def visit_TypeDef(self, lhs, rhs):
        assert isinstance(lhs, ast.Name)
        assert isinstance(rhs, ast.expr)
        # TODO Collect Type Information from rhs
        self.visit(rhs)
        return IOA.TYPE_DEF

    def visit_Where(self, cond):
        assert isinstance(cond, ast.expr)

        # TODO Check where clause is bool
        self.visit(cond)
        return IOA.WHERE

    def visit_StmtAssign(self, lhs, rhs):
        assert isinstance(lhs, ast.Name)
        assert isinstance(rhs, ast.expr)

        # TODO Check types of lhs and rhs are consistent
        self.visit(rhs)
        return IOA.ASSIGN

    def visit_StmtIf(self, stmt):
        # TODO
        return IOA.IF

    def visit_StmtPass(self, stmt):
        # TODO Do we have to differentiate pass statements appearing under different constructs
        return IOA.PASS

    def visit_Identifier(self, name: str):
        # TODO
        return IOA.IDENTIFIER

    def visit_Shorthand(self, typ):
        # TODO
        return IOA.SHORTHAND
