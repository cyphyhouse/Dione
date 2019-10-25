""" AST visitor interface that defines all required interface for our IOA language
"""

import abc
import ast
from typing import List, Optional


class IOAAstVisitorInterface(abc.ABC):
    @abc.abstractmethod
    def visit_ioa_spec(self, spec: ast.Module):
        pass

    @abc.abstractmethod
    def visit_ioa_primitive_automaton(self, prim: ast.FunctionDef):
        pass

    @abc.abstractmethod
    def visit_ioa_automaton_instance(self, aut_inst: ast.Call):
        pass

    @abc.abstractmethod
    def visit_ioa_composite_automaton(self, comp: ast.FunctionDef):
        pass

    @abc.abstractmethod
    def visit_ioa_component_list(self, comps: ast.ClassDef):
        pass

    @abc.abstractmethod
    def visit_ioa_decl_state_var(self, lhs: ast.expr, typ: ast.expr,
                                 rhs: Optional[ast.expr]):
        pass

    @abc.abstractmethod
    def visit_ioa_decl_component(self, lhs: ast.expr, typ: ast.expr,
                                 rhs: Optional[ast.expr]):
        pass

    @abc.abstractmethod
    def visit_ioa_effect(self, stmt_list: List[ast.stmt]):
        pass

    @abc.abstractmethod
    def visit_ioa_action_type(self, act_typ: str):
        pass

    @abc.abstractmethod
    def visit_ioa_formal_action(self, act: ast.FunctionDef):
        pass

    @abc.abstractmethod
    def visit_ioa_formal_para_list(self, para_list: List[ast.arg]):
        pass

    @abc.abstractmethod
    def visit_ioa_formal_para(self, para: ast.arg):
        pass

    @abc.abstractmethod
    def visit_ioa_actual_para_list(self, para_list):
        pass

    @abc.abstractmethod
    def visit_ioa_actual_para(self, para):
        pass

    @abc.abstractmethod
    def visit_ioa_hidden(self, node):
        pass

    @abc.abstractmethod
    def visit_ioa_identifier(self, name: ast.Name):
        pass

    @abc.abstractmethod
    def visit_ioa_signature(self, sig: ast.ClassDef):
        pass

    @abc.abstractmethod
    def visit_ioa_simulation(self, node):
        pass

    @abc.abstractmethod
    def visit_ioa_states(self, states: ast.ClassDef):
        pass

    @abc.abstractmethod
    def visit_ioa_trajectories(self, node):
        pass

    @abc.abstractmethod
    def visit_ioa_transition_list(self, tran_list: ast.ClassDef):
        pass

    @abc.abstractmethod
    def visit_ioa_transition(self, tran: ast.FunctionDef):
        pass

    @abc.abstractmethod
    def visit_ioa_type_def(self, lhs: ast.expr, rhs: ast.expr):
        pass

    @abc.abstractmethod
    def visit_ioa_initially(self, cond: ast.expr):
        pass

    @abc.abstractmethod
    def visit_ioa_invariant(self, cond: ast.expr):
        pass

    @abc.abstractmethod
    def visit_ioa_precondition(self, cond: ast.expr):
        pass

    @abc.abstractmethod
    def visit_ioa_automaton_where(self, cond: ast.expr):
        pass

    @abc.abstractmethod
    def visit_ioa_action_where(self, cond: ast.expr):
        pass

    @abc.abstractmethod
    def visit_ioa_stmt_assign(self, lhs: ast.expr, rhs: ast.expr):
        pass

    @abc.abstractmethod
    def visit_ioa_stmt_for(self, stmt: ast.For):
        pass

    @abc.abstractmethod
    def visit_ioa_stmt_if(self, stmt: ast.If):
        pass

    @abc.abstractmethod
    def visit_ioa_stmt_pass(self, stmt: ast.Pass):
        pass

    @abc.abstractmethod
    def visit_ioa_shorthand(self, typ: ast.Call):
        """ Shorthand is to build new types via enumeration, tuple, or union.
            See IOA manual Section 23
        """
        pass

    @abc.abstractmethod
    def visit_ioa_external_call(self, call: ast.Call):
        pass
