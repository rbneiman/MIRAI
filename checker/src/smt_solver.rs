// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use std::collections::HashMap;
use std::fmt::Formatter;
use std::fmt::Debug;
use std::rc::Rc;

use crate::abstract_value::AbstractValue;
use crate::constant_domain::ConstantDomain;
use crate::expression::Expression;
use crate::path::Path;
use crate::tag_domain::Tag;

use mirai_annotations::{get_model_field, precondition, set_model_field};
use serde::{Deserialize, Serialize};

/// The result of using the solver to solve an expression.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
pub enum SmtResult {
    /// There is an assignment of values to the free variables for which the expression is true.
    Satisfiable,
    /// There is a proof that no assignment of values to the free variables can make the expression true.
    Unsatisfiable,
    /// The solver timed out while trying to solve this expression.
    Undefined,
}

#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
pub enum SmtParamValue{
    Bool{val: bool},
    Numeral{val: i128},
    Unknown
}

impl std::fmt::Display for SmtParamValue{

    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&match self {
            SmtParamValue::Bool { val } => val.to_string(),
            SmtParamValue::Numeral { val } => val.to_string(),
            _ => "_".to_string(),
        }, f)
    }
}

#[derive(Clone, Debug)]
pub enum Combined{
    Path{val: Rc<Path>},
    AbstractValue{val: Rc<AbstractValue>},
    Expression{val: Expression},
    Tag{val: Tag},
    ConstantDomain{val: ConstantDomain},
    Solver{}
}

impl From<&Rc<Path>> for Combined{
    fn from(val: &Rc<Path>) -> Self {
        Combined::Path{val: val.clone()}
    }
}

impl From<Rc<Path>> for Combined{
    fn from(val: Rc<Path>) -> Self {
        Combined::Path{val}
    }
}

impl From<Rc<AbstractValue>> for Combined{
    fn from(val: Rc<AbstractValue>) -> Self {
        Combined::AbstractValue{val}
    }
}

impl From<&Expression> for Combined{
    fn from(val: &Expression) -> Self {
        Combined::Expression{val: val.clone()}
    }
}

impl From<&ConstantDomain> for Combined{
    fn from(val: &ConstantDomain) -> Self {
        Combined::ConstantDomain { val: val.clone()}
    }
}

impl From<&Tag> for Combined{
    fn from(val: &Tag) -> Self {
        Combined::Tag { val: val.clone()}
    }
}

pub trait SmtParam{

    fn get_debug_name(&self, debug_map: &HashMap<usize, Rc<String>>) -> String;

    fn get_name(&self) -> &str;

    fn get_expr(&self) -> Option<Combined>;

    fn get_path(&self) -> Option<Rc<Path>>;

    fn get_initializer(&self, debug_map: &HashMap<usize, Rc<String>>) -> Option<String>;

    fn get_val(&self) -> SmtParamValue;

    fn get_debug_string(&self) -> &str;
}

impl Debug for dyn SmtParam {
    
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.get_debug_string().fmt(f)
    }
}

/// The functionality that a solver must expose in order for MIRAI to use it.
pub trait SmtSolver<SmtExpressionType> {
    /// Returns a string representation of the given expression for use in debugging.
    fn as_debug_string(&self, expression: &SmtExpressionType) -> String;

    /// Adds the given expression to the current context.
    fn assert(&self, expression: &SmtExpressionType);

    fn reset(&self);

    /// Destroy the current context and restore the containing context as current.
    fn backtrack(&self) {
        precondition!(get_model_field!(&self, number_of_backtracks, 0) > 0);
    }

    /// Translate the MIRAI expression into a corresponding expression for the Solver.
    fn get_as_smt_predicate(&self, mirai_expression: &Expression) -> SmtExpressionType;

    /// Provides a string that contains a set of variable assignments that satisfied the
    /// assertions in the solver. Can only be called after self.solve return SmtResult::Satisfiable.
    fn get_model_as_string(&self) -> String;

    fn get_model_params(&self, mirai_expr: &Expression) -> Vec<Box<dyn SmtParam>>;

    /// Provides a string that contains a listing of all of the definitions and assertions that
    /// have been added to the solver.
    fn get_solver_state_as_string(&self) -> String;

    /// Returns an expression that is the logical inverse of the given expression.
    fn invert_predicate(&self, expression: &SmtExpressionType) -> SmtExpressionType;

    /// Create a nested context. When a matching backtrack is called, the current context (state)
    /// of the solver will be restored to what it was when this was called.
    fn set_backtrack_position(&self) {
        precondition!(get_model_field!(&self, number_of_backtracks, 0) < 1000);
        set_model_field!(
            &self,
            number_of_backtracks,
            get_model_field!(&self, number_of_backtracks, 0) + 1
        );
    }

    /// Try to find an assignment of values to the free variables so that the assertions in the
    /// current context are all true.
    fn solve(&self) -> SmtResult;

    /// Establish if the given expression can be satisfied (or not) without changing the current context.
    fn solve_expression(&self, expression: &SmtExpressionType) -> SmtResult {
        self.set_backtrack_position();
        self.assert(expression);
        let result = self.solve();
        self.backtrack();
        result
    }
}

/// A dummy implementation of SmtSolver to use in configurations where a real SMT solver is not available or required.
#[derive(Default)]
pub struct SolverStub {}

impl SmtSolver<usize> for SolverStub {
    fn as_debug_string(&self, _: &usize) -> String {
        String::from("not implemented")
    }

    fn assert(&self, _: &usize) {}

    fn reset(&self) {}

    fn backtrack(&self) {}

    fn get_as_smt_predicate(&self, _mirai_expression: &Expression) -> usize {
        0
    }

    fn get_model_as_string(&self) -> String {
        String::from("not implemented")
    }

    fn get_model_params(&self, _mirai_expr: &Expression) -> Vec<Box<dyn SmtParam>>{
        vec![]
    }

    fn get_solver_state_as_string(&self) -> String {
        String::from("not implemented")
    }

    fn invert_predicate(&self, _: &usize) -> usize {
        0
    }

    fn set_backtrack_position(&self) {}

    fn solve(&self) -> SmtResult {
        SmtResult::Undefined
    }
}
