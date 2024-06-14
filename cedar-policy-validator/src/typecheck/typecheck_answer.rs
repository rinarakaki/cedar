/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use cedar_policy_core::ast::{Expr, ExprBuilder, Literal, Var};

use crate::types::{EffectSet, Type};

/// TypecheckAnswer holds the result of typechecking an expression.
#[derive(Debug, Eq, PartialEq)]
pub(crate) enum TypecheckAnswer<'a, T> {
    /// Typechecking succeeded, and we know the type and a possibly empty effect
    /// set for the expression. The effect set is the set of
    /// (expression, attribute) pairs that are known as safe to access under the
    /// assumption that the expression evaluates to true.
    TypecheckSuccess {
        expr_type: T,
        expr_effect: EffectSet<'a>,
    },
    /// Typechecking failed. We might still be able to know the type of the
    /// overall expression, but not always. For instance, an `&&` expression
    /// will always have type `boolean`, so we populate `expr_recovery_type`
    /// with `Some(boolean)` even when there is a type error in the expression.
    TypecheckFail { expr_recovery_type: T },

    /// RecursionLimit Reached
    RecursionLimit,
}

impl<'a, T: AsRef<Option<Type>>> TypecheckAnswer<'a, T> {
    /// Construct a successful TypecheckAnswer with a type but with an empty
    /// effect set.
    pub fn success(expr_type: T) -> Self {
        Self::TypecheckSuccess {
            expr_type,
            expr_effect: EffectSet::new(),
        }
    }

    /// Construct a successful TypecheckAnswer with a type and an effect.
    pub fn success_with_effect(expr_type: T, expr_effect: EffectSet<'a>) -> Self {
        Self::TypecheckSuccess {
            expr_type,
            expr_effect,
        }
    }

    /// Construct a failing TypecheckAnswer with a type.
    pub fn fail(expr_type: T) -> Self {
        Self::TypecheckFail {
            expr_recovery_type: expr_type,
        }
    }

    /// Check if this TypecheckAnswer contains a particular type. It
    /// contains a type if the type annotated AST contains `Some`
    /// of the argument type at its root.
    pub fn contains_type(&self, ty: &Type) -> bool {
        match self {
            TypecheckAnswer::TypecheckSuccess { expr_type, .. } => Some(expr_type),
            TypecheckAnswer::TypecheckFail { expr_recovery_type } => Some(expr_recovery_type),
            TypecheckAnswer::RecursionLimit => None,
        }
        .and_then(|e| e.as_ref().as_ref())
            == Some(ty)
    }

    pub fn into_typed_expr(self) -> Option<T> {
        match self {
            TypecheckAnswer::TypecheckSuccess { expr_type, .. } => Some(expr_type),
            TypecheckAnswer::TypecheckFail { expr_recovery_type } => Some(expr_recovery_type),
            TypecheckAnswer::RecursionLimit => None,
        }
    }

    /// Return true if this represents successful typechecking.
    pub fn typechecked(&self) -> bool {
        match self {
            TypecheckAnswer::TypecheckSuccess { .. } => true,
            TypecheckAnswer::TypecheckFail { .. } => false,
            TypecheckAnswer::RecursionLimit => false,
        }
    }

    /// Transform the effect of this TypecheckAnswer without modifying the
    /// success or type.
    pub fn map_effect<F>(self, f: F) -> Self
    where
        F: FnOnce(EffectSet<'a>) -> EffectSet<'a>,
    {
        match self {
            TypecheckAnswer::TypecheckSuccess {
                expr_type,
                expr_effect,
            } => TypecheckAnswer::TypecheckSuccess {
                expr_type,
                expr_effect: f(expr_effect),
            },
            TypecheckAnswer::TypecheckFail { .. } => self,
            TypecheckAnswer::RecursionLimit => self,
        }
    }

    /// Convert this TypecheckAnswer into an equivalent answer for an expression
    /// that has failed to typecheck. If this is already TypecheckFail, then no
    /// change is required, otherwise, a TypecheckFail is constructed containing
    /// `Some` of the `expr_type`.
    pub fn into_fail(self) -> Self {
        match self {
            TypecheckAnswer::TypecheckSuccess { expr_type, .. } => TypecheckAnswer::fail(expr_type),
            TypecheckAnswer::TypecheckFail { .. } => self,
            TypecheckAnswer::RecursionLimit => self,
        }
    }

    /// Sequence another typechecking operation after this answer. The result of
    /// the operation will be adjusted to be a TypecheckFail if this is a
    /// TypecheckFail, otherwise it will be returned unaltered.
    pub fn then_typecheck<F>(self, f: F) -> Self
    where
        F: FnOnce(T, EffectSet<'a>) -> TypecheckAnswer<'a, T>,
    {
        match self {
            TypecheckAnswer::TypecheckSuccess {
                expr_type,
                expr_effect,
            } => f(expr_type, expr_effect),
            TypecheckAnswer::TypecheckFail { expr_recovery_type } => {
                f(expr_recovery_type, EffectSet::new()).into_fail()
            }
            TypecheckAnswer::RecursionLimit => self,
        }
    }

    /// Sequence another typechecking operation after all of the typechecking
    /// answers in the argument. The result of the operation is adjusted in the
    /// same manner as in `then_typecheck`, but accounts for the all the
    /// TypecheckAnswers.
    pub fn sequence_all_then_typecheck<F>(
        answers: impl IntoIterator<Item = TypecheckAnswer<'a, T>>,
        f: F,
    ) -> TypecheckAnswer<'a, T>
    where
        F: FnOnce(Vec<(T, EffectSet<'a>)>) -> TypecheckAnswer<'a, T>,
    {
        let mut unwrapped = Vec::new();
        let mut any_failed = false;
        let mut recusion_limit_reached = false;
        for ans in answers {
            any_failed |= !ans.typechecked();
            unwrapped.push(match ans {
                TypecheckAnswer::TypecheckSuccess {
                    expr_type,
                    expr_effect,
                } => (expr_type, expr_effect),
                TypecheckAnswer::TypecheckFail { expr_recovery_type } => {
                    (expr_recovery_type, EffectSet::new())
                }
                TypecheckAnswer::RecursionLimit => {
                    recusion_limit_reached = true;
                    break;
                }
            });
        }

        let ans = f(unwrapped);
        if recusion_limit_reached {
            TypecheckAnswer::RecursionLimit
        } else if any_failed {
            ans.into_fail()
        } else {
            ans
        }
    }
}

pub trait ExprTypeBuilder<T: AsRef<Option<Type>>> {
    fn new() -> Self;
    fn with_data(data: Option<Type>) -> Self;
    fn with_same_source_loc<U>(self, expr: &Expr<U>) -> Self;


    fn val(self, v: impl Into<Literal>) -> T;
    fn var(self, v: Var) -> T;
    fn and(self, e1: T, e2: T) -> T;
}

impl ExprTypeBuilder<Expr<Option<Type>>> for ExprBuilder<Option<Type>> {
    fn new() -> Self {
        ExprBuilder::new()
    }

    fn with_data(data: Option<Type>) -> Self {
        ExprBuilder::with_data(data)
    }

    fn with_same_source_loc<U>(self, expr: &Expr<U>) -> Self {
        self.with_same_source_loc(expr)
    }

    fn and(self, e1: Expr<Option<Type>>, e2: Expr<Option<Type>>) -> Expr<Option<Type>> {
        self.and(e1, e2)
    }
    
    fn val(self, v: impl Into<Literal>) -> Expr<Option<Type>> {
        self.val(v)
    }
 
    fn var(self, v: Var) -> Expr<Option<Type>> {
        self.var(v)
    }
}

struct TypeBuilder(Option<Type>);

impl AsRef<Option<Type>> for TypeBuilder {
    fn as_ref(&self) -> &Option<Type> {
        &self.0
    }
}

impl ExprTypeBuilder<TypeBuilder> for TypeBuilder {
    fn new() -> Self {
        Self(None)
    }
    fn with_data(data: Option<Type>) -> Self {
        Self(data)
    }

    fn with_same_source_loc<U>(self, _expr: &Expr<U>) -> Self {
        self
    }

    fn and(self, _e1: TypeBuilder, _e2: TypeBuilder) -> TypeBuilder {
        self
    }
    
    fn val(self, _v: impl Into<Literal>) -> TypeBuilder {
        self
    }
    
    fn var(self, _v: Var) -> TypeBuilder {
        self
    }
}
