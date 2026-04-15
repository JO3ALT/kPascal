#![feature(prelude_import)]
extern crate std;
#[prelude_import]
use std::prelude::rust_2021::*;
use pest::Parser;
use pest_derive::Parser;
use std::collections::HashSet;
use std::path::{Path, PathBuf};
mod ast {
    pub struct Program {
        #[allow(dead_code)]
        pub name: String,
        pub block: Block,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for Program {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "Program",
                "name",
                &self.name,
                "block",
                &&self.block,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for Program {
        #[inline]
        fn clone(&self) -> Program {
            Program {
                name: ::core::clone::Clone::clone(&self.name),
                block: ::core::clone::Clone::clone(&self.block),
            }
        }
    }
    pub struct Block {
        pub consts: Vec<ConstDecl>,
        pub types: Vec<TypeDecl>,
        pub vars: Vec<VarDecl>,
        pub routines: Vec<RoutineDecl>,
        pub body: Stmt,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for Block {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field5_finish(
                f,
                "Block",
                "consts",
                &self.consts,
                "types",
                &self.types,
                "vars",
                &self.vars,
                "routines",
                &self.routines,
                "body",
                &&self.body,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for Block {
        #[inline]
        fn clone(&self) -> Block {
            Block {
                consts: ::core::clone::Clone::clone(&self.consts),
                types: ::core::clone::Clone::clone(&self.types),
                vars: ::core::clone::Clone::clone(&self.vars),
                routines: ::core::clone::Clone::clone(&self.routines),
                body: ::core::clone::Clone::clone(&self.body),
            }
        }
    }
    #[automatically_derived]
    impl ::core::default::Default for Block {
        #[inline]
        fn default() -> Block {
            Block {
                consts: ::core::default::Default::default(),
                types: ::core::default::Default::default(),
                vars: ::core::default::Default::default(),
                routines: ::core::default::Default::default(),
                body: ::core::default::Default::default(),
            }
        }
    }
    pub struct ConstDecl {
        pub name: String,
        pub ty: Option<TypeRef>,
        pub expr: ConstExpr,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for ConstDecl {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "ConstDecl",
                "name",
                &self.name,
                "ty",
                &self.ty,
                "expr",
                &&self.expr,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for ConstDecl {
        #[inline]
        fn clone(&self) -> ConstDecl {
            ConstDecl {
                name: ::core::clone::Clone::clone(&self.name),
                ty: ::core::clone::Clone::clone(&self.ty),
                expr: ::core::clone::Clone::clone(&self.expr),
            }
        }
    }
    pub struct TypeDecl {
        pub name: String,
        pub spec: TypeSpec,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for TypeDecl {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "TypeDecl",
                "name",
                &self.name,
                "spec",
                &&self.spec,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for TypeDecl {
        #[inline]
        fn clone(&self) -> TypeDecl {
            TypeDecl {
                name: ::core::clone::Clone::clone(&self.name),
                spec: ::core::clone::Clone::clone(&self.spec),
            }
        }
    }
    pub struct VarDecl {
        pub name: String,
        pub ty: TypeRef,
        pub immutable: bool,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for VarDecl {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "VarDecl",
                "name",
                &self.name,
                "ty",
                &self.ty,
                "immutable",
                &&self.immutable,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for VarDecl {
        #[inline]
        fn clone(&self) -> VarDecl {
            VarDecl {
                name: ::core::clone::Clone::clone(&self.name),
                ty: ::core::clone::Clone::clone(&self.ty),
                immutable: ::core::clone::Clone::clone(&self.immutable),
            }
        }
    }
    pub enum RoutineDecl {
        Procedure(ProcedureDecl),
        Function(FunctionDecl),
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for RoutineDecl {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                RoutineDecl::Procedure(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Procedure",
                        &__self_0,
                    )
                }
                RoutineDecl::Function(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Function",
                        &__self_0,
                    )
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for RoutineDecl {
        #[inline]
        fn clone(&self) -> RoutineDecl {
            match self {
                RoutineDecl::Procedure(__self_0) => {
                    RoutineDecl::Procedure(::core::clone::Clone::clone(__self_0))
                }
                RoutineDecl::Function(__self_0) => {
                    RoutineDecl::Function(::core::clone::Clone::clone(__self_0))
                }
            }
        }
    }
    pub struct ProcedureDecl {
        pub name: String,
        pub params: Vec<ParamDecl>,
        pub block: Block,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for ProcedureDecl {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "ProcedureDecl",
                "name",
                &self.name,
                "params",
                &self.params,
                "block",
                &&self.block,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for ProcedureDecl {
        #[inline]
        fn clone(&self) -> ProcedureDecl {
            ProcedureDecl {
                name: ::core::clone::Clone::clone(&self.name),
                params: ::core::clone::Clone::clone(&self.params),
                block: ::core::clone::Clone::clone(&self.block),
            }
        }
    }
    pub struct FunctionDecl {
        pub name: String,
        pub params: Vec<ParamDecl>,
        pub ret_ty: TypeRef,
        pub block: Block,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for FunctionDecl {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field4_finish(
                f,
                "FunctionDecl",
                "name",
                &self.name,
                "params",
                &self.params,
                "ret_ty",
                &self.ret_ty,
                "block",
                &&self.block,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for FunctionDecl {
        #[inline]
        fn clone(&self) -> FunctionDecl {
            FunctionDecl {
                name: ::core::clone::Clone::clone(&self.name),
                params: ::core::clone::Clone::clone(&self.params),
                ret_ty: ::core::clone::Clone::clone(&self.ret_ty),
                block: ::core::clone::Clone::clone(&self.block),
            }
        }
    }
    pub struct ParamDecl {
        pub name: String,
        pub ty: TypeRef,
        pub by_ref: bool,
        pub conformant: Option<ConformantArrayParam>,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for ParamDecl {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field4_finish(
                f,
                "ParamDecl",
                "name",
                &self.name,
                "ty",
                &self.ty,
                "by_ref",
                &self.by_ref,
                "conformant",
                &&self.conformant,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for ParamDecl {
        #[inline]
        fn clone(&self) -> ParamDecl {
            ParamDecl {
                name: ::core::clone::Clone::clone(&self.name),
                ty: ::core::clone::Clone::clone(&self.ty),
                by_ref: ::core::clone::Clone::clone(&self.by_ref),
                conformant: ::core::clone::Clone::clone(&self.conformant),
            }
        }
    }
    pub enum TypeSpec {
        Basic(BasicType),
        Enum(Vec<String>),
        Record { fields: Vec<FieldDecl>, variant: Option<VariantPart> },
        SumRecord(Vec<SumArmDecl>),
        Array { dims: Vec<ArrayDim>, elem: TypeRef },
        Subrange { low: ConstExpr, high: ConstExpr },
        Set(TypeRef),
        Alias(TypeRef),
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for TypeSpec {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                TypeSpec::Basic(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Basic",
                        &__self_0,
                    )
                }
                TypeSpec::Enum(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Enum",
                        &__self_0,
                    )
                }
                TypeSpec::Record { fields: __self_0, variant: __self_1 } => {
                    ::core::fmt::Formatter::debug_struct_field2_finish(
                        f,
                        "Record",
                        "fields",
                        __self_0,
                        "variant",
                        &__self_1,
                    )
                }
                TypeSpec::SumRecord(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "SumRecord",
                        &__self_0,
                    )
                }
                TypeSpec::Array { dims: __self_0, elem: __self_1 } => {
                    ::core::fmt::Formatter::debug_struct_field2_finish(
                        f,
                        "Array",
                        "dims",
                        __self_0,
                        "elem",
                        &__self_1,
                    )
                }
                TypeSpec::Subrange { low: __self_0, high: __self_1 } => {
                    ::core::fmt::Formatter::debug_struct_field2_finish(
                        f,
                        "Subrange",
                        "low",
                        __self_0,
                        "high",
                        &__self_1,
                    )
                }
                TypeSpec::Set(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Set",
                        &__self_0,
                    )
                }
                TypeSpec::Alias(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Alias",
                        &__self_0,
                    )
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for TypeSpec {
        #[inline]
        fn clone(&self) -> TypeSpec {
            match self {
                TypeSpec::Basic(__self_0) => {
                    TypeSpec::Basic(::core::clone::Clone::clone(__self_0))
                }
                TypeSpec::Enum(__self_0) => {
                    TypeSpec::Enum(::core::clone::Clone::clone(__self_0))
                }
                TypeSpec::Record { fields: __self_0, variant: __self_1 } => {
                    TypeSpec::Record {
                        fields: ::core::clone::Clone::clone(__self_0),
                        variant: ::core::clone::Clone::clone(__self_1),
                    }
                }
                TypeSpec::SumRecord(__self_0) => {
                    TypeSpec::SumRecord(::core::clone::Clone::clone(__self_0))
                }
                TypeSpec::Array { dims: __self_0, elem: __self_1 } => {
                    TypeSpec::Array {
                        dims: ::core::clone::Clone::clone(__self_0),
                        elem: ::core::clone::Clone::clone(__self_1),
                    }
                }
                TypeSpec::Subrange { low: __self_0, high: __self_1 } => {
                    TypeSpec::Subrange {
                        low: ::core::clone::Clone::clone(__self_0),
                        high: ::core::clone::Clone::clone(__self_1),
                    }
                }
                TypeSpec::Set(__self_0) => {
                    TypeSpec::Set(::core::clone::Clone::clone(__self_0))
                }
                TypeSpec::Alias(__self_0) => {
                    TypeSpec::Alias(::core::clone::Clone::clone(__self_0))
                }
            }
        }
    }
    pub struct ConformantArrayParam {
        pub dims: Vec<ConformantArrayDim>,
        pub elem_ty: TypeRef,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for ConformantArrayParam {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "ConformantArrayParam",
                "dims",
                &self.dims,
                "elem_ty",
                &&self.elem_ty,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for ConformantArrayParam {
        #[inline]
        fn clone(&self) -> ConformantArrayParam {
            ConformantArrayParam {
                dims: ::core::clone::Clone::clone(&self.dims),
                elem_ty: ::core::clone::Clone::clone(&self.elem_ty),
            }
        }
    }
    pub struct ConformantArrayDim {
        pub low_name: String,
        pub high_name: String,
        pub index_ty: TypeRef,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for ConformantArrayDim {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "ConformantArrayDim",
                "low_name",
                &self.low_name,
                "high_name",
                &self.high_name,
                "index_ty",
                &&self.index_ty,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for ConformantArrayDim {
        #[inline]
        fn clone(&self) -> ConformantArrayDim {
            ConformantArrayDim {
                low_name: ::core::clone::Clone::clone(&self.low_name),
                high_name: ::core::clone::Clone::clone(&self.high_name),
                index_ty: ::core::clone::Clone::clone(&self.index_ty),
            }
        }
    }
    pub struct ArrayDim {
        pub low: ConstExpr,
        pub high: ConstExpr,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for ArrayDim {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "ArrayDim",
                "low",
                &self.low,
                "high",
                &&self.high,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for ArrayDim {
        #[inline]
        fn clone(&self) -> ArrayDim {
            ArrayDim {
                low: ::core::clone::Clone::clone(&self.low),
                high: ::core::clone::Clone::clone(&self.high),
            }
        }
    }
    pub struct FieldDecl {
        pub name: String,
        pub ty: TypeRef,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for FieldDecl {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "FieldDecl",
                "name",
                &self.name,
                "ty",
                &&self.ty,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for FieldDecl {
        #[inline]
        fn clone(&self) -> FieldDecl {
            FieldDecl {
                name: ::core::clone::Clone::clone(&self.name),
                ty: ::core::clone::Clone::clone(&self.ty),
            }
        }
    }
    pub struct SumArmDecl {
        pub name: String,
        pub fields: Vec<FieldDecl>,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for SumArmDecl {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "SumArmDecl",
                "name",
                &self.name,
                "fields",
                &&self.fields,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for SumArmDecl {
        #[inline]
        fn clone(&self) -> SumArmDecl {
            SumArmDecl {
                name: ::core::clone::Clone::clone(&self.name),
                fields: ::core::clone::Clone::clone(&self.fields),
            }
        }
    }
    pub struct VariantPart {
        pub tag_name: Option<String>,
        pub tag_ty: TypeRef,
        pub cases: Vec<VariantCase>,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for VariantPart {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "VariantPart",
                "tag_name",
                &self.tag_name,
                "tag_ty",
                &self.tag_ty,
                "cases",
                &&self.cases,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for VariantPart {
        #[inline]
        fn clone(&self) -> VariantPart {
            VariantPart {
                tag_name: ::core::clone::Clone::clone(&self.tag_name),
                tag_ty: ::core::clone::Clone::clone(&self.tag_ty),
                cases: ::core::clone::Clone::clone(&self.cases),
            }
        }
    }
    pub struct VariantCase {
        pub labels: Vec<CaseLabel>,
        pub fields: Vec<FieldDecl>,
        pub variant: Option<VariantPart>,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for VariantCase {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "VariantCase",
                "labels",
                &self.labels,
                "fields",
                &self.fields,
                "variant",
                &&self.variant,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for VariantCase {
        #[inline]
        fn clone(&self) -> VariantCase {
            VariantCase {
                labels: ::core::clone::Clone::clone(&self.labels),
                fields: ::core::clone::Clone::clone(&self.fields),
                variant: ::core::clone::Clone::clone(&self.variant),
            }
        }
    }
    pub enum BasicType {
        Integer,
        Boolean,
        Char,
        Real,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for BasicType {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(
                f,
                match self {
                    BasicType::Integer => "Integer",
                    BasicType::Boolean => "Boolean",
                    BasicType::Char => "Char",
                    BasicType::Real => "Real",
                },
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for BasicType {
        #[inline]
        fn clone(&self) -> BasicType {
            match self {
                BasicType::Integer => BasicType::Integer,
                BasicType::Boolean => BasicType::Boolean,
                BasicType::Char => BasicType::Char,
                BasicType::Real => BasicType::Real,
            }
        }
    }
    pub enum TypeRef {
        Basic(BasicType),
        Named(String),
        PointerNamed(String),
        Option(Box<TypeRef>),
        Result(Box<TypeRef>, Box<TypeRef>),
        Array { dims: Vec<ArrayDim>, elem: Box<TypeRef> },
        Subrange { low: ConstExpr, high: ConstExpr },
        Set(Box<TypeRef>),
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for TypeRef {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                TypeRef::Basic(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Basic",
                        &__self_0,
                    )
                }
                TypeRef::Named(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Named",
                        &__self_0,
                    )
                }
                TypeRef::PointerNamed(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "PointerNamed",
                        &__self_0,
                    )
                }
                TypeRef::Option(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Option",
                        &__self_0,
                    )
                }
                TypeRef::Result(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "Result",
                        __self_0,
                        &__self_1,
                    )
                }
                TypeRef::Array { dims: __self_0, elem: __self_1 } => {
                    ::core::fmt::Formatter::debug_struct_field2_finish(
                        f,
                        "Array",
                        "dims",
                        __self_0,
                        "elem",
                        &__self_1,
                    )
                }
                TypeRef::Subrange { low: __self_0, high: __self_1 } => {
                    ::core::fmt::Formatter::debug_struct_field2_finish(
                        f,
                        "Subrange",
                        "low",
                        __self_0,
                        "high",
                        &__self_1,
                    )
                }
                TypeRef::Set(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Set",
                        &__self_0,
                    )
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for TypeRef {
        #[inline]
        fn clone(&self) -> TypeRef {
            match self {
                TypeRef::Basic(__self_0) => {
                    TypeRef::Basic(::core::clone::Clone::clone(__self_0))
                }
                TypeRef::Named(__self_0) => {
                    TypeRef::Named(::core::clone::Clone::clone(__self_0))
                }
                TypeRef::PointerNamed(__self_0) => {
                    TypeRef::PointerNamed(::core::clone::Clone::clone(__self_0))
                }
                TypeRef::Option(__self_0) => {
                    TypeRef::Option(::core::clone::Clone::clone(__self_0))
                }
                TypeRef::Result(__self_0, __self_1) => {
                    TypeRef::Result(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                TypeRef::Array { dims: __self_0, elem: __self_1 } => {
                    TypeRef::Array {
                        dims: ::core::clone::Clone::clone(__self_0),
                        elem: ::core::clone::Clone::clone(__self_1),
                    }
                }
                TypeRef::Subrange { low: __self_0, high: __self_1 } => {
                    TypeRef::Subrange {
                        low: ::core::clone::Clone::clone(__self_0),
                        high: ::core::clone::Clone::clone(__self_1),
                    }
                }
                TypeRef::Set(__self_0) => {
                    TypeRef::Set(::core::clone::Clone::clone(__self_0))
                }
            }
        }
    }
    pub enum Stmt {
        #[default]
        Empty,
        Compound(Vec<Stmt>),
        Assign(LValue, Expr),
        Read(Vec<Expr>),
        ReadLn,
        For { var: String, init: Expr, limit: Expr, downto: bool, body: Box<Stmt> },
        If(Expr, Box<Stmt>, Option<Box<Stmt>>),
        With(Vec<LValue>, Box<Stmt>),
        While(Expr, Box<Stmt>),
        Repeat(Vec<Stmt>, Expr),
        Case {
            expr: Expr,
            arms: Vec<(Vec<CaseLabel>, Stmt)>,
            else_stmt: Option<Box<Stmt>>,
        },
        SumCase { expr: Expr, arms: Vec<SumCaseArm>, else_stmt: Option<Box<Stmt>> },
        ProcCall(String, Vec<Expr>),
        Write(Vec<Expr>),
        WriteLn(Vec<Expr>),
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for Stmt {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                Stmt::Empty => ::core::fmt::Formatter::write_str(f, "Empty"),
                Stmt::Compound(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Compound",
                        &__self_0,
                    )
                }
                Stmt::Assign(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "Assign",
                        __self_0,
                        &__self_1,
                    )
                }
                Stmt::Read(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Read",
                        &__self_0,
                    )
                }
                Stmt::ReadLn => ::core::fmt::Formatter::write_str(f, "ReadLn"),
                Stmt::For {
                    var: __self_0,
                    init: __self_1,
                    limit: __self_2,
                    downto: __self_3,
                    body: __self_4,
                } => {
                    ::core::fmt::Formatter::debug_struct_field5_finish(
                        f,
                        "For",
                        "var",
                        __self_0,
                        "init",
                        __self_1,
                        "limit",
                        __self_2,
                        "downto",
                        __self_3,
                        "body",
                        &__self_4,
                    )
                }
                Stmt::If(__self_0, __self_1, __self_2) => {
                    ::core::fmt::Formatter::debug_tuple_field3_finish(
                        f,
                        "If",
                        __self_0,
                        __self_1,
                        &__self_2,
                    )
                }
                Stmt::With(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "With",
                        __self_0,
                        &__self_1,
                    )
                }
                Stmt::While(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "While",
                        __self_0,
                        &__self_1,
                    )
                }
                Stmt::Repeat(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "Repeat",
                        __self_0,
                        &__self_1,
                    )
                }
                Stmt::Case { expr: __self_0, arms: __self_1, else_stmt: __self_2 } => {
                    ::core::fmt::Formatter::debug_struct_field3_finish(
                        f,
                        "Case",
                        "expr",
                        __self_0,
                        "arms",
                        __self_1,
                        "else_stmt",
                        &__self_2,
                    )
                }
                Stmt::SumCase { expr: __self_0, arms: __self_1, else_stmt: __self_2 } => {
                    ::core::fmt::Formatter::debug_struct_field3_finish(
                        f,
                        "SumCase",
                        "expr",
                        __self_0,
                        "arms",
                        __self_1,
                        "else_stmt",
                        &__self_2,
                    )
                }
                Stmt::ProcCall(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "ProcCall",
                        __self_0,
                        &__self_1,
                    )
                }
                Stmt::Write(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Write",
                        &__self_0,
                    )
                }
                Stmt::WriteLn(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "WriteLn",
                        &__self_0,
                    )
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for Stmt {
        #[inline]
        fn clone(&self) -> Stmt {
            match self {
                Stmt::Empty => Stmt::Empty,
                Stmt::Compound(__self_0) => {
                    Stmt::Compound(::core::clone::Clone::clone(__self_0))
                }
                Stmt::Assign(__self_0, __self_1) => {
                    Stmt::Assign(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                Stmt::Read(__self_0) => Stmt::Read(::core::clone::Clone::clone(__self_0)),
                Stmt::ReadLn => Stmt::ReadLn,
                Stmt::For {
                    var: __self_0,
                    init: __self_1,
                    limit: __self_2,
                    downto: __self_3,
                    body: __self_4,
                } => {
                    Stmt::For {
                        var: ::core::clone::Clone::clone(__self_0),
                        init: ::core::clone::Clone::clone(__self_1),
                        limit: ::core::clone::Clone::clone(__self_2),
                        downto: ::core::clone::Clone::clone(__self_3),
                        body: ::core::clone::Clone::clone(__self_4),
                    }
                }
                Stmt::If(__self_0, __self_1, __self_2) => {
                    Stmt::If(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                        ::core::clone::Clone::clone(__self_2),
                    )
                }
                Stmt::With(__self_0, __self_1) => {
                    Stmt::With(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                Stmt::While(__self_0, __self_1) => {
                    Stmt::While(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                Stmt::Repeat(__self_0, __self_1) => {
                    Stmt::Repeat(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                Stmt::Case { expr: __self_0, arms: __self_1, else_stmt: __self_2 } => {
                    Stmt::Case {
                        expr: ::core::clone::Clone::clone(__self_0),
                        arms: ::core::clone::Clone::clone(__self_1),
                        else_stmt: ::core::clone::Clone::clone(__self_2),
                    }
                }
                Stmt::SumCase { expr: __self_0, arms: __self_1, else_stmt: __self_2 } => {
                    Stmt::SumCase {
                        expr: ::core::clone::Clone::clone(__self_0),
                        arms: ::core::clone::Clone::clone(__self_1),
                        else_stmt: ::core::clone::Clone::clone(__self_2),
                    }
                }
                Stmt::ProcCall(__self_0, __self_1) => {
                    Stmt::ProcCall(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                Stmt::Write(__self_0) => {
                    Stmt::Write(::core::clone::Clone::clone(__self_0))
                }
                Stmt::WriteLn(__self_0) => {
                    Stmt::WriteLn(::core::clone::Clone::clone(__self_0))
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::default::Default for Stmt {
        #[inline]
        fn default() -> Stmt {
            Self::Empty
        }
    }
    pub struct SumCaseArm {
        pub ctor: String,
        pub binds: Vec<String>,
        pub body: Stmt,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for SumCaseArm {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "SumCaseArm",
                "ctor",
                &self.ctor,
                "binds",
                &self.binds,
                "body",
                &&self.body,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for SumCaseArm {
        #[inline]
        fn clone(&self) -> SumCaseArm {
            SumCaseArm {
                ctor: ::core::clone::Clone::clone(&self.ctor),
                binds: ::core::clone::Clone::clone(&self.binds),
                body: ::core::clone::Clone::clone(&self.body),
            }
        }
    }
    pub struct LValue {
        pub base: String,
        pub sels: Vec<Selector>,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for LValue {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "LValue",
                "base",
                &self.base,
                "sels",
                &&self.sels,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for LValue {
        #[inline]
        fn clone(&self) -> LValue {
            LValue {
                base: ::core::clone::Clone::clone(&self.base),
                sels: ::core::clone::Clone::clone(&self.sels),
            }
        }
    }
    pub enum Selector {
        Field(String),
        Index(Vec<Expr>),
        Deref,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for Selector {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                Selector::Field(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Field",
                        &__self_0,
                    )
                }
                Selector::Index(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Index",
                        &__self_0,
                    )
                }
                Selector::Deref => ::core::fmt::Formatter::write_str(f, "Deref"),
            }
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for Selector {
        #[inline]
        fn clone(&self) -> Selector {
            match self {
                Selector::Field(__self_0) => {
                    Selector::Field(::core::clone::Clone::clone(__self_0))
                }
                Selector::Index(__self_0) => {
                    Selector::Index(::core::clone::Clone::clone(__self_0))
                }
                Selector::Deref => Selector::Deref,
            }
        }
    }
    pub enum Expr {
        Int(i32),
        Bool(bool),
        Char(u32),
        Real(u32),
        Str(String),
        SetLit(Vec<SetItem>),
        Nil,
        Var(String),
        Call(String, Vec<Expr>),
        Ctor(String, Vec<(String, Expr)>),
        ArrayLit(Vec<Expr>),
        RecordUpdate(Box<Expr>, Vec<(String, Expr)>),
        ArrayUpdate(Box<Expr>, Vec<(Expr, Expr)>),
        OptionNone,
        OptionSome(Box<Expr>),
        Cond { arms: Vec<CondExprArm>, else_block: CondValueBlock },
        Deref(Box<Expr>),
        Field(Box<Expr>, String),
        Index(Box<Expr>, Box<Expr>),
        Cast(TypeRef, Box<Expr>),
        Unary(UnOp, Box<Expr>),
        Binary(Box<Expr>, BinOp, Box<Expr>),
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for Expr {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                Expr::Int(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Int",
                        &__self_0,
                    )
                }
                Expr::Bool(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Bool",
                        &__self_0,
                    )
                }
                Expr::Char(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Char",
                        &__self_0,
                    )
                }
                Expr::Real(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Real",
                        &__self_0,
                    )
                }
                Expr::Str(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Str",
                        &__self_0,
                    )
                }
                Expr::SetLit(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "SetLit",
                        &__self_0,
                    )
                }
                Expr::Nil => ::core::fmt::Formatter::write_str(f, "Nil"),
                Expr::Var(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Var",
                        &__self_0,
                    )
                }
                Expr::Call(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "Call",
                        __self_0,
                        &__self_1,
                    )
                }
                Expr::Ctor(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "Ctor",
                        __self_0,
                        &__self_1,
                    )
                }
                Expr::ArrayLit(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "ArrayLit",
                        &__self_0,
                    )
                }
                Expr::RecordUpdate(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "RecordUpdate",
                        __self_0,
                        &__self_1,
                    )
                }
                Expr::ArrayUpdate(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "ArrayUpdate",
                        __self_0,
                        &__self_1,
                    )
                }
                Expr::OptionNone => ::core::fmt::Formatter::write_str(f, "OptionNone"),
                Expr::OptionSome(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "OptionSome",
                        &__self_0,
                    )
                }
                Expr::Cond { arms: __self_0, else_block: __self_1 } => {
                    ::core::fmt::Formatter::debug_struct_field2_finish(
                        f,
                        "Cond",
                        "arms",
                        __self_0,
                        "else_block",
                        &__self_1,
                    )
                }
                Expr::Deref(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Deref",
                        &__self_0,
                    )
                }
                Expr::Field(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "Field",
                        __self_0,
                        &__self_1,
                    )
                }
                Expr::Index(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "Index",
                        __self_0,
                        &__self_1,
                    )
                }
                Expr::Cast(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "Cast",
                        __self_0,
                        &__self_1,
                    )
                }
                Expr::Unary(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "Unary",
                        __self_0,
                        &__self_1,
                    )
                }
                Expr::Binary(__self_0, __self_1, __self_2) => {
                    ::core::fmt::Formatter::debug_tuple_field3_finish(
                        f,
                        "Binary",
                        __self_0,
                        __self_1,
                        &__self_2,
                    )
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for Expr {
        #[inline]
        fn clone(&self) -> Expr {
            match self {
                Expr::Int(__self_0) => Expr::Int(::core::clone::Clone::clone(__self_0)),
                Expr::Bool(__self_0) => Expr::Bool(::core::clone::Clone::clone(__self_0)),
                Expr::Char(__self_0) => Expr::Char(::core::clone::Clone::clone(__self_0)),
                Expr::Real(__self_0) => Expr::Real(::core::clone::Clone::clone(__self_0)),
                Expr::Str(__self_0) => Expr::Str(::core::clone::Clone::clone(__self_0)),
                Expr::SetLit(__self_0) => {
                    Expr::SetLit(::core::clone::Clone::clone(__self_0))
                }
                Expr::Nil => Expr::Nil,
                Expr::Var(__self_0) => Expr::Var(::core::clone::Clone::clone(__self_0)),
                Expr::Call(__self_0, __self_1) => {
                    Expr::Call(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                Expr::Ctor(__self_0, __self_1) => {
                    Expr::Ctor(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                Expr::ArrayLit(__self_0) => {
                    Expr::ArrayLit(::core::clone::Clone::clone(__self_0))
                }
                Expr::RecordUpdate(__self_0, __self_1) => {
                    Expr::RecordUpdate(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                Expr::ArrayUpdate(__self_0, __self_1) => {
                    Expr::ArrayUpdate(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                Expr::OptionNone => Expr::OptionNone,
                Expr::OptionSome(__self_0) => {
                    Expr::OptionSome(::core::clone::Clone::clone(__self_0))
                }
                Expr::Cond { arms: __self_0, else_block: __self_1 } => {
                    Expr::Cond {
                        arms: ::core::clone::Clone::clone(__self_0),
                        else_block: ::core::clone::Clone::clone(__self_1),
                    }
                }
                Expr::Deref(__self_0) => {
                    Expr::Deref(::core::clone::Clone::clone(__self_0))
                }
                Expr::Field(__self_0, __self_1) => {
                    Expr::Field(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                Expr::Index(__self_0, __self_1) => {
                    Expr::Index(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                Expr::Cast(__self_0, __self_1) => {
                    Expr::Cast(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                Expr::Unary(__self_0, __self_1) => {
                    Expr::Unary(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                Expr::Binary(__self_0, __self_1, __self_2) => {
                    Expr::Binary(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                        ::core::clone::Clone::clone(__self_2),
                    )
                }
            }
        }
    }
    pub struct CondExprArm {
        pub cond: Expr,
        pub block: CondValueBlock,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for CondExprArm {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "CondExprArm",
                "cond",
                &self.cond,
                "block",
                &&self.block,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for CondExprArm {
        #[inline]
        fn clone(&self) -> CondExprArm {
            CondExprArm {
                cond: ::core::clone::Clone::clone(&self.cond),
                block: ::core::clone::Clone::clone(&self.block),
            }
        }
    }
    pub struct CondValueBlock {
        pub stmts: Vec<Stmt>,
        pub value: Box<Expr>,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for CondValueBlock {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "CondValueBlock",
                "stmts",
                &self.stmts,
                "value",
                &&self.value,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for CondValueBlock {
        #[inline]
        fn clone(&self) -> CondValueBlock {
            CondValueBlock {
                stmts: ::core::clone::Clone::clone(&self.stmts),
                value: ::core::clone::Clone::clone(&self.value),
            }
        }
    }
    pub enum SetItem {
        Single(Expr),
        Range(Expr, Expr),
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for SetItem {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                SetItem::Single(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Single",
                        &__self_0,
                    )
                }
                SetItem::Range(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "Range",
                        __self_0,
                        &__self_1,
                    )
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for SetItem {
        #[inline]
        fn clone(&self) -> SetItem {
            match self {
                SetItem::Single(__self_0) => {
                    SetItem::Single(::core::clone::Clone::clone(__self_0))
                }
                SetItem::Range(__self_0, __self_1) => {
                    SetItem::Range(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
            }
        }
    }
    pub enum CaseLabel {
        Single(ConstExpr),
        Range(ConstExpr, ConstExpr),
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for CaseLabel {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                CaseLabel::Single(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Single",
                        &__self_0,
                    )
                }
                CaseLabel::Range(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "Range",
                        __self_0,
                        &__self_1,
                    )
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for CaseLabel {
        #[inline]
        fn clone(&self) -> CaseLabel {
            match self {
                CaseLabel::Single(__self_0) => {
                    CaseLabel::Single(::core::clone::Clone::clone(__self_0))
                }
                CaseLabel::Range(__self_0, __self_1) => {
                    CaseLabel::Range(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
            }
        }
    }
    pub enum ConstExpr {
        Int(i32),
        Bool(bool),
        Char(u32),
        Real(u32),
        Const(String),
        Call(String, Vec<ConstExpr>),
        Unary(UnOp, Box<ConstExpr>),
        Binary(Box<ConstExpr>, BinOp, Box<ConstExpr>),
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for ConstExpr {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                ConstExpr::Int(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Int",
                        &__self_0,
                    )
                }
                ConstExpr::Bool(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Bool",
                        &__self_0,
                    )
                }
                ConstExpr::Char(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Char",
                        &__self_0,
                    )
                }
                ConstExpr::Real(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Real",
                        &__self_0,
                    )
                }
                ConstExpr::Const(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Const",
                        &__self_0,
                    )
                }
                ConstExpr::Call(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "Call",
                        __self_0,
                        &__self_1,
                    )
                }
                ConstExpr::Unary(__self_0, __self_1) => {
                    ::core::fmt::Formatter::debug_tuple_field2_finish(
                        f,
                        "Unary",
                        __self_0,
                        &__self_1,
                    )
                }
                ConstExpr::Binary(__self_0, __self_1, __self_2) => {
                    ::core::fmt::Formatter::debug_tuple_field3_finish(
                        f,
                        "Binary",
                        __self_0,
                        __self_1,
                        &__self_2,
                    )
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for ConstExpr {
        #[inline]
        fn clone(&self) -> ConstExpr {
            match self {
                ConstExpr::Int(__self_0) => {
                    ConstExpr::Int(::core::clone::Clone::clone(__self_0))
                }
                ConstExpr::Bool(__self_0) => {
                    ConstExpr::Bool(::core::clone::Clone::clone(__self_0))
                }
                ConstExpr::Char(__self_0) => {
                    ConstExpr::Char(::core::clone::Clone::clone(__self_0))
                }
                ConstExpr::Real(__self_0) => {
                    ConstExpr::Real(::core::clone::Clone::clone(__self_0))
                }
                ConstExpr::Const(__self_0) => {
                    ConstExpr::Const(::core::clone::Clone::clone(__self_0))
                }
                ConstExpr::Call(__self_0, __self_1) => {
                    ConstExpr::Call(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                ConstExpr::Unary(__self_0, __self_1) => {
                    ConstExpr::Unary(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                    )
                }
                ConstExpr::Binary(__self_0, __self_1, __self_2) => {
                    ConstExpr::Binary(
                        ::core::clone::Clone::clone(__self_0),
                        ::core::clone::Clone::clone(__self_1),
                        ::core::clone::Clone::clone(__self_2),
                    )
                }
            }
        }
    }
    pub enum UnOp {
        Neg,
        Not,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for UnOp {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(
                f,
                match self {
                    UnOp::Neg => "Neg",
                    UnOp::Not => "Not",
                },
            )
        }
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for UnOp {}
    #[automatically_derived]
    impl ::core::clone::Clone for UnOp {
        #[inline]
        fn clone(&self) -> UnOp {
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for UnOp {}
    pub enum BinOp {
        Add,
        Sub,
        Mul,
        RealDiv,
        Div,
        Mod,
        And,
        Or,
        Xor,
        In,
        Eq,
        Ne,
        Lt,
        Le,
        Gt,
        Ge,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for BinOp {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(
                f,
                match self {
                    BinOp::Add => "Add",
                    BinOp::Sub => "Sub",
                    BinOp::Mul => "Mul",
                    BinOp::RealDiv => "RealDiv",
                    BinOp::Div => "Div",
                    BinOp::Mod => "Mod",
                    BinOp::And => "And",
                    BinOp::Or => "Or",
                    BinOp::Xor => "Xor",
                    BinOp::In => "In",
                    BinOp::Eq => "Eq",
                    BinOp::Ne => "Ne",
                    BinOp::Lt => "Lt",
                    BinOp::Le => "Le",
                    BinOp::Gt => "Gt",
                    BinOp::Ge => "Ge",
                },
            )
        }
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for BinOp {}
    #[automatically_derived]
    impl ::core::clone::Clone for BinOp {
        #[inline]
        fn clone(&self) -> BinOp {
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for BinOp {}
}
mod codegen {
    use std::collections::HashMap;
    use crate::ast::*;
    use crate::sema::*;
    struct VarAccess {
        slot: String,
        ty: TypeInfo,
        by_ref: bool,
        conformant_bounds: Option<Vec<(String, String)>>,
    }
    #[automatically_derived]
    impl ::core::clone::Clone for VarAccess {
        #[inline]
        fn clone(&self) -> VarAccess {
            VarAccess {
                slot: ::core::clone::Clone::clone(&self.slot),
                ty: ::core::clone::Clone::clone(&self.ty),
                by_ref: ::core::clone::Clone::clone(&self.by_ref),
                conformant_bounds: ::core::clone::Clone::clone(&self.conformant_bounds),
            }
        }
    }
    struct Ctx {
        vars: HashMap<String, VarAccess>,
        routines: HashMap<String, String>,
    }
    #[automatically_derived]
    impl ::core::clone::Clone for Ctx {
        #[inline]
        fn clone(&self) -> Ctx {
            Ctx {
                vars: ::core::clone::Clone::clone(&self.vars),
                routines: ::core::clone::Clone::clone(&self.routines),
            }
        }
    }
    struct AddrRef {
        base_expr: String,
        offset: u32,
        dynamic_addr_expr: Option<String>,
        ty: TypeInfo,
        variant_checks: Vec<RuntimeVariantCheck>,
    }
    #[automatically_derived]
    impl ::core::clone::Clone for AddrRef {
        #[inline]
        fn clone(&self) -> AddrRef {
            AddrRef {
                base_expr: ::core::clone::Clone::clone(&self.base_expr),
                offset: ::core::clone::Clone::clone(&self.offset),
                dynamic_addr_expr: ::core::clone::Clone::clone(&self.dynamic_addr_expr),
                ty: ::core::clone::Clone::clone(&self.ty),
                variant_checks: ::core::clone::Clone::clone(&self.variant_checks),
            }
        }
    }
    struct RuntimeVariantCheck {
        tag_addr_expr: String,
        allowed_ranges: Vec<(i32, i32)>,
    }
    #[automatically_derived]
    impl ::core::clone::Clone for RuntimeVariantCheck {
        #[inline]
        fn clone(&self) -> RuntimeVariantCheck {
            RuntimeVariantCheck {
                tag_addr_expr: ::core::clone::Clone::clone(&self.tag_addr_expr),
                allowed_ranges: ::core::clone::Clone::clone(&self.allowed_ranges),
            }
        }
    }
    pub struct ForthGen<'a> {
        env: &'a Env,
        out: String,
        indent: usize,
        routine_frames: HashMap<String, Vec<String>>,
        string_literals: Vec<(String, String)>,
        sum_case_bind_sp: usize,
    }
    impl<'a> ForthGen<'a> {
        pub fn new(env: &'a Env) -> Self {
            Self {
                env,
                out: String::new(),
                indent: 0,
                routine_frames: HashMap::new(),
                string_literals: Vec::new(),
                sum_case_bind_sp: 0,
            }
        }
        fn wln(&mut self, s: &str) {
            for _ in 0..self.indent {
                self.out.push_str("  ");
            }
            self.out.push_str(s);
            self.out.push('\n');
        }
        pub fn finish(self) -> String {
            self.out
        }
        pub fn gen_program(mut self, prog: &Program) -> Result<String, String> {
            self.collect_string_literals_program(prog);
            self.collect_routine_frames(&prog.block.routines, "program");
            self.emit_debug_name_map(&prog.block.routines, "program");
            let max_agg_ret_bytes = self.max_aggregate_return_bytes(prog)?;
            self.wln("");
            for c in &prog.block.consts {
                let v = eval_const(self.env, &c.expr)?;
                match v {
                    ConstVal::I32(i) => {
                        self.wln(
                            &::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!("{1} CONSTANT {0}", c.name, i),
                                )
                            }),
                        )
                    }
                    ConstVal::U32(u) => {
                        self.wln(
                            &::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!("{1} CONSTANT {0}", c.name, u),
                                )
                            }),
                        )
                    }
                    ConstVal::Real(bits) => {
                        self.wln(
                            &::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!("{1} CONSTANT {0}", c.name, bits),
                                )
                            }),
                        )
                    }
                    ConstVal::EnumVal { ordinal, .. } => {
                        self.wln(
                            &::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!("{1} CONSTANT {0}", c.name, ordinal),
                                )
                            }),
                        )
                    }
                    ConstVal::Bool(b) => {
                        self.wln(
                            &::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!(
                                        "{0} CONSTANT {1}",
                                        if b { 1 } else { 0 },
                                        c.name,
                                    ),
                                )
                            }),
                        )
                    }
                }
            }
            for v in &prog.block.vars {
                let t = self
                    .env
                    .vars
                    .get(&v.name)
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("internal: missing var type for {0}", v.name),
                        )
                    }))?;
                self.emit_storage_decl(&v.name, t)?;
            }
            self.emit_string_literal_storage()?;
            self.wln("CREATE __CASE_MATCH 0 ,");
            self.wln("CREATE __WSTR_STOP 0 ,");
            self.wln("CREATE __CP_SRC 0 ,");
            self.wln("CREATE __CP_DST 0 ,");
            self.wln("CREATE __CP_N 0 ,");
            self.wln("CREATE __CP_I 0 ,");
            self.wln("CREATE __CALL_RET 0 ,");
            self.wln("CREATE __EQ_A 0 ,");
            self.wln("CREATE __EQ_B 0 ,");
            self.wln("CREATE __EQ_N 0 ,");
            self.wln("CREATE __EQ_I 0 ,");
            self.wln("CREATE __EQ_OK 0 ,");
            self.wln("CREATE __CRS 0 ,");
            self.emit_storage_bytes_decl("__CRA", max_agg_ret_bytes.max(4));
            for i in 0..32 {
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("CREATE __SCB{0} 0 ,", i))
                    }),
                );
            }
            self.wln("CREATE __NEWP 0 ,");
            self.wln("CREATE __HEX_PTR 0 ,");
            self.wln("CREATE __HEX_LEN 0 ,");
            self.wln("CREATE __HEX_ACC 0 ,");
            self.wln("CREATE __HEX_I 0 ,");
            self.wln("CREATE __HEX_STOP 0 ,");
            self.wln("CREATE __I2H_VAL 0 ,");
            self.wln("CREATE __I2H_PTR 0 ,");
            self.wln("CREATE __I2H_MAX 0 ,");
            self.wln("CREATE __I2H_FILL 0 ,");
            self.wln("CREATE __I2H_REQ 0 ,");
            self.wln("CREATE __I2H_WIDTH 0 ,");
            self.wln("CREATE __I2H_I 0 ,");
            self.wln("CREATE __I2H_SRC 0 ,");
            self.wln("CREATE __STR_SRC 0 ,");
            self.wln("CREATE __STR_DST 0 ,");
            self.wln("CREATE __STR_A 0 ,");
            self.wln("CREATE __STR_B 0 ,");
            self.wln("CREATE __STR_I 0 ,");
            self.wln("CREATE __STR_J 0 ,");
            self.wln("CREATE __STR_K 0 ,");
            self.wln("CREATE __STR_LEN 0 ,");
            self.wln("CREATE __STR_IDX 0 ,");
            self.wln("CREATE __STR_CNT 0 ,");
            self.wln("CREATE __STR_POS 0 ,");
            self.wln("CREATE __STR_MATCH 0 ,");
            self.wln("CREATE __VAR_TAG 0 ,");
            self.wln(": PAGG-EQ");
            self.indent += 1;
            self.wln("__EQ_N PVAR!");
            self.wln("__EQ_B PVAR!");
            self.wln("__EQ_A PVAR!");
            self.wln("1 __EQ_OK PVAR!");
            self.wln("0 __EQ_I PVAR!");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln("__EQ_OK PVAR@ 0 <> __EQ_I PVAR@ __EQ_N PVAR@ < AND WHILE");
            self.indent += 1;
            self.wln("__EQ_A PVAR@ __EQ_I PVAR@ 4 * + PVAR@");
            self.wln("__EQ_B PVAR@ __EQ_I PVAR@ 4 * + PVAR@");
            self.wln("= 0= IF");
            self.indent += 1;
            self.wln("0 __EQ_OK PVAR!");
            self.indent -= 1;
            self.wln("THEN");
            self.wln("__EQ_I PVAR@ 1 + __EQ_I PVAR!");
            self.indent -= 1;
            self.indent -= 1;
            self.wln("REPEAT");
            self.wln("__EQ_OK PVAR@");
            self.indent -= 1;
            self.wln(";");
            self.emit_slots_recursive(&prog.block.routines, "program")?;
            self.wln(": __HEX_TO_I32");
            self.indent += 1;
            self.wln("0 __HEX_ACC PVAR!");
            self.wln("0 __HEX_I PVAR!");
            self.wln("0 __HEX_STOP PVAR!");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln("__HEX_STOP PVAR@ 0= __HEX_I PVAR@ __HEX_LEN PVAR@ < AND WHILE");
            self.indent += 1;
            self.wln("__HEX_PTR PVAR@ __HEX_I PVAR@ 4 * + PVAR@ DUP 0= IF");
            self.indent += 1;
            self.wln("DROP");
            self.wln("1 __HEX_STOP PVAR!");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("DUP 48 >= OVER 57 <= AND IF");
            self.indent += 1;
            self.wln("48 - __HEX_ACC PVAR@ 16 * + __HEX_ACC PVAR!");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("DUP 65 >= OVER 70 <= AND IF");
            self.indent += 1;
            self.wln("55 - __HEX_ACC PVAR@ 16 * + __HEX_ACC PVAR!");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("DUP 97 >= OVER 102 <= AND IF");
            self.indent += 1;
            self.wln("87 - __HEX_ACC PVAR@ 16 * + __HEX_ACC PVAR!");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("DROP");
            self.wln("1 __HEX_STOP PVAR!");
            self.indent -= 1;
            self.wln("THEN");
            self.indent -= 1;
            self.wln("THEN");
            self.indent -= 1;
            self.wln("THEN");
            self.indent -= 1;
            self.wln("THEN");
            self.wln("__HEX_I PVAR@ 1 + __HEX_I PVAR!");
            self.indent -= 1;
            self.indent -= 1;
            self.wln("REPEAT");
            self.wln("__HEX_ACC PVAR@");
            self.indent -= 1;
            self.wln(";");
            self.wln(": __HEX_DIGIT");
            self.indent += 1;
            self.wln("DUP 10 < IF");
            self.indent += 1;
            self.wln("48 +");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("55 +");
            self.indent -= 1;
            self.wln("THEN");
            self.indent -= 1;
            self.wln(";");
            self.wln(": __I32_TO_HEX_STR");
            self.indent += 1;
            self.wln("__I2H_MAX PVAR@ 0< IF");
            self.indent += 1;
            self.wln("0 __I2H_MAX PVAR!");
            self.indent -= 1;
            self.wln("THEN");
            self.wln("1 __I2H_REQ PVAR!");
            self.wln("7 __I2H_I PVAR!");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln("__I2H_I PVAR@ 0 >= WHILE");
            self.indent += 1;
            self.wln("__I2H_VAL PVAR@ __I2H_I PVAR@ 4 * RSHIFT 15 AND DUP 0= 0= IF");
            self.indent += 1;
            self.wln("__I2H_I PVAR@ 1 + __I2H_REQ PVAR!");
            self.wln("DROP");
            self.wln("-1 __I2H_I PVAR!");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("DROP");
            self.wln("__I2H_I PVAR@ 1 - __I2H_I PVAR!");
            self.indent -= 1;
            self.wln("THEN");
            self.indent -= 1;
            self.indent -= 1;
            self.wln("REPEAT");
            self.wln("__I2H_FILL PVAR@ IF");
            self.indent += 1;
            self.wln("__I2H_MAX PVAR@ __I2H_WIDTH PVAR!");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("__I2H_REQ PVAR@ __I2H_MAX PVAR@ < IF");
            self.indent += 1;
            self.wln("__I2H_REQ PVAR@ __I2H_WIDTH PVAR!");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("__I2H_MAX PVAR@ __I2H_WIDTH PVAR!");
            self.indent -= 1;
            self.wln("THEN");
            self.indent -= 1;
            self.wln("THEN");
            self.wln("0 __I2H_I PVAR!");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln("__I2H_I PVAR@ __I2H_WIDTH PVAR@ < WHILE");
            self.indent += 1;
            self.wln("__I2H_FILL PVAR@ IF");
            self.indent += 1;
            self.wln("__I2H_WIDTH PVAR@ __I2H_I PVAR@ 1 + - __I2H_SRC PVAR!");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln(
                "__I2H_REQ PVAR@ __I2H_WIDTH PVAR@ - __I2H_WIDTH PVAR@ __I2H_I PVAR@ 1 + - + __I2H_SRC PVAR!",
            );
            self.indent -= 1;
            self.wln("THEN");
            self.wln("__I2H_SRC PVAR@ 8 >= IF");
            self.indent += 1;
            self.wln("48");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("__I2H_VAL PVAR@ __I2H_SRC PVAR@ 4 * RSHIFT 15 AND __HEX_DIGIT");
            self.indent -= 1;
            self.wln("THEN");
            self.wln("__I2H_PTR PVAR@ __I2H_I PVAR@ 4 * + PVAR!");
            self.wln("__I2H_I PVAR@ 1 + __I2H_I PVAR!");
            self.indent -= 1;
            self.indent -= 1;
            self.wln("REPEAT");
            self.wln("0 __I2H_PTR PVAR@ __I2H_WIDTH PVAR@ 4 * + PVAR!");
            self.indent -= 1;
            self.wln(";");
            self.wln(": __STRLEN");
            self.indent += 1;
            self.wln("0 __STR_I PVAR!");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln("__STR_SRC PVAR@ __STR_I PVAR@ 4 * + PVAR@ 0= IF");
            self.indent += 1;
            self.wln("1");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("__STR_I PVAR@ 1 + __STR_I PVAR!");
            self.wln("0");
            self.indent -= 1;
            self.wln("THEN");
            self.indent -= 1;
            self.wln("UNTIL");
            self.wln("__STR_I PVAR@");
            self.indent -= 1;
            self.wln(";");
            self.wln(": __STRCPY");
            self.indent += 1;
            self.wln("0 __STR_I PVAR!");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln(
                "__STR_SRC PVAR@ __STR_I PVAR@ 4 * + PVAR@ DUP __STR_DST PVAR@ __STR_I PVAR@ 4 * + PVAR!",
            );
            self.wln("0= IF");
            self.indent += 1;
            self.wln("1");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("__STR_I PVAR@ 1 + __STR_I PVAR!");
            self.wln("0");
            self.indent -= 1;
            self.wln("THEN");
            self.indent -= 1;
            self.wln("UNTIL");
            self.indent -= 1;
            self.wln(";");
            self.wln(": __STRPOS");
            self.indent += 1;
            self.wln("__STR_A PVAR@ __STR_SRC PVAR!");
            self.wln("__STRLEN __STR_LEN PVAR!");
            self.wln("__STR_LEN PVAR@ 0= IF");
            self.indent += 1;
            self.wln("1");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("0 __STR_POS PVAR!");
            self.wln("0 __STR_I PVAR!");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln(
                "__STR_POS PVAR@ 0= __STR_B PVAR@ __STR_I PVAR@ 4 * + PVAR@ 0= 0= AND WHILE",
            );
            self.indent += 1;
            self.wln("0 __STR_J PVAR!");
            self.wln("1 __STR_MATCH PVAR!");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln(
                "__STR_MATCH PVAR@ __STR_A PVAR@ __STR_J PVAR@ 4 * + PVAR@ 0= 0= AND WHILE",
            );
            self.indent += 1;
            self.wln("__STR_B PVAR@ __STR_I PVAR@ __STR_J PVAR@ + 4 * + PVAR@");
            self.wln("__STR_A PVAR@ __STR_J PVAR@ 4 * + PVAR@ = 0= IF");
            self.indent += 1;
            self.wln("0 __STR_MATCH PVAR!");
            self.indent -= 1;
            self.wln("THEN");
            self.wln("__STR_B PVAR@ __STR_I PVAR@ __STR_J PVAR@ + 4 * + PVAR@ 0= IF");
            self.indent += 1;
            self.wln("0 __STR_MATCH PVAR!");
            self.indent -= 1;
            self.wln("THEN");
            self.wln("__STR_J PVAR@ 1 + __STR_J PVAR!");
            self.indent -= 1;
            self.indent -= 1;
            self.wln("REPEAT");
            self.wln(
                "__STR_MATCH PVAR@ __STR_A PVAR@ __STR_J PVAR@ 4 * + PVAR@ 0= AND IF",
            );
            self.indent += 1;
            self.wln("__STR_I PVAR@ 1 + __STR_POS PVAR!");
            self.indent -= 1;
            self.wln("THEN");
            self.wln("__STR_I PVAR@ 1 + __STR_I PVAR!");
            self.indent -= 1;
            self.indent -= 1;
            self.wln("REPEAT");
            self.wln("__STR_POS PVAR@");
            self.indent -= 1;
            self.wln("THEN");
            self.indent -= 1;
            self.wln(";");
            self.wln(": __STRDELETE");
            self.indent += 1;
            self.wln("__STR_CNT PVAR@ 0 <= IF");
            self.indent += 1;
            self.wln("( no-op )");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("__STR_IDX PVAR@ 1 < IF");
            self.indent += 1;
            self.wln("1 __STR_IDX PVAR!");
            self.indent -= 1;
            self.wln("THEN");
            self.wln("__STR_IDX PVAR@ 1 - __STR_I PVAR!");
            self.wln("__STR_I PVAR@ __STR_CNT PVAR@ + __STR_J PVAR!");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln(
                "__STR_DST PVAR@ __STR_J PVAR@ 4 * + PVAR@ DUP __STR_DST PVAR@ __STR_I PVAR@ 4 * + PVAR!",
            );
            self.wln("0= IF");
            self.indent += 1;
            self.wln("1");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("__STR_I PVAR@ 1 + __STR_I PVAR!");
            self.wln("__STR_J PVAR@ 1 + __STR_J PVAR!");
            self.wln("0");
            self.indent -= 1;
            self.wln("THEN");
            self.indent -= 1;
            self.wln("UNTIL");
            self.indent -= 1;
            self.wln("THEN");
            self.indent -= 1;
            self.wln(";");
            self.wln(": __STRINSERT");
            self.indent += 1;
            self.wln("__STR_SRC PVAR@ __STR_A PVAR!");
            self.wln("__STR_DST PVAR@ __STR_B PVAR!");
            self.wln("__STR_A PVAR@ __STR_SRC PVAR!");
            self.wln("__STRLEN __STR_LEN PVAR!");
            self.wln("__STR_IDX PVAR@ 1 < IF");
            self.indent += 1;
            self.wln("1 __STR_IDX PVAR!");
            self.indent -= 1;
            self.wln("THEN");
            self.wln("__STR_B PVAR@ __STR_SRC PVAR!");
            self.wln("__STRLEN __STR_J PVAR!");
            self.wln("__STR_IDX PVAR@ 1 - __STR_I PVAR!");
            self.wln("__STR_I PVAR@ __STR_J PVAR@ > IF");
            self.indent += 1;
            self.wln("__STR_J PVAR@ __STR_I PVAR!");
            self.indent -= 1;
            self.wln("THEN");
            self.wln("__STR_J PVAR@ __STR_K PVAR!");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln(
                "__STR_DST PVAR@ __STR_K PVAR@ 4 * + PVAR@ __STR_DST PVAR@ __STR_K PVAR@ __STR_LEN PVAR@ + 4 * + PVAR!",
            );
            self.wln("__STR_K PVAR@ __STR_I PVAR@ = IF");
            self.indent += 1;
            self.wln("1");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("__STR_K PVAR@ 1 - __STR_K PVAR!");
            self.wln("0");
            self.indent -= 1;
            self.wln("THEN");
            self.indent -= 1;
            self.wln("UNTIL");
            self.wln("0 __STR_K PVAR!");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln("__STR_A PVAR@ __STR_K PVAR@ 4 * + PVAR@ DUP 0= IF");
            self.indent += 1;
            self.wln("DROP");
            self.wln("1");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("__STR_DST PVAR@ __STR_I PVAR@ __STR_K PVAR@ + 4 * + PVAR!");
            self.wln("__STR_K PVAR@ 1 + __STR_K PVAR!");
            self.wln("0");
            self.indent -= 1;
            self.wln("THEN");
            self.indent -= 1;
            self.wln("UNTIL");
            self.indent -= 1;
            self.wln(";");
            self.wln(": __VARIANT_MISMATCH");
            self.indent += 1;
            self.wln("S\" Variant tag mismatch\" TYPE");
            self.wln("PWRITELN");
            self.wln("1 0 / DROP");
            self.indent -= 1;
            self.wln(";");
            self.wln(": __SUBRANGE_MISMATCH");
            self.indent += 1;
            self.wln("S\" Subrange check failed\" TYPE");
            self.wln("PWRITELN");
            self.wln("1 0 / DROP");
            self.indent -= 1;
            self.wln(";");
            self.wln("");
            let main_ctx = self.main_ctx(&prog.block.routines, "program");
            self.emit_routines_recursive(&prog.block.routines, "program", &main_ctx)?;
            self.wln(": MAIN");
            self.indent += 1;
            self.gen_stmt_with_ctx(&prog.block.body, &main_ctx)?;
            self.indent -= 1;
            self.wln(";");
            self.wln("MAIN");
            Ok(self.finish())
        }
        fn emit_debug_name_map(&mut self, routines: &[RoutineDecl], scope: &str) {
            self.wln("( DEBUG NAME MAP: Pascal scoped name => generated word )");
            self.emit_debug_name_map_recursive(routines, scope);
        }
        fn emit_debug_name_map_recursive(
            &mut self,
            routines: &[RoutineDecl],
            scope: &str,
        ) {
            for r in routines {
                let (name, block, params, has_ret) = match r {
                    RoutineDecl::Procedure(p) => (&p.name, &p.block, &p.params, false),
                    RoutineDecl::Function(f) => (&f.name, &f.block, &f.params, true),
                };
                let scoped = ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0}::{1}", scope, name))
                });
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "( ROUTINE {1} => {0} )",
                                self.routine_word(&scoped),
                                scoped,
                            ),
                        )
                    }),
                );
                for prm in params {
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "( SLOT {2}::{0} => {1} )",
                                    prm.name,
                                    self.slot_name(&scoped, &prm.name),
                                    scoped,
                                ),
                            )
                        }),
                    );
                }
                for lv in &block.vars {
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "( SLOT {2}::{0} => {1} )",
                                    lv.name,
                                    self.slot_name(&scoped, &lv.name),
                                    scoped,
                                ),
                            )
                        }),
                    );
                }
                if has_ret {
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "( SLOT {1}::{2} => {0} )",
                                    self.slot_name(&scoped, name),
                                    scoped,
                                    name,
                                ),
                            )
                        }),
                    );
                }
                self.emit_debug_name_map_recursive(&block.routines, &scoped);
            }
        }
        fn emit_slots_recursive(
            &mut self,
            routines: &[RoutineDecl],
            scope: &str,
        ) -> Result<(), String> {
            for r in routines {
                let (name, block, params, has_ret) = match r {
                    RoutineDecl::Procedure(p) => (&p.name, &p.block, &p.params, false),
                    RoutineDecl::Function(f) => (&f.name, &f.block, &f.params, true),
                };
                let scoped = ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0}::{1}", scope, name))
                });
                for prm in params {
                    if let Some(c) = &prm.conformant {
                        for dim in &c.dims {
                            self.emit_storage_decl(
                                &self.slot_name(&scoped, &dim.low_name),
                                &self.ty_of_typeref(&dim.index_ty)?,
                            )?;
                            self.emit_storage_decl(
                                &self.slot_name(&scoped, &dim.high_name),
                                &self.ty_of_typeref(&dim.index_ty)?,
                            )?;
                        }
                        self.emit_storage_decl(
                            &self.slot_name(&scoped, &prm.name),
                            &TypeInfo::Pointer("__conformant_array".into()),
                        )?;
                        continue;
                    }
                    let ty = self.ty_of_typeref(&prm.ty)?;
                    self.emit_storage_decl(&self.slot_name(&scoped, &prm.name), &ty)?;
                }
                for lv in &block.vars {
                    let ty = self.ty_of_typeref(&lv.ty)?;
                    self.emit_storage_decl(&self.slot_name(&scoped, &lv.name), &ty)?;
                }
                if has_ret {
                    let ty = match r {
                        RoutineDecl::Function(f) => self.ty_of_typeref(&f.ret_ty)?,
                        _ => TypeInfo::Basic(BasicType::Integer),
                    };
                    self.emit_storage_decl(&self.slot_name(&scoped, name), &ty)?;
                }
                self.emit_slots_recursive(&block.routines, &scoped)?;
            }
            Ok(())
        }
        fn emit_routines_recursive(
            &mut self,
            routines: &[RoutineDecl],
            scope: &str,
            parent_ctx: &Ctx,
        ) -> Result<(), String> {
            let visible = self
                .extend_routine_visibility(&parent_ctx.routines, routines, scope);
            for r in routines {
                let (name, block) = match r {
                    RoutineDecl::Procedure(p) => (&p.name, &p.block),
                    RoutineDecl::Function(f) => (&f.name, &f.block),
                };
                let scoped = ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0}::{1}", scope, name))
                });
                let mut routine_ctx = Ctx {
                    vars: parent_ctx.vars.clone(),
                    routines: visible.clone(),
                };
                self.extend_vars_for_routine(r, &scoped, &mut routine_ctx)?;
                let body_routines = self
                    .extend_routine_visibility(
                        &routine_ctx.routines,
                        &block.routines,
                        &scoped,
                    );
                let body_ctx = Ctx {
                    vars: routine_ctx.vars.clone(),
                    routines: body_routines,
                };
                self.emit_routines_recursive(&block.routines, &scoped, &routine_ctx)?;
                self.gen_routine_scoped(r, &scoped, &body_ctx)?;
                self.wln("");
            }
            Ok(())
        }
        fn gen_routine_scoped(
            &mut self,
            r: &RoutineDecl,
            scoped: &str,
            ctx: &Ctx,
        ) -> Result<(), String> {
            match r {
                RoutineDecl::Procedure(p) => {
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(": {0}", self.routine_word(scoped)),
                            )
                        }),
                    );
                    self.indent += 1;
                    for prm in p.params.iter().rev() {
                        for slot in self
                            .runtime_param_slots(scoped, std::slice::from_ref(prm))
                            .iter()
                            .rev()
                        {
                            if slot == &self.slot_name(scoped, &prm.name) && !prm.by_ref
                                && prm.conformant.is_none()
                            {
                                self.emit_param_store(slot, &self.ty_of_typeref(&prm.ty)?);
                            } else {
                                self.wln(
                                    &::alloc::__export::must_use({
                                        ::alloc::fmt::format(format_args!("{0} PVAR!", slot))
                                    }),
                                );
                            }
                        }
                    }
                    self.gen_stmt_with_ctx(&p.block.body, ctx)?;
                    self.indent -= 1;
                    self.wln(";");
                }
                RoutineDecl::Function(f) => {
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(": {0}", self.routine_word(scoped)),
                            )
                        }),
                    );
                    self.indent += 1;
                    for prm in f.params.iter().rev() {
                        for slot in self
                            .runtime_param_slots(scoped, std::slice::from_ref(prm))
                            .iter()
                            .rev()
                        {
                            if slot == &self.slot_name(scoped, &prm.name) && !prm.by_ref
                                && prm.conformant.is_none()
                            {
                                self.emit_param_store(slot, &self.ty_of_typeref(&prm.ty)?);
                            } else {
                                self.wln(
                                    &::alloc::__export::must_use({
                                        ::alloc::fmt::format(format_args!("{0} PVAR!", slot))
                                    }),
                                );
                            }
                        }
                    }
                    self.gen_stmt_with_ctx(&f.block.body, ctx)?;
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} PVAR@", self.slot_name(scoped, &f.name)),
                            )
                        }),
                    );
                    self.indent -= 1;
                    self.wln(";");
                }
            }
            Ok(())
        }
        fn gen_stmt_with_ctx(&mut self, s: &Stmt, ctx: &Ctx) -> Result<(), String> {
            match s {
                Stmt::Empty => Ok(()),
                Stmt::Compound(stmts) => {
                    for st in stmts {
                        self.gen_stmt_with_ctx(st, ctx)?;
                    }
                    Ok(())
                }
                Stmt::Assign(lv, rhs) => {
                    let dst = self.resolve_lvalue_addr_ctx(lv, ctx)?;
                    self.gen_assign_expr_to_dst(&dst, rhs, ctx)
                }
                Stmt::Read(args) => {
                    let mut i = 0usize;
                    while i < args.len() {
                        let lv = expr_to_lvalue(&args[i])
                            .ok_or(
                                "Read arguments must be lvalues, except string max length",
                            )?;
                        let dst = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                        if #[allow(non_exhaustive_omitted_patterns)]
                        match &dst.ty {
                            TypeInfo::Array(
                                ai,
                            ) if #[allow(non_exhaustive_omitted_patterns)]
                            match ai.elem_ty.as_ref() {
                                TypeInfo::Basic(BasicType::Char) => true,
                                _ => false,
                            } => true,
                            _ => false,
                        } {
                            if i + 1 >= args.len() {
                                return Err(
                                    "Read on array of char requires max length".into(),
                                );
                            }
                            self.emit_char_array_read(
                                &dst,
                                &self.gen_expr_inline_ctx(&args[i + 1], ctx)?,
                                ctx,
                                lv.base.as_str(),
                            )?;
                            i += 2;
                            continue;
                        }
                        let read_word = match dst.ty {
                            TypeInfo::Basic(BasicType::Integer) => "PREAD-I32",
                            TypeInfo::Basic(BasicType::Boolean) => "PREAD-BOOL",
                            TypeInfo::Basic(BasicType::Char) => "PREAD-CHAR",
                            TypeInfo::Basic(BasicType::Real) => "PREAD-F32",
                            TypeInfo::Enum(_) | TypeInfo::Subrange(_) => "PREAD-I32",
                            TypeInfo::Pointer(_) | TypeInfo::Nil => "PREAD-I32",
                            TypeInfo::Record(_)
                            | TypeInfo::Sum(_)
                            | TypeInfo::Array(_) => {
                                return Err("Read on aggregate type is not supported".into());
                            }
                            TypeInfo::Set(_) => {
                                return Err("Read on set type is not supported".into());
                            }
                        };
                        self.emit_store(read_word, &dst);
                        i += 1;
                    }
                    Ok(())
                }
                Stmt::ReadLn => {
                    self.wln("PREADLN");
                    Ok(())
                }
                Stmt::For { var, init, limit, downto, body } => {
                    let lv = LValue {
                        base: var.clone(),
                        sels: ::alloc::vec::Vec::new(),
                    };
                    let dst = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                    self.emit_store(&self.gen_expr_inline_ctx(init, ctx)?, &dst);
                    self.wln("BEGIN");
                    self.indent += 1;
                    let cur = self.emit_load_inline(&dst);
                    let lim = self.gen_expr_inline_ctx(limit, ctx)?;
                    if *downto {
                        self.wln(
                            &::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!("{0} {1} >= WHILE", cur, lim),
                                )
                            }),
                        );
                    } else {
                        self.wln(
                            &::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!("{0} {1} <= WHILE", cur, lim),
                                )
                            }),
                        );
                    }
                    self.indent += 1;
                    self.gen_stmt_with_ctx(body, ctx)?;
                    let step = if *downto { "1 -" } else { "1 +" };
                    let upd = ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("{0} {1}", self.emit_load_inline(&dst), step),
                        )
                    });
                    self.emit_store(&upd, &dst);
                    self.indent -= 1;
                    self.indent -= 1;
                    self.wln("REPEAT");
                    Ok(())
                }
                Stmt::Case { expr, arms, else_stmt } => {
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} >R", self.gen_expr_inline_ctx(expr, ctx)?),
                            )
                        }),
                    );
                    self.wln("0 __CASE_MATCH PVAR!");
                    for (labels, st) in arms {
                        self.wln("__CASE_MATCH PVAR@ 0= IF");
                        self.indent += 1;
                        self.wln(
                            &::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!("{0} IF", self.case_labels_inline(labels)?),
                                )
                            }),
                        );
                        self.indent += 1;
                        self.wln("1 __CASE_MATCH PVAR!");
                        self.gen_stmt_with_ctx(st, ctx)?;
                        self.indent -= 1;
                        self.wln("THEN");
                        self.indent -= 1;
                        self.wln("THEN");
                    }
                    if let Some(es) = else_stmt {
                        self.wln("__CASE_MATCH PVAR@ 0= IF");
                        self.indent += 1;
                        self.gen_stmt_with_ctx(es, ctx)?;
                        self.indent -= 1;
                        self.wln("THEN");
                    }
                    self.wln("R> DROP");
                    Ok(())
                }
                Stmt::SumCase { expr, arms, else_stmt } => {
                    self.gen_sum_case_stmt(expr, arms, else_stmt.as_deref(), ctx)
                }
                Stmt::ProcCall(name, args) => {
                    if name == "Copy" {
                        return self.gen_builtin_copy(args, ctx);
                    }
                    if name == "Concat" {
                        return self.gen_builtin_concat(args, ctx);
                    }
                    if name == "Delete" {
                        return self.gen_builtin_delete(args, ctx);
                    }
                    if name == "Insert" {
                        return self.gen_builtin_insert(args, ctx);
                    }
                    if name == "IntToHex" {
                        return self.gen_builtin_inttohex(args, ctx);
                    }
                    if name == "SetAddr" {
                        return self.gen_builtin_setaddr(args, ctx);
                    }
                    if name.eq_ignore_ascii_case("new")
                        || name.eq_ignore_ascii_case("dispose")
                    {
                        return self.gen_builtin_new_dispose(name, args, ctx);
                    }
                    self.wln(&self.gen_call_inline_ctx(name, args, ctx)?);
                    Ok(())
                }
                Stmt::If(cond, then_s, else_s) => {
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} IF", self.gen_expr_inline_ctx(cond, ctx)?),
                            )
                        }),
                    );
                    self.indent += 1;
                    self.gen_stmt_with_ctx(then_s, ctx)?;
                    self.indent -= 1;
                    if let Some(es) = else_s {
                        self.wln("ELSE");
                        self.indent += 1;
                        self.gen_stmt_with_ctx(es, ctx)?;
                        self.indent -= 1;
                    }
                    self.wln("THEN");
                    Ok(())
                }
                Stmt::With(bases, body) => {
                    let rewritten = self.rewrite_stmt_with_ctx(body, bases, ctx)?;
                    self.gen_stmt_with_ctx(&rewritten, ctx)
                }
                Stmt::While(cond, body) => {
                    self.wln("BEGIN");
                    self.indent += 1;
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "{0} WHILE",
                                    self.gen_expr_inline_ctx(cond, ctx)?,
                                ),
                            )
                        }),
                    );
                    self.indent += 1;
                    self.gen_stmt_with_ctx(body, ctx)?;
                    self.indent -= 1;
                    self.indent -= 1;
                    self.wln("REPEAT");
                    Ok(())
                }
                Stmt::Repeat(stmts, cond) => {
                    self.wln("BEGIN");
                    self.indent += 1;
                    for st in stmts {
                        self.gen_stmt_with_ctx(st, ctx)?;
                    }
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "{0} UNTIL",
                                    self.gen_expr_inline_ctx(cond, ctx)?,
                                ),
                            )
                        }),
                    );
                    self.indent -= 1;
                    Ok(())
                }
                Stmt::Write(args) => {
                    for e in args {
                        match e {
                            Expr::Str(s) => {
                                self.emit_string_write(s);
                            }
                            _ => {
                                let t = type_of_expr_scoped(
                                    self.env,
                                    &self.ctx_to_types(ctx),
                                    &ctx.routines,
                                    e,
                                )?;
                                if #[allow(non_exhaustive_omitted_patterns)]
                                match &t {
                                    TypeInfo::Array(
                                        ai,
                                    ) if #[allow(non_exhaustive_omitted_patterns)]
                                    match ai.elem_ty.as_ref() {
                                        TypeInfo::Basic(BasicType::Char) => true,
                                        _ => false,
                                    } => true,
                                    _ => false,
                                } {
                                    let lv = expr_to_lvalue(e)
                                        .ok_or("char array write requires lvalue in codegen")?;
                                    let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                                    self.emit_char_array_write(&a, ctx, lv.base.as_str())?;
                                    continue;
                                }
                                match t {
                                    TypeInfo::Basic(BasicType::Char) => {
                                        self.wln(
                                            &::alloc::__export::must_use({
                                                ::alloc::fmt::format(
                                                    format_args!(
                                                        "{0} PWRITE-CHAR",
                                                        self.gen_expr_inline_ctx(e, ctx)?,
                                                    ),
                                                )
                                            }),
                                        );
                                    }
                                    TypeInfo::Basic(BasicType::Boolean) => {
                                        self.wln(
                                            &::alloc::__export::must_use({
                                                ::alloc::fmt::format(
                                                    format_args!(
                                                        "{0} PWRITE-BOOL",
                                                        self.gen_expr_inline_ctx(e, ctx)?,
                                                    ),
                                                )
                                            }),
                                        );
                                    }
                                    TypeInfo::Basic(BasicType::Real) => {
                                        self.wln(
                                            &::alloc::__export::must_use({
                                                ::alloc::fmt::format(
                                                    format_args!(
                                                        "{0} PWRITE-F32",
                                                        self.gen_expr_inline_ctx(e, ctx)?,
                                                    ),
                                                )
                                            }),
                                        );
                                    }
                                    _ => {
                                        self.wln(
                                            &::alloc::__export::must_use({
                                                ::alloc::fmt::format(
                                                    format_args!(
                                                        "{0} PWRITE-I32",
                                                        self.gen_expr_inline_ctx(e, ctx)?,
                                                    ),
                                                )
                                            }),
                                        );
                                    }
                                }
                            }
                        }
                    }
                    Ok(())
                }
                Stmt::WriteLn(args) => {
                    self.gen_stmt_with_ctx(&Stmt::Write(args.clone()), ctx)?;
                    self.wln("PWRITELN");
                    Ok(())
                }
            }
        }
        fn gen_assign_expr_to_dst(
            &mut self,
            dst: &AddrRef,
            rhs: &Expr,
            ctx: &Ctx,
        ) -> Result<(), String> {
            if let Expr::Str(s) = rhs {
                self.emit_char_array_assign(dst, s)?;
                return Ok(());
            }
            if let Expr::Cond { arms, else_block } = rhs {
                return self.gen_cond_assign(dst, arms, else_block, ctx);
            }
            match &dst.ty {
                TypeInfo::Basic(_)
                | TypeInfo::Enum(_)
                | TypeInfo::Subrange(_)
                | TypeInfo::Set(_)
                | TypeInfo::Pointer(_)
                | TypeInfo::Nil => {
                    let rhs_code = self.gen_expr_inline_ctx(rhs, ctx)?;
                    self.emit_store(&rhs_code, dst);
                    Ok(())
                }
                TypeInfo::Record(rec) => {
                    if let Expr::Ctor(name, named) = rhs {
                        return self.emit_record_ctor_into(dst, rec, name, named, ctx);
                    }
                    if let Expr::RecordUpdate(base, updates) = rhs {
                        return self
                            .emit_record_update_into(dst, rec, base, updates, ctx);
                    }
                    if let Expr::Call(name, args) = rhs {
                        return self.gen_aggregate_call_assign(name, args, dst, ctx);
                    }
                    let rlv = expr_to_lvalue(rhs)
                        .ok_or("aggregate assignment requires lvalue rhs in codegen")?;
                    let src = self.resolve_lvalue_addr_ctx(&rlv, ctx)?;
                    let size = self.type_size_bytes(&dst.ty)?;
                    self.emit_aggregate_copy(&src, dst, size);
                    Ok(())
                }
                TypeInfo::Array(_) => {
                    if let Expr::ArrayLit(elems) = rhs {
                        return self.emit_array_literal_into(dst, elems, ctx);
                    }
                    if let Expr::ArrayUpdate(base, updates) = rhs {
                        return self.emit_array_update_into(dst, base, updates, ctx);
                    }
                    if let Expr::Call(name, args) = rhs {
                        return self.gen_aggregate_call_assign(name, args, dst, ctx);
                    }
                    let rlv = expr_to_lvalue(rhs)
                        .ok_or("aggregate assignment requires lvalue rhs in codegen")?;
                    let src = self.resolve_lvalue_addr_ctx(&rlv, ctx)?;
                    let size = self.type_size_bytes(&dst.ty)?;
                    self.emit_aggregate_copy(&src, dst, size);
                    Ok(())
                }
                TypeInfo::Sum(sum) => self.gen_sum_assign(dst, sum, rhs, ctx),
            }
        }
        fn gen_cond_assign(
            &mut self,
            dst: &AddrRef,
            arms: &[CondExprArm],
            else_block: &CondValueBlock,
            ctx: &Ctx,
        ) -> Result<(), String> {
            if arms.is_empty() {
                return Err("COND requires at least one arm".into());
            }
            let cond0 = self.gen_expr_inline_ctx(&arms[0].cond, ctx)?;
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} IF", cond0))
                }),
            );
            self.indent += 1;
            for st in &arms[0].block.stmts {
                self.gen_stmt_with_ctx(st, ctx)?;
            }
            self.gen_assign_expr_to_dst(dst, &arms[0].block.value, ctx)?;
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            if arms.len() == 1 {
                for st in &else_block.stmts {
                    self.gen_stmt_with_ctx(st, ctx)?;
                }
                self.gen_assign_expr_to_dst(dst, &else_block.value, ctx)?;
            } else {
                self.gen_cond_assign(dst, &arms[1..], else_block, ctx)?;
            }
            self.indent -= 1;
            self.wln("THEN");
            Ok(())
        }
        fn gen_sum_assign(
            &mut self,
            dst: &AddrRef,
            sum: &SumInfo,
            rhs: &Expr,
            ctx: &Ctx,
        ) -> Result<(), String> {
            match rhs {
                Expr::Ctor(name, named) => {
                    self.emit_sum_ctor_into(dst, sum, name, named, ctx)
                }
                Expr::OptionNone => self.emit_sum_ctor_into(dst, sum, "none", &[], ctx),
                Expr::OptionSome(v) => {
                    self.emit_sum_ctor_into(
                        dst,
                        sum,
                        "some",
                        &[("value".to_string(), (**v).clone())],
                        ctx,
                    )
                }
                Expr::Call(name, args) if args.is_empty() => {
                    self.emit_sum_ctor_into(dst, sum, name, &[], ctx)
                }
                Expr::Call(name, args) => {
                    self.gen_aggregate_call_assign(name, args, dst, ctx)
                }
                _ => {
                    let rlv = expr_to_lvalue(rhs)
                        .ok_or(
                            "sum-record assignment requires lvalue/constructor/COND rhs in codegen",
                        )?;
                    let src = self.resolve_lvalue_addr_ctx(&rlv, ctx)?;
                    let size = self.type_size_bytes(&dst.ty)?;
                    self.emit_aggregate_copy(&src, dst, size);
                    Ok(())
                }
            }
        }
        fn emit_sum_ctor_into(
            &mut self,
            dst: &AddrRef,
            sum: &SumInfo,
            ctor_name: &str,
            named_args: &[(String, Expr)],
            ctx: &Ctx,
        ) -> Result<(), String> {
            let arm = sum
                .arms
                .iter()
                .find(|a| a.name.eq_ignore_ascii_case(ctor_name))
                .ok_or_else(|| ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("unknown sum constructor: {0}", ctor_name),
                    )
                }))?;
            let total = 4 + sum.payload_size_bytes;
            for ofs in (0..total).step_by(4usize) {
                self.emit_store_at("0", dst, ofs);
            }
            self.emit_store_at(&arm.tag.to_string(), dst, 0);
            for f in &arm.fields {
                let (_, expr) = named_args
                    .iter()
                    .find(|(n, _)| n.eq_ignore_ascii_case(&f.name))
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "constructor {1} missing field {0}",
                                f.name,
                                ctor_name,
                            ),
                        )
                    }))?;
                match &f.ty {
                    TypeInfo::Basic(_)
                    | TypeInfo::Enum(_)
                    | TypeInfo::Subrange(_)
                    | TypeInfo::Set(_)
                    | TypeInfo::Pointer(_)
                    | TypeInfo::Nil => {
                        let rhs = self.gen_expr_inline_ctx(expr, ctx)?;
                        self.emit_store_at(&rhs, dst, 4 + f.offset_bytes);
                    }
                    TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_) => {
                        let lv = expr_to_lvalue(expr)
                            .ok_or_else(|| {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "aggregate constructor field {0} must be lvalue in codegen",
                                            f.name,
                                        ),
                                    )
                                })
                            })?;
                        let src = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                        let field_dst = AddrRef {
                            base_expr: dst.base_expr.clone(),
                            offset: dst.offset + 4 + f.offset_bytes,
                            dynamic_addr_expr: dst.dynamic_addr_expr.clone(),
                            ty: f.ty.clone(),
                            variant_checks: Vec::new(),
                        };
                        let sz = self.type_size_bytes(&f.ty)?;
                        self.emit_aggregate_copy(&src, &field_dst, sz);
                    }
                }
            }
            Ok(())
        }
        fn emit_record_ctor_into(
            &mut self,
            dst: &AddrRef,
            rec: &RecordInfo,
            ctor_name: &str,
            named_args: &[(String, Expr)],
            ctx: &Ctx,
        ) -> Result<(), String> {
            for (fname, finfo) in &rec.fields {
                let (_, expr) = named_args
                    .iter()
                    .find(|(n, _)| n.eq_ignore_ascii_case(fname))
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "constructor {0} missing field {1}",
                                ctor_name,
                                fname,
                            ),
                        )
                    }))?;
                let field_dst = AddrRef {
                    base_expr: dst.base_expr.clone(),
                    offset: dst.offset + finfo.offset_bytes,
                    dynamic_addr_expr: dst.dynamic_addr_expr.clone(),
                    ty: finfo.ty.clone(),
                    variant_checks: Vec::new(),
                };
                self.gen_assign_expr_to_dst(&field_dst, expr, ctx)?;
            }
            Ok(())
        }
        fn emit_array_literal_into(
            &mut self,
            dst: &AddrRef,
            elems: &[Expr],
            ctx: &Ctx,
        ) -> Result<(), String> {
            let arr = match &dst.ty {
                TypeInfo::Array(a) => a.clone(),
                _ => {
                    return Err("internal: array literal destination is not array".into());
                }
            };
            if elems.len() != arr.len as usize {
                return Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "array literal length mismatch in codegen: expected {0}, got {1}",
                                arr.len,
                                elems.len(),
                            ),
                        )
                    }),
                );
            }
            for (i, e) in elems.iter().enumerate() {
                let elem_dst = AddrRef {
                    base_expr: dst.base_expr.clone(),
                    offset: dst.offset + (i as u32) * arr.elem_size_bytes,
                    dynamic_addr_expr: dst.dynamic_addr_expr.clone(),
                    ty: (*arr.elem_ty).clone(),
                    variant_checks: Vec::new(),
                };
                self.gen_assign_expr_to_dst(&elem_dst, e, ctx)?;
            }
            Ok(())
        }
        fn emit_record_update_into(
            &mut self,
            dst: &AddrRef,
            rec: &RecordInfo,
            base: &Expr,
            updates: &[(String, Expr)],
            ctx: &Ctx,
        ) -> Result<(), String> {
            let blv = expr_to_lvalue(base)
                .ok_or("record update base must be lvalue in codegen")?;
            let src = self.resolve_lvalue_addr_ctx(&blv, ctx)?;
            let size = self.type_size_bytes(&dst.ty)?;
            self.emit_aggregate_copy(&src, dst, size);
            for (fname, expr) in updates {
                let (_, finfo) = rec
                    .fields
                    .iter()
                    .find(|(n, _)| n.eq_ignore_ascii_case(fname))
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("record update has no field {0}", fname),
                        )
                    }))?;
                let field_dst = AddrRef {
                    base_expr: dst.base_expr.clone(),
                    offset: dst.offset + finfo.offset_bytes,
                    dynamic_addr_expr: dst.dynamic_addr_expr.clone(),
                    ty: finfo.ty.clone(),
                    variant_checks: Vec::new(),
                };
                self.gen_assign_expr_to_dst(&field_dst, expr, ctx)?;
            }
            Ok(())
        }
        fn emit_array_update_into(
            &mut self,
            dst: &AddrRef,
            base: &Expr,
            updates: &[(Expr, Expr)],
            ctx: &Ctx,
        ) -> Result<(), String> {
            let blv = expr_to_lvalue(base)
                .ok_or("array update base must be lvalue in codegen")?;
            let src = self.resolve_lvalue_addr_ctx(&blv, ctx)?;
            let size = self.type_size_bytes(&dst.ty)?;
            self.emit_aggregate_copy(&src, dst, size);
            let arr = match &dst.ty {
                TypeInfo::Array(a) => a.clone(),
                _ => return Err("internal: array update destination is not array".into()),
            };
            for (idx_expr, val_expr) in updates {
                let idx_code = self.gen_expr_inline_ctx(idx_expr, ctx)?;
                let logical_idx = if arr.low == 0 {
                    idx_code
                } else if arr.low > 0 {
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("{1} {0} -", arr.low, idx_code),
                        )
                    })
                } else {
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("{1} {0} +", -arr.low, idx_code),
                        )
                    })
                };
                let scaled = if arr.elem_size_bytes == 1 {
                    logical_idx
                } else {
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("{1} {0} *", arr.elem_size_bytes, logical_idx),
                        )
                    })
                };
                let elem_dst = AddrRef {
                    base_expr: dst.base_expr.clone(),
                    offset: 0,
                    dynamic_addr_expr: Some(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "{0} {1} +",
                                    self.emit_addr_inline(dst),
                                    scaled,
                                ),
                            )
                        }),
                    ),
                    ty: (*arr.elem_ty).clone(),
                    variant_checks: Vec::new(),
                };
                self.gen_assign_expr_to_dst(&elem_dst, val_expr, ctx)?;
            }
            Ok(())
        }
        fn gen_sum_case_stmt(
            &mut self,
            expr: &Expr,
            arms: &[SumCaseArm],
            else_stmt: Option<&Stmt>,
            ctx: &Ctx,
        ) -> Result<(), String> {
            let et = type_of_expr_scoped(
                self.env,
                &self.ctx_to_types(ctx),
                &ctx.routines,
                expr,
            )?;
            let sum = match et {
                TypeInfo::Sum(s) => s,
                _ => return Err("sum-case requires sum-record expression".into()),
            };
            let lv = expr_to_lvalue(expr)
                .ok_or("sum-case expression must be lvalue in codegen")?;
            let src = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
            let tag_expr = self.emit_load_at(&src, 0);
            self.wln("0 __CASE_MATCH PVAR!");
            for arm in arms {
                let sinfo = sum
                    .arms
                    .iter()
                    .find(|a| a.name.eq_ignore_ascii_case(&arm.ctor))
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "unknown sum-case arm constructor: {0}",
                                arm.ctor,
                            ),
                        )
                    }))?;
                self.wln("__CASE_MATCH PVAR@ 0= IF");
                self.indent += 1;
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("{1} {0} = IF", sinfo.tag, tag_expr),
                        )
                    }),
                );
                self.indent += 1;
                self.wln("1 __CASE_MATCH PVAR!");
                let base = self.sum_case_bind_sp;
                if base + arm.binds.len() > 32 {
                    return Err("sum-case bind temp overflow".into());
                }
                self.sum_case_bind_sp += arm.binds.len();
                let mut arm_ctx = ctx.clone();
                for (idx, bind) in arm.binds.iter().enumerate() {
                    let slot = ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("__SCB{0}", base + idx))
                    });
                    let fi = &sinfo.fields[idx];
                    match &fi.ty {
                        TypeInfo::Basic(_)
                        | TypeInfo::Enum(_)
                        | TypeInfo::Subrange(_)
                        | TypeInfo::Set(_)
                        | TypeInfo::Pointer(_)
                        | TypeInfo::Nil => {
                            let rhs = self.emit_load_at(&src, 4 + fi.offset_bytes);
                            self.wln(
                                &::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0} {1} PVAR!", rhs, slot),
                                    )
                                }),
                            );
                            arm_ctx
                                .vars
                                .insert(
                                    bind.clone(),
                                    VarAccess {
                                        slot,
                                        ty: fi.ty.clone(),
                                        by_ref: false,
                                        conformant_bounds: None,
                                    },
                                );
                        }
                        TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_) => {
                            let field_src = AddrRef {
                                base_expr: src.base_expr.clone(),
                                offset: src.offset + 4 + fi.offset_bytes,
                                dynamic_addr_expr: src.dynamic_addr_expr.clone(),
                                ty: fi.ty.clone(),
                                variant_checks: Vec::new(),
                            };
                            let addr = self.emit_addr_inline(&field_src);
                            self.wln(
                                &::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0} {1} PVAR!", addr, slot),
                                    )
                                }),
                            );
                            arm_ctx
                                .vars
                                .insert(
                                    bind.clone(),
                                    VarAccess {
                                        slot,
                                        ty: fi.ty.clone(),
                                        by_ref: true,
                                        conformant_bounds: None,
                                    },
                                );
                        }
                    }
                }
                self.gen_stmt_with_ctx(&arm.body, &arm_ctx)?;
                self.sum_case_bind_sp = base;
                self.indent -= 1;
                self.wln("THEN");
                self.indent -= 1;
                self.wln("THEN");
            }
            if let Some(es) = else_stmt {
                self.wln("__CASE_MATCH PVAR@ 0= IF");
                self.indent += 1;
                self.gen_stmt_with_ctx(es, ctx)?;
                self.indent -= 1;
                self.wln("THEN");
            }
            Ok(())
        }
        fn gen_expr_inline_ctx(&self, e: &Expr, ctx: &Ctx) -> Result<String, String> {
            match e {
                Expr::Int(i) => Ok(i.to_string()),
                Expr::Bool(b) => Ok(if *b { "1".to_string() } else { "0".to_string() }),
                Expr::Char(u) => Ok(u.to_string()),
                Expr::Real(bits) => Ok(bits.to_string()),
                Expr::Str(_) => {
                    Err("string literal is only allowed in Write/WriteLn".into())
                }
                Expr::Ctor(_, _)
                | Expr::ArrayLit(_)
                | Expr::RecordUpdate(_, _)
                | Expr::ArrayUpdate(_, _)
                | Expr::OptionNone
                | Expr::OptionSome(_)
                | Expr::Cond { .. } => {
                    Err("expression codegen is not integrated for this form yet".into())
                }
                Expr::Cast(_, inner) => self.gen_expr_inline_ctx(inner, ctx),
                Expr::SetLit(items) => self.gen_set_lit_inline(items, ctx),
                Expr::Nil => Ok("0".into()),
                Expr::Var(n) => {
                    if let Some(c) = self.env.consts.get(n) {
                        Ok(
                            match c {
                                ConstVal::I32(i) => i.to_string(),
                                ConstVal::U32(u) => u.to_string(),
                                ConstVal::Real(bits) => bits.to_string(),
                                ConstVal::EnumVal { ordinal, .. } => ordinal.to_string(),
                                ConstVal::Bool(b) => {
                                    if *b { "1".to_string() } else { "0".to_string() }
                                }
                            },
                        )
                    } else {
                        let lv = LValue {
                            base: n.clone(),
                            sels: ::alloc::vec::Vec::new(),
                        };
                        let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                        Ok(self.emit_load_inline(&a))
                    }
                }
                Expr::Call(name, args) => {
                    if let Some(b) = self.gen_builtin_expr_call(name, args, ctx)? {
                        return Ok(b);
                    }
                    self.gen_call_inline_ctx(name, args, ctx)
                }
                Expr::Deref(_) => {
                    let lv = expr_to_lvalue(e).ok_or("deref base must be variable")?;
                    let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                    Ok(self.emit_load_inline(&a))
                }
                Expr::Field(_, _) => {
                    let lv = expr_to_lvalue(e).ok_or("field base must be variable")?;
                    let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                    Ok(self.emit_load_inline(&a))
                }
                Expr::Index(_, _) => {
                    let lv = expr_to_lvalue(e).ok_or("index base must be variable")?;
                    let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                    Ok(self.emit_load_inline(&a))
                }
                Expr::Unary(op, inner) => {
                    let a = self.gen_expr_inline_ctx(inner, ctx)?;
                    match op {
                        UnOp::Neg => {
                            let t = type_of_expr_scoped(
                                self.env,
                                &self.ctx_to_types(ctx),
                                &ctx.routines,
                                inner,
                            )?;
                            Ok(
                                if #[allow(non_exhaustive_omitted_patterns)]
                                match t {
                                    TypeInfo::Basic(BasicType::Real) => true,
                                    _ => false,
                                } {
                                    ::alloc::__export::must_use({
                                        ::alloc::fmt::format(format_args!("{0} FNEGATE", a))
                                    })
                                } else {
                                    ::alloc::__export::must_use({
                                        ::alloc::fmt::format(format_args!("{0} NEGATE", a))
                                    })
                                },
                            )
                        }
                        UnOp::Not => {
                            Ok(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} 0=", a))
                                }),
                            )
                        }
                    }
                }
                Expr::Binary(a, op, b) => {
                    let la = self.gen_expr_inline_ctx(a, ctx)?;
                    let lb = self.gen_expr_inline_ctx(b, ctx)?;
                    use BinOp::*;
                    let ta = type_of_expr_scoped(
                        self.env,
                        &self.ctx_to_types(ctx),
                        &ctx.routines,
                        a,
                    )?;
                    let tb = type_of_expr_scoped(
                        self.env,
                        &self.ctx_to_types(ctx),
                        &ctx.routines,
                        b,
                    )?;
                    let both_realish = #[allow(non_exhaustive_omitted_patterns)]
                    match ta {
                        TypeInfo::Basic(BasicType::Real) => true,
                        _ => false,
                    } || #[allow(non_exhaustive_omitted_patterns)]
                        match tb {
                            TypeInfo::Basic(BasicType::Real) => true,
                            _ => false,
                        } || #[allow(non_exhaustive_omitted_patterns)]
                        match op {
                            RealDiv => true,
                            _ => false,
                        };
                    let la = if both_realish {
                        self.coerce_real_inline(a, &ta, ctx)?
                    } else {
                        la
                    };
                    let lb = if both_realish {
                        self.coerce_real_inline(b, &tb, ctx)?
                    } else {
                        lb
                    };
                    if #[allow(non_exhaustive_omitted_patterns)]
                    match op {
                        BinOp::Eq | BinOp::Ne => true,
                        _ => false,
                    } && #[allow(non_exhaustive_omitted_patterns)]
                        match ta {
                            TypeInfo::Record(_)
                            | TypeInfo::Sum(_)
                            | TypeInfo::Array(_) => true,
                            _ => false,
                        }
                    {
                        let alv = expr_to_lvalue(a)
                            .ok_or(
                                "aggregate comparison requires lvalue lhs in codegen",
                            )?;
                        let blv = expr_to_lvalue(b)
                            .ok_or(
                                "aggregate comparison requires lvalue rhs in codegen",
                            )?;
                        let aa = self.resolve_lvalue_addr_ctx(&alv, ctx)?;
                        let bb = self.resolve_lvalue_addr_ctx(&blv, ctx)?;
                        let cells = self.type_size_bytes(&ta)? / 4;
                        let mut out = ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "{0} {1} {2} PAGG-EQ",
                                    self.emit_addr_inline(&aa),
                                    self.emit_addr_inline(&bb),
                                    cells,
                                ),
                            )
                        });
                        if #[allow(non_exhaustive_omitted_patterns)]
                        match op {
                            BinOp::Ne => true,
                            _ => false,
                        } {
                            out.push_str(" 0=");
                        }
                        return Ok(out);
                    }
                    let s = match op {
                        Add => {
                            if #[allow(non_exhaustive_omitted_patterns)]
                            match ta {
                                TypeInfo::Set(_) => true,
                                _ => false,
                            } {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} OR", la, lb))
                                })
                            } else if both_realish {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} FADD", la, lb))
                                })
                            } else {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} +", la, lb))
                                })
                            }
                        }
                        Sub => {
                            if #[allow(non_exhaustive_omitted_patterns)]
                            match ta {
                                TypeInfo::Set(_) => true,
                                _ => false,
                            } {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0} -1 XOR {1} AND", lb, la),
                                    )
                                })
                            } else if both_realish {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} FSUB", la, lb))
                                })
                            } else {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} -", la, lb))
                                })
                            }
                        }
                        Mul => {
                            if both_realish {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} FMUL", la, lb))
                                })
                            } else if #[allow(non_exhaustive_omitted_patterns)]
                            match ta {
                                TypeInfo::Set(_) => true,
                                _ => false,
                            } {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} AND", la, lb))
                                })
                            } else {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} *", la, lb))
                                })
                            }
                        }
                        RealDiv => {
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(format_args!("{0} {1} FDIV", la, lb))
                            })
                        }
                        Div => {
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(format_args!("{0} {1} /", la, lb))
                            })
                        }
                        Mod => {
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(format_args!("{0} {1} MOD", la, lb))
                            })
                        }
                        And => {
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(format_args!("{0} {1} AND", la, lb))
                            })
                        }
                        Or => {
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(format_args!("{0} {1} OR", la, lb))
                            })
                        }
                        Xor => {
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(format_args!("{0} {1} XOR", la, lb))
                            })
                        }
                        In => {
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!(
                                        "1 {0} {1} - LSHIFT {2} AND 0= 0=",
                                        self.ordinal_inline(a, ctx)?,
                                        self.set_low_bound_expr(b, ctx)?,
                                        self.gen_expr_inline_ctx(b, ctx)?,
                                    ),
                                )
                            })
                        }
                        Eq => {
                            if both_realish {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} F=", la, lb))
                                })
                            } else {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} =", la, lb))
                                })
                            }
                        }
                        Ne => {
                            if both_realish {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} F= 0=", la, lb))
                                })
                            } else {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} <>", la, lb))
                                })
                            }
                        }
                        Lt => {
                            if #[allow(non_exhaustive_omitted_patterns)]
                            match ta {
                                TypeInfo::Set(_) => true,
                                _ => false,
                            } {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0} {1} AND {0} = {0} {1} <> AND", la, lb),
                                    )
                                })
                            } else if both_realish {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} F<", la, lb))
                                })
                            } else {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} <", la, lb))
                                })
                            }
                        }
                        Le => {
                            if #[allow(non_exhaustive_omitted_patterns)]
                            match ta {
                                TypeInfo::Set(_) => true,
                                _ => false,
                            } {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0} {1} AND {0} =", la, lb),
                                    )
                                })
                            } else if both_realish {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} F<=", la, lb))
                                })
                            } else {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} <=", la, lb))
                                })
                            }
                        }
                        Gt => {
                            if #[allow(non_exhaustive_omitted_patterns)]
                            match ta {
                                TypeInfo::Set(_) => true,
                                _ => false,
                            } {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0} {1} AND {1} = {0} {1} <> AND", la, lb),
                                    )
                                })
                            } else if both_realish {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} F<", lb, la))
                                })
                            } else {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} >", la, lb))
                                })
                            }
                        }
                        Ge => {
                            if #[allow(non_exhaustive_omitted_patterns)]
                            match ta {
                                TypeInfo::Set(_) => true,
                                _ => false,
                            } {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0} {1} AND {1} =", la, lb),
                                    )
                                })
                            } else if both_realish {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} F<=", lb, la))
                                })
                            } else {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} {1} >=", la, lb))
                                })
                            }
                        }
                    };
                    Ok(s)
                }
            }
        }
        fn gen_builtin_expr_call(
            &self,
            name: &str,
            args: &[Expr],
            ctx: &Ctx,
        ) -> Result<Option<String>, String> {
            let n = name.to_ascii_lowercase();
            match n.as_str() {
                "ord" => {
                    if args.len() != 1 {
                        return Err("Ord requires 1 argument".into());
                    }
                    let t = type_of_expr_scoped(
                        self.env,
                        &self.ctx_to_types(ctx),
                        &ctx.routines,
                        &args[0],
                    )?;
                    let v = self.gen_expr_inline_ctx(&args[0], ctx)?;
                    let out = match t {
                        TypeInfo::Basic(BasicType::Boolean) => {
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(format_args!("{0} PBOOL", v))
                            })
                        }
                        _ => v,
                    };
                    Ok(Some(out))
                }
                "chr" => {
                    if args.len() != 1 {
                        return Err("Chr requires 1 argument".into());
                    }
                    Ok(Some(self.gen_expr_inline_ctx(&args[0], ctx)?))
                }
                "abs" => {
                    if args.len() != 1 {
                        return Err("Abs requires 1 argument".into());
                    }
                    let t = type_of_expr_scoped(
                        self.env,
                        &self.ctx_to_types(ctx),
                        &ctx.routines,
                        &args[0],
                    )?;
                    let v = self.gen_expr_inline_ctx(&args[0], ctx)?;
                    Ok(
                        Some(
                            if #[allow(non_exhaustive_omitted_patterns)]
                            match t {
                                TypeInfo::Basic(BasicType::Real) => true,
                                _ => false,
                            } {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} FABS", v))
                                })
                            } else {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0} DUP 0< IF NEGATE THEN", v),
                                    )
                                })
                            },
                        ),
                    )
                }
                "sqr" => {
                    if args.len() != 1 {
                        return Err("Sqr requires 1 argument".into());
                    }
                    let t = type_of_expr_scoped(
                        self.env,
                        &self.ctx_to_types(ctx),
                        &ctx.routines,
                        &args[0],
                    )?;
                    let v = self.gen_expr_inline_ctx(&args[0], ctx)?;
                    Ok(
                        Some(
                            if #[allow(non_exhaustive_omitted_patterns)]
                            match t {
                                TypeInfo::Basic(BasicType::Real) => true,
                                _ => false,
                            } {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} DUP FMUL", v))
                                })
                            } else {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} DUP *", v))
                                })
                            },
                        ),
                    )
                }
                "round" => {
                    if args.len() != 1 {
                        return Err("Round requires 1 argument".into());
                    }
                    let t = type_of_expr_scoped(
                        self.env,
                        &self.ctx_to_types(ctx),
                        &ctx.routines,
                        &args[0],
                    )?;
                    let v = self.gen_expr_inline_ctx(&args[0], ctx)?;
                    Ok(
                        Some(
                            if #[allow(non_exhaustive_omitted_patterns)]
                            match t {
                                TypeInfo::Basic(BasicType::Real) => true,
                                _ => false,
                            } {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} FROUND-I32", v))
                                })
                            } else {
                                v
                            },
                        ),
                    )
                }
                "trunc" => {
                    if args.len() != 1 {
                        return Err("Trunc requires 1 argument".into());
                    }
                    let t = type_of_expr_scoped(
                        self.env,
                        &self.ctx_to_types(ctx),
                        &ctx.routines,
                        &args[0],
                    )?;
                    let v = self.gen_expr_inline_ctx(&args[0], ctx)?;
                    Ok(
                        Some(
                            if #[allow(non_exhaustive_omitted_patterns)]
                            match t {
                                TypeInfo::Basic(BasicType::Real) => true,
                                _ => false,
                            } {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("{0} F>S", v))
                                })
                            } else {
                                v
                            },
                        ),
                    )
                }
                "succ" => {
                    if args.len() != 1 {
                        return Err("Succ requires 1 argument".into());
                    }
                    Ok(
                        Some(
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!(
                                        "{0} 1 +",
                                        self.gen_expr_inline_ctx(&args[0], ctx)?,
                                    ),
                                )
                            }),
                        ),
                    )
                }
                "pred" => {
                    if args.len() != 1 {
                        return Err("Pred requires 1 argument".into());
                    }
                    Ok(
                        Some(
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!(
                                        "{0} 1 -",
                                        self.gen_expr_inline_ctx(&args[0], ctx)?,
                                    ),
                                )
                            }),
                        ),
                    )
                }
                "odd" => {
                    if args.len() != 1 {
                        return Err("Odd requires 1 argument".into());
                    }
                    Ok(
                        Some(
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!(
                                        "{0} 1 AND 0= 0=",
                                        self.gen_expr_inline_ctx(&args[0], ctx)?,
                                    ),
                                )
                            }),
                        ),
                    )
                }
                "hextoint" => {
                    if args.len() != 1 {
                        return Err("HexToInt requires 1 argument".into());
                    }
                    match &args[0] {
                        Expr::Str(s) => Ok(Some(parse_hex_text(s)?.to_string())),
                        _ => {
                            let lv = expr_to_lvalue(&args[0])
                                .ok_or(
                                    "HexToInt argument must be lvalue char array in codegen",
                                )?;
                            let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                            let arr_len = match &a.ty {
                                TypeInfo::Array(ai) => {
                                    match ai.elem_ty.as_ref() {
                                        TypeInfo::Basic(BasicType::Char) => ai.len.to_string(),
                                        _ => {
                                            return Err("HexToInt argument must be array of char".into());
                                        }
                                    }
                                }
                                _ => {
                                    return Err("HexToInt argument must be array of char".into());
                                }
                            };
                            let arr_len = if let Some(v) = ctx.vars.get(&lv.base) {
                                if let Some(bounds) = &v.conformant_bounds {
                                    let (low_name, high_name) = bounds
                                        .first()
                                        .ok_or("missing conformant string bounds")?;
                                    let low = self.runtime_bound_slot_expr(low_name, ctx)?;
                                    let high = self.runtime_bound_slot_expr(high_name, ctx)?;
                                    ::alloc::__export::must_use({
                                        ::alloc::fmt::format(
                                            format_args!("{0} {1} - 1 +", high, low),
                                        )
                                    })
                                } else {
                                    arr_len
                                }
                            } else {
                                arr_len
                            };
                            Ok(
                                Some(
                                    ::alloc::__export::must_use({
                                        ::alloc::fmt::format(
                                            format_args!(
                                                "{0} __HEX_PTR PVAR! {1} __HEX_LEN PVAR! __HEX_TO_I32",
                                                self.emit_addr_inline(&a),
                                                arr_len,
                                            ),
                                        )
                                    }),
                                ),
                            )
                        }
                    }
                }
                "addr" => {
                    if args.len() != 1 {
                        return Err("Addr requires 1 argument".into());
                    }
                    let lv = expr_to_lvalue(&args[0])
                        .ok_or("Addr argument must be an lvalue")?;
                    let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                    Ok(Some(self.emit_addr_inline(&a)))
                }
                "pos" => {
                    if args.len() != 2 {
                        return Err("Pos requires 2 arguments".into());
                    }
                    let needle = self
                        .resolve_char_array_arg(&args[0], ctx, "Pos first argument")?;
                    let hay = self
                        .resolve_char_array_arg(&args[1], ctx, "Pos second argument")?;
                    Ok(
                        Some(
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!(
                                        "{0} __STR_A PVAR! {1} __STR_B PVAR! __STRPOS",
                                        self.emit_addr_inline(&needle),
                                        self.emit_addr_inline(&hay),
                                    ),
                                )
                            }),
                        ),
                    )
                }
                "upcase" => {
                    if args.len() != 1 {
                        return Err("UpCase requires 1 argument".into());
                    }
                    let v = self.gen_expr_inline_ctx(&args[0], ctx)?;
                    Ok(
                        Some(
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!(
                                        "{0} DUP 97 >= OVER 122 <= AND IF 32 - THEN",
                                        v,
                                    ),
                                )
                            }),
                        ),
                    )
                }
                "length" => {
                    if args.len() != 1 {
                        return Err("Length requires 1 argument".into());
                    }
                    if let Some((low, high)) = self
                        .runtime_array_bounds_for_expr(&args[0], ctx)
                    {
                        return Ok(
                            Some(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0} {1} - 1 +", high, low),
                                    )
                                }),
                            ),
                        );
                    }
                    let t = type_of_expr_scoped(
                        self.env,
                        &self.ctx_to_types(ctx),
                        &ctx.routines,
                        &args[0],
                    )?;
                    if let TypeInfo::Array(a) = t {
                        Ok(Some(a.len.to_string()))
                    } else {
                        Err("Length argument must be array".into())
                    }
                }
                "high" => {
                    if args.len() != 1 {
                        return Err("High requires 1 argument".into());
                    }
                    if let Some((_, high)) = self
                        .runtime_array_bounds_for_expr(&args[0], ctx)
                    {
                        return Ok(Some(high));
                    }
                    let t = type_of_expr_scoped(
                        self.env,
                        &self.ctx_to_types(ctx),
                        &ctx.routines,
                        &args[0],
                    )?;
                    if let TypeInfo::Array(a) = t {
                        Ok(Some(a.high.to_string()))
                    } else {
                        Err("High argument must be array".into())
                    }
                }
                "low" => {
                    if args.len() != 1 {
                        return Err("Low requires 1 argument".into());
                    }
                    if let Some((low, _)) = self
                        .runtime_array_bounds_for_expr(&args[0], ctx)
                    {
                        return Ok(Some(low));
                    }
                    let t = type_of_expr_scoped(
                        self.env,
                        &self.ctx_to_types(ctx),
                        &ctx.routines,
                        &args[0],
                    )?;
                    if let TypeInfo::Array(_) = t {
                        if let TypeInfo::Array(a) = t {
                            Ok(Some(a.low.to_string()))
                        } else {
                            ::core::panicking::panic(
                                "internal error: entered unreachable code",
                            )
                        }
                    } else {
                        Err("Low argument must be array".into())
                    }
                }
                _ => Ok(None),
            }
        }
        fn resolve_call_target(
            &self,
            ctx: &Ctx,
            name: &str,
        ) -> Result<(String, RoutineSig), String> {
            let key = ctx
                .routines
                .get(name)
                .ok_or_else(|| ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("unknown routine in scope: {0}", name),
                    )
                }))?;
            let sig = self
                .env
                .routines
                .get(key)
                .cloned()
                .ok_or_else(|| ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("internal: missing routine signature for {0}", key),
                    )
                }))?;
            Ok((self.routine_word(key), sig))
        }
        fn gen_call_args_inline(
            &self,
            name: &str,
            args: &[Expr],
            ctx: &Ctx,
        ) -> Result<String, String> {
            let (_, sig) = self.resolve_call_target(ctx, name)?;
            let mut out = ::alloc::vec::Vec::new();
            for (arg, p) in args.iter().zip(&sig.params) {
                if let Some(_c) = &p.conformant {
                    let lv = expr_to_lvalue(arg)
                        .ok_or_else(|| {
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!(
                                        "conformant array argument must be lvalue in call to {0}",
                                        name,
                                    ),
                                )
                            })
                        })?;
                    let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                    let mut cur = &a.ty;
                    let mut rank = 0usize;
                    while let TypeInfo::Array(ai) = cur {
                        out.push(ai.low.to_string());
                        out.push(ai.high.to_string());
                        cur = ai.elem_ty.as_ref();
                        rank += 1;
                    }
                    if rank == 0 {
                        return Err(
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!(
                                        "conformant array argument must be array in call to {0}",
                                        name,
                                    ),
                                )
                            }),
                        );
                    }
                    out.push(self.emit_addr_inline(&a));
                } else if p.by_ref {
                    let lv = expr_to_lvalue(arg)
                        .ok_or_else(|| ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "by-ref argument must be lvalue in call to {0}",
                                    name,
                                ),
                            )
                        }))?;
                    let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                    out.push(self.emit_addr_inline(&a));
                } else {
                    out.push(self.gen_expr_inline_ctx(arg, ctx)?);
                }
            }
            Ok(out.join(" "))
        }
        fn gen_call_inline_ctx(
            &self,
            name: &str,
            args: &[Expr],
            ctx: &Ctx,
        ) -> Result<String, String> {
            let key = ctx
                .routines
                .get(name)
                .ok_or_else(|| ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("unknown routine in scope: {0}", name),
                    )
                }))?;
            let (word, sig) = self.resolve_call_target(ctx, name)?;
            let mut parts = ::alloc::vec::Vec::new();
            let frame_slots = self.routine_frames.get(key).cloned().unwrap_or_default();
            for slot in &frame_slots {
                parts
                    .push(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} PVAR@ >R", slot))
                        }),
                    );
            }
            let argc = self.gen_call_args_inline(name, args, ctx)?;
            if !argc.is_empty() {
                parts.push(argc);
            }
            parts.push(word);
            if sig.ret.is_some() {
                parts.push("__CALL_RET PVAR!".into());
            }
            for slot in frame_slots.iter().rev() {
                parts
                    .push(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("R> {0} PVAR!", slot))
                        }),
                    );
            }
            if sig.ret.is_some() {
                parts.push("__CALL_RET PVAR@".into());
            }
            Ok(parts.join(" "))
        }
        fn gen_aggregate_call_assign(
            &mut self,
            name: &str,
            args: &[Expr],
            dst: &AddrRef,
            ctx: &Ctx,
        ) -> Result<(), String> {
            let key = ctx
                .routines
                .get(name)
                .ok_or_else(|| ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("unknown routine in scope: {0}", name),
                    )
                }))?;
            let (word, sig) = self.resolve_call_target(ctx, name)?;
            let ret_ty = sig
                .ret
                .clone()
                .ok_or_else(|| ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("procedure used as expression: {0}", name),
                    )
                }))?;
            if #[allow(non_exhaustive_omitted_patterns)]
            match ret_ty {
                TypeInfo::Basic(_)
                | TypeInfo::Enum(_)
                | TypeInfo::Subrange(_)
                | TypeInfo::Set(_)
                | TypeInfo::Pointer(_)
                | TypeInfo::Nil => true,
                _ => false,
            } {
                return Err(
                    "internal: scalar function routed to aggregate assignment path"
                        .into(),
                );
            }
            let frame_slots = self.routine_frames.get(key).cloned().unwrap_or_default();
            for slot in &frame_slots {
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("{0} PVAR@ >R", slot))
                    }),
                );
            }
            let argc = self.gen_call_args_inline(name, args, ctx)?;
            if !argc.is_empty() {
                self.wln(&argc);
            }
            self.wln(&word);
            self.wln("__CRS PVAR!");
            let size = self.type_size_bytes(&ret_ty)?;
            let src_tmp = AddrRef {
                base_expr: "__CRS".into(),
                offset: 0,
                dynamic_addr_expr: Some("__CRS PVAR@".into()),
                ty: ret_ty.clone(),
                variant_checks: Vec::new(),
            };
            let dst_tmp = AddrRef {
                base_expr: "__CRA".into(),
                offset: 0,
                dynamic_addr_expr: None,
                ty: ret_ty.clone(),
                variant_checks: Vec::new(),
            };
            self.emit_aggregate_copy(&src_tmp, &dst_tmp, size);
            for slot in frame_slots.iter().rev() {
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("R> {0} PVAR!", slot))
                    }),
                );
            }
            self.emit_aggregate_copy(&dst_tmp, dst, size);
            Ok(())
        }
        fn emit_store(&mut self, rhs: &str, dst: &AddrRef) {
            let checks = self.variant_check_prefix(dst);
            let rhs_checked = self.checked_rhs_for_type(rhs, &dst.ty);
            if let Some(addr) = &dst.dynamic_addr_expr {
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("{0}{1} {2} PVAR!", checks, rhs_checked, addr),
                        )
                    }),
                );
            } else if dst.offset == 0 {
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "{1}{2} {0} PVAR!",
                                dst.base_expr,
                                checks,
                                rhs_checked,
                            ),
                        )
                    }),
                );
            } else {
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "{2}{3} {0} {1} PFIELD!",
                                dst.base_expr,
                                dst.offset,
                                checks,
                                rhs_checked,
                            ),
                        )
                    }),
                );
            }
        }
        fn emit_load_inline(&self, src: &AddrRef) -> String {
            let checks = self.variant_check_prefix(src);
            if let Some(addr) = &src.dynamic_addr_expr {
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0}{1} PVAR@", checks, addr))
                })
            } else if src.offset == 0 {
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{1}{0} PVAR@", src.base_expr, checks),
                    )
                })
            } else {
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!(
                            "{2}{0} {1} PFIELD@",
                            src.base_expr,
                            src.offset,
                            checks,
                        ),
                    )
                })
            }
        }
        fn emit_addr_inline(&self, a: &AddrRef) -> String {
            let checks = self.variant_check_prefix(a);
            if let Some(addr) = &a.dynamic_addr_expr {
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0}{1}", checks, addr))
                })
            } else if a.offset == 0 {
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{1}{0}", a.base_expr, checks))
                })
            } else {
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{2}{0} {1} +", a.base_expr, a.offset, checks),
                    )
                })
            }
        }
        fn variant_check_prefix(&self, addr: &AddrRef) -> String {
            let mut out = String::new();
            for check in &addr.variant_checks {
                out.push_str(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "{0} PVAR@ __VAR_TAG PVAR! ",
                                check.tag_addr_expr,
                            ),
                        )
                    }),
                );
                let mut first = true;
                for (lo, hi) in &check.allowed_ranges {
                    let cond = if lo == hi {
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("__VAR_TAG PVAR@ {0} =", lo),
                            )
                        })
                    } else {
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "__VAR_TAG PVAR@ {0} >= __VAR_TAG PVAR@ {1} <= AND",
                                    lo,
                                    hi,
                                ),
                            )
                        })
                    };
                    if first {
                        out.push_str(&cond);
                        first = false;
                    } else {
                        out.push(' ');
                        out.push_str(&cond);
                        out.push_str(" OR");
                    }
                    out.push(' ');
                }
                if first {
                    out.push_str("0 ");
                }
                out.push_str("0= IF __VARIANT_MISMATCH THEN ");
            }
            out
        }
        fn checked_rhs_for_type(&self, rhs: &str, ty: &TypeInfo) -> String {
            match ty {
                TypeInfo::Subrange(s) => {
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "{2} DUP {0} >= OVER {1} <= AND 0= IF __SUBRANGE_MISMATCH THEN",
                                s.low,
                                s.high,
                                rhs,
                            ),
                        )
                    })
                }
                _ => rhs.to_string(),
            }
        }
        fn emit_param_store(&mut self, slot: &str, ty: &TypeInfo) {
            match ty {
                TypeInfo::Subrange(s) => {
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "DUP {0} >= OVER {1} <= AND 0= IF __SUBRANGE_MISMATCH THEN {2} PVAR!",
                                    s.low,
                                    s.high,
                                    slot,
                                ),
                            )
                        }),
                    )
                }
                _ => {
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{0} PVAR!", slot))
                        }),
                    )
                }
            }
        }
        fn resolve_lvalue_addr_ctx(
            &self,
            lv: &LValue,
            ctx: &Ctx,
        ) -> Result<AddrRef, String> {
            let v = ctx
                .vars
                .get(&lv.base)
                .ok_or_else(|| ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("unknown var: {0}", lv.base))
                }))?;
            let base_expr = if v.by_ref {
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} PVAR@", v.slot))
                })
            } else {
                v.slot.clone()
            };
            let mut t = v.ty.clone();
            let mut offset = 0u32;
            let mut dynamic_addr_expr: Option<String> = None;
            let mut conformant_bounds = v.conformant_bounds.clone();
            let mut variant_checks = Vec::new();
            for sel in &lv.sels {
                match sel {
                    Selector::Deref => {
                        match t {
                            TypeInfo::Pointer(ref target) => {
                                let cur = AddrRef {
                                    base_expr: base_expr.clone(),
                                    offset,
                                    dynamic_addr_expr: dynamic_addr_expr.clone(),
                                    ty: t.clone(),
                                    variant_checks: variant_checks.clone(),
                                };
                                dynamic_addr_expr = Some(self.emit_load_inline(&cur));
                                offset = 0;
                                t = lookup_type(self.env, target)
                                    .ok_or_else(|| ::alloc::__export::must_use({
                                        ::alloc::fmt::format(
                                            format_args!("unknown pointed type: {0}", target),
                                        )
                                    }))?;
                            }
                            _ => return Err("deref on non-pointer lvalue".into()),
                        }
                    }
                    Selector::Field(f) => {
                        match t {
                            TypeInfo::Record(ref r) => {
                                let fi = r
                                    .fields
                                    .get(f)
                                    .ok_or_else(|| ::alloc::__export::must_use({
                                        ::alloc::fmt::format(format_args!("unknown field: {0}", f))
                                    }))?;
                                let record_base = if let Some(cur) = &dynamic_addr_expr {
                                    if offset == 0 {
                                        cur.clone()
                                    } else {
                                        ::alloc::__export::must_use({
                                            ::alloc::fmt::format(format_args!("{0} {1} +", cur, offset))
                                        })
                                    }
                                } else if offset == 0 {
                                    base_expr.clone()
                                } else {
                                    ::alloc::__export::must_use({
                                        ::alloc::fmt::format(
                                            format_args!("{0} {1} +", base_expr, offset),
                                        )
                                    })
                                };
                                for check in &fi.variant_checks {
                                    let tag_addr_expr = if check.tag_offset_bytes == 0 {
                                        record_base.clone()
                                    } else {
                                        ::alloc::__export::must_use({
                                            ::alloc::fmt::format(
                                                format_args!(
                                                    "{1} {0} +",
                                                    check.tag_offset_bytes,
                                                    record_base,
                                                ),
                                            )
                                        })
                                    };
                                    variant_checks
                                        .push(RuntimeVariantCheck {
                                            tag_addr_expr,
                                            allowed_ranges: check.allowed_ranges.clone(),
                                        });
                                }
                                if let Some(cur) = dynamic_addr_expr.take() {
                                    dynamic_addr_expr = Some(
                                        ::alloc::__export::must_use({
                                            ::alloc::fmt::format(
                                                format_args!("{1} {0} +", fi.offset_bytes, cur),
                                            )
                                        }),
                                    );
                                } else {
                                    offset += fi.offset_bytes;
                                }
                                t = fi.ty.clone();
                            }
                            _ => return Err("field on non-record lvalue".into()),
                        }
                    }
                    Selector::Index(idxs) => {
                        for ix in idxs {
                            let (low, len, elem_size, elem_ty) = match t {
                                TypeInfo::Array(ref a) => {
                                    (a.low, a.len, a.elem_size_bytes, (*a.elem_ty).clone())
                                }
                                _ => return Err("index on non-array lvalue".into()),
                            };
                            let idx_expr = self.gen_expr_inline_ctx(ix, ctx)?;
                            let _ = len;
                            let scaled = if let Some((low_name, high_name)) = conformant_bounds
                                .as_mut()
                                .and_then(|bounds| {
                                    if bounds.is_empty() {
                                        None
                                    } else {
                                        Some(bounds.remove(0))
                                    }
                                })
                            {
                                let low = self.runtime_bound_slot_expr(&low_name, ctx)?;
                                let stride = self
                                    .runtime_conformant_size_expr(
                                        &elem_ty,
                                        conformant_bounds.as_deref().unwrap_or(&[]),
                                        ctx,
                                    )?;
                                let _ = high_name;
                                if stride == "1" {
                                    ::alloc::__export::must_use({
                                        ::alloc::fmt::format(
                                            format_args!("{0} {1} -", idx_expr, low),
                                        )
                                    })
                                } else {
                                    ::alloc::__export::must_use({
                                        ::alloc::fmt::format(
                                            format_args!("{0} {1} - {2} *", idx_expr, low, stride),
                                        )
                                    })
                                }
                            } else if elem_size == 1 {
                                if low == 0 {
                                    idx_expr
                                } else {
                                    ::alloc::__export::must_use({
                                        ::alloc::fmt::format(
                                            format_args!("{0} {1} -", idx_expr, low),
                                        )
                                    })
                                }
                            } else if low == 0 {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0} {1} *", idx_expr, elem_size),
                                    )
                                })
                            } else {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0} {1} - {2} *", idx_expr, low, elem_size),
                                    )
                                })
                            };
                            let base_addr = if let Some(cur) = dynamic_addr_expr.take() {
                                cur
                            } else if offset == 0 {
                                base_expr.clone()
                            } else {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0} {1} +", base_expr, offset),
                                    )
                                })
                            };
                            dynamic_addr_expr = Some(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0} {1} +", base_addr, scaled),
                                    )
                                }),
                            );
                            offset = 0;
                            t = elem_ty;
                        }
                    }
                }
            }
            Ok(AddrRef {
                base_expr,
                offset,
                dynamic_addr_expr,
                ty: t,
                variant_checks,
            })
        }
        fn emit_string_write(&mut self, s: &str) {
            if !s.is_empty() && s.is_ascii() && !s.contains('"') && !s.contains('\n')
                && !s.contains('\r')
            {
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("S\" {0}\" TYPE", s))
                    }),
                );
                return;
            }
            for ch in s.chars() {
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("{0} PWRITE-CHAR", ch as u32))
                    }),
                );
            }
        }
        fn emit_string_literal_storage(&mut self) -> Result<(), String> {
            for (name, value) in self.string_literals.clone() {
                let len = value.chars().count() as u32 + 1;
                let ty = TypeInfo::Array(ArrayInfo {
                    low: 0,
                    high: len as i32 - 1,
                    len,
                    elem_ty: Box::new(TypeInfo::Basic(BasicType::Char)),
                    elem_size_bytes: 4,
                    size_bytes: len * 4,
                });
                self.emit_storage_decl(&name, &ty)?;
                let addr = AddrRef {
                    base_expr: name,
                    offset: 0,
                    dynamic_addr_expr: None,
                    ty,
                    variant_checks: Vec::new(),
                };
                self.emit_char_array_assign(&addr, &value)?;
            }
            Ok(())
        }
        fn emit_aggregate_copy(
            &mut self,
            src: &AddrRef,
            dst: &AddrRef,
            size_bytes: u32,
        ) {
            let cells = size_bytes / 4;
            if cells > 8 {
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "{0} __CP_SRC PVAR!",
                                self.emit_addr_inline(src),
                            ),
                        )
                    }),
                );
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "{0} __CP_DST PVAR!",
                                self.emit_addr_inline(dst),
                            ),
                        )
                    }),
                );
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("{0} __CP_N PVAR!", cells))
                    }),
                );
                self.wln("0 __CP_I PVAR!");
                self.wln("BEGIN");
                self.indent += 1;
                self.wln("__CP_I PVAR@ __CP_N PVAR@ < WHILE");
                self.indent += 1;
                self.wln("__CP_SRC PVAR@ __CP_I PVAR@ 4 * + PVAR@");
                self.wln("__CP_DST PVAR@ __CP_I PVAR@ 4 * + PVAR!");
                self.wln("__CP_I PVAR@ 1 + __CP_I PVAR!");
                self.indent -= 1;
                self.indent -= 1;
                self.wln("REPEAT");
                return;
            }
            for i in 0..cells {
                let ofs = i * 4;
                let rhs = self.emit_load_at(src, ofs);
                self.emit_store_at(&rhs, dst, ofs);
            }
        }
        fn emit_load_at(&self, src: &AddrRef, add_ofs: u32) -> String {
            if let Some(addr) = &src.dynamic_addr_expr {
                if add_ofs == 0 {
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("{0} PVAR@", addr))
                    })
                } else {
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("{0} {1} + PVAR@", addr, add_ofs),
                        )
                    })
                }
            } else {
                let total = src.offset + add_ofs;
                if total == 0 {
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("{0} PVAR@", src.base_expr))
                    })
                } else {
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("{0} {1} PFIELD@", src.base_expr, total),
                        )
                    })
                }
            }
        }
        fn emit_store_at(&mut self, rhs: &str, dst: &AddrRef, add_ofs: u32) {
            if let Some(addr) = &dst.dynamic_addr_expr {
                if add_ofs == 0 {
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} {1} PVAR!", rhs, addr),
                            )
                        }),
                    );
                } else {
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} {1} {2} + PVAR!", rhs, addr, add_ofs),
                            )
                        }),
                    );
                }
            } else {
                let total = dst.offset + add_ofs;
                if total == 0 {
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{1} {0} PVAR!", dst.base_expr, rhs),
                            )
                        }),
                    );
                } else {
                    self.wln(
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "{1} {0} {2} PFIELD!",
                                    dst.base_expr,
                                    rhs,
                                    total,
                                ),
                            )
                        }),
                    );
                }
            }
        }
        fn emit_char_array_assign(
            &mut self,
            dst: &AddrRef,
            s: &str,
        ) -> Result<(), String> {
            let len = match &dst.ty {
                TypeInfo::Array(a) => {
                    match a.elem_ty.as_ref() {
                        TypeInfo::Basic(BasicType::Char) => a.len,
                        _ => {
                            return Err(
                                "string literal assignment requires array of char lhs"
                                    .into(),
                            );
                        }
                    }
                }
                _ => {
                    return Err(
                        "string literal assignment requires array of char lhs".into(),
                    );
                }
            };
            if len == 0 {
                return Ok(());
            }
            let chars: Vec<u32> = s.chars().map(|c| c as u32).collect();
            let body = len - 1;
            let copied = body.min(chars.len() as u32);
            for i in 0..copied {
                let v = chars[i as usize];
                self.emit_store_at(&v.to_string(), dst, i * 4);
            }
            self.emit_store_at("0", dst, copied * 4);
            Ok(())
        }
        fn emit_char_array_write(
            &mut self,
            a: &AddrRef,
            ctx: &Ctx,
            base_name: &str,
        ) -> Result<(), String> {
            let arr_len = match &a.ty {
                TypeInfo::Array(ai) => {
                    match ai.elem_ty.as_ref() {
                        TypeInfo::Basic(BasicType::Char) => ai.len.to_string(),
                        _ => {
                            return Err(
                                "Write/WriteLn char array requires array of char".into(),
                            );
                        }
                    }
                }
                _ => return Err("Write/WriteLn char array requires array of char".into()),
            };
            let arr_len = if let Some(v) = ctx.vars.get(base_name) {
                if let Some(bounds) = &v.conformant_bounds {
                    let (low_name, high_name) = bounds
                        .first()
                        .ok_or("missing conformant string bounds")?;
                    let low = self.runtime_bound_slot_expr(low_name, ctx)?;
                    let high = self.runtime_bound_slot_expr(high_name, ctx)?;
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("{0} {1} - 1 +", high, low))
                    })
                } else {
                    arr_len
                }
            } else {
                arr_len
            };
            let base_addr = self.emit_addr_inline(a);
            self.wln("0 __WSTR_STOP PVAR!");
            self.wln("0 >R");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("__WSTR_STOP PVAR@ 0= R@ {0} < AND WHILE", arr_len),
                    )
                }),
            );
            self.indent += 1;
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{0} R@ 4 * + PVAR@ DUP 0= IF", base_addr),
                    )
                }),
            );
            self.indent += 1;
            self.wln("DROP");
            self.wln("1 __WSTR_STOP PVAR!");
            self.indent -= 1;
            self.wln("ELSE");
            self.indent += 1;
            self.wln("PWRITE-CHAR");
            self.indent -= 1;
            self.wln("THEN");
            self.wln("R> 1 + >R");
            self.indent -= 1;
            self.indent -= 1;
            self.wln("REPEAT");
            self.wln("R> DROP");
            Ok(())
        }
        fn emit_char_array_read(
            &mut self,
            dst: &AddrRef,
            max_len_expr: &str,
            ctx: &Ctx,
            base_name: &str,
        ) -> Result<(), String> {
            let arr_len = match &dst.ty {
                TypeInfo::Array(ai) => {
                    match ai.elem_ty.as_ref() {
                        TypeInfo::Basic(BasicType::Char) => ai.len.to_string(),
                        _ => return Err("Read char array requires array of char".into()),
                    }
                }
                _ => return Err("Read char array requires array of char".into()),
            };
            let arr_len = if let Some(v) = ctx.vars.get(base_name) {
                if let Some(bounds) = &v.conformant_bounds {
                    let (low_name, high_name) = bounds
                        .first()
                        .ok_or("missing conformant string bounds")?;
                    let low = self.runtime_bound_slot_expr(low_name, ctx)?;
                    let high = self.runtime_bound_slot_expr(high_name, ctx)?;
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("{0} {1} - 1 +", high, low))
                    })
                } else {
                    arr_len
                }
            } else {
                arr_len
            };
            let cap = ::alloc::__export::must_use({
                ::alloc::fmt::format(format_args!("{0} 1 -", arr_len))
            });
            let base_addr = self.emit_addr_inline(dst);
            self.wln("0 >R");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("R@ {0} < R@ {1} < AND WHILE", max_len_expr, cap),
                    )
                }),
            );
            self.indent += 1;
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("PREAD-CHAR {0} R@ 4 * + PVAR!", base_addr),
                    )
                }),
            );
            self.wln("R> 1 + >R");
            self.indent -= 1;
            self.indent -= 1;
            self.wln("REPEAT");
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("0 {0} R@ 4 * + PVAR!", base_addr))
                }),
            );
            self.wln("R> DROP");
            Ok(())
        }
        fn emit_storage_decl(
            &mut self,
            name: &str,
            ty: &TypeInfo,
        ) -> Result<(), String> {
            let sz = self.type_size_bytes(ty)?;
            self.emit_storage_bytes_decl(name, sz);
            Ok(())
        }
        fn emit_storage_bytes_decl(&mut self, name: &str, sz: u32) {
            if sz <= 4 {
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("CREATE {0} 0 ,", name))
                    }),
                );
            } else {
                self.wln(
                    &::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("CREATE {1} 0 , {0} ALLOT", sz - 4, name),
                        )
                    }),
                );
            }
        }
        fn max_aggregate_return_bytes(&self, prog: &Program) -> Result<u32, String> {
            self.max_aggregate_return_bytes_in_routines(&prog.block.routines)
        }
        fn max_aggregate_return_bytes_in_routines(
            &self,
            routines: &[RoutineDecl],
        ) -> Result<u32, String> {
            let mut max = 0;
            for routine in routines {
                match routine {
                    RoutineDecl::Procedure(p) => {
                        max = max
                            .max(
                                self
                                    .max_aggregate_return_bytes_in_routines(&p.block.routines)?,
                            );
                    }
                    RoutineDecl::Function(f) => {
                        let ty = self.ty_of_typeref(&f.ret_ty)?;
                        if #[allow(non_exhaustive_omitted_patterns)]
                        match ty {
                            TypeInfo::Record(_)
                            | TypeInfo::Sum(_)
                            | TypeInfo::Array(_) => true,
                            _ => false,
                        } {
                            max = max.max(self.type_size_bytes(&ty)?);
                        }
                        max = max
                            .max(
                                self
                                    .max_aggregate_return_bytes_in_routines(&f.block.routines)?,
                            );
                    }
                }
            }
            Ok(max)
        }
        fn type_size_bytes(&self, ty: &TypeInfo) -> Result<u32, String> {
            match ty {
                TypeInfo::Basic(_)
                | TypeInfo::Enum(_)
                | TypeInfo::Subrange(_)
                | TypeInfo::Set(_)
                | TypeInfo::Pointer(_)
                | TypeInfo::Nil => Ok(4),
                TypeInfo::Record(r) => Ok(r.size_bytes),
                TypeInfo::Sum(s) => Ok(s.size_bytes),
                TypeInfo::Array(a) => Ok(a.size_bytes),
            }
        }
        fn const_to_token(&self, c: &ConstExpr) -> Result<String, String> {
            Ok(
                match eval_const(self.env, c)? {
                    ConstVal::I32(i) => i.to_string(),
                    ConstVal::U32(u) => u.to_string(),
                    ConstVal::Real(bits) => bits.to_string(),
                    ConstVal::EnumVal { ordinal, .. } => ordinal.to_string(),
                    ConstVal::Bool(b) => {
                        if b { "1".to_string() } else { "0".to_string() }
                    }
                },
            )
        }
        fn routine_word(&self, scoped: &str) -> String {
            ::alloc::__export::must_use({
                ::alloc::fmt::format(
                    format_args!("R_{0}", self.short_symbol(scoped, 12)),
                )
            })
        }
        fn slot_name(&self, scoped: &str, vname: &str) -> String {
            ::alloc::__export::must_use({
                ::alloc::fmt::format(
                    format_args!(
                        "S_{0}",
                        self
                            .short_symbol(
                                &::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("{0}::{1}", scoped, vname),
                                    )
                                }),
                                12,
                            ),
                    ),
                )
            })
        }
        fn runtime_param_slots(
            &self,
            scoped: &str,
            params: &[ParamDecl],
        ) -> Vec<String> {
            let mut slots = Vec::new();
            for prm in params {
                if let Some(c) = &prm.conformant {
                    for dim in &c.dims {
                        slots.push(self.slot_name(scoped, &dim.low_name));
                        slots.push(self.slot_name(scoped, &dim.high_name));
                    }
                }
                slots.push(self.slot_name(scoped, &prm.name));
            }
            slots
        }
        fn short_symbol(&self, raw: &str, max_len: usize) -> String {
            let cleaned: String = raw
                .chars()
                .map(|c| {
                    if c.is_ascii_alphanumeric() { c.to_ascii_uppercase() } else { '_' }
                })
                .collect();
            if cleaned.len() <= max_len {
                return cleaned;
            }
            let mut h: u32 = 2166136261;
            for b in cleaned.as_bytes() {
                h ^= *b as u32;
                h = h.wrapping_mul(16777619);
            }
            let suffix = ::alloc::__export::must_use({
                ::alloc::fmt::format(format_args!("{0:06X}", h & 0x00FF_FFFF))
            });
            let head_len = max_len.saturating_sub(7);
            let head = &cleaned[..head_len];
            ::alloc::__export::must_use({
                ::alloc::fmt::format(format_args!("{0}_{1}", head, suffix))
            })
        }
        fn main_ctx(&self, top_routines: &[RoutineDecl], scope: &str) -> Ctx {
            let mut vars = HashMap::new();
            for (n, t) in &self.env.vars {
                vars.insert(
                    n.clone(),
                    VarAccess {
                        slot: n.clone(),
                        ty: t.clone(),
                        by_ref: false,
                        conformant_bounds: None,
                    },
                );
            }
            let routines = self
                .extend_routine_visibility(&HashMap::new(), top_routines, scope);
            Ctx { vars, routines }
        }
        fn extend_vars_for_routine(
            &self,
            r: &RoutineDecl,
            scoped: &str,
            ctx: &mut Ctx,
        ) -> Result<(), String> {
            match r {
                RoutineDecl::Procedure(p) => {
                    for prm in &p.params {
                        let ty = self.ty_of_param_decl(prm)?;
                        ctx.vars
                            .insert(
                                prm.name.clone(),
                                VarAccess {
                                    slot: self.slot_name(scoped, &prm.name),
                                    ty,
                                    by_ref: prm.by_ref || prm.conformant.is_some(),
                                    conformant_bounds: prm
                                        .conformant
                                        .as_ref()
                                        .map(|c| {
                                            c.dims
                                                .iter()
                                                .map(|d| (d.low_name.clone(), d.high_name.clone()))
                                                .collect()
                                        }),
                                },
                            );
                        if let Some(c) = &prm.conformant {
                            for dim in &c.dims {
                                let bound_ty = self.ty_of_typeref(&dim.index_ty)?;
                                ctx.vars
                                    .insert(
                                        dim.low_name.clone(),
                                        VarAccess {
                                            slot: self.slot_name(scoped, &dim.low_name),
                                            ty: bound_ty.clone(),
                                            by_ref: false,
                                            conformant_bounds: None,
                                        },
                                    );
                                ctx.vars
                                    .insert(
                                        dim.high_name.clone(),
                                        VarAccess {
                                            slot: self.slot_name(scoped, &dim.high_name),
                                            ty: bound_ty,
                                            by_ref: false,
                                            conformant_bounds: None,
                                        },
                                    );
                            }
                        }
                    }
                    for lv in &p.block.vars {
                        let ty = self.ty_of_typeref(&lv.ty)?;
                        ctx.vars
                            .insert(
                                lv.name.clone(),
                                VarAccess {
                                    slot: self.slot_name(scoped, &lv.name),
                                    ty,
                                    by_ref: false,
                                    conformant_bounds: None,
                                },
                            );
                    }
                }
                RoutineDecl::Function(f) => {
                    for prm in &f.params {
                        let ty = self.ty_of_param_decl(prm)?;
                        ctx.vars
                            .insert(
                                prm.name.clone(),
                                VarAccess {
                                    slot: self.slot_name(scoped, &prm.name),
                                    ty,
                                    by_ref: prm.by_ref || prm.conformant.is_some(),
                                    conformant_bounds: prm
                                        .conformant
                                        .as_ref()
                                        .map(|c| {
                                            c.dims
                                                .iter()
                                                .map(|d| (d.low_name.clone(), d.high_name.clone()))
                                                .collect()
                                        }),
                                },
                            );
                        if let Some(c) = &prm.conformant {
                            for dim in &c.dims {
                                let bound_ty = self.ty_of_typeref(&dim.index_ty)?;
                                ctx.vars
                                    .insert(
                                        dim.low_name.clone(),
                                        VarAccess {
                                            slot: self.slot_name(scoped, &dim.low_name),
                                            ty: bound_ty.clone(),
                                            by_ref: false,
                                            conformant_bounds: None,
                                        },
                                    );
                                ctx.vars
                                    .insert(
                                        dim.high_name.clone(),
                                        VarAccess {
                                            slot: self.slot_name(scoped, &dim.high_name),
                                            ty: bound_ty,
                                            by_ref: false,
                                            conformant_bounds: None,
                                        },
                                    );
                            }
                        }
                    }
                    for lv in &f.block.vars {
                        let ty = self.ty_of_typeref(&lv.ty)?;
                        ctx.vars
                            .insert(
                                lv.name.clone(),
                                VarAccess {
                                    slot: self.slot_name(scoped, &lv.name),
                                    ty,
                                    by_ref: false,
                                    conformant_bounds: None,
                                },
                            );
                    }
                    ctx.vars
                        .insert(
                            f.name.clone(),
                            VarAccess {
                                slot: self.slot_name(scoped, &f.name),
                                ty: self.ty_of_typeref(&f.ret_ty)?,
                                by_ref: false,
                                conformant_bounds: None,
                            },
                        );
                }
            }
            Ok(())
        }
        fn extend_routine_visibility(
            &self,
            parent: &HashMap<String, String>,
            routines: &[RoutineDecl],
            scope: &str,
        ) -> HashMap<String, String> {
            let mut out = parent.clone();
            for r in routines {
                let name = match r {
                    RoutineDecl::Procedure(p) => &p.name,
                    RoutineDecl::Function(f) => &f.name,
                };
                out.insert(
                    name.clone(),
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("{0}::{1}", scope, name))
                    }),
                );
            }
            out
        }
        fn collect_routine_frames(&mut self, routines: &[RoutineDecl], scope: &str) {
            for r in routines {
                let (name, block, params, ret_name) = match r {
                    RoutineDecl::Procedure(p) => (&p.name, &p.block, &p.params, None),
                    RoutineDecl::Function(f) => {
                        (&f.name, &f.block, &f.params, Some(f.name.as_str()))
                    }
                };
                let scoped = ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0}::{1}", scope, name))
                });
                let mut slots = Vec::new();
                for prm in params {
                    slots
                        .extend(
                            self.runtime_param_slots(&scoped, std::slice::from_ref(prm)),
                        );
                }
                for lv in &block.vars {
                    slots.push(self.slot_name(&scoped, &lv.name));
                }
                if let Some(ret) = ret_name {
                    slots.push(self.slot_name(&scoped, ret));
                }
                self.routine_frames.insert(scoped.clone(), slots);
                self.collect_routine_frames(&block.routines, &scoped);
            }
        }
        fn ty_of_typeref(&self, tr: &TypeRef) -> Result<TypeInfo, String> {
            match tr {
                TypeRef::Basic(b) => Ok(TypeInfo::Basic(b.clone())),
                TypeRef::PointerNamed(n) => Ok(TypeInfo::Pointer(n.clone())),
                TypeRef::Option(inner) => {
                    let inner_ty = self.ty_of_typeref(inner)?;
                    let payload = self.type_size_bytes(&inner_ty)?;
                    Ok(
                        TypeInfo::Sum(SumInfo {
                            arms: <[_]>::into_vec(
                                ::alloc::boxed::box_new([
                                    SumArmInfo {
                                        name: "none".into(),
                                        tag: 0,
                                        fields: ::alloc::vec::Vec::new(),
                                    },
                                    SumArmInfo {
                                        name: "some".into(),
                                        tag: 1,
                                        fields: <[_]>::into_vec(
                                            ::alloc::boxed::box_new([
                                                SumFieldInfo {
                                                    name: "value".into(),
                                                    offset_bytes: 0,
                                                    ty: inner_ty,
                                                },
                                            ]),
                                        ),
                                    },
                                ]),
                            ),
                            payload_size_bytes: payload,
                            size_bytes: 4 + payload,
                        }),
                    )
                }
                TypeRef::Result(ok_ty, err_ty) => {
                    let ok = self.ty_of_typeref(ok_ty)?;
                    let err = self.ty_of_typeref(err_ty)?;
                    let ok_sz = self.type_size_bytes(&ok)?;
                    let err_sz = self.type_size_bytes(&err)?;
                    let payload = ok_sz.max(err_sz);
                    Ok(
                        TypeInfo::Sum(SumInfo {
                            arms: <[_]>::into_vec(
                                ::alloc::boxed::box_new([
                                    SumArmInfo {
                                        name: "ok".into(),
                                        tag: 0,
                                        fields: <[_]>::into_vec(
                                            ::alloc::boxed::box_new([
                                                SumFieldInfo {
                                                    name: "value".into(),
                                                    offset_bytes: 0,
                                                    ty: ok,
                                                },
                                            ]),
                                        ),
                                    },
                                    SumArmInfo {
                                        name: "err".into(),
                                        tag: 1,
                                        fields: <[_]>::into_vec(
                                            ::alloc::boxed::box_new([
                                                SumFieldInfo {
                                                    name: "error".into(),
                                                    offset_bytes: 0,
                                                    ty: err,
                                                },
                                            ]),
                                        ),
                                    },
                                ]),
                            ),
                            payload_size_bytes: payload,
                            size_bytes: 4 + payload,
                        }),
                    )
                }
                TypeRef::Array { dims, elem } => build_array_info(self.env, dims, elem),
                TypeRef::Subrange { low, high } => {
                    build_subrange_info(self.env, low, high)
                }
                TypeRef::Set(elem) => build_set_info(self.env, elem),
                TypeRef::Named(n) => {
                    lookup_type(self.env, n)
                        .ok_or_else(|| ::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("unknown type: {0}", n))
                        }))
                }
            }
        }
        fn ty_of_param_decl(&self, prm: &ParamDecl) -> Result<TypeInfo, String> {
            if let Some(c) = &prm.conformant {
                let mut ty = self.ty_of_typeref(&c.elem_ty)?;
                for _ in c.dims.iter().rev() {
                    let elem_size_bytes = self.type_size_bytes(&ty)?;
                    ty = TypeInfo::Array(ArrayInfo {
                        low: 0,
                        high: 0,
                        len: 0,
                        elem_ty: Box::new(ty),
                        elem_size_bytes,
                        size_bytes: 0,
                    });
                }
                Ok(ty)
            } else {
                self.ty_of_typeref(&prm.ty)
            }
        }
        fn ctx_to_types(&self, ctx: &Ctx) -> HashMap<String, TypeInfo> {
            let mut m = HashMap::new();
            for (k, v) in &ctx.vars {
                m.insert(k.clone(), v.ty.clone());
            }
            m
        }
        fn runtime_array_bounds_for_lvalue(
            &self,
            lv: &LValue,
            ctx: &Ctx,
        ) -> Option<(String, String)> {
            if !lv.sels.is_empty() {
                return None;
            }
            let v = ctx.vars.get(&lv.base)?;
            let bounds = v.conformant_bounds.as_ref()?;
            let (low_name, high_name) = bounds.first()?;
            let low_slot = ctx.vars.get(low_name)?.slot.clone();
            let high_slot = ctx.vars.get(high_name)?.slot.clone();
            Some((
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} PVAR@", low_slot))
                }),
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} PVAR@", high_slot))
                }),
            ))
        }
        fn runtime_array_bounds_for_expr(
            &self,
            expr: &Expr,
            ctx: &Ctx,
        ) -> Option<(String, String)> {
            let lv = expr_to_lvalue(expr)?;
            self.runtime_array_bounds_for_lvalue(&lv, ctx)
        }
        fn runtime_bound_slot_expr(
            &self,
            name: &str,
            ctx: &Ctx,
        ) -> Result<String, String> {
            let slot = ctx
                .vars
                .get(name)
                .ok_or_else(|| ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("unknown var: {0}", name))
                }))?
                .slot
                .clone();
            Ok(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} PVAR@", slot))
                }),
            )
        }
        fn runtime_conformant_size_expr(
            &self,
            ty: &TypeInfo,
            bounds: &[(String, String)],
            ctx: &Ctx,
        ) -> Result<String, String> {
            if let TypeInfo::Array(a) = ty {
                if !bounds.is_empty() {
                    let (low_name, high_name) = &bounds[0];
                    let low = self.runtime_bound_slot_expr(low_name, ctx)?;
                    let high = self.runtime_bound_slot_expr(high_name, ctx)?;
                    let inner = self
                        .runtime_conformant_size_expr(
                            a.elem_ty.as_ref(),
                            &bounds[1..],
                            ctx,
                        )?;
                    return Ok(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} {1} - 1 + {2} *", high, low, inner),
                            )
                        }),
                    );
                }
                if a.size_bytes != 0 {
                    return Ok(a.size_bytes.to_string());
                }
                return self.runtime_conformant_size_expr(a.elem_ty.as_ref(), &[], ctx);
            }
            Ok(self.type_size_bytes(ty)?.to_string())
        }
        fn rewrite_stmt_with_ctx(
            &self,
            stmt: &Stmt,
            bases: &[LValue],
            ctx: &Ctx,
        ) -> Result<Stmt, String> {
            Ok(
                match stmt {
                    Stmt::Empty => Stmt::Empty,
                    Stmt::Compound(v) => {
                        Stmt::Compound(
                            v
                                .iter()
                                .map(|s| self.rewrite_stmt_with_ctx(s, bases, ctx))
                                .collect::<Result<Vec<_>, _>>()?,
                        )
                    }
                    Stmt::Assign(lv, rhs) => {
                        Stmt::Assign(
                            self.rewrite_lvalue_with_ctx(lv, bases, ctx)?,
                            self.rewrite_expr_with_ctx(rhs, bases, ctx)?,
                        )
                    }
                    Stmt::Read(args) => {
                        Stmt::Read(
                            args
                                .iter()
                                .map(|e| self.rewrite_expr_with_ctx(e, bases, ctx))
                                .collect::<Result<Vec<_>, _>>()?,
                        )
                    }
                    Stmt::ReadLn => Stmt::ReadLn,
                    Stmt::For { var, init, limit, downto, body } => {
                        Stmt::For {
                            var: var.clone(),
                            init: self.rewrite_expr_with_ctx(init, bases, ctx)?,
                            limit: self.rewrite_expr_with_ctx(limit, bases, ctx)?,
                            downto: *downto,
                            body: Box::new(self.rewrite_stmt_with_ctx(body, bases, ctx)?),
                        }
                    }
                    Stmt::If(c, t, e) => {
                        Stmt::If(
                            self.rewrite_expr_with_ctx(c, bases, ctx)?,
                            Box::new(self.rewrite_stmt_with_ctx(t, bases, ctx)?),
                            e
                                .as_ref()
                                .map(|s| {
                                    self.rewrite_stmt_with_ctx(s, bases, ctx).map(Box::new)
                                })
                                .transpose()?,
                        )
                    }
                    Stmt::With(inner, body) => {
                        let mut merged = bases.to_vec();
                        merged.extend(inner.iter().cloned());
                        self.rewrite_stmt_with_ctx(body, &merged, ctx)?
                    }
                    Stmt::While(c, b) => {
                        Stmt::While(
                            self.rewrite_expr_with_ctx(c, bases, ctx)?,
                            Box::new(self.rewrite_stmt_with_ctx(b, bases, ctx)?),
                        )
                    }
                    Stmt::Repeat(v, c) => {
                        Stmt::Repeat(
                            v
                                .iter()
                                .map(|s| self.rewrite_stmt_with_ctx(s, bases, ctx))
                                .collect::<Result<Vec<_>, _>>()?,
                            self.rewrite_expr_with_ctx(c, bases, ctx)?,
                        )
                    }
                    Stmt::Case { expr, arms, else_stmt } => {
                        Stmt::Case {
                            expr: self.rewrite_expr_with_ctx(expr, bases, ctx)?,
                            arms: arms.clone(),
                            else_stmt: else_stmt
                                .as_ref()
                                .map(|s| {
                                    self.rewrite_stmt_with_ctx(s, bases, ctx).map(Box::new)
                                })
                                .transpose()?,
                        }
                    }
                    Stmt::ProcCall(name, args) => {
                        Stmt::ProcCall(
                            name.clone(),
                            args
                                .iter()
                                .map(|e| self.rewrite_expr_with_ctx(e, bases, ctx))
                                .collect::<Result<Vec<_>, _>>()?,
                        )
                    }
                    Stmt::Write(args) => {
                        Stmt::Write(
                            args
                                .iter()
                                .map(|e| self.rewrite_expr_with_ctx(e, bases, ctx))
                                .collect::<Result<Vec<_>, _>>()?,
                        )
                    }
                    Stmt::WriteLn(args) => {
                        Stmt::WriteLn(
                            args
                                .iter()
                                .map(|e| self.rewrite_expr_with_ctx(e, bases, ctx))
                                .collect::<Result<Vec<_>, _>>()?,
                        )
                    }
                    Stmt::SumCase { .. } => stmt.clone(),
                },
            )
        }
        fn rewrite_expr_with_ctx(
            &self,
            expr: &Expr,
            bases: &[LValue],
            ctx: &Ctx,
        ) -> Result<Expr, String> {
            Ok(
                match expr {
                    Expr::Var(
                        name,
                    ) if !ctx.vars.contains_key(name)
                        && !self.env.consts.contains_key(name)
                        && !ctx.routines.contains_key(name) => {
                        Self::lvalue_to_expr(
                            self
                                .rewrite_lvalue_with_ctx(
                                    &LValue {
                                        base: name.clone(),
                                        sels: ::alloc::vec::Vec::new(),
                                    },
                                    bases,
                                    ctx,
                                )?,
                        )
                    }
                    Expr::Call(name, args) => {
                        Expr::Call(
                            name.clone(),
                            args
                                .iter()
                                .map(|e| self.rewrite_expr_with_ctx(e, bases, ctx))
                                .collect::<Result<Vec<_>, _>>()?,
                        )
                    }
                    Expr::Field(_, _) | Expr::Index(_, _) | Expr::Deref(_) => {
                        if let Some(lv) = expr_to_lvalue(expr) {
                            Self::lvalue_to_expr(
                                self.rewrite_lvalue_with_ctx(&lv, bases, ctx)?,
                            )
                        } else {
                            expr.clone()
                        }
                    }
                    Expr::Unary(op, inner) => {
                        Expr::Unary(
                            *op,
                            Box::new(self.rewrite_expr_with_ctx(inner, bases, ctx)?),
                        )
                    }
                    Expr::Binary(a, op, b) => {
                        Expr::Binary(
                            Box::new(self.rewrite_expr_with_ctx(a, bases, ctx)?),
                            *op,
                            Box::new(self.rewrite_expr_with_ctx(b, bases, ctx)?),
                        )
                    }
                    Expr::SetLit(items) => {
                        Expr::SetLit(
                            items
                                .iter()
                                .map(|item| match item {
                                    SetItem::Single(e) => {
                                        self.rewrite_expr_with_ctx(e, bases, ctx)
                                            .map(SetItem::Single)
                                    }
                                    SetItem::Range(lo, hi) => {
                                        Ok(
                                            SetItem::Range(
                                                self.rewrite_expr_with_ctx(lo, bases, ctx)?,
                                                self.rewrite_expr_with_ctx(hi, bases, ctx)?,
                                            ),
                                        )
                                    }
                                })
                                .collect::<Result<Vec<_>, _>>()?,
                        )
                    }
                    Expr::Ctor(_, _)
                    | Expr::ArrayLit(_)
                    | Expr::RecordUpdate(_, _)
                    | Expr::ArrayUpdate(_, _)
                    | Expr::OptionNone
                    | Expr::OptionSome(_)
                    | Expr::Cond { .. }
                    | Expr::Cast(_, _)
                    | Expr::Int(_)
                    | Expr::Bool(_)
                    | Expr::Char(_)
                    | Expr::Real(_)
                    | Expr::Str(_)
                    | Expr::Var(_)
                    | Expr::Nil => expr.clone(),
                },
            )
        }
        fn rewrite_lvalue_with_ctx(
            &self,
            lv: &LValue,
            bases: &[LValue],
            ctx: &Ctx,
        ) -> Result<LValue, String> {
            if ctx.vars.contains_key(&lv.base) {
                return Ok(lv.clone());
            }
            for base in bases.iter().rev() {
                let bt = self.resolve_lvalue_addr_ctx(base, ctx)?.ty;
                if let TypeInfo::Record(r) = bt {
                    if r.fields.contains_key(&lv.base) {
                        let mut sels = base.sels.clone();
                        sels.push(Selector::Field(lv.base.clone()));
                        sels.extend(lv.sels.clone());
                        return Ok(LValue {
                            base: base.base.clone(),
                            sels,
                        });
                    }
                }
            }
            Ok(lv.clone())
        }
        fn lvalue_to_expr(lv: LValue) -> Expr {
            let mut e = Expr::Var(lv.base);
            for sel in lv.sels {
                e = match sel {
                    Selector::Deref => Expr::Deref(Box::new(e)),
                    Selector::Field(f) => Expr::Field(Box::new(e), f),
                    Selector::Index(ixs) => {
                        let mut acc = e;
                        for ix in ixs {
                            acc = Expr::Index(Box::new(acc), Box::new(ix));
                        }
                        acc
                    }
                };
            }
            e
        }
        fn coerce_real_inline(
            &self,
            e: &Expr,
            t: &TypeInfo,
            ctx: &Ctx,
        ) -> Result<String, String> {
            let v = self.gen_expr_inline_ctx(e, ctx)?;
            Ok(
                if #[allow(non_exhaustive_omitted_patterns)]
                match t {
                    TypeInfo::Basic(BasicType::Real) => true,
                    _ => false,
                } {
                    v
                } else {
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("{0} S>F", v))
                    })
                },
            )
        }
        fn ordinal_inline(&self, e: &Expr, ctx: &Ctx) -> Result<String, String> {
            self.gen_expr_inline_ctx(e, ctx)
        }
        fn set_low_bound_expr(
            &self,
            set_expr: &Expr,
            ctx: &Ctx,
        ) -> Result<String, String> {
            let ty = type_of_expr_scoped(
                self.env,
                &self.ctx_to_types(ctx),
                &ctx.routines,
                set_expr,
            )?;
            match ty {
                TypeInfo::Set(s) => Ok(s.low.to_string()),
                _ => Err("right-hand side of 'in' must be a set".into()),
            }
        }
        fn gen_set_lit_inline(
            &self,
            items: &[SetItem],
            ctx: &Ctx,
        ) -> Result<String, String> {
            if items.is_empty() {
                return Ok("0".into());
            }
            let first_expr = match &items[0] {
                SetItem::Single(e) => e,
                SetItem::Range(lo, _) => lo,
            };
            let first_ty = type_of_expr_scoped(
                self.env,
                &self.ctx_to_types(ctx),
                &ctx.routines,
                first_expr,
            )?;
            let low = match first_ty {
                TypeInfo::Enum(ref e) => e.low,
                TypeInfo::Subrange(ref s) => s.low,
                TypeInfo::Basic(BasicType::Boolean) => 0,
                TypeInfo::Basic(BasicType::Char) => 0,
                TypeInfo::Basic(BasicType::Integer) => 0,
                _ => return Err("set literal items must be ordinal".into()),
            };
            let mut parts = Vec::new();
            for item in items {
                match item {
                    SetItem::Single(expr) => {
                        let iv = self.ordinal_inline(expr, ctx)?;
                        parts
                            .push(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("1 {0} {1} - LSHIFT", iv, low),
                                    )
                                }),
                            );
                    }
                    SetItem::Range(lo_expr, hi_expr) => {
                        let lo = self.ordinal_inline(lo_expr, ctx)?;
                        let hi = self.ordinal_inline(hi_expr, ctx)?;
                        parts
                            .push(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "1 {0} {1} - 1 + LSHIFT 1 - {1} {2} - LSHIFT",
                                            hi,
                                            lo,
                                            low,
                                        ),
                                    )
                                }),
                            );
                    }
                }
            }
            let mut out = String::new();
            for (idx, part) in parts.iter().enumerate() {
                if idx > 0 {
                    out.push(' ');
                }
                out.push_str(part);
                if idx > 0 {
                    out.push_str(" OR");
                }
            }
            Ok(out)
        }
        fn case_labels_inline(&self, labels: &[CaseLabel]) -> Result<String, String> {
            let mut parts = Vec::new();
            for label in labels {
                match label {
                    CaseLabel::Single(c) => {
                        parts
                            .push(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("R@ {0} =", self.const_to_token(c)?),
                                    )
                                }),
                            )
                    }
                    CaseLabel::Range(lo, hi) => {
                        parts
                            .push(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "R@ {0} >= R@ {1} <= AND",
                                            self.const_to_token(lo)?,
                                            self.const_to_token(hi)?,
                                        ),
                                    )
                                }),
                            );
                    }
                }
            }
            if parts.is_empty() {
                return Ok("0".into());
            }
            let mut out = String::new();
            for (idx, part) in parts.iter().enumerate() {
                if idx > 0 {
                    out.push(' ');
                }
                out.push_str(part);
                if idx > 0 {
                    out.push_str(" OR");
                }
            }
            Ok(out)
        }
        fn gen_builtin_new_dispose(
            &mut self,
            name: &str,
            args: &[Expr],
            ctx: &Ctx,
        ) -> Result<(), String> {
            if args.len() != 1 {
                return Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("{0} requires 1 argument", name),
                        )
                    }),
                );
            }
            let lv = expr_to_lvalue(&args[0])
                .ok_or_else(|| ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{0} argument must be lvalue pointer", name),
                    )
                }))?;
            let dst = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
            if name.eq_ignore_ascii_case("dispose") {
                self.emit_store("0", &dst);
                return Ok(());
            }
            let target = match &dst.ty {
                TypeInfo::Pointer(n) => n.clone(),
                _ => return Err("new argument must be pointer".into()),
            };
            let pointee = lookup_type(self.env, &target)
                .ok_or_else(|| ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("unknown pointed type: {0}", target),
                    )
                }))?;
            let sz = self.type_size_bytes(&pointee)?;
            self.wln("HERE __NEWP PVAR!");
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} ALLOT", sz))
                }),
            );
            self.emit_store("__NEWP PVAR@", &dst);
            Ok(())
        }
        fn gen_builtin_inttohex(
            &mut self,
            args: &[Expr],
            ctx: &Ctx,
        ) -> Result<(), String> {
            if args.len() != 4 {
                return Err("IntToHex requires 4 arguments".into());
            }
            let value = self.gen_expr_inline_ctx(&args[0], ctx)?;
            let lv = expr_to_lvalue(&args[1])
                .ok_or("IntToHex second argument must be lvalue char array")?;
            let dst = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
            match &dst.ty {
                TypeInfo::Array(ai) if #[allow(non_exhaustive_omitted_patterns)]
                match ai.elem_ty.as_ref() {
                    TypeInfo::Basic(BasicType::Char) => true,
                    _ => false,
                } => {}
                _ => return Err("IntToHex second argument must be array of char".into()),
            }
            let max_len = self.gen_expr_inline_ctx(&args[2], ctx)?;
            let zero_fill = self.gen_expr_inline_ctx(&args[3], ctx)?;
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} __I2H_VAL PVAR!", value))
                }),
            );
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{0} __I2H_PTR PVAR!", self.emit_addr_inline(&dst)),
                    )
                }),
            );
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} __I2H_MAX PVAR!", max_len))
                }),
            );
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} __I2H_FILL PVAR!", zero_fill))
                }),
            );
            self.wln("__I32_TO_HEX_STR");
            Ok(())
        }
        fn gen_builtin_setaddr(
            &mut self,
            args: &[Expr],
            ctx: &Ctx,
        ) -> Result<(), String> {
            if args.len() != 2 {
                return Err("SetAddr requires 2 arguments".into());
            }
            let lv = expr_to_lvalue(&args[0])
                .ok_or("SetAddr first argument must be lvalue pointer")?;
            let dst = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
            match dst.ty {
                TypeInfo::Pointer(_) => {}
                _ => return Err("SetAddr first argument must be pointer".into()),
            }
            let addr = self.gen_expr_inline_ctx(&args[1], ctx)?;
            self.emit_store(&addr, &dst);
            Ok(())
        }
        fn gen_builtin_copy(&mut self, args: &[Expr], ctx: &Ctx) -> Result<(), String> {
            if args.len() != 2 {
                return Err("Copy requires 2 arguments".into());
            }
            let src = self.resolve_char_array_arg(&args[0], ctx, "Copy source")?;
            let dst = self
                .resolve_char_array_lvalue_arg(&args[1], ctx, "Copy destination")?;
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{0} __STR_SRC PVAR!", self.emit_addr_inline(&src)),
                    )
                }),
            );
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{0} __STR_DST PVAR!", self.emit_addr_inline(&dst)),
                    )
                }),
            );
            self.wln("__STRCPY");
            Ok(())
        }
        fn gen_builtin_concat(
            &mut self,
            args: &[Expr],
            ctx: &Ctx,
        ) -> Result<(), String> {
            if args.len() != 3 {
                return Err("Concat requires 3 arguments".into());
            }
            let a = self.resolve_char_array_arg(&args[0], ctx, "Concat first source")?;
            let b = self.resolve_char_array_arg(&args[1], ctx, "Concat second source")?;
            let dst = self
                .resolve_char_array_lvalue_arg(&args[2], ctx, "Concat destination")?;
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{0} __STR_SRC PVAR!", self.emit_addr_inline(&a)),
                    )
                }),
            );
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{0} __STR_DST PVAR!", self.emit_addr_inline(&dst)),
                    )
                }),
            );
            self.wln("__STRCPY");
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{0} __STR_SRC PVAR!", self.emit_addr_inline(&a)),
                    )
                }),
            );
            self.wln("__STRLEN __STR_LEN PVAR!");
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{0} __STR_SRC PVAR!", self.emit_addr_inline(&b)),
                    )
                }),
            );
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!(
                            "{0} __STR_LEN PVAR@ 4 * + __STR_DST PVAR!",
                            self.emit_addr_inline(&dst),
                        ),
                    )
                }),
            );
            self.wln("__STRCPY");
            Ok(())
        }
        fn gen_builtin_delete(
            &mut self,
            args: &[Expr],
            ctx: &Ctx,
        ) -> Result<(), String> {
            if args.len() != 3 {
                return Err("Delete requires 3 arguments".into());
            }
            let dst = self
                .resolve_char_array_lvalue_arg(&args[0], ctx, "Delete target")?;
            let idx = self.gen_expr_inline_ctx(&args[1], ctx)?;
            let cnt = self.gen_expr_inline_ctx(&args[2], ctx)?;
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{0} __STR_DST PVAR!", self.emit_addr_inline(&dst)),
                    )
                }),
            );
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} __STR_IDX PVAR!", idx))
                }),
            );
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} __STR_CNT PVAR!", cnt))
                }),
            );
            self.wln("__STRDELETE");
            Ok(())
        }
        fn gen_builtin_insert(
            &mut self,
            args: &[Expr],
            ctx: &Ctx,
        ) -> Result<(), String> {
            if args.len() != 3 {
                return Err("Insert requires 3 arguments".into());
            }
            let src = self.resolve_char_array_arg(&args[0], ctx, "Insert source")?;
            let dst = self
                .resolve_char_array_lvalue_arg(&args[1], ctx, "Insert destination")?;
            let idx = self.gen_expr_inline_ctx(&args[2], ctx)?;
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{0} __STR_SRC PVAR!", self.emit_addr_inline(&src)),
                    )
                }),
            );
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("{0} __STR_DST PVAR!", self.emit_addr_inline(&dst)),
                    )
                }),
            );
            self.wln(
                &::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} __STR_IDX PVAR!", idx))
                }),
            );
            self.wln("__STRINSERT");
            Ok(())
        }
        fn resolve_char_array_arg(
            &self,
            expr: &Expr,
            ctx: &Ctx,
            what: &str,
        ) -> Result<AddrRef, String> {
            if let Expr::Str(s) = expr {
                let Some((name, _)) = self
                    .string_literals
                    .iter()
                    .find(|(_, value)| value == s) else {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "internal: missing string literal backing storage for {0}",
                                    what,
                                ),
                            )
                        }),
                    );
                };
                let len = s.chars().count() as u32 + 1;
                return Ok(AddrRef {
                    base_expr: name.clone(),
                    offset: 0,
                    dynamic_addr_expr: None,
                    ty: TypeInfo::Array(ArrayInfo {
                        low: 0,
                        high: len as i32 - 1,
                        len,
                        elem_ty: Box::new(TypeInfo::Basic(BasicType::Char)),
                        elem_size_bytes: 4,
                        size_bytes: len * 4,
                    }),
                    variant_checks: Vec::new(),
                });
            }
            let lv = expr_to_lvalue(expr)
                .ok_or_else(|| ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} must be array of char", what))
                }))?;
            let addr = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
            match &addr.ty {
                TypeInfo::Array(ai) if #[allow(non_exhaustive_omitted_patterns)]
                match ai.elem_ty.as_ref() {
                    TypeInfo::Basic(BasicType::Char) => true,
                    _ => false,
                } => Ok(addr),
                _ => {
                    Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} must be array of char", what),
                            )
                        }),
                    )
                }
            }
        }
        fn resolve_char_array_lvalue_arg(
            &self,
            expr: &Expr,
            ctx: &Ctx,
            what: &str,
        ) -> Result<AddrRef, String> {
            self.resolve_char_array_arg(expr, ctx, what)
        }
        fn collect_string_literals_program(&mut self, prog: &Program) {
            self.collect_string_literals_block(&prog.block);
        }
        fn collect_string_literals_block(&mut self, block: &Block) {
            for decl in &block.consts {
                self.collect_string_literals_const_expr(&decl.expr);
            }
            for routine in &block.routines {
                match routine {
                    RoutineDecl::Procedure(p) => {
                        self.collect_string_literals_block(&p.block)
                    }
                    RoutineDecl::Function(f) => {
                        self.collect_string_literals_block(&f.block)
                    }
                }
            }
            self.collect_string_literals_stmt(&block.body);
        }
        fn collect_string_literals_stmt(&mut self, stmt: &Stmt) {
            match stmt {
                Stmt::Empty | Stmt::ReadLn => {}
                Stmt::Compound(stmts) => {
                    for stmt in stmts {
                        self.collect_string_literals_stmt(stmt);
                    }
                }
                Stmt::Assign(_, expr) => self.collect_string_literals_expr(expr),
                Stmt::Read(args) | Stmt::Write(args) | Stmt::WriteLn(args) => {
                    for expr in args {
                        self.collect_string_literals_expr(expr);
                    }
                }
                Stmt::For { init, limit, body, .. } => {
                    self.collect_string_literals_expr(init);
                    self.collect_string_literals_expr(limit);
                    self.collect_string_literals_stmt(body);
                }
                Stmt::If(cond, then_s, else_s) => {
                    self.collect_string_literals_expr(cond);
                    self.collect_string_literals_stmt(then_s);
                    if let Some(else_s) = else_s {
                        self.collect_string_literals_stmt(else_s);
                    }
                }
                Stmt::With(_, body) | Stmt::While(_, body) => {
                    if let Stmt::While(cond, _) = stmt {
                        self.collect_string_literals_expr(cond);
                    }
                    self.collect_string_literals_stmt(body);
                }
                Stmt::Repeat(stmts, cond) => {
                    for stmt in stmts {
                        self.collect_string_literals_stmt(stmt);
                    }
                    self.collect_string_literals_expr(cond);
                }
                Stmt::Case { expr, arms, else_stmt } => {
                    self.collect_string_literals_expr(expr);
                    for (_, stmt) in arms {
                        self.collect_string_literals_stmt(stmt);
                    }
                    if let Some(stmt) = else_stmt {
                        self.collect_string_literals_stmt(stmt);
                    }
                }
                Stmt::ProcCall(_, args) => {
                    for expr in args {
                        self.collect_string_literals_expr(expr);
                    }
                }
                Stmt::SumCase { expr, arms, else_stmt } => {
                    self.collect_string_literals_expr(expr);
                    for arm in arms {
                        self.collect_string_literals_stmt(&arm.body);
                    }
                    if let Some(stmt) = else_stmt {
                        self.collect_string_literals_stmt(stmt);
                    }
                }
            }
        }
        fn collect_string_literals_expr(&mut self, expr: &Expr) {
            match expr {
                Expr::Str(s) => self.intern_string_literal(s),
                Expr::Call(_, args) => {
                    for expr in args {
                        self.collect_string_literals_expr(expr);
                    }
                }
                Expr::Ctor(_, named) => {
                    for (_, expr) in named {
                        self.collect_string_literals_expr(expr);
                    }
                }
                Expr::ArrayLit(items) => {
                    for expr in items {
                        self.collect_string_literals_expr(expr);
                    }
                }
                Expr::RecordUpdate(base, named) => {
                    self.collect_string_literals_expr(base);
                    for (_, expr) in named {
                        self.collect_string_literals_expr(expr);
                    }
                }
                Expr::ArrayUpdate(base, pairs) => {
                    self.collect_string_literals_expr(base);
                    for (idx, expr) in pairs {
                        self.collect_string_literals_expr(idx);
                        self.collect_string_literals_expr(expr);
                    }
                }
                Expr::OptionSome(expr) | Expr::Cast(_, expr) => {
                    self.collect_string_literals_expr(expr)
                }
                Expr::Cond { arms, else_block } => {
                    for arm in arms {
                        self.collect_string_literals_expr(&arm.cond);
                        for stmt in &arm.block.stmts {
                            self.collect_string_literals_stmt(stmt);
                        }
                        self.collect_string_literals_expr(&arm.block.value);
                    }
                    for stmt in &else_block.stmts {
                        self.collect_string_literals_stmt(stmt);
                    }
                    self.collect_string_literals_expr(&else_block.value);
                }
                Expr::Deref(expr) | Expr::Field(expr, _) | Expr::Unary(_, expr) => {
                    self.collect_string_literals_expr(expr)
                }
                Expr::Index(base, index) | Expr::Binary(base, _, index) => {
                    self.collect_string_literals_expr(base);
                    self.collect_string_literals_expr(index);
                }
                Expr::SetLit(items) => {
                    for item in items {
                        match item {
                            SetItem::Single(expr) => {
                                self.collect_string_literals_expr(expr)
                            }
                            SetItem::Range(lo, hi) => {
                                self.collect_string_literals_expr(lo);
                                self.collect_string_literals_expr(hi);
                            }
                        }
                    }
                }
                Expr::Int(_)
                | Expr::Bool(_)
                | Expr::Char(_)
                | Expr::Real(_)
                | Expr::Nil
                | Expr::OptionNone
                | Expr::Var(_) => {}
            }
        }
        fn collect_string_literals_const_expr(&mut self, expr: &ConstExpr) {
            match expr {
                ConstExpr::Call(_, args) => {
                    for expr in args {
                        self.collect_string_literals_const_expr(expr);
                    }
                }
                ConstExpr::Unary(_, expr) => {
                    self.collect_string_literals_const_expr(expr)
                }
                ConstExpr::Binary(a, _, b) => {
                    self.collect_string_literals_const_expr(a);
                    self.collect_string_literals_const_expr(b);
                }
                ConstExpr::Int(_)
                | ConstExpr::Bool(_)
                | ConstExpr::Char(_)
                | ConstExpr::Real(_)
                | ConstExpr::Const(_) => {}
            }
        }
        fn intern_string_literal(&mut self, value: &str) {
            if self.string_literals.iter().any(|(_, existing)| existing == value) {
                return;
            }
            let name = ::alloc::__export::must_use({
                ::alloc::fmt::format(
                    format_args!("__STRLIT_{0}", self.string_literals.len()),
                )
            });
            self.string_literals.push((name, value.to_string()));
        }
    }
    fn parse_hex_text(s: &str) -> Result<i32, String> {
        let raw = s.trim();
        let raw = raw
            .strip_prefix("0x")
            .or_else(|| raw.strip_prefix("0X"))
            .or_else(|| raw.strip_prefix('$'))
            .unwrap_or(raw);
        if raw.is_empty() {
            return Ok(0);
        }
        i32::from_str_radix(raw, 16)
            .map_err(|_| "invalid hex string literal for HexToInt".into())
    }
}
mod sema {
    use std::collections::{HashMap, HashSet};
    use crate::ast::*;
    pub enum TypeInfo {
        Basic(BasicType),
        Enum(EnumInfo),
        Subrange(SubrangeInfo),
        Set(SetInfo),
        Pointer(String),
        Nil,
        Record(RecordInfo),
        Sum(SumInfo),
        Array(ArrayInfo),
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for TypeInfo {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                TypeInfo::Basic(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Basic",
                        &__self_0,
                    )
                }
                TypeInfo::Enum(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Enum",
                        &__self_0,
                    )
                }
                TypeInfo::Subrange(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Subrange",
                        &__self_0,
                    )
                }
                TypeInfo::Set(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Set",
                        &__self_0,
                    )
                }
                TypeInfo::Pointer(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Pointer",
                        &__self_0,
                    )
                }
                TypeInfo::Nil => ::core::fmt::Formatter::write_str(f, "Nil"),
                TypeInfo::Record(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Record",
                        &__self_0,
                    )
                }
                TypeInfo::Sum(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Sum",
                        &__self_0,
                    )
                }
                TypeInfo::Array(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Array",
                        &__self_0,
                    )
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for TypeInfo {
        #[inline]
        fn clone(&self) -> TypeInfo {
            match self {
                TypeInfo::Basic(__self_0) => {
                    TypeInfo::Basic(::core::clone::Clone::clone(__self_0))
                }
                TypeInfo::Enum(__self_0) => {
                    TypeInfo::Enum(::core::clone::Clone::clone(__self_0))
                }
                TypeInfo::Subrange(__self_0) => {
                    TypeInfo::Subrange(::core::clone::Clone::clone(__self_0))
                }
                TypeInfo::Set(__self_0) => {
                    TypeInfo::Set(::core::clone::Clone::clone(__self_0))
                }
                TypeInfo::Pointer(__self_0) => {
                    TypeInfo::Pointer(::core::clone::Clone::clone(__self_0))
                }
                TypeInfo::Nil => TypeInfo::Nil,
                TypeInfo::Record(__self_0) => {
                    TypeInfo::Record(::core::clone::Clone::clone(__self_0))
                }
                TypeInfo::Sum(__self_0) => {
                    TypeInfo::Sum(::core::clone::Clone::clone(__self_0))
                }
                TypeInfo::Array(__self_0) => {
                    TypeInfo::Array(::core::clone::Clone::clone(__self_0))
                }
            }
        }
    }
    pub struct EnumInfo {
        pub name: String,
        pub low: i32,
        pub high: i32,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for EnumInfo {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "EnumInfo",
                "name",
                &self.name,
                "low",
                &self.low,
                "high",
                &&self.high,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for EnumInfo {
        #[inline]
        fn clone(&self) -> EnumInfo {
            EnumInfo {
                name: ::core::clone::Clone::clone(&self.name),
                low: ::core::clone::Clone::clone(&self.low),
                high: ::core::clone::Clone::clone(&self.high),
            }
        }
    }
    pub struct SubrangeInfo {
        pub base: Box<TypeInfo>,
        pub low: i32,
        pub high: i32,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for SubrangeInfo {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "SubrangeInfo",
                "base",
                &self.base,
                "low",
                &self.low,
                "high",
                &&self.high,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for SubrangeInfo {
        #[inline]
        fn clone(&self) -> SubrangeInfo {
            SubrangeInfo {
                base: ::core::clone::Clone::clone(&self.base),
                low: ::core::clone::Clone::clone(&self.low),
                high: ::core::clone::Clone::clone(&self.high),
            }
        }
    }
    pub struct SetInfo {
        pub elem_ty: Box<TypeInfo>,
        pub low: i32,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for SetInfo {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "SetInfo",
                "elem_ty",
                &self.elem_ty,
                "low",
                &&self.low,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for SetInfo {
        #[inline]
        fn clone(&self) -> SetInfo {
            SetInfo {
                elem_ty: ::core::clone::Clone::clone(&self.elem_ty),
                low: ::core::clone::Clone::clone(&self.low),
            }
        }
    }
    pub struct RecordInfo {
        pub fields: HashMap<String, FieldInfo>,
        pub size_bytes: u32,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for RecordInfo {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "RecordInfo",
                "fields",
                &self.fields,
                "size_bytes",
                &&self.size_bytes,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for RecordInfo {
        #[inline]
        fn clone(&self) -> RecordInfo {
            RecordInfo {
                fields: ::core::clone::Clone::clone(&self.fields),
                size_bytes: ::core::clone::Clone::clone(&self.size_bytes),
            }
        }
    }
    pub struct FieldInfo {
        pub offset_bytes: u32,
        pub ty: TypeInfo,
        pub variant_checks: Vec<VariantCheckInfo>,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for FieldInfo {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "FieldInfo",
                "offset_bytes",
                &self.offset_bytes,
                "ty",
                &self.ty,
                "variant_checks",
                &&self.variant_checks,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for FieldInfo {
        #[inline]
        fn clone(&self) -> FieldInfo {
            FieldInfo {
                offset_bytes: ::core::clone::Clone::clone(&self.offset_bytes),
                ty: ::core::clone::Clone::clone(&self.ty),
                variant_checks: ::core::clone::Clone::clone(&self.variant_checks),
            }
        }
    }
    pub struct VariantCheckInfo {
        pub tag_offset_bytes: u32,
        pub allowed_ranges: Vec<(i32, i32)>,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for VariantCheckInfo {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "VariantCheckInfo",
                "tag_offset_bytes",
                &self.tag_offset_bytes,
                "allowed_ranges",
                &&self.allowed_ranges,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for VariantCheckInfo {
        #[inline]
        fn clone(&self) -> VariantCheckInfo {
            VariantCheckInfo {
                tag_offset_bytes: ::core::clone::Clone::clone(&self.tag_offset_bytes),
                allowed_ranges: ::core::clone::Clone::clone(&self.allowed_ranges),
            }
        }
    }
    pub struct ArrayInfo {
        pub low: i32,
        pub high: i32,
        pub len: u32,
        pub elem_ty: Box<TypeInfo>,
        pub elem_size_bytes: u32,
        pub size_bytes: u32,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for ArrayInfo {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            let names: &'static _ = &[
                "low",
                "high",
                "len",
                "elem_ty",
                "elem_size_bytes",
                "size_bytes",
            ];
            let values: &[&dyn ::core::fmt::Debug] = &[
                &self.low,
                &self.high,
                &self.len,
                &self.elem_ty,
                &self.elem_size_bytes,
                &&self.size_bytes,
            ];
            ::core::fmt::Formatter::debug_struct_fields_finish(
                f,
                "ArrayInfo",
                names,
                values,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for ArrayInfo {
        #[inline]
        fn clone(&self) -> ArrayInfo {
            ArrayInfo {
                low: ::core::clone::Clone::clone(&self.low),
                high: ::core::clone::Clone::clone(&self.high),
                len: ::core::clone::Clone::clone(&self.len),
                elem_ty: ::core::clone::Clone::clone(&self.elem_ty),
                elem_size_bytes: ::core::clone::Clone::clone(&self.elem_size_bytes),
                size_bytes: ::core::clone::Clone::clone(&self.size_bytes),
            }
        }
    }
    pub struct SumInfo {
        pub arms: Vec<SumArmInfo>,
        pub payload_size_bytes: u32,
        pub size_bytes: u32,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for SumInfo {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "SumInfo",
                "arms",
                &self.arms,
                "payload_size_bytes",
                &self.payload_size_bytes,
                "size_bytes",
                &&self.size_bytes,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for SumInfo {
        #[inline]
        fn clone(&self) -> SumInfo {
            SumInfo {
                arms: ::core::clone::Clone::clone(&self.arms),
                payload_size_bytes: ::core::clone::Clone::clone(
                    &self.payload_size_bytes,
                ),
                size_bytes: ::core::clone::Clone::clone(&self.size_bytes),
            }
        }
    }
    pub struct SumArmInfo {
        pub name: String,
        pub tag: u32,
        pub fields: Vec<SumFieldInfo>,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for SumArmInfo {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "SumArmInfo",
                "name",
                &self.name,
                "tag",
                &self.tag,
                "fields",
                &&self.fields,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for SumArmInfo {
        #[inline]
        fn clone(&self) -> SumArmInfo {
            SumArmInfo {
                name: ::core::clone::Clone::clone(&self.name),
                tag: ::core::clone::Clone::clone(&self.tag),
                fields: ::core::clone::Clone::clone(&self.fields),
            }
        }
    }
    pub struct SumFieldInfo {
        pub name: String,
        pub offset_bytes: u32,
        pub ty: TypeInfo,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for SumFieldInfo {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "SumFieldInfo",
                "name",
                &self.name,
                "offset_bytes",
                &self.offset_bytes,
                "ty",
                &&self.ty,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for SumFieldInfo {
        #[inline]
        fn clone(&self) -> SumFieldInfo {
            SumFieldInfo {
                name: ::core::clone::Clone::clone(&self.name),
                offset_bytes: ::core::clone::Clone::clone(&self.offset_bytes),
                ty: ::core::clone::Clone::clone(&self.ty),
            }
        }
    }
    pub struct ParamSig {
        pub ty: TypeInfo,
        pub by_ref: bool,
        pub conformant: Option<ConformantArrayParam>,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for ParamSig {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field3_finish(
                f,
                "ParamSig",
                "ty",
                &self.ty,
                "by_ref",
                &self.by_ref,
                "conformant",
                &&self.conformant,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for ParamSig {
        #[inline]
        fn clone(&self) -> ParamSig {
            ParamSig {
                ty: ::core::clone::Clone::clone(&self.ty),
                by_ref: ::core::clone::Clone::clone(&self.by_ref),
                conformant: ::core::clone::Clone::clone(&self.conformant),
            }
        }
    }
    pub struct RoutineSig {
        pub params: Vec<ParamSig>,
        pub ret: Option<TypeInfo>,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for RoutineSig {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "RoutineSig",
                "params",
                &self.params,
                "ret",
                &&self.ret,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for RoutineSig {
        #[inline]
        fn clone(&self) -> RoutineSig {
            RoutineSig {
                params: ::core::clone::Clone::clone(&self.params),
                ret: ::core::clone::Clone::clone(&self.ret),
            }
        }
    }
    pub struct Env {
        pub consts: HashMap<String, ConstVal>,
        pub types: HashMap<String, TypeInfo>,
        pub vars: HashMap<String, TypeInfo>,
        pub immutables: HashSet<String>,
        pub routines: HashMap<String, RoutineSig>,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for Env {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field5_finish(
                f,
                "Env",
                "consts",
                &self.consts,
                "types",
                &self.types,
                "vars",
                &self.vars,
                "immutables",
                &self.immutables,
                "routines",
                &&self.routines,
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for Env {
        #[inline]
        fn clone(&self) -> Env {
            Env {
                consts: ::core::clone::Clone::clone(&self.consts),
                types: ::core::clone::Clone::clone(&self.types),
                vars: ::core::clone::Clone::clone(&self.vars),
                immutables: ::core::clone::Clone::clone(&self.immutables),
                routines: ::core::clone::Clone::clone(&self.routines),
            }
        }
    }
    pub enum ConstVal {
        I32(i32),
        U32(u32),
        Bool(bool),
        Real(u32),
        EnumVal { type_name: String, ordinal: i32 },
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for ConstVal {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                ConstVal::I32(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "I32",
                        &__self_0,
                    )
                }
                ConstVal::U32(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "U32",
                        &__self_0,
                    )
                }
                ConstVal::Bool(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Bool",
                        &__self_0,
                    )
                }
                ConstVal::Real(__self_0) => {
                    ::core::fmt::Formatter::debug_tuple_field1_finish(
                        f,
                        "Real",
                        &__self_0,
                    )
                }
                ConstVal::EnumVal { type_name: __self_0, ordinal: __self_1 } => {
                    ::core::fmt::Formatter::debug_struct_field2_finish(
                        f,
                        "EnumVal",
                        "type_name",
                        __self_0,
                        "ordinal",
                        &__self_1,
                    )
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for ConstVal {
        #[inline]
        fn clone(&self) -> ConstVal {
            match self {
                ConstVal::I32(__self_0) => {
                    ConstVal::I32(::core::clone::Clone::clone(__self_0))
                }
                ConstVal::U32(__self_0) => {
                    ConstVal::U32(::core::clone::Clone::clone(__self_0))
                }
                ConstVal::Bool(__self_0) => {
                    ConstVal::Bool(::core::clone::Clone::clone(__self_0))
                }
                ConstVal::Real(__self_0) => {
                    ConstVal::Real(::core::clone::Clone::clone(__self_0))
                }
                ConstVal::EnumVal { type_name: __self_0, ordinal: __self_1 } => {
                    ConstVal::EnumVal {
                        type_name: ::core::clone::Clone::clone(__self_0),
                        ordinal: ::core::clone::Clone::clone(__self_1),
                    }
                }
            }
        }
    }
    impl Env {
        pub fn new() -> Self {
            let mut types = HashMap::new();
            types.insert("integer".to_string(), TypeInfo::Basic(BasicType::Integer));
            types.insert("boolean".to_string(), TypeInfo::Basic(BasicType::Boolean));
            types.insert("char".to_string(), TypeInfo::Basic(BasicType::Char));
            types.insert("real".to_string(), TypeInfo::Basic(BasicType::Real));
            Self {
                consts: HashMap::new(),
                types,
                vars: HashMap::new(),
                immutables: HashSet::new(),
                routines: HashMap::new(),
            }
        }
    }
    pub fn lookup_type(env: &Env, name: &str) -> Option<TypeInfo> {
        env.types
            .iter()
            .find(|(type_name, _)| type_name.eq_ignore_ascii_case(name))
            .map(|(_, ty)| ty.clone())
    }
    fn tyref_to_info(env: &Env, tr: &TypeRef) -> Result<TypeInfo, String> {
        match tr {
            TypeRef::Basic(b) => Ok(TypeInfo::Basic(b.clone())),
            TypeRef::Option(inner) => {
                let inner_ty = tyref_to_info(env, inner)?;
                make_option_type(inner_ty)
            }
            TypeRef::Result(ok_ty, err_ty) => {
                let ok = tyref_to_info(env, ok_ty)?;
                let err = tyref_to_info(env, err_ty)?;
                make_result_type(ok, err)
            }
            TypeRef::Named(n) => {
                lookup_type(env, n)
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("unknown type: {0}", n))
                    }))
            }
            TypeRef::PointerNamed(n) => Ok(TypeInfo::Pointer(n.clone())),
            TypeRef::Subrange { low, high } => build_subrange_info(env, low, high),
            TypeRef::Set(elem) => build_set_info(env, elem),
            TypeRef::Array { dims, elem } => build_array_info(env, dims, elem),
        }
    }
    fn make_option_type(inner: TypeInfo) -> Result<TypeInfo, String> {
        let payload_size = sizeof_type(&inner)?;
        Ok(
            TypeInfo::Sum(SumInfo {
                arms: <[_]>::into_vec(
                    ::alloc::boxed::box_new([
                        SumArmInfo {
                            name: "none".into(),
                            tag: 0,
                            fields: ::alloc::vec::Vec::new(),
                        },
                        SumArmInfo {
                            name: "some".into(),
                            tag: 1,
                            fields: <[_]>::into_vec(
                                ::alloc::boxed::box_new([
                                    SumFieldInfo {
                                        name: "value".into(),
                                        offset_bytes: 0,
                                        ty: inner,
                                    },
                                ]),
                            ),
                        },
                    ]),
                ),
                payload_size_bytes: payload_size,
                size_bytes: 4 + payload_size,
            }),
        )
    }
    fn make_result_type(ok_ty: TypeInfo, err_ty: TypeInfo) -> Result<TypeInfo, String> {
        let ok_sz = sizeof_type(&ok_ty)?;
        let err_sz = sizeof_type(&err_ty)?;
        let payload_size = ok_sz.max(err_sz);
        Ok(
            TypeInfo::Sum(SumInfo {
                arms: <[_]>::into_vec(
                    ::alloc::boxed::box_new([
                        SumArmInfo {
                            name: "ok".into(),
                            tag: 0,
                            fields: <[_]>::into_vec(
                                ::alloc::boxed::box_new([
                                    SumFieldInfo {
                                        name: "value".into(),
                                        offset_bytes: 0,
                                        ty: ok_ty,
                                    },
                                ]),
                            ),
                        },
                        SumArmInfo {
                            name: "err".into(),
                            tag: 1,
                            fields: <[_]>::into_vec(
                                ::alloc::boxed::box_new([
                                    SumFieldInfo {
                                        name: "error".into(),
                                        offset_bytes: 0,
                                        ty: err_ty,
                                    },
                                ]),
                            ),
                        },
                    ]),
                ),
                payload_size_bytes: payload_size,
                size_bytes: 4 + payload_size,
            }),
        )
    }
    fn conformant_param_type(
        env: &Env,
        c: &ConformantArrayParam,
    ) -> Result<TypeInfo, String> {
        let mut ty = tyref_to_info(env, &c.elem_ty)?;
        for _ in c.dims.iter().rev() {
            let elem_size_bytes = sizeof_type(&ty)?;
            ty = TypeInfo::Array(ArrayInfo {
                low: 0,
                high: 0,
                len: 0,
                elem_ty: Box::new(ty),
                elem_size_bytes,
                size_bytes: 0,
            });
        }
        Ok(ty)
    }
    pub fn build_subrange_info(
        env: &Env,
        low: &ConstExpr,
        high: &ConstExpr,
    ) -> Result<TypeInfo, String> {
        let lv = eval_const(env, low)?;
        let hv = eval_const(env, high)?;
        let base = match (&lv, &hv) {
            (ConstVal::I32(_), ConstVal::I32(_)) => TypeInfo::Basic(BasicType::Integer),
            (ConstVal::U32(_), ConstVal::U32(_)) => TypeInfo::Basic(BasicType::Char),
            (
                ConstVal::EnumVal { type_name: a, .. },
                ConstVal::EnumVal { type_name: b, .. },
            ) if a == b => {
                lookup_type(env, a)
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("unknown type: {0}", a))
                    }))?
            }
            _ => return Err("subrange bounds must share the same ordinal type".into()),
        };
        let low_i = ordinal_const_value(&lv)?;
        let high_i = ordinal_const_value(&hv)?;
        if low_i > high_i {
            return Err("subrange low bound must be <= high bound".into());
        }
        Ok(
            TypeInfo::Subrange(SubrangeInfo {
                base: Box::new(base),
                low: low_i,
                high: high_i,
            }),
        )
    }
    pub fn build_set_info(env: &Env, elem: &TypeRef) -> Result<TypeInfo, String> {
        let elem_ty = tyref_to_info(env, elem)?;
        let (low, high) = ordinal_bounds(&elem_ty)?;
        if low < 0 || high > 31 {
            return Err("set base type must fit within 0..31".into());
        }
        Ok(
            TypeInfo::Set(SetInfo {
                elem_ty: Box::new(elem_ty),
                low,
            }),
        )
    }
    pub fn build_array_info(
        env: &Env,
        dims: &[ArrayDim],
        elem: &TypeRef,
    ) -> Result<TypeInfo, String> {
        let mut t = tyref_to_info(env, elem)?;
        for d in dims.iter().rev() {
            let dim_ty = build_subrange_info(env, &d.low, &d.high)?;
            let (low, high) = ordinal_bounds(&dim_ty)?;
            let len = (high - low + 1) as u32;
            let esz = sizeof_type(&t)?;
            let sz = len
                .checked_mul(esz)
                .ok_or_else(|| "array size overflow".to_string())?;
            t = TypeInfo::Array(ArrayInfo {
                low,
                high,
                len,
                elem_ty: Box::new(t),
                elem_size_bytes: esz,
                size_bytes: sz,
            });
        }
        Ok(t)
    }
    pub fn build_env(prog: &Program) -> Result<Env, String> {
        let mut env = Env::new();
        collect_block_decls(&mut env, &prog.block, true, "program")?;
        Ok(env)
    }
    fn collect_block_decls(
        env: &mut Env,
        block: &Block,
        collect_vars: bool,
        scope: &str,
    ) -> Result<(), String> {
        for td in &block.types {
            if env.types.contains_key(&td.name) {
                return Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("type redefined in {1}: {0}", td.name, scope),
                        )
                    }),
                );
            }
            env.types.insert(td.name.clone(), TypeInfo::Basic(BasicType::Integer));
        }
        for td in &block.types {
            let info = match &td.spec {
                TypeSpec::Basic(b) => TypeInfo::Basic(b.clone()),
                TypeSpec::Alias(r) => tyref_to_info(env, r)?,
                TypeSpec::Enum(members) => {
                    let mut variants = HashMap::new();
                    for (idx, name) in members.iter().enumerate() {
                        if variants.insert(name.clone(), idx as i32).is_some() {
                            return Err(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "duplicate enum value in {0}: {1}",
                                            scope,
                                            name,
                                        ),
                                    )
                                }),
                            );
                        }
                        env.consts
                            .insert(
                                name.clone(),
                                ConstVal::EnumVal {
                                    type_name: td.name.clone(),
                                    ordinal: idx as i32,
                                },
                            );
                    }
                    TypeInfo::Enum(EnumInfo {
                        name: td.name.clone(),
                        low: 0,
                        high: members.len() as i32 - 1,
                    })
                }
                TypeSpec::Subrange { low, high } => build_subrange_info(env, low, high)?,
                TypeSpec::Set(elem) => build_set_info(env, elem)?,
                TypeSpec::Record { fields, variant } => {
                    let mut ftab = HashMap::new();
                    let offset = layout_record_members(
                        env,
                        fields,
                        variant,
                        &mut ftab,
                        0,
                        scope,
                    )?;
                    TypeInfo::Record(RecordInfo {
                        fields: ftab,
                        size_bytes: offset,
                    })
                }
                TypeSpec::SumRecord(arms) => {
                    let mut out_arms = ::alloc::vec::Vec::new();
                    let mut arm_names = HashSet::new();
                    let mut max_payload = 0u32;
                    for (tag, arm) in arms.iter().enumerate() {
                        if !arm_names.insert(arm.name.to_ascii_lowercase()) {
                            return Err(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "duplicate sum arm name in {1}: {0}",
                                            arm.name,
                                            scope,
                                        ),
                                    )
                                }),
                            );
                        }
                        let mut fields = ::alloc::vec::Vec::new();
                        let mut field_names = HashSet::new();
                        let mut offset = 0u32;
                        for f in &arm.fields {
                            if !field_names.insert(f.name.to_ascii_lowercase()) {
                                return Err(
                                    ::alloc::__export::must_use({
                                        ::alloc::fmt::format(
                                            format_args!(
                                                "duplicate field name in {2} arm {0}: {1}",
                                                arm.name,
                                                f.name,
                                                scope,
                                            ),
                                        )
                                    }),
                                );
                            }
                            let ty = tyref_to_info(env, &f.ty)?;
                            let sz = sizeof_type(&ty)?;
                            fields
                                .push(SumFieldInfo {
                                    name: f.name.clone(),
                                    offset_bytes: offset,
                                    ty,
                                });
                            offset += sz;
                        }
                        max_payload = max_payload.max(offset);
                        out_arms
                            .push(SumArmInfo {
                                name: arm.name.clone(),
                                tag: tag as u32,
                                fields,
                            });
                    }
                    TypeInfo::Sum(SumInfo {
                        arms: out_arms,
                        payload_size_bytes: max_payload,
                        size_bytes: 4 + max_payload,
                    })
                }
                TypeSpec::Array { dims, elem } => build_array_info(env, dims, elem)?,
            };
            env.types.insert(td.name.clone(), info);
        }
        for cd in &block.consts {
            if env.consts.contains_key(&cd.name) {
                return Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("const redefined in {1}: {0}", cd.name, scope),
                        )
                    }),
                );
            }
            let v = eval_const(env, &cd.expr)?;
            if let Some(ty) = &cd.ty {
                let expected = tyref_to_info(env, ty)?;
                let actual = const_type_from_val(v.clone(), env)?;
                if !assignment_compatible(&expected, &actual) {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "const type mismatch for {0}: expected {1}, got {2}",
                                    cd.name,
                                    type_desc(&expected),
                                    type_desc(&actual),
                                ),
                            )
                        }),
                    );
                }
            }
            env.consts.insert(cd.name.clone(), v);
        }
        if collect_vars {
            for vd in &block.vars {
                if env.vars.contains_key(&vd.name) {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("var redefined in {1}: {0}", vd.name, scope),
                            )
                        }),
                    );
                }
                env.vars.insert(vd.name.clone(), tyref_to_info(env, &vd.ty)?);
                if vd.immutable {
                    env.immutables.insert(vd.name.clone());
                }
            }
        }
        let mut local_routine_names = HashSet::new();
        for r in &block.routines {
            let (name, params, ret_ty) = match r {
                RoutineDecl::Procedure(p) => (&p.name, &p.params, None),
                RoutineDecl::Function(f) => (&f.name, &f.params, Some(&f.ret_ty)),
            };
            if !local_routine_names.insert(name.clone()) {
                return Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("routine redefined in {0}: {1}", scope, name),
                        )
                    }),
                );
            }
            let scoped = ::alloc::__export::must_use({
                ::alloc::fmt::format(format_args!("{0}::{1}", scope, name))
            });
            let params = params
                .iter()
                .map(|p| {
                    Ok(ParamSig {
                        ty: if let Some(c) = &p.conformant {
                            conformant_param_type(env, c)?
                        } else {
                            tyref_to_info(env, &p.ty)?
                        },
                        by_ref: p.by_ref || p.conformant.is_some(),
                        conformant: p.conformant.clone(),
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            let ret = ret_ty.map(|t| tyref_to_info(env, t)).transpose()?;
            env.routines.insert(scoped, RoutineSig { params, ret });
        }
        for r in &block.routines {
            match r {
                RoutineDecl::Procedure(p) => {
                    collect_block_decls(
                        env,
                        &p.block,
                        false,
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{1}::{0}", p.name, scope))
                        }),
                    )?
                }
                RoutineDecl::Function(f) => {
                    collect_block_decls(
                        env,
                        &f.block,
                        false,
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{1}::{0}", f.name, scope))
                        }),
                    )?
                }
            }
        }
        Ok(())
    }
    fn layout_record_members(
        env: &Env,
        fields: &[FieldDecl],
        variant: &Option<VariantPart>,
        ftab: &mut HashMap<String, FieldInfo>,
        offset: u32,
        scope: &str,
    ) -> Result<u32, String> {
        layout_record_members_checked(env, fields, variant, ftab, offset, scope, &[])
    }
    fn layout_record_members_checked(
        env: &Env,
        fields: &[FieldDecl],
        variant: &Option<VariantPart>,
        ftab: &mut HashMap<String, FieldInfo>,
        mut offset: u32,
        scope: &str,
        active_checks: &[VariantCheckInfo],
    ) -> Result<u32, String> {
        for f in fields {
            let fty = tyref_to_info(env, &f.ty)?;
            let finfo = FieldInfo {
                offset_bytes: offset,
                ty: fty.clone(),
                variant_checks: active_checks.to_vec(),
            };
            if ftab.insert(f.name.clone(), finfo).is_some() {
                return Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "duplicate field name in {1}: {0}",
                                f.name,
                                scope,
                            ),
                        )
                    }),
                );
            }
            offset += sizeof_type(&fty)?;
        }
        if let Some(variant) = variant {
            if let Some(tag_name) = &variant.tag_name {
                let tag_ty = tyref_to_info(env, &variant.tag_ty)?;
                let finfo = FieldInfo {
                    offset_bytes: offset,
                    ty: tag_ty.clone(),
                    variant_checks: active_checks.to_vec(),
                };
                if ftab.insert(tag_name.clone(), finfo).is_some() {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "duplicate field name in {0}: {1}",
                                    scope,
                                    tag_name,
                                ),
                            )
                        }),
                    );
                }
                offset += sizeof_type(&tag_ty)?;
            }
            let union_ofs = offset;
            let mut max_case = 0u32;
            let tag_offset = if variant.tag_name.is_some() {
                Some(union_ofs - sizeof_type(&tyref_to_info(env, &variant.tag_ty)?)?)
            } else {
                None
            };
            for case in &variant.cases {
                let mut case_checks = active_checks.to_vec();
                if let Some(tag_offset_bytes) = tag_offset {
                    case_checks
                        .push(VariantCheckInfo {
                            tag_offset_bytes,
                            allowed_ranges: case_label_ranges(env, &case.labels)?,
                        });
                }
                let case_sz = layout_record_members_checked(
                    env,
                    &case.fields,
                    &case.variant,
                    ftab,
                    union_ofs,
                    scope,
                    &case_checks,
                )? - union_ofs;
                max_case = max_case.max(case_sz);
            }
            offset += max_case;
        }
        Ok(offset)
    }
    fn case_label_ranges(
        env: &Env,
        labels: &[CaseLabel],
    ) -> Result<Vec<(i32, i32)>, String> {
        let mut out = Vec::new();
        for label in labels {
            match label {
                CaseLabel::Single(c) => {
                    let v = ordinal_const_value(&eval_const(env, c)?)?;
                    out.push((v, v));
                }
                CaseLabel::Range(lo, hi) => {
                    let lo_v = ordinal_const_value(&eval_const(env, lo)?)?;
                    let hi_v = ordinal_const_value(&eval_const(env, hi)?)?;
                    out.push((lo_v, hi_v));
                }
            }
        }
        Ok(out)
    }
    #[allow(dead_code)]
    pub fn type_of_expr(env: &Env, e: &Expr) -> Result<TypeInfo, String> {
        type_of_expr_scoped(env, &env.vars, &HashMap::new(), e)
    }
    pub fn type_of_expr_scoped(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        e: &Expr,
    ) -> Result<TypeInfo, String> {
        match e {
            Expr::Int(_) => Ok(TypeInfo::Basic(BasicType::Integer)),
            Expr::Bool(_) => Ok(TypeInfo::Basic(BasicType::Boolean)),
            Expr::Char(_) => Ok(TypeInfo::Basic(BasicType::Char)),
            Expr::Real(_) => Ok(TypeInfo::Basic(BasicType::Real)),
            Expr::Str(_) => Err("string literal is only allowed in Write/WriteLn".into()),
            Expr::Ctor(_, _) => {
                Err("constructor expression requires target type context".into())
            }
            Expr::ArrayLit(_) => Err("array literal requires target type context".into()),
            Expr::RecordUpdate(base, _) => {
                type_of_expr_scoped(env, vars, visible_routines, base)
            }
            Expr::ArrayUpdate(base, _) => {
                type_of_expr_scoped(env, vars, visible_routines, base)
            }
            Expr::OptionNone => Err("NONE requires OPTION target type context".into()),
            Expr::OptionSome(_) => Err("SOME requires OPTION target type context".into()),
            Expr::Cond { .. } => {
                Err("COND expression requires target type context".into())
            }
            Expr::Cast(tr, inner) => {
                let src = type_of_expr_scoped(env, vars, visible_routines, inner)?;
                let dst = tyref_to_info(env, tr)?;
                let src_sz = sizeof_type(&src)?;
                let dst_sz = sizeof_type(&dst)?;
                if src_sz != dst_sz {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "cast size mismatch: {0} bytes -> {1} bytes",
                                    src_sz,
                                    dst_sz,
                                ),
                            )
                        }),
                    );
                }
                let ok = #[allow(non_exhaustive_omitted_patterns)]
                match (&src, &dst) {
                    (TypeInfo::Pointer(_), TypeInfo::Pointer(_))
                    | (TypeInfo::Pointer(_), TypeInfo::Basic(BasicType::Integer))
                    | (TypeInfo::Basic(BasicType::Integer), TypeInfo::Pointer(_))
                    | (
                        TypeInfo::Basic(BasicType::Integer),
                        TypeInfo::Basic(BasicType::Integer),
                    ) => true,
                    _ => false,
                };
                if !ok {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "unsafe cast is only supported for pointer/integer 32-bit values (got {0} -> {1})",
                                    type_desc(&src),
                                    type_desc(&dst),
                                ),
                            )
                        }),
                    );
                }
                Ok(dst)
            }
            Expr::SetLit(items) => {
                let mut elem_ty: Option<TypeInfo> = None;
                for item in items {
                    match item {
                        SetItem::Single(expr) => {
                            let t = type_of_expr_scoped(
                                env,
                                vars,
                                visible_routines,
                                expr,
                            )?;
                            if !is_ordinal_type(&t) {
                                return Err("set literal items must be ordinal".into());
                            }
                            if let Some(prev) = &elem_ty {
                                if !same_type(prev, &t) {
                                    return Err(
                                        "set literal items must have the same type".into(),
                                    );
                                }
                            } else {
                                elem_ty = Some(t);
                            }
                        }
                        SetItem::Range(lo, hi) => {
                            let lt = type_of_expr_scoped(
                                env,
                                vars,
                                visible_routines,
                                lo,
                            )?;
                            let ht = type_of_expr_scoped(
                                env,
                                vars,
                                visible_routines,
                                hi,
                            )?;
                            if !is_ordinal_type(&lt) || !same_type(&lt, &ht) {
                                return Err(
                                    "set range bounds must share the same ordinal type".into(),
                                );
                            }
                            if let Some(prev) = &elem_ty {
                                if !same_type(prev, &lt) {
                                    return Err(
                                        "set literal items must have the same type".into(),
                                    );
                                }
                            } else {
                                elem_ty = Some(lt);
                            }
                        }
                    }
                }
                let elem_ty = elem_ty.unwrap_or(TypeInfo::Basic(BasicType::Integer));
                let (low, high) = ordinal_bounds(&elem_ty)?;
                if low < 0 || high > 31 {
                    return Err("set base type must fit within 0..31".into());
                }
                Ok(
                    TypeInfo::Set(SetInfo {
                        elem_ty: Box::new(elem_ty),
                        low,
                    }),
                )
            }
            Expr::Var(n) => {
                if let Some(t) = vars.get(n) {
                    Ok(t.clone())
                } else if let Some(c) = env.consts.get(n) {
                    Ok(const_type_from_val(c.clone(), env)?)
                } else {
                    Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("unknown identifier: {0}", n),
                            )
                        }),
                    )
                }
            }
            Expr::Nil => Ok(TypeInfo::Nil),
            Expr::Call(name, args) => {
                if let Some(t) = builtin_expr_type(
                    env,
                    vars,
                    visible_routines,
                    name,
                    args,
                )? {
                    return Ok(t);
                }
                let key = visible_routines
                    .get(name)
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("unknown routine in scope: {0}", name),
                        )
                    }))?;
                let sig = env
                    .routines
                    .get(key)
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "internal: missing routine signature for {0}",
                                key,
                            ),
                        )
                    }))?;
                let ret = sig
                    .ret
                    .clone()
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("procedure used as expression: {0}", name),
                        )
                    }))?;
                check_call_args_scoped(env, vars, visible_routines, name, sig, args)?;
                Ok(ret)
            }
            Expr::Deref(base) => {
                match type_of_expr_scoped(env, vars, visible_routines, base)? {
                    TypeInfo::Pointer(target) => {
                        lookup_type(env, &target)
                            .ok_or_else(|| ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!("unknown pointed type: {0}", target),
                                )
                            }))
                    }
                    _ => Err("deref on non-pointer".into()),
                }
            }
            Expr::Field(base, fname) => {
                match type_of_expr_scoped(env, vars, visible_routines, base)? {
                    TypeInfo::Record(r) => {
                        r.fields
                            .get(fname)
                            .map(|fi| fi.ty.clone())
                            .ok_or_else(|| ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!("unknown field {0}", fname),
                                )
                            }))
                    }
                    _ => Err("field access on non-record".into()),
                }
            }
            Expr::Index(base, idx) => {
                let bt = type_of_expr_scoped(env, vars, visible_routines, base)?;
                let it = type_of_expr_scoped(env, vars, visible_routines, idx)?;
                expect_array_index_type(&it, "array index")?;
                match bt {
                    TypeInfo::Array(a) => Ok((*a.elem_ty).clone()),
                    _ => Err("index access on non-array".into()),
                }
            }
            Expr::Unary(op, inner) => {
                let it = type_of_expr_scoped(env, vars, visible_routines, inner)?;
                match op {
                    UnOp::Neg => {
                        if is_real_type(&it) {
                            Ok(it)
                        } else {
                            expect_integer_like(&it, "NEG")?;
                            Ok(TypeInfo::Basic(BasicType::Integer))
                        }
                    }
                    UnOp::Not => {
                        expect_basic(&it, BasicType::Boolean, "NOT")?;
                        Ok(TypeInfo::Basic(BasicType::Boolean))
                    }
                }
            }
            Expr::Binary(a, op, b) => {
                let ta = type_of_expr_scoped(env, vars, visible_routines, a)?;
                let tb = type_of_expr_scoped(env, vars, visible_routines, b)?;
                use BinOp::*;
                match op {
                    Add | Sub | Mul => {
                        if is_set_type(&ta) || is_set_type(&tb) {
                            if same_type(&ta, &tb) {
                                Ok(ta)
                            } else {
                                Err("set operands must have the same type".into())
                            }
                        } else if is_real_type(&ta) || is_real_type(&tb) {
                            if is_numeric_type(&ta) && is_numeric_type(&tb) {
                                Ok(TypeInfo::Basic(BasicType::Real))
                            } else {
                                Err("arithmetic operands must be numeric".into())
                            }
                        } else {
                            expect_integer_like(&ta, "arithmetic lhs")?;
                            expect_integer_like(&tb, "arithmetic rhs")?;
                            Ok(TypeInfo::Basic(BasicType::Integer))
                        }
                    }
                    RealDiv => {
                        if is_numeric_type(&ta) && is_numeric_type(&tb) {
                            Ok(TypeInfo::Basic(BasicType::Real))
                        } else {
                            Err("real division operands must be numeric".into())
                        }
                    }
                    Div | Mod => {
                        expect_integer_like(&ta, "integer arithmetic lhs")?;
                        expect_integer_like(&tb, "integer arithmetic rhs")?;
                        Ok(TypeInfo::Basic(BasicType::Integer))
                    }
                    And | Or | Xor => {
                        if is_set_type(&ta) || is_set_type(&tb) {
                            if same_type(&ta, &tb) {
                                Ok(ta)
                            } else {
                                Err("set operands must have the same type".into())
                            }
                        } else {
                            expect_basic(&ta, BasicType::Boolean, "boolean lhs")?;
                            expect_basic(&tb, BasicType::Boolean, "boolean rhs")?;
                            Ok(TypeInfo::Basic(BasicType::Boolean))
                        }
                    }
                    In => {
                        let set = match &tb {
                            TypeInfo::Set(s) => s,
                            _ => {
                                return Err("right-hand side of 'in' must be a set".into());
                            }
                        };
                        if ordinal_compatible(&ta, &set.elem_ty) {
                            Ok(TypeInfo::Basic(BasicType::Boolean))
                        } else {
                            Err("set membership type mismatch".into())
                        }
                    }
                    Eq | Ne => {
                        if equality_compatible(&ta, &tb) {
                            Ok(TypeInfo::Basic(BasicType::Boolean))
                        } else {
                            Err("type mismatch in equality comparison".into())
                        }
                    }
                    Lt | Le | Gt | Ge => {
                        if order_compatible(&ta, &tb) {
                            Ok(TypeInfo::Basic(BasicType::Boolean))
                        } else {
                            Err("type mismatch in order comparison".into())
                        }
                    }
                }
            }
        }
    }
    fn check_call_args_scoped(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        name: &str,
        sig: &RoutineSig,
        args: &[Expr],
    ) -> Result<(), String> {
        if sig.params.len() != args.len() {
            return Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!(
                            "argument count mismatch for {2}: expected {0}, got {1}",
                            sig.params.len(),
                            args.len(),
                            name,
                        ),
                    )
                }),
            );
        }
        for (idx, (p, a)) in sig.params.iter().zip(args).enumerate() {
            let arg_no = idx + 1;
            if (p.by_ref || p.conformant.is_some()) && expr_to_lvalue(a).is_none() {
                return Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "argument #{0} in call to {1} must be lvalue for var parameter",
                                arg_no,
                                name,
                            ),
                        )
                    }),
                );
            }
            let at = type_of_expr_scoped(env, vars, visible_routines, a)?;
            if let Some(conf) = &p.conformant {
                let Some((actual_dims, actual_elem)) = array_rank_and_elem(&at) else {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "argument #{1} type mismatch in call to {2}: expected conformant array, got {0}",
                                    type_desc(&at),
                                    arg_no,
                                    name,
                                ),
                            )
                        }),
                    );
                };
                let declared_elem = tyref_to_info(env, &conf.elem_ty)?;
                if actual_dims != conf.dims.len()
                    || !same_type(&declared_elem, actual_elem)
                {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "argument #{0} type mismatch in call to {1}: expected conformant array",
                                    arg_no,
                                    name,
                                ),
                            )
                        }),
                    );
                }
                for dim in &conf.dims {
                    let _ = tyref_to_info(env, &dim.index_ty)?;
                }
                continue;
            }
            if !assignment_compatible(&p.ty, &at) {
                return Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "argument #{2} type mismatch in call to {3}: expected {0}, got {1}",
                                type_desc(&p.ty),
                                type_desc(&at),
                                arg_no,
                                name,
                            ),
                        )
                    }),
                );
            }
        }
        Ok(())
    }
    fn sizeof_type(t: &TypeInfo) -> Result<u32, String> {
        match t {
            TypeInfo::Basic(_)
            | TypeInfo::Enum(_)
            | TypeInfo::Subrange(_)
            | TypeInfo::Set(_)
            | TypeInfo::Pointer(_)
            | TypeInfo::Nil => Ok(4),
            TypeInfo::Record(r) => Ok(r.size_bytes),
            TypeInfo::Sum(s) => Ok(s.size_bytes),
            TypeInfo::Array(a) => Ok(a.size_bytes),
        }
    }
    pub fn eval_const(env: &Env, e: &ConstExpr) -> Result<ConstVal, String> {
        match e {
            ConstExpr::Int(i) => Ok(ConstVal::I32(*i)),
            ConstExpr::Bool(b) => Ok(ConstVal::Bool(*b)),
            ConstExpr::Char(u) => Ok(ConstVal::U32(*u)),
            ConstExpr::Real(bits) => Ok(ConstVal::Real(*bits)),
            ConstExpr::Const(n) => {
                env.consts
                    .get(n)
                    .cloned()
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("unknown const: {0}", n))
                    }))
            }
            ConstExpr::Call(name, args) => {
                let u = name.to_ascii_lowercase();
                match u.as_str() {
                    "ord" => {
                        if args.len() != 1 {
                            return Err("Ord requires 1 argument in const expr".into());
                        }
                        Ok(
                            ConstVal::I32(
                                ordinal_const_value(&eval_const(env, &args[0])?)?,
                            ),
                        )
                    }
                    "chr" => {
                        if args.len() != 1 {
                            return Err("Chr requires 1 argument in const expr".into());
                        }
                        let i = to_i32(eval_const(env, &args[0])?)?;
                        if i < 0 {
                            return Err("Chr const argument must be non-negative".into());
                        }
                        Ok(ConstVal::U32(i as u32))
                    }
                    _ => {
                        Err(
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!("unsupported const function: {0}", name),
                                )
                            }),
                        )
                    }
                }
            }
            ConstExpr::Unary(UnOp::Neg, inner) => {
                match eval_const(env, inner)? {
                    ConstVal::I32(i) => Ok(ConstVal::I32(-i)),
                    ConstVal::Real(bits) => {
                        Ok(ConstVal::Real((-(f32::from_bits(bits))).to_bits()))
                    }
                    _ => Err("NEG on unsupported const".into()),
                }
            }
            ConstExpr::Unary(UnOp::Not, inner) => {
                match eval_const(env, inner)? {
                    ConstVal::Bool(b) => Ok(ConstVal::Bool(!b)),
                    ConstVal::I32(i) => Ok(ConstVal::Bool(i == 0)),
                    _ => Err("NOT on unsupported const".into()),
                }
            }
            ConstExpr::Binary(a, op, b) => {
                let av = eval_const(env, a)?;
                let bv = eval_const(env, b)?;
                use BinOp::*;
                match op {
                    Add | Sub | Mul | Div | Mod | And | Or | Xor => {
                        let ai = to_i32(av)?;
                        let bi = to_i32(bv)?;
                        if #[allow(non_exhaustive_omitted_patterns)]
                        match op {
                            Div | Mod => true,
                            _ => false,
                        } && bi == 0
                        {
                            return Err("division by zero in const expr".into());
                        }
                        Ok(
                            ConstVal::I32(
                                match op {
                                    Add => ai + bi,
                                    Sub => ai - bi,
                                    Mul => ai * bi,
                                    Div => ai / bi,
                                    Mod => ai % bi,
                                    And => ai & bi,
                                    Or => ai | bi,
                                    Xor => ai ^ bi,
                                    _ => {
                                        ::core::panicking::panic(
                                            "internal error: entered unreachable code",
                                        )
                                    }
                                },
                            ),
                        )
                    }
                    RealDiv => {
                        let af = to_f32(av)?;
                        let bf = to_f32(bv)?;
                        Ok(ConstVal::Real((af / bf).to_bits()))
                    }
                    Eq | Ne | Lt | Le | Gt | Ge => {
                        if #[allow(non_exhaustive_omitted_patterns)]
                        match av {
                            ConstVal::Real(_) => true,
                            _ => false,
                        } || #[allow(non_exhaustive_omitted_patterns)]
                            match bv {
                                ConstVal::Real(_) => true,
                                _ => false,
                            }
                        {
                            let af = to_f32(av)?;
                            let bf = to_f32(bv)?;
                            let r = match op {
                                Eq => af == bf,
                                Ne => af != bf,
                                Lt => af < bf,
                                Le => af <= bf,
                                Gt => af > bf,
                                Ge => af >= bf,
                                _ => {
                                    ::core::panicking::panic(
                                        "internal error: entered unreachable code",
                                    )
                                }
                            };
                            Ok(ConstVal::Bool(r))
                        } else {
                            let ai = ordinal_const_value(&av)?;
                            let bi = ordinal_const_value(&bv)?;
                            let r = match op {
                                Eq => ai == bi,
                                Ne => ai != bi,
                                Lt => ai < bi,
                                Le => ai <= bi,
                                Gt => ai > bi,
                                Ge => ai >= bi,
                                _ => {
                                    ::core::panicking::panic(
                                        "internal error: entered unreachable code",
                                    )
                                }
                            };
                            Ok(ConstVal::Bool(r))
                        }
                    }
                    In => Err("'in' is not supported in const expr".into()),
                }
            }
        }
    }
    fn to_i32(v: ConstVal) -> Result<i32, String> {
        match v {
            ConstVal::I32(i) => Ok(i),
            ConstVal::Bool(b) => Ok(if b { 1 } else { 0 }),
            ConstVal::U32(u) => {
                Ok(i32::try_from(u).map_err(|_| "u32 too large for i32".to_string())?)
            }
            ConstVal::EnumVal { ordinal, .. } => Ok(ordinal),
            ConstVal::Real(_) => Err("real const is not integer".into()),
        }
    }
    fn to_f32(v: ConstVal) -> Result<f32, String> {
        match v {
            ConstVal::Real(bits) => Ok(f32::from_bits(bits)),
            ConstVal::I32(i) => Ok(i as f32),
            _ => Err("const is not numeric".into()),
        }
    }
    fn ordinal_const_value(v: &ConstVal) -> Result<i32, String> {
        match v {
            ConstVal::I32(i) => Ok(*i),
            ConstVal::Bool(b) => Ok(if *b { 1 } else { 0 }),
            ConstVal::U32(u) => Ok(*u as i32),
            ConstVal::EnumVal { ordinal, .. } => Ok(*ordinal),
            _ => Err("const is not ordinal".into()),
        }
    }
    #[allow(dead_code)]
    pub fn resolve_lvalue_addr(
        env: &Env,
        lv: &LValue,
    ) -> Result<(String, u32, TypeInfo), String> {
        let ty = resolve_lvalue_type_scoped(env, &env.vars, &HashMap::new(), lv)?;
        Ok((lv.base.clone(), 0, ty))
    }
    #[allow(dead_code)]
    pub fn resolve_lvalue_addr_with_vars(
        vars: &HashMap<String, TypeInfo>,
        lv: &LValue,
    ) -> Result<(String, u32, TypeInfo), String> {
        let t = vars
            .get(&lv.base)
            .cloned()
            .ok_or_else(|| ::alloc::__export::must_use({
                ::alloc::fmt::format(format_args!("unknown var: {0}", lv.base))
            }))?;
        if lv.sels.is_empty() {
            return Ok((lv.base.clone(), 0, t));
        }
        Err(
            "resolve_lvalue_addr_with_vars does not support selectors; use scoped checker"
                .into(),
        )
    }
    fn resolve_lvalue_type_scoped(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        lv: &LValue,
    ) -> Result<TypeInfo, String> {
        let mut t = vars
            .get(&lv.base)
            .cloned()
            .ok_or_else(|| ::alloc::__export::must_use({
                ::alloc::fmt::format(format_args!("unknown var: {0}", lv.base))
            }))?;
        for sel in &lv.sels {
            match sel {
                Selector::Field(f) => {
                    match t {
                        TypeInfo::Record(ref r) => {
                            let fi = r
                                .fields
                                .get(f)
                                .ok_or_else(|| ::alloc::__export::must_use({
                                    ::alloc::fmt::format(format_args!("unknown field: {0}", f))
                                }))?;
                            t = fi.ty.clone();
                        }
                        _ => return Err("field on non-record lvalue".into()),
                    }
                }
                Selector::Index(idxs) => {
                    for ix in idxs {
                        let it = type_of_expr_scoped(env, vars, visible_routines, ix)?;
                        expect_array_index_type(&it, "array index")?;
                        match t {
                            TypeInfo::Array(ref a) => t = (*a.elem_ty).clone(),
                            _ => return Err("index on non-array lvalue".into()),
                        }
                    }
                }
                Selector::Deref => {
                    match t {
                        TypeInfo::Pointer(ref target) => {
                            t = lookup_type(env, target)
                                .ok_or_else(|| ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("unknown pointed type: {0}", target),
                                    )
                                }))?;
                        }
                        _ => return Err("deref on non-pointer lvalue".into()),
                    }
                }
            }
        }
        Ok(t)
    }
    pub fn expr_to_lvalue(e: &Expr) -> Option<LValue> {
        match e {
            Expr::Var(n) => {
                Some(LValue {
                    base: n.clone(),
                    sels: ::alloc::vec::Vec::new(),
                })
            }
            Expr::Deref(_) | Expr::Field(_, _) | Expr::Index(_, _) => {
                let mut sels = ::alloc::vec::Vec::new();
                let mut cur = e;
                loop {
                    match cur {
                        Expr::Deref(inner) => {
                            sels.push(Selector::Deref);
                            cur = inner;
                        }
                        Expr::Field(inner, f) => {
                            sels.push(Selector::Field(f.clone()));
                            cur = inner;
                        }
                        Expr::Index(inner, ix) => {
                            sels.push(
                                Selector::Index(
                                    <[_]>::into_vec(::alloc::boxed::box_new([(**ix).clone()])),
                                ),
                            );
                            cur = inner;
                        }
                        _ => break,
                    }
                }
                if let Expr::Var(base) = cur {
                    sels.reverse();
                    Some(LValue { base: base.clone(), sels })
                } else {
                    None
                }
            }
            _ => None,
        }
    }
    fn sum_arm_by_name<'a>(sum: &'a SumInfo, name: &str) -> Option<&'a SumArmInfo> {
        sum.arms.iter().find(|a| a.name.eq_ignore_ascii_case(name))
    }
    fn check_expr_matches_type_scoped(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        e: &Expr,
        expected: &TypeInfo,
    ) -> Result<(), String> {
        match e {
            Expr::OptionNone => {
                match expected {
                    TypeInfo::Sum(sum) => {
                        let arm = sum_arm_by_name(sum, "none")
                            .ok_or("NONE used with non-OPTION compatible sum type")?;
                        if !arm.fields.is_empty() {
                            return Err("NONE arm must have no fields".into());
                        }
                        Ok(())
                    }
                    _ => Err("NONE requires OPTION target type".into()),
                }
            }
            Expr::OptionSome(inner) => {
                match expected {
                    TypeInfo::Sum(sum) => {
                        let arm = sum_arm_by_name(sum, "some")
                            .ok_or("SOME used with non-OPTION compatible sum type")?;
                        if arm.fields.len() != 1 {
                            return Err("SOME arm must have exactly 1 field".into());
                        }
                        check_expr_matches_type_scoped(
                            env,
                            vars,
                            visible_routines,
                            inner,
                            &arm.fields[0].ty,
                        )
                    }
                    _ => Err("SOME requires OPTION target type".into()),
                }
            }
            Expr::Ctor(name, named_args) => {
                match expected {
                    TypeInfo::Record(rec) => {
                        if !ctor_name_matches_record_type(env, name, rec) {
                            return Err(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "constructor {0} does not match target record type",
                                            name,
                                        ),
                                    )
                                }),
                            );
                        }
                        if rec.fields.len() != named_args.len() {
                            return Err(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "constructor {2} argument count mismatch: expected {0}, got {1}",
                                            rec.fields.len(),
                                            named_args.len(),
                                            name,
                                        ),
                                    )
                                }),
                            );
                        }
                        for (fname, finfo) in &rec.fields {
                            let (_, expr) = named_args
                                .iter()
                                .find(|(n, _)| n.eq_ignore_ascii_case(fname))
                                .ok_or_else(|| ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "constructor {0} missing field {1}",
                                            name,
                                            fname,
                                        ),
                                    )
                                }))?;
                            check_expr_matches_type_scoped(
                                env,
                                vars,
                                visible_routines,
                                expr,
                                &finfo.ty,
                            )?;
                        }
                        for (n, _) in named_args {
                            if !rec.fields.keys().any(|f| f.eq_ignore_ascii_case(n)) {
                                return Err(
                                    ::alloc::__export::must_use({
                                        ::alloc::fmt::format(
                                            format_args!("constructor {0} has no field {1}", name, n),
                                        )
                                    }),
                                );
                            }
                        }
                        Ok(())
                    }
                    TypeInfo::Sum(sum) => {
                        let arm = sum_arm_by_name(sum, name)
                            .ok_or_else(|| ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!("unknown constructor for sum type: {0}", name),
                                )
                            }))?;
                        if arm.fields.len() != named_args.len() {
                            return Err(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "constructor {2} argument count mismatch: expected {0}, got {1}",
                                            arm.fields.len(),
                                            named_args.len(),
                                            name,
                                        ),
                                    )
                                }),
                            );
                        }
                        for f in &arm.fields {
                            let (_, expr) = named_args
                                .iter()
                                .find(|(n, _)| n.eq_ignore_ascii_case(&f.name))
                                .ok_or_else(|| ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "constructor {1} missing field {0}",
                                            f.name,
                                            name,
                                        ),
                                    )
                                }))?;
                            check_expr_matches_type_scoped(
                                env,
                                vars,
                                visible_routines,
                                expr,
                                &f.ty,
                            )?;
                        }
                        for (n, _) in named_args {
                            if !arm.fields.iter().any(|f| f.name.eq_ignore_ascii_case(n))
                            {
                                return Err(
                                    ::alloc::__export::must_use({
                                        ::alloc::fmt::format(
                                            format_args!("constructor {0} has no field {1}", name, n),
                                        )
                                    }),
                                );
                            }
                        }
                        Ok(())
                    }
                    _ => {
                        Err(
                            "constructor expression requires record/sum target type"
                                .into(),
                        )
                    }
                }
            }
            Expr::ArrayLit(elems) => {
                match expected {
                    TypeInfo::Array(arr) => {
                        if elems.len() != arr.len as usize {
                            return Err(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "array literal length mismatch: expected {0}, got {1}",
                                            arr.len,
                                            elems.len(),
                                        ),
                                    )
                                }),
                            );
                        }
                        for e in elems {
                            check_expr_matches_type_scoped(
                                env,
                                vars,
                                visible_routines,
                                e,
                                &arr.elem_ty,
                            )?;
                        }
                        Ok(())
                    }
                    _ => Err("array literal requires array target type".into()),
                }
            }
            Expr::RecordUpdate(base, updates) => {
                match expected {
                    TypeInfo::Record(rec) => {
                        let bt = type_of_expr_scoped(env, vars, visible_routines, base)?;
                        if !same_type(&bt, expected) {
                            return Err(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "record update base type mismatch: expected {0}, got {1}",
                                            type_desc(expected),
                                            type_desc(&bt),
                                        ),
                                    )
                                }),
                            );
                        }
                        if updates.is_empty() {
                            return Err(
                                "record update requires at least one field assignment"
                                    .into(),
                            );
                        }
                        let mut seen = HashSet::new();
                        for (fname, expr) in updates {
                            let key = fname.to_ascii_lowercase();
                            if !seen.insert(key) {
                                return Err("duplicate record update field".into());
                            }
                            let (_, finfo) = rec
                                .fields
                                .iter()
                                .find(|(n, _)| n.eq_ignore_ascii_case(fname))
                                .ok_or_else(|| ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!("record update has no field {0}", fname),
                                    )
                                }))?;
                            check_expr_matches_type_scoped(
                                env,
                                vars,
                                visible_routines,
                                expr,
                                &finfo.ty,
                            )?;
                        }
                        Ok(())
                    }
                    _ => Err("record update requires record target type".into()),
                }
            }
            Expr::ArrayUpdate(base, updates) => {
                match expected {
                    TypeInfo::Array(arr) => {
                        let bt = type_of_expr_scoped(env, vars, visible_routines, base)?;
                        if !same_type(&bt, expected) {
                            return Err(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "array update base type mismatch: expected {0}, got {1}",
                                            type_desc(expected),
                                            type_desc(&bt),
                                        ),
                                    )
                                }),
                            );
                        }
                        if updates.is_empty() {
                            return Err(
                                "array update requires at least one element assignment"
                                    .into(),
                            );
                        }
                        for (idx, val) in updates {
                            let it = type_of_expr_scoped(
                                env,
                                vars,
                                visible_routines,
                                idx,
                            )?;
                            expect_array_index_type(&it, "array update index")?;
                            check_expr_matches_type_scoped(
                                env,
                                vars,
                                visible_routines,
                                val,
                                &arr.elem_ty,
                            )?;
                        }
                        Ok(())
                    }
                    _ => Err("array update requires array target type".into()),
                }
            }
            Expr::Call(
                name,
                args,
            ) if #[allow(non_exhaustive_omitted_patterns)]
            match expected {
                TypeInfo::Sum(_) => true,
                _ => false,
            } && args.is_empty() => {
                match expected {
                    TypeInfo::Sum(sum) => {
                        let arm = sum_arm_by_name(sum, name)
                            .ok_or_else(|| {
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "unknown zero-field constructor for sum type: {0}",
                                            name,
                                        ),
                                    )
                                })
                            })?;
                        if !arm.fields.is_empty() {
                            return Err(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "constructor {1} requires named fields ({0} field(s))",
                                            arm.fields.len(),
                                            name,
                                        ),
                                    )
                                }),
                            );
                        }
                        Ok(())
                    }
                    _ => {
                        ::core::panicking::panic(
                            "internal error: entered unreachable code",
                        )
                    }
                }
            }
            Expr::Cond { arms, else_block } => {
                for arm in arms {
                    let ct = type_of_expr_scoped(
                        env,
                        vars,
                        visible_routines,
                        &arm.cond,
                    )?;
                    expect_basic(&ct, BasicType::Boolean, "cond arm condition")?;
                    for st in &arm.block.stmts {
                        check_stmt_with_vars(env, vars, visible_routines, st)?;
                    }
                    check_expr_matches_type_scoped(
                        env,
                        vars,
                        visible_routines,
                        &arm.block.value,
                        expected,
                    )?;
                }
                for st in &else_block.stmts {
                    check_stmt_with_vars(env, vars, visible_routines, st)?;
                }
                check_expr_matches_type_scoped(
                    env,
                    vars,
                    visible_routines,
                    &else_block.value,
                    expected,
                )
            }
            Expr::Nil => {
                match expected {
                    TypeInfo::Pointer(_) => Ok(()),
                    _ => {
                        Err(
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!(
                                        "type mismatch: expected {0}, got nil",
                                        type_desc(expected),
                                    ),
                                )
                            }),
                        )
                    }
                }
            }
            _ => {
                let actual = type_of_expr_scoped(env, vars, visible_routines, e)?;
                if assignment_compatible(expected, &actual)
                    || same_type(&actual, expected)
                {
                    Ok(())
                } else {
                    Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "type mismatch: expected {0}, got {1}",
                                    type_desc(expected),
                                    type_desc(&actual),
                                ),
                            )
                        }),
                    )
                }
            }
        }
    }
    pub fn check_program(env: &Env, prog: &Program) -> Result<(), String> {
        check_block(env, &prog.block, &HashMap::new(), &HashMap::new(), "program")
    }
    fn check_block(
        env: &Env,
        block: &Block,
        outer_vars: &HashMap<String, TypeInfo>,
        outer_routines: &HashMap<String, String>,
        scope: &str,
    ) -> Result<(), String> {
        let mut vars = outer_vars.clone();
        for v in &block.vars {
            if vars.contains_key(&v.name) {
                return Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "name conflict in {1}: local variable \'{0}\' shadows an outer name (shadowing is not allowed)",
                                v.name,
                                scope,
                            ),
                        )
                    }),
                );
            }
            vars.insert(v.name.clone(), tyref_to_info(env, &v.ty)?);
        }
        let mut visible_routines = outer_routines.clone();
        let mut local_names = HashSet::new();
        for r in &block.routines {
            let name = match r {
                RoutineDecl::Procedure(p) => &p.name,
                RoutineDecl::Function(f) => &f.name,
            };
            if !local_names.insert(name.clone()) {
                return Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("routine redefined in {0}: {1}", scope, name),
                        )
                    }),
                );
            }
            visible_routines
                .insert(
                    name.clone(),
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("{0}::{1}", scope, name))
                    }),
                );
        }
        check_stmt_with_vars(env, &vars, &visible_routines, &block.body)?;
        check_imut_block(env, block, &vars, &visible_routines)?;
        for r in &block.routines {
            match r {
                RoutineDecl::Procedure(p) => {
                    let mut rvars = vars.clone();
                    for prm in &p.params {
                        if rvars.contains_key(&prm.name) {
                            return Err(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "name conflict in procedure {0}: parameter \'{1}\' duplicates or shadows an existing name",
                                            p.name,
                                            prm.name,
                                        ),
                                    )
                                }),
                            );
                        }
                        let pty = if let Some(c) = &prm.conformant {
                            for dim in &c.dims {
                                if rvars.contains_key(&dim.low_name)
                                    || rvars.contains_key(&dim.high_name)
                                {
                                    return Err(
                                        ::alloc::__export::must_use({
                                            ::alloc::fmt::format(
                                                format_args!(
                                                    "name conflict in procedure {0}: conformant bounds conflict with an existing name",
                                                    p.name,
                                                ),
                                            )
                                        }),
                                    );
                                }
                                let bty = tyref_to_info(env, &dim.index_ty)?;
                                rvars.insert(dim.low_name.clone(), bty.clone());
                                rvars.insert(dim.high_name.clone(), bty);
                            }
                            conformant_param_type(env, c)?
                        } else {
                            tyref_to_info(env, &prm.ty)?
                        };
                        rvars.insert(prm.name.clone(), pty);
                    }
                    check_block(
                        env,
                        &p.block,
                        &rvars,
                        &visible_routines,
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{1}::{0}", p.name, scope))
                        }),
                    )?;
                }
                RoutineDecl::Function(f) => {
                    let mut rvars = vars.clone();
                    for prm in &f.params {
                        if rvars.contains_key(&prm.name) {
                            return Err(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "name conflict in function {0}: parameter \'{1}\' duplicates or shadows an existing name",
                                            f.name,
                                            prm.name,
                                        ),
                                    )
                                }),
                            );
                        }
                        let pty = if let Some(c) = &prm.conformant {
                            for dim in &c.dims {
                                if rvars.contains_key(&dim.low_name)
                                    || rvars.contains_key(&dim.high_name)
                                {
                                    return Err(
                                        ::alloc::__export::must_use({
                                            ::alloc::fmt::format(
                                                format_args!(
                                                    "name conflict in function {0}: conformant bounds conflict with an existing name",
                                                    f.name,
                                                ),
                                            )
                                        }),
                                    );
                                }
                                let bty = tyref_to_info(env, &dim.index_ty)?;
                                rvars.insert(dim.low_name.clone(), bty.clone());
                                rvars.insert(dim.high_name.clone(), bty);
                            }
                            conformant_param_type(env, c)?
                        } else {
                            tyref_to_info(env, &prm.ty)?
                        };
                        rvars.insert(prm.name.clone(), pty);
                    }
                    rvars.insert(f.name.clone(), tyref_to_info(env, &f.ret_ty)?);
                    check_block(
                        env,
                        &f.block,
                        &rvars,
                        &visible_routines,
                        &::alloc::__export::must_use({
                            ::alloc::fmt::format(format_args!("{1}::{0}", f.name, scope))
                        }),
                    )?;
                }
            }
        }
        Ok(())
    }
    fn check_imut_block(
        env: &Env,
        block: &Block,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
    ) -> Result<(), String> {
        let local_imuts: HashSet<String> = block
            .vars
            .iter()
            .filter(|v| v.immutable)
            .map(|v| v.name.clone())
            .collect();
        let mut initialized = HashSet::new();
        check_imut_stmt(
            env,
            vars,
            visible_routines,
            &block.body,
            &local_imuts,
            &mut initialized,
        )
    }
    fn check_imut_stmt(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        stmt: &Stmt,
        local_imuts: &HashSet<String>,
        initialized: &mut HashSet<String>,
    ) -> Result<(), String> {
        match stmt {
            Stmt::Empty | Stmt::ReadLn => Ok(()),
            Stmt::Compound(stmts) => {
                for s in stmts {
                    check_imut_stmt(
                        env,
                        vars,
                        visible_routines,
                        s,
                        local_imuts,
                        initialized,
                    )?;
                }
                Ok(())
            }
            Stmt::Assign(lv, rhs) => {
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    rhs,
                    local_imuts,
                    initialized,
                )?;
                if local_imuts.contains(&lv.base) {
                    if !lv.sels.is_empty() {
                        return Err(
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!(
                                        "imut variable cannot be mutated via field/index: {0}",
                                        lv.base,
                                    ),
                                )
                            }),
                        );
                    }
                    if initialized.contains(&lv.base) {
                        return Err(
                            ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!(
                                        "imut variable cannot be reassigned: {0}",
                                        lv.base,
                                    ),
                                )
                            }),
                        );
                    }
                    initialized.insert(lv.base.clone());
                }
                Ok(())
            }
            Stmt::Read(args) => {
                for e in args {
                    if let Some(lv) = expr_to_lvalue(e) {
                        if local_imuts.contains(&lv.base) {
                            return Err(
                                ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "imut variable cannot be assigned by Read: {0}",
                                            lv.base,
                                        ),
                                    )
                                }),
                            );
                        }
                    }
                    check_imut_reads_in_expr(
                        env,
                        vars,
                        visible_routines,
                        e,
                        local_imuts,
                        initialized,
                    )?;
                }
                Ok(())
            }
            Stmt::For { var, init, limit, body, .. } => {
                if local_imuts.contains(var) {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "imut variable cannot be used as for loop variable: {0}",
                                    var,
                                ),
                            )
                        }),
                    );
                }
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    init,
                    local_imuts,
                    initialized,
                )?;
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    limit,
                    local_imuts,
                    initialized,
                )?;
                check_imut_stmt(
                    env,
                    vars,
                    visible_routines,
                    body,
                    local_imuts,
                    initialized,
                )
            }
            Stmt::If(cond, then_s, else_s) => {
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    cond,
                    local_imuts,
                    initialized,
                )?;
                check_imut_stmt(
                    env,
                    vars,
                    visible_routines,
                    then_s,
                    local_imuts,
                    initialized,
                )?;
                if let Some(es) = else_s {
                    check_imut_stmt(
                        env,
                        vars,
                        visible_routines,
                        es,
                        local_imuts,
                        initialized,
                    )?;
                }
                Ok(())
            }
            Stmt::With(_, body) => {
                check_imut_stmt(
                    env,
                    vars,
                    visible_routines,
                    body,
                    local_imuts,
                    initialized,
                )
            }
            Stmt::While(cond, body) => {
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    cond,
                    local_imuts,
                    initialized,
                )?;
                check_imut_stmt(
                    env,
                    vars,
                    visible_routines,
                    body,
                    local_imuts,
                    initialized,
                )
            }
            Stmt::Repeat(stmts, cond) => {
                for s in stmts {
                    check_imut_stmt(
                        env,
                        vars,
                        visible_routines,
                        s,
                        local_imuts,
                        initialized,
                    )?;
                }
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    cond,
                    local_imuts,
                    initialized,
                )
            }
            Stmt::Case { expr, arms, else_stmt } => {
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    expr,
                    local_imuts,
                    initialized,
                )?;
                for (_, s) in arms {
                    check_imut_stmt(
                        env,
                        vars,
                        visible_routines,
                        s,
                        local_imuts,
                        initialized,
                    )?;
                }
                if let Some(es) = else_stmt {
                    check_imut_stmt(
                        env,
                        vars,
                        visible_routines,
                        es,
                        local_imuts,
                        initialized,
                    )?;
                }
                Ok(())
            }
            Stmt::SumCase { expr, arms, else_stmt } => {
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    expr,
                    local_imuts,
                    initialized,
                )?;
                for arm in arms {
                    check_imut_stmt(
                        env,
                        vars,
                        visible_routines,
                        &arm.body,
                        local_imuts,
                        initialized,
                    )?;
                }
                if let Some(es) = else_stmt {
                    check_imut_stmt(
                        env,
                        vars,
                        visible_routines,
                        es,
                        local_imuts,
                        initialized,
                    )?;
                }
                Ok(())
            }
            Stmt::ProcCall(name, args) => {
                let key = visible_routines.get(name);
                for (idx, arg) in args.iter().enumerate() {
                    check_imut_reads_in_expr(
                        env,
                        vars,
                        visible_routines,
                        arg,
                        local_imuts,
                        initialized,
                    )?;
                    if let Some(key) = key {
                        if let Some(sig) = env.routines.get(key) {
                            if sig.params.get(idx).map(|p| p.by_ref).unwrap_or(false) {
                                if let Some(lv) = expr_to_lvalue(arg) {
                                    if local_imuts.contains(&lv.base) {
                                        return Err(
                                            ::alloc::__export::must_use({
                                                ::alloc::fmt::format(
                                                    format_args!(
                                                        "imut variable cannot be passed to var parameter: {0}",
                                                        lv.base,
                                                    ),
                                                )
                                            }),
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
                Ok(())
            }
            Stmt::Write(args) | Stmt::WriteLn(args) => {
                for e in args {
                    check_imut_reads_in_expr(
                        env,
                        vars,
                        visible_routines,
                        e,
                        local_imuts,
                        initialized,
                    )?;
                }
                Ok(())
            }
        }
    }
    fn check_imut_reads_in_expr(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        expr: &Expr,
        local_imuts: &HashSet<String>,
        initialized: &HashSet<String>,
    ) -> Result<(), String> {
        match expr {
            Expr::Var(n) => {
                if local_imuts.contains(n) && !initialized.contains(n) {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "imut variable used before initialization: {0}",
                                    n,
                                ),
                            )
                        }),
                    );
                }
                Ok(())
            }
            Expr::Call(_, args) | Expr::ArrayLit(args) => {
                for e in args {
                    check_imut_reads_in_expr(
                        env,
                        vars,
                        visible_routines,
                        e,
                        local_imuts,
                        initialized,
                    )?;
                }
                Ok(())
            }
            Expr::Ctor(_, named) | Expr::RecordUpdate(_, named) => {
                for (_, e) in named {
                    check_imut_reads_in_expr(
                        env,
                        vars,
                        visible_routines,
                        e,
                        local_imuts,
                        initialized,
                    )?;
                }
                Ok(())
            }
            Expr::ArrayUpdate(base, updates) => {
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    base,
                    local_imuts,
                    initialized,
                )?;
                for (i, v) in updates {
                    check_imut_reads_in_expr(
                        env,
                        vars,
                        visible_routines,
                        i,
                        local_imuts,
                        initialized,
                    )?;
                    check_imut_reads_in_expr(
                        env,
                        vars,
                        visible_routines,
                        v,
                        local_imuts,
                        initialized,
                    )?;
                }
                Ok(())
            }
            Expr::OptionSome(inner)
            | Expr::Deref(inner)
            | Expr::Unary(_, inner)
            | Expr::Cast(_, inner) => {
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    inner,
                    local_imuts,
                    initialized,
                )
            }
            Expr::Field(base, _) => {
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    base,
                    local_imuts,
                    initialized,
                )
            }
            Expr::Index(base, idx) | Expr::Binary(base, _, idx) => {
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    base,
                    local_imuts,
                    initialized,
                )?;
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    idx,
                    local_imuts,
                    initialized,
                )
            }
            Expr::Cond { arms, else_block } => {
                for arm in arms {
                    check_imut_reads_in_expr(
                        env,
                        vars,
                        visible_routines,
                        &arm.cond,
                        local_imuts,
                        initialized,
                    )?;
                    for s in &arm.block.stmts {
                        let mut init2 = initialized.clone();
                        check_imut_stmt(
                            env,
                            vars,
                            visible_routines,
                            s,
                            local_imuts,
                            &mut init2,
                        )?;
                    }
                    check_imut_reads_in_expr(
                        env,
                        vars,
                        visible_routines,
                        &arm.block.value,
                        local_imuts,
                        initialized,
                    )?;
                }
                for s in &else_block.stmts {
                    let mut init2 = initialized.clone();
                    check_imut_stmt(
                        env,
                        vars,
                        visible_routines,
                        s,
                        local_imuts,
                        &mut init2,
                    )?;
                }
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    &else_block.value,
                    local_imuts,
                    initialized,
                )
            }
            Expr::Int(_)
            | Expr::Bool(_)
            | Expr::Char(_)
            | Expr::Real(_)
            | Expr::Str(_)
            | Expr::SetLit(_)
            | Expr::Nil
            | Expr::OptionNone => Ok(()),
        }
    }
    fn check_stmt_with_vars(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        s: &Stmt,
    ) -> Result<(), String> {
        match s {
            Stmt::Empty => Ok(()),
            Stmt::Compound(v) => {
                for st in v {
                    check_stmt_with_vars(env, vars, visible_routines, st)?;
                }
                Ok(())
            }
            Stmt::Assign(lv, rhs) => {
                let lt = resolve_lvalue_type_scoped(env, vars, visible_routines, lv)?;
                if let Expr::Str(_) = rhs {
                    if char_array_len(&lt).is_none() {
                        return Err(
                            "string literal assignment requires array of char lhs".into(),
                        );
                    }
                    return Ok(());
                }
                check_expr_matches_type_scoped(env, vars, visible_routines, rhs, &lt)
                    .map_err(|e| ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("type mismatch in assignment: {0}", e),
                        )
                    }))?;
                let rt = type_of_expr_scoped(env, vars, visible_routines, rhs).ok();
                let is_aggregate_call_result = #[allow(non_exhaustive_omitted_patterns)]
                match rhs {
                    Expr::Call(_, _) | Expr::Ctor(_, _) => true,
                    _ => false,
                } || #[allow(non_exhaustive_omitted_patterns)]
                    match rhs {
                        Expr::ArrayLit(_) => true,
                        _ => false,
                    } || #[allow(non_exhaustive_omitted_patterns)]
                    match rhs {
                        Expr::RecordUpdate(_, _) | Expr::ArrayUpdate(_, _) => true,
                        _ => false,
                    } || #[allow(non_exhaustive_omitted_patterns)]
                    match rhs {
                        Expr::OptionNone | Expr::OptionSome(_) => true,
                        _ => false,
                    } || #[allow(non_exhaustive_omitted_patterns)]
                    match rhs {
                        Expr::Cond { .. } => true,
                        _ => false,
                    };
                if !is_scalar_like(&lt) && expr_to_lvalue(rhs).is_none()
                    && !#[allow(non_exhaustive_omitted_patterns)]
                    match rhs {
                        Expr::SetLit(_) => true,
                        _ => false,
                    } && !is_aggregate_call_result
                {
                    return Err("aggregate assignment requires lvalue rhs".into());
                }
                if let Some(rt) = rt {
                    if !assignment_compatible(&lt, &rt) && !is_aggregate_call_result {
                        return Err("type mismatch in assignment".into());
                    }
                }
                Ok(())
            }
            Stmt::Read(args) => {
                let mut i = 0usize;
                while i < args.len() {
                    let Some(lv) = expr_to_lvalue(&args[i]) else {
                        return Err(
                            "Read arguments must be lvalues, except string max length"
                                .into(),
                        );
                    };
                    let t = resolve_lvalue_type_scoped(
                        env,
                        vars,
                        visible_routines,
                        &lv,
                    )?;
                    if char_array_len(&t).is_some() {
                        if i + 1 >= args.len() {
                            return Err(
                                "Read on array of char requires max length".into(),
                            );
                        }
                        let nt = type_of_expr_scoped(
                            env,
                            vars,
                            visible_routines,
                            &args[i + 1],
                        )?;
                        expect_integer_like(&nt, "Read string max length")?;
                        i += 2;
                        continue;
                    }
                    if !is_readable_scalar(&t) {
                        return Err("Read on aggregate type is not supported".into());
                    }
                    i += 1;
                }
                Ok(())
            }
            Stmt::ReadLn => Ok(()),
            Stmt::For { var, init, limit, body, .. } => {
                let vt = vars
                    .get(var)
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("unknown var: {0}", var))
                    }))?;
                expect_integer_like(vt, "for variable")?;
                expect_integer_like(
                    &type_of_expr_scoped(env, vars, visible_routines, init)?,
                    "for init",
                )?;
                expect_integer_like(
                    &type_of_expr_scoped(env, vars, visible_routines, limit)?,
                    "for limit",
                )?;
                check_stmt_with_vars(env, vars, visible_routines, body)
            }
            Stmt::Case { expr, arms, else_stmt } => {
                let et = type_of_expr_scoped(env, vars, visible_routines, expr)?;
                let mut used = HashSet::new();
                for (labels, st) in arms {
                    for label in labels {
                        match label {
                            CaseLabel::Single(ce) => {
                                let cv = eval_const(env, ce)?;
                                let token = ::alloc::__export::must_use({
                                    ::alloc::fmt::format(
                                        format_args!(
                                            "{0}:{1}",
                                            type_desc(&const_type_from_val(cv.clone(), env)?),
                                            ordinal_const_value(&cv)?,
                                        ),
                                    )
                                });
                                if !used.insert(token) {
                                    return Err("duplicate case label".into());
                                }
                                let ct = const_type_from_val(cv, env)?;
                                if !assignment_compatible(&et, &ct) {
                                    return Err("case arm constant type mismatch".into());
                                }
                            }
                            CaseLabel::Range(lo, hi) => {
                                let lv = eval_const(env, lo)?;
                                let hv = eval_const(env, hi)?;
                                let lt = const_type_from_val(lv.clone(), env)?;
                                let ht = const_type_from_val(hv.clone(), env)?;
                                if !assignment_compatible(&lt, &ht)
                                    || !assignment_compatible(&et, &lt)
                                {
                                    return Err("case arm range type mismatch".into());
                                }
                                let lo_i = ordinal_const_value(&lv)?;
                                let hi_i = ordinal_const_value(&hv)?;
                                if lo_i > hi_i {
                                    return Err("case label range low must be <= high".into());
                                }
                                for i in lo_i..=hi_i {
                                    let token = ::alloc::__export::must_use({
                                        ::alloc::fmt::format(
                                            format_args!("{0}:{1}", type_desc(&lt), i),
                                        )
                                    });
                                    if !used.insert(token) {
                                        return Err("duplicate case label".into());
                                    }
                                }
                            }
                        }
                    }
                    check_stmt_with_vars(env, vars, visible_routines, st)?;
                }
                if else_stmt.is_none() {
                    if let TypeInfo::Enum(enum_info) = &et {
                        let type_key = type_desc(&et);
                        for ordinal in enum_info.low..=enum_info.high {
                            let token = ::alloc::__export::must_use({
                                ::alloc::fmt::format(
                                    format_args!("{0}:{1}", type_key, ordinal),
                                )
                            });
                            if !used.contains(&token) {
                                return Err(
                                    "enum case must be exhaustive or include else".into(),
                                );
                            }
                        }
                    }
                }
                if let Some(es) = else_stmt {
                    check_stmt_with_vars(env, vars, visible_routines, es)?;
                }
                Ok(())
            }
            Stmt::SumCase { expr, arms, else_stmt } => {
                let et = type_of_expr_scoped(env, vars, visible_routines, expr)?;
                let sum = match et {
                    TypeInfo::Sum(s) => s,
                    _ => return Err("sum-case requires sum-record expression".into()),
                };
                for arm in arms {
                    let sinfo = sum_arm_by_name(&sum, &arm.ctor)
                        .ok_or_else(|| ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!(
                                    "unknown sum-case arm constructor: {0}",
                                    arm.ctor,
                                ),
                            )
                        }))?;
                    if sinfo.fields.len() != arm.binds.len() {
                        return Err("sum-case bind count mismatch".into());
                    }
                    let mut arm_vars = vars.clone();
                    for (bind, field) in arm.binds.iter().zip(&sinfo.fields) {
                        arm_vars.insert(bind.clone(), field.ty.clone());
                    }
                    check_stmt_with_vars(env, &arm_vars, visible_routines, &arm.body)?;
                }
                if let Some(es) = else_stmt {
                    check_stmt_with_vars(env, vars, visible_routines, es)?;
                }
                Ok(())
            }
            Stmt::ProcCall(name, args) => {
                if name == "Copy" {
                    return check_builtin_copy(env, vars, visible_routines, args);
                }
                if name == "Concat" {
                    return check_builtin_concat(env, vars, visible_routines, args);
                }
                if name == "Delete" {
                    return check_builtin_delete(env, vars, visible_routines, args);
                }
                if name == "Insert" {
                    return check_builtin_insert(env, vars, visible_routines, args);
                }
                if name == "IntToHex" {
                    return check_builtin_inttohex(env, vars, visible_routines, args);
                }
                if name == "SetAddr" {
                    return check_builtin_setaddr(env, vars, visible_routines, args);
                }
                if name.eq_ignore_ascii_case("new")
                    || name.eq_ignore_ascii_case("dispose")
                {
                    return check_builtin_new_dispose(
                        env,
                        vars,
                        visible_routines,
                        name,
                        args,
                    );
                }
                let key = visible_routines
                    .get(name)
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("unknown routine in scope: {0}", name),
                        )
                    }))?;
                let sig = env
                    .routines
                    .get(key)
                    .ok_or_else(|| ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!(
                                "internal: missing routine signature for {0}",
                                key,
                            ),
                        )
                    }))?;
                if sig.ret.is_some() {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("function used as procedure: {0}", name),
                            )
                        }),
                    );
                }
                check_call_args_scoped(env, vars, visible_routines, name, sig, args)
            }
            Stmt::If(cond, then_s, else_s) => {
                expect_basic(
                    &type_of_expr_scoped(env, vars, visible_routines, cond)?,
                    BasicType::Boolean,
                    "if condition",
                )?;
                check_stmt_with_vars(env, vars, visible_routines, then_s)?;
                if let Some(es) = else_s {
                    check_stmt_with_vars(env, vars, visible_routines, es)?;
                }
                Ok(())
            }
            Stmt::With(bases, body) => {
                let rewritten = rewrite_stmt_with(
                    env,
                    vars,
                    visible_routines,
                    body,
                    bases,
                )?;
                check_stmt_with_vars(env, vars, visible_routines, &rewritten)
            }
            Stmt::While(cond, body) => {
                expect_basic(
                    &type_of_expr_scoped(env, vars, visible_routines, cond)?,
                    BasicType::Boolean,
                    "while condition",
                )?;
                check_stmt_with_vars(env, vars, visible_routines, body)
            }
            Stmt::Repeat(stmts, cond) => {
                for st in stmts {
                    check_stmt_with_vars(env, vars, visible_routines, st)?;
                }
                expect_basic(
                    &type_of_expr_scoped(env, vars, visible_routines, cond)?,
                    BasicType::Boolean,
                    "repeat condition",
                )
            }
            Stmt::Write(args) | Stmt::WriteLn(args) => {
                for e in args {
                    match e {
                        Expr::Str(_) => {}
                        _ => {
                            let t = type_of_expr_scoped(env, vars, visible_routines, e)?;
                            if !is_writable_scalar(&t) && char_array_len(&t).is_none() {
                                return Err(
                                    "Write/WriteLn supports only scalar values".into(),
                                );
                            }
                        }
                    }
                }
                Ok(())
            }
        }
    }
    fn rewrite_stmt_with(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        stmt: &Stmt,
        bases: &[LValue],
    ) -> Result<Stmt, String> {
        Ok(
            match stmt {
                Stmt::Empty => Stmt::Empty,
                Stmt::Compound(v) => {
                    Stmt::Compound(
                        v
                            .iter()
                            .map(|s| rewrite_stmt_with(
                                env,
                                vars,
                                visible_routines,
                                s,
                                bases,
                            ))
                            .collect::<Result<Vec<_>, _>>()?,
                    )
                }
                Stmt::Assign(lv, rhs) => {
                    Stmt::Assign(
                        rewrite_lvalue_with(env, vars, visible_routines, lv, bases)?,
                        rewrite_expr_with(env, vars, visible_routines, rhs, bases)?,
                    )
                }
                Stmt::Read(args) => {
                    Stmt::Read(
                        args
                            .iter()
                            .map(|e| rewrite_expr_with(
                                env,
                                vars,
                                visible_routines,
                                e,
                                bases,
                            ))
                            .collect::<Result<Vec<_>, _>>()?,
                    )
                }
                Stmt::ReadLn => Stmt::ReadLn,
                Stmt::For { var, init, limit, downto, body } => {
                    Stmt::For {
                        var: var.clone(),
                        init: rewrite_expr_with(
                            env,
                            vars,
                            visible_routines,
                            init,
                            bases,
                        )?,
                        limit: rewrite_expr_with(
                            env,
                            vars,
                            visible_routines,
                            limit,
                            bases,
                        )?,
                        downto: *downto,
                        body: Box::new(
                            rewrite_stmt_with(env, vars, visible_routines, body, bases)?,
                        ),
                    }
                }
                Stmt::If(c, t, e) => {
                    Stmt::If(
                        rewrite_expr_with(env, vars, visible_routines, c, bases)?,
                        Box::new(
                            rewrite_stmt_with(env, vars, visible_routines, t, bases)?,
                        ),
                        e
                            .as_ref()
                            .map(|s| {
                                rewrite_stmt_with(env, vars, visible_routines, s, bases)
                                    .map(Box::new)
                            })
                            .transpose()?,
                    )
                }
                Stmt::With(inner, body) => {
                    let mut merged = bases.to_vec();
                    merged.extend(inner.iter().cloned());
                    rewrite_stmt_with(env, vars, visible_routines, body, &merged)?
                }
                Stmt::While(c, b) => {
                    Stmt::While(
                        rewrite_expr_with(env, vars, visible_routines, c, bases)?,
                        Box::new(
                            rewrite_stmt_with(env, vars, visible_routines, b, bases)?,
                        ),
                    )
                }
                Stmt::Repeat(v, c) => {
                    Stmt::Repeat(
                        v
                            .iter()
                            .map(|s| rewrite_stmt_with(
                                env,
                                vars,
                                visible_routines,
                                s,
                                bases,
                            ))
                            .collect::<Result<Vec<_>, _>>()?,
                        rewrite_expr_with(env, vars, visible_routines, c, bases)?,
                    )
                }
                Stmt::Case { expr, arms, else_stmt } => {
                    Stmt::Case {
                        expr: rewrite_expr_with(
                            env,
                            vars,
                            visible_routines,
                            expr,
                            bases,
                        )?,
                        arms: arms.clone(),
                        else_stmt: else_stmt
                            .as_ref()
                            .map(|s| {
                                rewrite_stmt_with(env, vars, visible_routines, s, bases)
                                    .map(Box::new)
                            })
                            .transpose()?,
                    }
                }
                Stmt::ProcCall(name, args) => {
                    Stmt::ProcCall(
                        name.clone(),
                        args
                            .iter()
                            .map(|e| rewrite_expr_with(
                                env,
                                vars,
                                visible_routines,
                                e,
                                bases,
                            ))
                            .collect::<Result<Vec<_>, _>>()?,
                    )
                }
                Stmt::Write(args) => {
                    Stmt::Write(
                        args
                            .iter()
                            .map(|e| rewrite_expr_with(
                                env,
                                vars,
                                visible_routines,
                                e,
                                bases,
                            ))
                            .collect::<Result<Vec<_>, _>>()?,
                    )
                }
                Stmt::WriteLn(args) => {
                    Stmt::WriteLn(
                        args
                            .iter()
                            .map(|e| rewrite_expr_with(
                                env,
                                vars,
                                visible_routines,
                                e,
                                bases,
                            ))
                            .collect::<Result<Vec<_>, _>>()?,
                    )
                }
                Stmt::SumCase { .. } => stmt.clone(),
            },
        )
    }
    fn rewrite_expr_with(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        expr: &Expr,
        bases: &[LValue],
    ) -> Result<Expr, String> {
        Ok(
            match expr {
                Expr::Var(
                    name,
                ) if !vars.contains_key(name) && !env.consts.contains_key(name)
                    && !visible_routines.contains_key(name) => {
                    lvalue_to_expr(
                        rewrite_lvalue_with(
                            env,
                            vars,
                            visible_routines,
                            &LValue {
                                base: name.clone(),
                                sels: ::alloc::vec::Vec::new(),
                            },
                            bases,
                        )?,
                    )
                }
                Expr::Call(name, args) => {
                    Expr::Call(
                        name.clone(),
                        args
                            .iter()
                            .map(|e| rewrite_expr_with(
                                env,
                                vars,
                                visible_routines,
                                e,
                                bases,
                            ))
                            .collect::<Result<Vec<_>, _>>()?,
                    )
                }
                Expr::Field(_, _) | Expr::Index(_, _) | Expr::Deref(_) => {
                    if let Some(lv) = expr_to_lvalue(expr) {
                        lvalue_to_expr(
                            rewrite_lvalue_with(env, vars, visible_routines, &lv, bases)?,
                        )
                    } else {
                        expr.clone()
                    }
                }
                Expr::Unary(op, inner) => {
                    Expr::Unary(
                        *op,
                        Box::new(
                            rewrite_expr_with(env, vars, visible_routines, inner, bases)?,
                        ),
                    )
                }
                Expr::Binary(a, op, b) => {
                    Expr::Binary(
                        Box::new(
                            rewrite_expr_with(env, vars, visible_routines, a, bases)?,
                        ),
                        *op,
                        Box::new(
                            rewrite_expr_with(env, vars, visible_routines, b, bases)?,
                        ),
                    )
                }
                Expr::SetLit(items) => {
                    Expr::SetLit(
                        items
                            .iter()
                            .map(|item| match item {
                                SetItem::Single(e) => {
                                    rewrite_expr_with(env, vars, visible_routines, e, bases)
                                        .map(SetItem::Single)
                                }
                                SetItem::Range(lo, hi) => {
                                    Ok(
                                        SetItem::Range(
                                            rewrite_expr_with(env, vars, visible_routines, lo, bases)?,
                                            rewrite_expr_with(env, vars, visible_routines, hi, bases)?,
                                        ),
                                    )
                                }
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                    )
                }
                Expr::Ctor(_, _)
                | Expr::ArrayLit(_)
                | Expr::RecordUpdate(_, _)
                | Expr::ArrayUpdate(_, _)
                | Expr::OptionNone
                | Expr::OptionSome(_)
                | Expr::Cond { .. }
                | Expr::Cast(_, _)
                | Expr::Int(_)
                | Expr::Bool(_)
                | Expr::Char(_)
                | Expr::Real(_)
                | Expr::Str(_)
                | Expr::Var(_)
                | Expr::Nil => expr.clone(),
            },
        )
    }
    fn rewrite_lvalue_with(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        lv: &LValue,
        bases: &[LValue],
    ) -> Result<LValue, String> {
        if vars.contains_key(&lv.base) {
            return Ok(lv.clone());
        }
        for base in bases.iter().rev() {
            let bt = resolve_lvalue_type_scoped(env, vars, visible_routines, base)?;
            if let TypeInfo::Record(r) = bt {
                if r.fields.contains_key(&lv.base) {
                    let mut sels = base.sels.clone();
                    sels.push(Selector::Field(lv.base.clone()));
                    sels.extend(lv.sels.clone());
                    return Ok(LValue {
                        base: base.base.clone(),
                        sels,
                    });
                }
            }
        }
        Ok(lv.clone())
    }
    fn lvalue_to_expr(lv: LValue) -> Expr {
        let mut e = Expr::Var(lv.base);
        for sel in lv.sels {
            e = match sel {
                Selector::Deref => Expr::Deref(Box::new(e)),
                Selector::Field(f) => Expr::Field(Box::new(e), f),
                Selector::Index(ixs) => {
                    let mut acc = e;
                    for ix in ixs {
                        acc = Expr::Index(Box::new(acc), Box::new(ix));
                    }
                    acc
                }
            };
        }
        e
    }
    fn builtin_expr_type(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        name: &str,
        args: &[Expr],
    ) -> Result<Option<TypeInfo>, String> {
        let n = name.to_ascii_lowercase();
        match n.as_str() {
            "ord" => {
                if args.len() != 1 {
                    return Err("Ord requires 1 argument".into());
                }
                let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
                if is_ordinal_type(&t) {
                    Ok(Some(TypeInfo::Basic(BasicType::Integer)))
                } else {
                    Err("Ord argument must be ordinal".into())
                }
            }
            "chr" => {
                if args.len() != 1 {
                    return Err("Chr requires 1 argument".into());
                }
                let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
                expect_integer_like(&t, "Chr argument")?;
                Ok(Some(TypeInfo::Basic(BasicType::Char)))
            }
            "abs" => {
                if args.len() != 1 {
                    return Err("Abs requires 1 argument".into());
                }
                let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
                if is_numeric_type(&t) {
                    Ok(Some(t))
                } else {
                    Err("Abs argument must be numeric".into())
                }
            }
            "sqr" => {
                if args.len() != 1 {
                    return Err("Sqr requires 1 argument".into());
                }
                let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
                if is_numeric_type(&t) {
                    Ok(Some(t))
                } else {
                    Err("Sqr argument must be numeric".into())
                }
            }
            "round" | "trunc" => {
                if args.len() != 1 {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} requires 1 argument", name),
                            )
                        }),
                    );
                }
                let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
                if is_numeric_type(&t) {
                    Ok(Some(TypeInfo::Basic(BasicType::Integer)))
                } else {
                    Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} argument must be numeric", name),
                            )
                        }),
                    )
                }
            }
            "succ" | "pred" => {
                if args.len() != 1 {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} requires 1 argument", name),
                            )
                        }),
                    );
                }
                let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
                if is_ordinal_type(&t) {
                    Ok(Some(t))
                } else {
                    Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} argument must be ordinal", name),
                            )
                        }),
                    )
                }
            }
            "odd" => {
                if args.len() != 1 {
                    return Err("Odd requires 1 argument".into());
                }
                let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
                expect_integer_like(&t, "Odd argument")?;
                Ok(Some(TypeInfo::Basic(BasicType::Boolean)))
            }
            "hextoint" => {
                if args.len() != 1 {
                    return Err("HexToInt requires 1 argument".into());
                }
                match &args[0] {
                    Expr::Str(_) => Ok(Some(TypeInfo::Basic(BasicType::Integer))),
                    _ => {
                        let t = type_of_expr_scoped(
                            env,
                            vars,
                            visible_routines,
                            &args[0],
                        )?;
                        if char_array_len(&t).is_some() {
                            Ok(Some(TypeInfo::Basic(BasicType::Integer)))
                        } else {
                            Err(
                                "HexToInt argument must be array of char or string literal"
                                    .into(),
                            )
                        }
                    }
                }
            }
            "addr" => {
                if args.len() != 1 {
                    return Err("Addr requires 1 argument".into());
                }
                let _ = expr_to_lvalue(&args[0])
                    .ok_or("Addr argument must be an lvalue")?;
                Ok(Some(TypeInfo::Basic(BasicType::Integer)))
            }
            "pos" => {
                if args.len() != 2 {
                    return Err("Pos requires 2 arguments".into());
                }
                expect_string_like_expr(
                    env,
                    vars,
                    visible_routines,
                    &args[0],
                    "Pos first argument",
                )?;
                expect_string_like_expr(
                    env,
                    vars,
                    visible_routines,
                    &args[1],
                    "Pos second argument",
                )?;
                Ok(Some(TypeInfo::Basic(BasicType::Integer)))
            }
            "upcase" => {
                if args.len() != 1 {
                    return Err("UpCase requires 1 argument".into());
                }
                let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
                expect_basic(&t, BasicType::Char, "UpCase argument")?;
                Ok(Some(TypeInfo::Basic(BasicType::Char)))
            }
            "length" | "high" | "low" => {
                if args.len() != 1 {
                    return Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} requires 1 argument", name),
                            )
                        }),
                    );
                }
                let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
                if let TypeInfo::Array(_) = t {
                    Ok(Some(TypeInfo::Basic(BasicType::Integer)))
                } else {
                    Err(
                        ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("{0} argument must be array", name),
                            )
                        }),
                    )
                }
            }
            _ => Ok(None),
        }
    }
    fn check_builtin_inttohex(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        args: &[Expr],
    ) -> Result<(), String> {
        if args.len() != 4 {
            return Err("IntToHex requires 4 arguments".into());
        }
        let vt = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
        expect_integer_like(&vt, "IntToHex value")?;
        let lv = expr_to_lvalue(&args[1])
            .ok_or("IntToHex second argument must be lvalue char array")?;
        let at = resolve_lvalue_type_scoped(env, vars, visible_routines, &lv)?;
        let Some(_) = char_array_len(&at) else {
            return Err("IntToHex second argument must be array of char".into());
        };
        let mt = type_of_expr_scoped(env, vars, visible_routines, &args[2])?;
        expect_integer_like(&mt, "IntToHex max length")?;
        let ft = type_of_expr_scoped(env, vars, visible_routines, &args[3])?;
        expect_basic(&ft, BasicType::Boolean, "IntToHex zero-fill flag")?;
        Ok(())
    }
    fn check_builtin_copy(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        args: &[Expr],
    ) -> Result<(), String> {
        if args.len() != 2 {
            return Err("Copy requires 2 arguments".into());
        }
        expect_string_like_expr(env, vars, visible_routines, &args[0], "Copy source")?;
        expect_char_array_lvalue_expr(
            env,
            vars,
            visible_routines,
            &args[1],
            "Copy destination",
        )
    }
    fn check_builtin_concat(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        args: &[Expr],
    ) -> Result<(), String> {
        if args.len() != 3 {
            return Err("Concat requires 3 arguments".into());
        }
        expect_string_like_expr(
            env,
            vars,
            visible_routines,
            &args[0],
            "Concat first source",
        )?;
        expect_string_like_expr(
            env,
            vars,
            visible_routines,
            &args[1],
            "Concat second source",
        )?;
        expect_char_array_lvalue_expr(
            env,
            vars,
            visible_routines,
            &args[2],
            "Concat destination",
        )
    }
    fn check_builtin_delete(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        args: &[Expr],
    ) -> Result<(), String> {
        if args.len() != 3 {
            return Err("Delete requires 3 arguments".into());
        }
        expect_char_array_lvalue_expr(
            env,
            vars,
            visible_routines,
            &args[0],
            "Delete target",
        )?;
        let idx_ty = type_of_expr_scoped(env, vars, visible_routines, &args[1])?;
        expect_integer_like(&idx_ty, "Delete index")?;
        let count_ty = type_of_expr_scoped(env, vars, visible_routines, &args[2])?;
        expect_integer_like(&count_ty, "Delete count")
    }
    fn check_builtin_insert(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        args: &[Expr],
    ) -> Result<(), String> {
        if args.len() != 3 {
            return Err("Insert requires 3 arguments".into());
        }
        expect_string_like_expr(env, vars, visible_routines, &args[0], "Insert source")?;
        expect_char_array_lvalue_expr(
            env,
            vars,
            visible_routines,
            &args[1],
            "Insert destination",
        )?;
        let idx_ty = type_of_expr_scoped(env, vars, visible_routines, &args[2])?;
        expect_integer_like(&idx_ty, "Insert index")
    }
    fn check_builtin_new_dispose(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        name: &str,
        args: &[Expr],
    ) -> Result<(), String> {
        if args.len() != 1 {
            return Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} requires 1 argument", name))
                }),
            );
        }
        let lv = expr_to_lvalue(&args[0])
            .ok_or_else(|| ::alloc::__export::must_use({
                ::alloc::fmt::format(
                    format_args!("{0} argument must be lvalue pointer", name),
                )
            }))?;
        let t = resolve_lvalue_type_scoped(env, vars, visible_routines, &lv)?;
        match t {
            TypeInfo::Pointer(_) => Ok(()),
            _ => {
                Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("{0} argument must be pointer", name),
                        )
                    }),
                )
            }
        }
    }
    fn check_builtin_setaddr(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        args: &[Expr],
    ) -> Result<(), String> {
        if args.len() != 2 {
            return Err("SetAddr requires 2 arguments".into());
        }
        let lv = expr_to_lvalue(&args[0])
            .ok_or("SetAddr first argument must be lvalue pointer")?;
        let ptr_ty = resolve_lvalue_type_scoped(env, vars, visible_routines, &lv)?;
        match ptr_ty {
            TypeInfo::Pointer(_) => {}
            _ => return Err("SetAddr first argument must be pointer".into()),
        }
        let addr_ty = type_of_expr_scoped(env, vars, visible_routines, &args[1])?;
        expect_integer_like(&addr_ty, "SetAddr address")
    }
    fn const_type_from_val(v: ConstVal, env: &Env) -> Result<TypeInfo, String> {
        Ok(
            match v {
                ConstVal::I32(_) => TypeInfo::Basic(BasicType::Integer),
                ConstVal::U32(_) => TypeInfo::Basic(BasicType::Char),
                ConstVal::Bool(_) => TypeInfo::Basic(BasicType::Boolean),
                ConstVal::Real(_) => TypeInfo::Basic(BasicType::Real),
                ConstVal::EnumVal { type_name, .. } => {
                    env.types
                        .get(&type_name)
                        .cloned()
                        .ok_or_else(|| ::alloc::__export::must_use({
                            ::alloc::fmt::format(
                                format_args!("unknown type: {0}", type_name),
                            )
                        }))?
                }
            },
        )
    }
    fn expect_basic(t: &TypeInfo, want: BasicType, what: &str) -> Result<(), String> {
        match scalar_base_type(t) {
            Some(b) if std::mem::discriminant(&b) == std::mem::discriminant(&want) => {
                Ok(())
            }
            _ => {
                Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("type error in {0}", what))
                    }),
                )
            }
        }
    }
    fn expect_integer_like(t: &TypeInfo, what: &str) -> Result<(), String> {
        if is_integer_like(t) {
            Ok(())
        } else {
            Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("type error in {0}", what))
                }),
            )
        }
    }
    fn expect_array_index_type(t: &TypeInfo, what: &str) -> Result<(), String> {
        if is_array_index_type(t) {
            Ok(())
        } else {
            Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("type error in {0}", what))
                }),
            )
        }
    }
    fn ctor_name_matches_record_type(
        env: &Env,
        ctor_name: &str,
        expected: &RecordInfo,
    ) -> bool {
        env.types
            .iter()
            .any(|(name, ty)| {
                if !name.eq_ignore_ascii_case(ctor_name) {
                    return false;
                }
                match ty {
                    TypeInfo::Record(r) => same_record(r, expected),
                    _ => false,
                }
            })
    }
    fn same_type(a: &TypeInfo, b: &TypeInfo) -> bool {
        match (a, b) {
            (TypeInfo::Nil, TypeInfo::Nil) => true,
            (TypeInfo::Pointer(_), TypeInfo::Nil)
            | (TypeInfo::Nil, TypeInfo::Pointer(_)) => true,
            (TypeInfo::Basic(x), TypeInfo::Basic(y)) => {
                std::mem::discriminant(x) == std::mem::discriminant(y)
            }
            (TypeInfo::Enum(x), TypeInfo::Enum(y)) => x.name == y.name,
            (TypeInfo::Pointer(x), TypeInfo::Pointer(y)) => x.eq_ignore_ascii_case(y),
            (TypeInfo::Subrange(x), TypeInfo::Subrange(y)) => {
                x.low == y.low && x.high == y.high && same_type(&x.base, &y.base)
            }
            (TypeInfo::Set(x), TypeInfo::Set(y)) => same_type(&x.elem_ty, &y.elem_ty),
            (TypeInfo::Record(rx), TypeInfo::Record(ry)) => same_record(rx, ry),
            (TypeInfo::Sum(sx), TypeInfo::Sum(sy)) => same_sum(sx, sy),
            (TypeInfo::Array(ax), TypeInfo::Array(ay)) => {
                ax.low == ay.low && ax.high == ay.high
                    && same_type(&ax.elem_ty, &ay.elem_ty)
            }
            _ => false,
        }
    }
    fn assignment_compatible(lhs: &TypeInfo, rhs: &TypeInfo) -> bool {
        same_type(lhs, rhs) || (is_real_type(lhs) && is_numeric_type(rhs))
            || (is_integer_like(lhs) && is_integer_like(rhs)
                && ordinal_compatible(lhs, rhs))
            || #[allow(non_exhaustive_omitted_patterns)]
            match (lhs, rhs) {
                (TypeInfo::Pointer(_), TypeInfo::Nil) => true,
                _ => false,
            }
    }
    fn equality_compatible(a: &TypeInfo, b: &TypeInfo) -> bool {
        same_type(a, b) || (is_numeric_type(a) && is_numeric_type(b))
            || (is_integer_like(a) && is_integer_like(b) && ordinal_compatible(a, b))
            || #[allow(non_exhaustive_omitted_patterns)]
            match (a, b) {
                (TypeInfo::Pointer(_), TypeInfo::Nil)
                | (TypeInfo::Nil, TypeInfo::Pointer(_)) => true,
                _ => false,
            }
    }
    fn order_compatible(a: &TypeInfo, b: &TypeInfo) -> bool {
        (is_numeric_type(a) && is_numeric_type(b))
            || (is_integer_like(a) && is_integer_like(b) && ordinal_compatible(a, b))
            || (is_set_type(a) && is_set_type(b) && same_type(a, b))
    }
    fn ordinal_compatible(a: &TypeInfo, b: &TypeInfo) -> bool {
        match (ordinal_root(a), ordinal_root(b)) {
            (Some(x), Some(y)) => x == y,
            _ => false,
        }
    }
    fn ordinal_root(t: &TypeInfo) -> Option<String> {
        match t {
            TypeInfo::Basic(BasicType::Integer) => Some("integer".into()),
            TypeInfo::Basic(BasicType::Boolean) => Some("boolean".into()),
            TypeInfo::Basic(BasicType::Char) => Some("char".into()),
            TypeInfo::Enum(e) => {
                Some(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(format_args!("enum:{0}", e.name))
                    }),
                )
            }
            TypeInfo::Subrange(s) => ordinal_root(&s.base),
            _ => None,
        }
    }
    fn ordinal_bounds(t: &TypeInfo) -> Result<(i32, i32), String> {
        match t {
            TypeInfo::Basic(BasicType::Boolean) => Ok((0, 1)),
            TypeInfo::Basic(BasicType::Char) => Ok((0, 255)),
            TypeInfo::Basic(BasicType::Integer) => Ok((i32::MIN, i32::MAX)),
            TypeInfo::Enum(e) => Ok((e.low, e.high)),
            TypeInfo::Subrange(s) => Ok((s.low, s.high)),
            _ => Err("type is not ordinal".into()),
        }
    }
    fn scalar_base_type(t: &TypeInfo) -> Option<BasicType> {
        match t {
            TypeInfo::Basic(b) => Some(b.clone()),
            TypeInfo::Subrange(s) => scalar_base_type(&s.base),
            _ => None,
        }
    }
    fn same_record(a: &RecordInfo, b: &RecordInfo) -> bool {
        if a.fields.len() != b.fields.len() {
            return false;
        }
        for (k, fa) in &a.fields {
            let Some(fb) = b.fields.get(k) else {
                return false;
            };
            if fa.offset_bytes != fb.offset_bytes || !same_type(&fa.ty, &fb.ty) {
                return false;
            }
        }
        true
    }
    fn same_sum(a: &SumInfo, b: &SumInfo) -> bool {
        if a.arms.len() != b.arms.len() {
            return false;
        }
        for (aa, bb) in a.arms.iter().zip(&b.arms) {
            if !aa.name.eq_ignore_ascii_case(&bb.name)
                || aa.fields.len() != bb.fields.len()
            {
                return false;
            }
            for (fa, fb) in aa.fields.iter().zip(&bb.fields) {
                if !fa.name.eq_ignore_ascii_case(&fb.name)
                    || fa.offset_bytes != fb.offset_bytes || !same_type(&fa.ty, &fb.ty)
                {
                    return false;
                }
            }
        }
        true
    }
    fn is_set_type(t: &TypeInfo) -> bool {
        #[allow(non_exhaustive_omitted_patterns)]
        match t {
            TypeInfo::Set(_) => true,
            _ => false,
        }
    }
    fn array_rank_and_elem(t: &TypeInfo) -> Option<(usize, &TypeInfo)> {
        let mut rank = 0usize;
        let mut cur = t;
        while let TypeInfo::Array(a) = cur {
            rank += 1;
            cur = a.elem_ty.as_ref();
        }
        if rank == 0 { None } else { Some((rank, cur)) }
    }
    fn is_real_type(t: &TypeInfo) -> bool {
        #[allow(non_exhaustive_omitted_patterns)]
        match t {
            TypeInfo::Basic(BasicType::Real) => true,
            _ => false,
        }
    }
    fn is_numeric_type(t: &TypeInfo) -> bool {
        is_integer_like(t) || is_real_type(t)
    }
    fn is_integer_like(t: &TypeInfo) -> bool {
        #[allow(non_exhaustive_omitted_patterns)]
        match t {
            TypeInfo::Basic(BasicType::Integer)
            | TypeInfo::Basic(BasicType::Boolean)
            | TypeInfo::Basic(BasicType::Char)
            | TypeInfo::Enum(_)
            | TypeInfo::Subrange(_) => true,
            _ => false,
        }
    }
    fn is_array_index_type(t: &TypeInfo) -> bool {
        #[allow(non_exhaustive_omitted_patterns)]
        match t {
            TypeInfo::Basic(BasicType::Integer)
            | TypeInfo::Basic(BasicType::Char)
            | TypeInfo::Enum(_)
            | TypeInfo::Subrange(_) => true,
            _ => false,
        }
    }
    fn is_ordinal_type(t: &TypeInfo) -> bool {
        is_integer_like(t)
    }
    fn is_scalar_like(t: &TypeInfo) -> bool {
        #[allow(non_exhaustive_omitted_patterns)]
        match t {
            TypeInfo::Basic(_)
            | TypeInfo::Enum(_)
            | TypeInfo::Subrange(_)
            | TypeInfo::Set(_) => true,
            _ => false,
        }
    }
    fn is_readable_scalar(t: &TypeInfo) -> bool {
        #[allow(non_exhaustive_omitted_patterns)]
        match t {
            TypeInfo::Basic(_) | TypeInfo::Enum(_) | TypeInfo::Subrange(_) => true,
            _ => false,
        }
    }
    fn is_writable_scalar(t: &TypeInfo) -> bool {
        #[allow(non_exhaustive_omitted_patterns)]
        match t {
            TypeInfo::Basic(_) | TypeInfo::Enum(_) | TypeInfo::Subrange(_) => true,
            _ => false,
        }
    }
    fn char_array_len(t: &TypeInfo) -> Option<u32> {
        match t {
            TypeInfo::Array(a) => {
                match a.elem_ty.as_ref() {
                    TypeInfo::Basic(BasicType::Char) => Some(a.len),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    fn expect_string_like_expr(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        expr: &Expr,
        what: &str,
    ) -> Result<(), String> {
        if #[allow(non_exhaustive_omitted_patterns)]
        match expr {
            Expr::Str(_) => true,
            _ => false,
        } {
            return Ok(());
        }
        let t = type_of_expr_scoped(env, vars, visible_routines, expr)?;
        if char_array_len(&t).is_some() {
            Ok(())
        } else {
            Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} must be array of char", what))
                }),
            )
        }
    }
    fn expect_char_array_lvalue_expr(
        env: &Env,
        vars: &HashMap<String, TypeInfo>,
        visible_routines: &HashMap<String, String>,
        expr: &Expr,
        what: &str,
    ) -> Result<(), String> {
        let lv = expr_to_lvalue(expr)
            .ok_or_else(|| ::alloc::__export::must_use({
                ::alloc::fmt::format(
                    format_args!("{0} must be lvalue array of char", what),
                )
            }))?;
        let t = resolve_lvalue_type_scoped(env, vars, visible_routines, &lv)?;
        if char_array_len(&t).is_some() {
            Ok(())
        } else {
            Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0} must be array of char", what))
                }),
            )
        }
    }
    fn type_desc(t: &TypeInfo) -> String {
        match t {
            TypeInfo::Basic(BasicType::Integer) => "integer".into(),
            TypeInfo::Basic(BasicType::Boolean) => "boolean".into(),
            TypeInfo::Basic(BasicType::Char) => "char".into(),
            TypeInfo::Basic(BasicType::Real) => "real".into(),
            TypeInfo::Enum(e) => {
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("enum {0}", e.name))
                })
            }
            TypeInfo::Subrange(s) => {
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("{0}..{1}", s.low, s.high))
                })
            }
            TypeInfo::Set(s) => {
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("set of {0}", type_desc(&s.elem_ty)),
                    )
                })
            }
            TypeInfo::Pointer(n) => {
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("^{0}", n))
                })
            }
            TypeInfo::Nil => "nil".into(),
            TypeInfo::Record(_) => "record".into(),
            TypeInfo::Sum(_) => "record of".into(),
            TypeInfo::Array(a) => {
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!(
                            "array[{0}..{1}] of {2}",
                            a.low,
                            a.high,
                            type_desc(&a.elem_ty),
                        ),
                    )
                })
            }
        }
    }
}
use ast::*;
use codegen::ForthGen;
use sema::*;
#[grammar = "kpascal.pest"]
struct PascalParser;
#[allow(non_upper_case_globals)]
const _PEST_GRAMMAR_PascalParser: [&'static str; 1usize] = [
    "WHITESPACE = _{ \" \" | \"\\t\" | \"\\r\" | \"\\n\" }\nCOMMENT    = _{ \"{\" ~ (!\"}\" ~ ANY)* ~ \"}\" | \"(*\" ~ (!\"*)\" ~ ANY)* ~ \"*)\" }\n\nident      = @{ (ASCII_ALPHA | \"_\") ~ (ASCII_ALPHANUMERIC | \"_\")* }\n\nprogram    =  { SOI ~ ^\"program\" ~ ident ~ \";\" ~ block ~ \".\" ~ EOI }\nblock      =  { block_item* ~ compound_stmt }\nblock_item  = _{ const_section | type_section | var_section | imut_section | routine_decl }\n\nconst_section = { ^\"const\" ~ const_decl+ }\nconst_decl    = { ident ~ (\":\" ~ type_ref_or_basic)? ~ \"=\" ~ const_expr ~ \";\" }\n\ntype_section  = { ^\"type\" ~ type_decl+ }\ntype_decl     = { ident ~ \"=\" ~ type_spec ~ \";\" }\n\ntype_spec     = _{ set_type | subrange_type | sum_record_type | enum_type | record_type | array_type | result_type | option_type | pointer_type | type_ref | basic_type }\nbasic_type    = { ^\"integer\" | ^\"boolean\" | ^\"char\" | ^\"real\" }\ntype_ref      = { ident }\npointer_type  = { \"^\" ~ ident }\noption_type   = { ^\"option\" ~ ^\"of\" ~ type_ref_or_basic }\nresult_type   = { ^\"result\" ~ ^\"of\" ~ type_ref_or_basic ~ \",\" ~ type_ref_or_basic }\nenum_type     = { \"(\" ~ ident ~ (\",\" ~ ident)* ~ \")\" }\nsubrange_type = { const_expr ~ \"..\" ~ const_expr }\nset_type      = { ^\"set\" ~ ^\"of\" ~ type_ref_or_basic }\n\nrecord_type   = { ^\"record\" ~ field_decl* ~ variant_part? ~ ^\"end\" }\nsum_record_type = { ^\"record\" ~ ^\"of\" ~ sum_arm_decl ~ (\";\" ~ sum_arm_decl)* ~ \";\"? ~ ^\"end\" }\nsum_arm_decl  = { ident ~ \":\" ~ \"(\" ~ sum_arm_fields? ~ \")\" }\nsum_arm_fields = { field_decl_inline ~ (\";\" ~ field_decl_inline)* ~ \";\"? }\nfield_decl_inline = { ident ~ \":\" ~ type_ref_or_basic }\nvariant_part  = { ^\"case\" ~ ident? ~ (\":\" ~ type_ref_or_basic)? ~ ^\"of\" ~ variant_case ~ (\";\" ~ variant_case)* ~ \";\"? }\nvariant_case  = { case_label_list ~ \":\" ~ \"(\" ~ field_decl* ~ variant_part? ~ \")\" }\narray_type    = { ^\"array\" ~ \"[\" ~ array_dim ~ ((\",\" | \";\") ~ array_dim)* ~ \"]\" ~ ^\"of\" ~ type_ref_or_basic }\narray_dim     = { const_expr ~ ( \"..\" ~ const_expr )? }\nfield_decl    = { ident ~ \":\" ~ type_ref_or_basic ~ \";\" }\ntype_ref_or_basic = _{ set_type | array_type | subrange_type | result_type | option_type | pointer_type | type_ref | basic_type }\n\nvar_section   = { ^\"var\" ~ var_decl+ }\nimut_section  = { ^\"imut\" ~ var_decl+ }\ndecl_stopper  = { ^\"imut\" | ^\"procedure\" | ^\"function\" | ^\"begin\" }\nvar_decl      = { ident ~ \":\" ~ type_ref_or_basic ~ \";\" }\nroutine_decl  = _{ procedure_decl | function_decl }\nprocedure_decl = { ^\"procedure\" ~ ident ~ formal_params? ~ \";\" ~ block ~ \";\" }\nfunction_decl  = { ^\"function\" ~ ident ~ formal_params? ~ \":\" ~ type_ref_or_basic ~ \";\" ~ block ~ \";\" }\nformal_params  = { \"(\" ~ formal_param_group ~ (\";\" ~ formal_param_group)* ~ \")\" }\nformal_param_group = { ^\"var\"? ~ ident ~ (\",\" ~ ident)* ~ \":\" ~ (conformant_array_param | type_ref_or_basic) }\nconformant_array_param = { \"array\" ~ \"[\" ~ conformant_array_dim ~ (\";\" ~ conformant_array_dim)* ~ \"]\" ~ \"of\" ~ type_ref_or_basic }\nconformant_array_dim = { ident ~ \"..\" ~ ident ~ \":\" ~ type_ref_or_basic }\n\ncompound_stmt = { ^\"begin\" ~ stmt_list? ~ ^\"end\" }\nstmt_list     = { stmt ~ (\";\" ~ stmt)* ~ \";\"? }\n\nstmt          = _{ compound_stmt\n                 | assign_stmt\n                 | read_stmt\n                 | readln_stmt\n                 | for_stmt\n                 | write_stmt\n                 | writeln_stmt\n                 | sum_case_stmt\n                 | case_stmt\n                 | proc_call_stmt\n                 | if_stmt\n                 | with_stmt\n                 | while_stmt\n                 | repeat_stmt\n                 | empty_stmt\n                 }\n\nempty_stmt    = { \"\" }\n\nassign_stmt   = { lvalue ~ \":=\" ~ expr }\nread_stmt     = { ^\"Read\" ~ \"(\" ~ expr_list ~ \")\" }\nreadln_stmt   = { ^\"ReadLn\" ~ ( \"(\" ~ \")\" )? }\nfor_stmt      = { ^\"for\" ~ ident ~ \":=\" ~ expr ~ for_dir ~ expr ~ ^\"do\" ~ stmt }\nfor_dir       = { ^\"to\" | ^\"downto\" }\ncase_stmt     = { ^\"case\" ~ expr ~ ^\"of\" ~ case_arm+ ~ (^\"else\" ~ stmt)? ~ ^\"end\" }\ncase_arm      = { case_label_list ~ \":\" ~ stmt ~ \";\"? }\ncase_label_list = { case_label ~ (\",\" ~ case_label)* }\ncase_label    = { const_expr ~ (\"..\" ~ const_expr)? }\nsum_case_stmt = { ^\"case\" ~ expr ~ ^\"of\" ~ sum_case_arm ~ (\";\" ~ sum_case_arm)* ~ (\";\" ~ sum_case_else)? ~ \";\"? ~ ^\"end\" }\nsum_case_else = { ^\"else\" ~ \":\" ~ stmt }\nsum_case_arm  = { ident ~ \"(\" ~ bind_list? ~ \")\" ~ \":\" ~ stmt }\nbind_list     = { ident ~ (\",\" ~ ident)* }\nproc_call_stmt = { ident ~ \"(\" ~ expr_list? ~ \")\" }\nlvalue        = { ident ~ selector* }\nselector      = _{ deref_access | field_access | index_access }\nderef_access  = { \"^\" }\nfield_access  = { \".\" ~ ident }\nindex_access  = { \"[\" ~ expr ~ (\",\" ~ expr)* ~ \"]\" }\nlvalue_list   = { lvalue ~ (\",\" ~ lvalue)* }\n\nif_stmt       = { ^\"if\" ~ expr ~ ^\"then\" ~ stmt ~ (^\"else\" ~ stmt)? }\nwith_stmt     = { ^\"with\" ~ lvalue ~ (\",\" ~ lvalue)* ~ ^\"do\" ~ stmt }\nwhile_stmt    = { ^\"while\" ~ expr ~ ^\"do\" ~ stmt }\nrepeat_stmt   = { ^\"repeat\" ~ stmt_list? ~ ^\"until\" ~ expr }\n\nwrite_stmt    = { ^\"Write\" ~ \"(\" ~ expr_list? ~ \")\" }\nwriteln_stmt  = { ^\"WriteLn\" ~ ( \"(\" ~ expr_list? ~ \")\" )? }\nexpr_list     = { expr ~ (\",\" ~ expr)* }\n\nexpr          = _{ rel }\nrel           = { add ~ (rel_op ~ add)? }\nrel_op        = { \"<=\" | \">=\" | \"<>\" | \"=\" | \"<\" | \">\" | ^\"in\" }\n\nadd           = { mul ~ (add_op ~ mul)* }\nadd_op        = { \"+\" | \"-\" | ^\"or\" | ^\"xor\" }\n\nmul           = { unary ~ (mul_op ~ unary)* }\nmul_op        = { \"*\" | \"/\" | ^\"div\" | ^\"mod\" | ^\"and\" }\n\nunary         = { (unary_op ~ unary) | primary }\nunary_op      = { \"-\" | ^\"not\" }\n\nprimary       = { cond_expr | nil_expr | none_expr | some_expr | cast_expr | set_lit | bool_lit | real_lit | number | string_lit | char_code | array_lit | array_update_expr | record_update_expr | ctor_call_named | func_call | lvalue | \"(\" ~ expr ~ \")\" }\ncast_expr     = { ^\"cast\" ~ \"(\" ~ type_ref_or_basic ~ \",\" ~ expr ~ \")\" }\ncond_expr     = { ^\"cond\" ~ \"(\" ~ cond_arm ~ (\";\" ~ cond_arm)* ~ \";\" ~ cond_else_arm ~ \")\" }\ncond_arm      = { !(^\"else\" ~ \":\") ~ expr ~ \":\" ~ cond_block }\ncond_else_arm = { ^\"else\" ~ \":\" ~ cond_block }\ncond_block    = { ^\"begin\" ~ cond_stmt* ~ value_stmt ~ ^\"end\" }\ncond_stmt     = { cond_stmt_inner ~ \";\" }\ncond_stmt_inner = _{ compound_stmt | assign_stmt | read_stmt | readln_stmt | for_stmt | write_stmt | writeln_stmt | sum_case_stmt | case_stmt | proc_call_stmt | if_stmt | with_stmt | while_stmt | repeat_stmt }\nvalue_stmt    = { ^\"value\" ~ expr }\nnone_expr     = { ^\"none\" }\nsome_expr     = { ^\"some\" ~ \"(\" ~ expr ~ \")\" }\nnil_expr      = { ^\"nil\" }\nset_lit       = { \"[\" ~ set_item_list? ~ \"]\" }\nset_item_list = { set_item ~ (\",\" ~ set_item)* }\nset_item      = { expr ~ (\"..\" ~ expr)? }\narray_lit     = { \"[\" ~ expr_list? ~ \"]\" }\nrecord_update_expr = { ident ~ ^\"with\" ~ \"(\" ~ ctor_named_args ~ \")\" }\narray_update_expr  = { ident ~ ^\"with\" ~ \"[\" ~ array_update_args ~ \"]\" }\narray_update_args  = { array_update_arg ~ (\",\" ~ array_update_arg)* ~ \",\"? }\narray_update_arg   = { expr ~ \":=\" ~ expr }\nctor_call_named = { ident ~ \"(\" ~ ctor_named_args ~ \")\" }\nctor_named_args = { ctor_named_arg ~ (\";\" ~ ctor_named_arg)* ~ \";\"? }\nctor_named_arg = { ident ~ \":=\" ~ expr }\nfunc_call     = { ident ~ \"(\" ~ expr_list? ~ \")\" }\nbool_lit      = { ^\"false\" | ^\"true\" }\n\nnumber        = @{ (\"0x\" ~ ASCII_HEX_DIGIT+) | (\"$\" ~ ASCII_HEX_DIGIT+) | ASCII_DIGIT+ }\nexp_part      = _{ (\"e\" | \"E\") ~ (\"+\" | \"-\")? ~ ASCII_DIGIT+ }\nreal_lit     = @{ (ASCII_DIGIT+ ~ \".\" ~ ASCII_DIGIT+ ~ exp_part?) | (\".\" ~ ASCII_DIGIT+ ~ exp_part?) | (ASCII_DIGIT+ ~ exp_part) }\n\nstring_lit    = @{ \"\'\" ~ ( \"\'\'\" | !(\"\'\" ) ~ ANY )* ~ \"\'\" }\nchar_code     = { \"#\" ~ number }                     // #123 \u{5f62}\u{5f0f}\u{ff08}UTF-32 code point\u{ff09}\n\nconst_expr    = _{ const_rel }\nconst_rel     = { const_add ~ (rel_op ~ const_add)? }\nconst_add     = { const_mul ~ (add_op ~ const_mul)* }\nconst_mul     = { const_unary ~ (mul_op ~ const_unary)* }\nconst_unary   = { (unary_op ~ const_unary) | const_primary }\nconst_primary = { bool_lit | real_lit | number | string_lit | char_code | const_func_call | ident | \"(\" ~ const_expr ~ \")\" }\nconst_func_call = { ident ~ \"(\" ~ const_expr_list? ~ \")\" }\nconst_expr_list = { const_expr ~ (\",\" ~ const_expr)* }\n",
];
#[allow(dead_code, non_camel_case_types, clippy::upper_case_acronyms)]
pub enum Rule {
    ///End-of-input
    EOI,
    WHITESPACE,
    COMMENT,
    ident,
    program,
    block,
    block_item,
    const_section,
    const_decl,
    type_section,
    type_decl,
    type_spec,
    basic_type,
    type_ref,
    pointer_type,
    option_type,
    result_type,
    enum_type,
    subrange_type,
    set_type,
    record_type,
    sum_record_type,
    sum_arm_decl,
    sum_arm_fields,
    field_decl_inline,
    variant_part,
    variant_case,
    array_type,
    array_dim,
    field_decl,
    type_ref_or_basic,
    var_section,
    imut_section,
    decl_stopper,
    var_decl,
    routine_decl,
    procedure_decl,
    function_decl,
    formal_params,
    formal_param_group,
    conformant_array_param,
    conformant_array_dim,
    compound_stmt,
    stmt_list,
    stmt,
    empty_stmt,
    assign_stmt,
    read_stmt,
    readln_stmt,
    for_stmt,
    for_dir,
    case_stmt,
    case_arm,
    case_label_list,
    case_label,
    sum_case_stmt,
    sum_case_else,
    sum_case_arm,
    bind_list,
    proc_call_stmt,
    lvalue,
    selector,
    deref_access,
    field_access,
    index_access,
    lvalue_list,
    if_stmt,
    with_stmt,
    while_stmt,
    repeat_stmt,
    write_stmt,
    writeln_stmt,
    expr_list,
    expr,
    rel,
    rel_op,
    add,
    add_op,
    mul,
    mul_op,
    unary,
    unary_op,
    primary,
    cast_expr,
    cond_expr,
    cond_arm,
    cond_else_arm,
    cond_block,
    cond_stmt,
    cond_stmt_inner,
    value_stmt,
    none_expr,
    some_expr,
    nil_expr,
    set_lit,
    set_item_list,
    set_item,
    array_lit,
    record_update_expr,
    array_update_expr,
    array_update_args,
    array_update_arg,
    ctor_call_named,
    ctor_named_args,
    ctor_named_arg,
    func_call,
    bool_lit,
    number,
    exp_part,
    real_lit,
    string_lit,
    char_code,
    const_expr,
    const_rel,
    const_add,
    const_mul,
    const_unary,
    const_primary,
    const_func_call,
    const_expr_list,
}
#[automatically_derived]
#[doc(hidden)]
#[allow(dead_code, non_camel_case_types, clippy::upper_case_acronyms)]
unsafe impl ::core::clone::TrivialClone for Rule {}
#[automatically_derived]
#[allow(dead_code, non_camel_case_types, clippy::upper_case_acronyms)]
impl ::core::clone::Clone for Rule {
    #[inline]
    fn clone(&self) -> Rule {
        *self
    }
}
#[automatically_derived]
#[allow(dead_code, non_camel_case_types, clippy::upper_case_acronyms)]
impl ::core::marker::Copy for Rule {}
#[automatically_derived]
#[allow(dead_code, non_camel_case_types, clippy::upper_case_acronyms)]
impl ::core::fmt::Debug for Rule {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        ::core::fmt::Formatter::write_str(
            f,
            match self {
                Rule::EOI => "EOI",
                Rule::WHITESPACE => "WHITESPACE",
                Rule::COMMENT => "COMMENT",
                Rule::ident => "ident",
                Rule::program => "program",
                Rule::block => "block",
                Rule::block_item => "block_item",
                Rule::const_section => "const_section",
                Rule::const_decl => "const_decl",
                Rule::type_section => "type_section",
                Rule::type_decl => "type_decl",
                Rule::type_spec => "type_spec",
                Rule::basic_type => "basic_type",
                Rule::type_ref => "type_ref",
                Rule::pointer_type => "pointer_type",
                Rule::option_type => "option_type",
                Rule::result_type => "result_type",
                Rule::enum_type => "enum_type",
                Rule::subrange_type => "subrange_type",
                Rule::set_type => "set_type",
                Rule::record_type => "record_type",
                Rule::sum_record_type => "sum_record_type",
                Rule::sum_arm_decl => "sum_arm_decl",
                Rule::sum_arm_fields => "sum_arm_fields",
                Rule::field_decl_inline => "field_decl_inline",
                Rule::variant_part => "variant_part",
                Rule::variant_case => "variant_case",
                Rule::array_type => "array_type",
                Rule::array_dim => "array_dim",
                Rule::field_decl => "field_decl",
                Rule::type_ref_or_basic => "type_ref_or_basic",
                Rule::var_section => "var_section",
                Rule::imut_section => "imut_section",
                Rule::decl_stopper => "decl_stopper",
                Rule::var_decl => "var_decl",
                Rule::routine_decl => "routine_decl",
                Rule::procedure_decl => "procedure_decl",
                Rule::function_decl => "function_decl",
                Rule::formal_params => "formal_params",
                Rule::formal_param_group => "formal_param_group",
                Rule::conformant_array_param => "conformant_array_param",
                Rule::conformant_array_dim => "conformant_array_dim",
                Rule::compound_stmt => "compound_stmt",
                Rule::stmt_list => "stmt_list",
                Rule::stmt => "stmt",
                Rule::empty_stmt => "empty_stmt",
                Rule::assign_stmt => "assign_stmt",
                Rule::read_stmt => "read_stmt",
                Rule::readln_stmt => "readln_stmt",
                Rule::for_stmt => "for_stmt",
                Rule::for_dir => "for_dir",
                Rule::case_stmt => "case_stmt",
                Rule::case_arm => "case_arm",
                Rule::case_label_list => "case_label_list",
                Rule::case_label => "case_label",
                Rule::sum_case_stmt => "sum_case_stmt",
                Rule::sum_case_else => "sum_case_else",
                Rule::sum_case_arm => "sum_case_arm",
                Rule::bind_list => "bind_list",
                Rule::proc_call_stmt => "proc_call_stmt",
                Rule::lvalue => "lvalue",
                Rule::selector => "selector",
                Rule::deref_access => "deref_access",
                Rule::field_access => "field_access",
                Rule::index_access => "index_access",
                Rule::lvalue_list => "lvalue_list",
                Rule::if_stmt => "if_stmt",
                Rule::with_stmt => "with_stmt",
                Rule::while_stmt => "while_stmt",
                Rule::repeat_stmt => "repeat_stmt",
                Rule::write_stmt => "write_stmt",
                Rule::writeln_stmt => "writeln_stmt",
                Rule::expr_list => "expr_list",
                Rule::expr => "expr",
                Rule::rel => "rel",
                Rule::rel_op => "rel_op",
                Rule::add => "add",
                Rule::add_op => "add_op",
                Rule::mul => "mul",
                Rule::mul_op => "mul_op",
                Rule::unary => "unary",
                Rule::unary_op => "unary_op",
                Rule::primary => "primary",
                Rule::cast_expr => "cast_expr",
                Rule::cond_expr => "cond_expr",
                Rule::cond_arm => "cond_arm",
                Rule::cond_else_arm => "cond_else_arm",
                Rule::cond_block => "cond_block",
                Rule::cond_stmt => "cond_stmt",
                Rule::cond_stmt_inner => "cond_stmt_inner",
                Rule::value_stmt => "value_stmt",
                Rule::none_expr => "none_expr",
                Rule::some_expr => "some_expr",
                Rule::nil_expr => "nil_expr",
                Rule::set_lit => "set_lit",
                Rule::set_item_list => "set_item_list",
                Rule::set_item => "set_item",
                Rule::array_lit => "array_lit",
                Rule::record_update_expr => "record_update_expr",
                Rule::array_update_expr => "array_update_expr",
                Rule::array_update_args => "array_update_args",
                Rule::array_update_arg => "array_update_arg",
                Rule::ctor_call_named => "ctor_call_named",
                Rule::ctor_named_args => "ctor_named_args",
                Rule::ctor_named_arg => "ctor_named_arg",
                Rule::func_call => "func_call",
                Rule::bool_lit => "bool_lit",
                Rule::number => "number",
                Rule::exp_part => "exp_part",
                Rule::real_lit => "real_lit",
                Rule::string_lit => "string_lit",
                Rule::char_code => "char_code",
                Rule::const_expr => "const_expr",
                Rule::const_rel => "const_rel",
                Rule::const_add => "const_add",
                Rule::const_mul => "const_mul",
                Rule::const_unary => "const_unary",
                Rule::const_primary => "const_primary",
                Rule::const_func_call => "const_func_call",
                Rule::const_expr_list => "const_expr_list",
            },
        )
    }
}
#[automatically_derived]
#[allow(dead_code, non_camel_case_types, clippy::upper_case_acronyms)]
impl ::core::cmp::Eq for Rule {
    #[inline]
    #[doc(hidden)]
    #[coverage(off)]
    fn assert_receiver_is_total_eq(&self) -> () {}
}
#[automatically_derived]
#[allow(dead_code, non_camel_case_types, clippy::upper_case_acronyms)]
impl ::core::hash::Hash for Rule {
    #[inline]
    fn hash<__H: ::core::hash::Hasher>(&self, state: &mut __H) -> () {
        let __self_discr = ::core::intrinsics::discriminant_value(self);
        ::core::hash::Hash::hash(&__self_discr, state)
    }
}
#[automatically_derived]
#[allow(dead_code, non_camel_case_types, clippy::upper_case_acronyms)]
impl ::core::cmp::Ord for Rule {
    #[inline]
    fn cmp(&self, other: &Rule) -> ::core::cmp::Ordering {
        let __self_discr = ::core::intrinsics::discriminant_value(self);
        let __arg1_discr = ::core::intrinsics::discriminant_value(other);
        ::core::cmp::Ord::cmp(&__self_discr, &__arg1_discr)
    }
}
#[automatically_derived]
#[allow(dead_code, non_camel_case_types, clippy::upper_case_acronyms)]
impl ::core::marker::StructuralPartialEq for Rule {}
#[automatically_derived]
#[allow(dead_code, non_camel_case_types, clippy::upper_case_acronyms)]
impl ::core::cmp::PartialEq for Rule {
    #[inline]
    fn eq(&self, other: &Rule) -> bool {
        let __self_discr = ::core::intrinsics::discriminant_value(self);
        let __arg1_discr = ::core::intrinsics::discriminant_value(other);
        __self_discr == __arg1_discr
    }
}
#[automatically_derived]
#[allow(dead_code, non_camel_case_types, clippy::upper_case_acronyms)]
impl ::core::cmp::PartialOrd for Rule {
    #[inline]
    fn partial_cmp(
        &self,
        other: &Rule,
    ) -> ::core::option::Option<::core::cmp::Ordering> {
        let __self_discr = ::core::intrinsics::discriminant_value(self);
        let __arg1_discr = ::core::intrinsics::discriminant_value(other);
        ::core::cmp::PartialOrd::partial_cmp(&__self_discr, &__arg1_discr)
    }
}
impl Rule {
    pub fn all_rules() -> &'static [Rule] {
        &[
            Rule::WHITESPACE,
            Rule::COMMENT,
            Rule::ident,
            Rule::program,
            Rule::block,
            Rule::block_item,
            Rule::const_section,
            Rule::const_decl,
            Rule::type_section,
            Rule::type_decl,
            Rule::type_spec,
            Rule::basic_type,
            Rule::type_ref,
            Rule::pointer_type,
            Rule::option_type,
            Rule::result_type,
            Rule::enum_type,
            Rule::subrange_type,
            Rule::set_type,
            Rule::record_type,
            Rule::sum_record_type,
            Rule::sum_arm_decl,
            Rule::sum_arm_fields,
            Rule::field_decl_inline,
            Rule::variant_part,
            Rule::variant_case,
            Rule::array_type,
            Rule::array_dim,
            Rule::field_decl,
            Rule::type_ref_or_basic,
            Rule::var_section,
            Rule::imut_section,
            Rule::decl_stopper,
            Rule::var_decl,
            Rule::routine_decl,
            Rule::procedure_decl,
            Rule::function_decl,
            Rule::formal_params,
            Rule::formal_param_group,
            Rule::conformant_array_param,
            Rule::conformant_array_dim,
            Rule::compound_stmt,
            Rule::stmt_list,
            Rule::stmt,
            Rule::empty_stmt,
            Rule::assign_stmt,
            Rule::read_stmt,
            Rule::readln_stmt,
            Rule::for_stmt,
            Rule::for_dir,
            Rule::case_stmt,
            Rule::case_arm,
            Rule::case_label_list,
            Rule::case_label,
            Rule::sum_case_stmt,
            Rule::sum_case_else,
            Rule::sum_case_arm,
            Rule::bind_list,
            Rule::proc_call_stmt,
            Rule::lvalue,
            Rule::selector,
            Rule::deref_access,
            Rule::field_access,
            Rule::index_access,
            Rule::lvalue_list,
            Rule::if_stmt,
            Rule::with_stmt,
            Rule::while_stmt,
            Rule::repeat_stmt,
            Rule::write_stmt,
            Rule::writeln_stmt,
            Rule::expr_list,
            Rule::expr,
            Rule::rel,
            Rule::rel_op,
            Rule::add,
            Rule::add_op,
            Rule::mul,
            Rule::mul_op,
            Rule::unary,
            Rule::unary_op,
            Rule::primary,
            Rule::cast_expr,
            Rule::cond_expr,
            Rule::cond_arm,
            Rule::cond_else_arm,
            Rule::cond_block,
            Rule::cond_stmt,
            Rule::cond_stmt_inner,
            Rule::value_stmt,
            Rule::none_expr,
            Rule::some_expr,
            Rule::nil_expr,
            Rule::set_lit,
            Rule::set_item_list,
            Rule::set_item,
            Rule::array_lit,
            Rule::record_update_expr,
            Rule::array_update_expr,
            Rule::array_update_args,
            Rule::array_update_arg,
            Rule::ctor_call_named,
            Rule::ctor_named_args,
            Rule::ctor_named_arg,
            Rule::func_call,
            Rule::bool_lit,
            Rule::number,
            Rule::exp_part,
            Rule::real_lit,
            Rule::string_lit,
            Rule::char_code,
            Rule::const_expr,
            Rule::const_rel,
            Rule::const_add,
            Rule::const_mul,
            Rule::const_unary,
            Rule::const_primary,
            Rule::const_func_call,
            Rule::const_expr_list,
        ]
    }
}
#[allow(clippy::all)]
impl ::pest::Parser<Rule> for PascalParser {
    fn parse<'i>(
        rule: Rule,
        input: &'i str,
    ) -> ::std::result::Result<
        ::pest::iterators::Pairs<'i, Rule>,
        ::pest::error::Error<Rule>,
    > {
        mod rules {
            #![allow(clippy::upper_case_acronyms)]
            pub mod hidden {
                use super::super::Rule;
                #[inline]
                #[allow(dead_code, non_snake_case, unused_variables)]
                pub fn skip(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    if state.atomicity() == ::pest::Atomicity::NonAtomic {
                        state
                            .sequence(|state| {
                                state
                                    .repeat(|state| super::visible::WHITESPACE(state))
                                    .and_then(|state| {
                                        state
                                            .repeat(|state| {
                                                state
                                                    .sequence(|state| {
                                                        super::visible::COMMENT(state)
                                                            .and_then(|state| {
                                                                state.repeat(|state| super::visible::WHITESPACE(state))
                                                            })
                                                    })
                                            })
                                    })
                            })
                    } else {
                        Ok(state)
                    }
                }
            }
            pub mod visible {
                use super::super::Rule;
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn WHITESPACE(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .atomic(
                            ::pest::Atomicity::Atomic,
                            |state| {
                                state
                                    .match_string(" ")
                                    .or_else(|state| { state.match_string("\t") })
                                    .or_else(|state| { state.match_string("\r") })
                                    .or_else(|state| { state.match_string("\n") })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn COMMENT(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .atomic(
                            ::pest::Atomicity::Atomic,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_string("{")
                                            .and_then(|state| {
                                                state
                                                    .repeat(|state| {
                                                        state
                                                            .sequence(|state| {
                                                                state
                                                                    .lookahead(false, |state| { state.match_string("}") })
                                                                    .and_then(|state| { self::ANY(state) })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { state.match_string("}") })
                                    })
                                    .or_else(|state| {
                                        state
                                            .sequence(|state| {
                                                state
                                                    .match_string("(*")
                                                    .and_then(|state| {
                                                        state
                                                            .repeat(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .lookahead(false, |state| { state.match_string("*)") })
                                                                            .and_then(|state| { self::ANY(state) })
                                                                    })
                                                            })
                                                    })
                                                    .and_then(|state| { state.match_string("*)") })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn ident(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::ident,
                            |state| {
                                state
                                    .atomic(
                                        ::pest::Atomicity::Atomic,
                                        |state| {
                                            state
                                                .sequence(|state| {
                                                    self::ASCII_ALPHA(state)
                                                        .or_else(|state| { state.match_string("_") })
                                                        .and_then(|state| {
                                                            state
                                                                .repeat(|state| {
                                                                    self::ASCII_ALPHANUMERIC(state)
                                                                        .or_else(|state| { state.match_string("_") })
                                                                })
                                                        })
                                                })
                                        },
                                    )
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn program(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::program,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::SOI(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("program") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::ident(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(";") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::block(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(".") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::EOI(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn block(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::block,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .sequence(|state| {
                                                state
                                                    .optional(|state| {
                                                        self::block_item(state)
                                                            .and_then(|state| {
                                                                state
                                                                    .repeat(|state| {
                                                                        state
                                                                            .sequence(|state| {
                                                                                super::hidden::skip(state)
                                                                                    .and_then(|state| { self::block_item(state) })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::compound_stmt(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn block_item(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    self::const_section(state)
                        .or_else(|state| { self::type_section(state) })
                        .or_else(|state| { self::var_section(state) })
                        .or_else(|state| { self::imut_section(state) })
                        .or_else(|state| { self::routine_decl(state) })
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn const_section(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::const_section,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("const")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::const_decl(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                self::const_decl(state)
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| { self::const_decl(state) })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn const_decl(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::const_decl,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .optional(|state| {
                                                        state
                                                            .sequence(|state| {
                                                                state
                                                                    .match_string(":")
                                                                    .and_then(|state| { super::hidden::skip(state) })
                                                                    .and_then(|state| { self::type_ref_or_basic(state) })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("=") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::const_expr(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(";") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn type_section(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::type_section,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("type")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_decl(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                self::type_decl(state)
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| { self::type_decl(state) })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn type_decl(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::type_decl,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("=") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_spec(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(";") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn type_spec(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    self::set_type(state)
                        .or_else(|state| { self::subrange_type(state) })
                        .or_else(|state| { self::sum_record_type(state) })
                        .or_else(|state| { self::enum_type(state) })
                        .or_else(|state| { self::record_type(state) })
                        .or_else(|state| { self::array_type(state) })
                        .or_else(|state| { self::result_type(state) })
                        .or_else(|state| { self::option_type(state) })
                        .or_else(|state| { self::pointer_type(state) })
                        .or_else(|state| { self::type_ref(state) })
                        .or_else(|state| { self::basic_type(state) })
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn basic_type(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::basic_type,
                            |state| {
                                state
                                    .match_insensitive("integer")
                                    .or_else(|state| { state.match_insensitive("boolean") })
                                    .or_else(|state| { state.match_insensitive("char") })
                                    .or_else(|state| { state.match_insensitive("real") })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn type_ref(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state.rule(Rule::type_ref, |state| { self::ident(state) })
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn pointer_type(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::pointer_type,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_string("^")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::ident(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn option_type(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::option_type,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("option")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("of") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_ref_or_basic(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn result_type(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::result_type,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("result")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("of") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_ref_or_basic(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(",") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_ref_or_basic(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn enum_type(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::enum_type,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_string("(")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::ident(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(",")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::ident(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(",")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::ident(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn subrange_type(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::subrange_type,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::const_expr(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("..") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::const_expr(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn set_type(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::set_type,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("set")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("of") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_ref_or_basic(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn record_type(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::record_type,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("record")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                self::field_decl(state)
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| { self::field_decl(state) })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::variant_part(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("end") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn sum_record_type(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::sum_record_type,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("record")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("of") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::sum_arm_decl(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(";")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::sum_arm_decl(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(";")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::sum_arm_decl(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { state.match_string(";") })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("end") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn sum_arm_decl(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::sum_arm_decl,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("(") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::sum_arm_fields(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn sum_arm_fields(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::sum_arm_fields,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::field_decl_inline(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(";")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::field_decl_inline(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(";")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::field_decl_inline(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { state.match_string(";") })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn field_decl_inline(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::field_decl_inline,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_ref_or_basic(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn variant_part(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::variant_part,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("case")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::ident(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .optional(|state| {
                                                        state
                                                            .sequence(|state| {
                                                                state
                                                                    .match_string(":")
                                                                    .and_then(|state| { super::hidden::skip(state) })
                                                                    .and_then(|state| { self::type_ref_or_basic(state) })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("of") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::variant_case(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(";")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::variant_case(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(";")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::variant_case(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { state.match_string(";") })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn variant_case(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::variant_case,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::case_label_list(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("(") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                self::field_decl(state)
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| { self::field_decl(state) })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::variant_part(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn array_type(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::array_type,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("array")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("[") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::array_dim(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(",")
                                                                            .or_else(|state| { state.match_string(";") })
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::array_dim(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(",")
                                                                                                            .or_else(|state| { state.match_string(";") })
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::array_dim(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("]") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("of") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_ref_or_basic(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn array_dim(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::array_dim,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::const_expr(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .optional(|state| {
                                                        state
                                                            .sequence(|state| {
                                                                state
                                                                    .match_string("..")
                                                                    .and_then(|state| { super::hidden::skip(state) })
                                                                    .and_then(|state| { self::const_expr(state) })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn field_decl(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::field_decl,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_ref_or_basic(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(";") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn type_ref_or_basic(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    self::set_type(state)
                        .or_else(|state| { self::array_type(state) })
                        .or_else(|state| { self::subrange_type(state) })
                        .or_else(|state| { self::result_type(state) })
                        .or_else(|state| { self::option_type(state) })
                        .or_else(|state| { self::pointer_type(state) })
                        .or_else(|state| { self::type_ref(state) })
                        .or_else(|state| { self::basic_type(state) })
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn var_section(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::var_section,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("var")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::var_decl(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                self::var_decl(state)
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| { self::var_decl(state) })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn imut_section(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::imut_section,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("imut")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::var_decl(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                self::var_decl(state)
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| { self::var_decl(state) })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn decl_stopper(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::decl_stopper,
                            |state| {
                                state
                                    .match_insensitive("imut")
                                    .or_else(|state| { state.match_insensitive("procedure") })
                                    .or_else(|state| { state.match_insensitive("function") })
                                    .or_else(|state| { state.match_insensitive("begin") })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn var_decl(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::var_decl,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_ref_or_basic(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(";") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn routine_decl(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    self::procedure_decl(state)
                        .or_else(|state| { self::function_decl(state) })
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn procedure_decl(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::procedure_decl,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("procedure")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::ident(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::formal_params(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(";") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::block(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(";") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn function_decl(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::function_decl,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("function")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::ident(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::formal_params(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_ref_or_basic(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(";") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::block(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(";") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn formal_params(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::formal_params,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_string("(")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::formal_param_group(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(";")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::formal_param_group(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(";")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::formal_param_group(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn formal_param_group(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::formal_param_group,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .optional(|state| { state.match_insensitive("var") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::ident(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(",")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::ident(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(",")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::ident(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                self::conformant_array_param(state)
                                                    .or_else(|state| { self::type_ref_or_basic(state) })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn conformant_array_param(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::conformant_array_param,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_string("array")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("[") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::conformant_array_dim(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(";")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::conformant_array_dim(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(";")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::conformant_array_dim(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("]") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("of") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_ref_or_basic(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn conformant_array_dim(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::conformant_array_dim,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("..") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::ident(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_ref_or_basic(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn compound_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::compound_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("begin")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::stmt_list(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("end") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn stmt_list(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::stmt_list,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::stmt(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(";")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::stmt(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(";")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::stmt(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { state.match_string(";") })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    self::compound_stmt(state)
                        .or_else(|state| { self::assign_stmt(state) })
                        .or_else(|state| { self::read_stmt(state) })
                        .or_else(|state| { self::readln_stmt(state) })
                        .or_else(|state| { self::for_stmt(state) })
                        .or_else(|state| { self::write_stmt(state) })
                        .or_else(|state| { self::writeln_stmt(state) })
                        .or_else(|state| { self::sum_case_stmt(state) })
                        .or_else(|state| { self::case_stmt(state) })
                        .or_else(|state| { self::proc_call_stmt(state) })
                        .or_else(|state| { self::if_stmt(state) })
                        .or_else(|state| { self::with_stmt(state) })
                        .or_else(|state| { self::while_stmt(state) })
                        .or_else(|state| { self::repeat_stmt(state) })
                        .or_else(|state| { self::empty_stmt(state) })
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn empty_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state.rule(Rule::empty_stmt, |state| { state.match_string("") })
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn assign_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::assign_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::lvalue(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":=") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn read_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::read_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("Read")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("(") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr_list(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn readln_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::readln_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("ReadLn")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .optional(|state| {
                                                        state
                                                            .sequence(|state| {
                                                                state
                                                                    .match_string("(")
                                                                    .and_then(|state| { super::hidden::skip(state) })
                                                                    .and_then(|state| { state.match_string(")") })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn for_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::for_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("for")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::ident(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":=") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::for_dir(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("do") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::stmt(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn for_dir(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::for_dir,
                            |state| {
                                state
                                    .match_insensitive("to")
                                    .or_else(|state| { state.match_insensitive("downto") })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn case_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::case_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("case")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("of") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        self::case_arm(state)
                                                            .and_then(|state| { super::hidden::skip(state) })
                                                            .and_then(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .optional(|state| {
                                                                                self::case_arm(state)
                                                                                    .and_then(|state| {
                                                                                        state
                                                                                            .repeat(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        super::hidden::skip(state)
                                                                                                            .and_then(|state| { self::case_arm(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .optional(|state| {
                                                        state
                                                            .sequence(|state| {
                                                                state
                                                                    .match_insensitive("else")
                                                                    .and_then(|state| { super::hidden::skip(state) })
                                                                    .and_then(|state| { self::stmt(state) })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("end") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn case_arm(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::case_arm,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::case_label_list(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::stmt(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { state.match_string(";") })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn case_label_list(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::case_label_list,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::case_label(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(",")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::case_label(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(",")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::case_label(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn case_label(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::case_label,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::const_expr(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .optional(|state| {
                                                        state
                                                            .sequence(|state| {
                                                                state
                                                                    .match_string("..")
                                                                    .and_then(|state| { super::hidden::skip(state) })
                                                                    .and_then(|state| { self::const_expr(state) })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn sum_case_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::sum_case_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("case")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("of") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::sum_case_arm(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(";")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::sum_case_arm(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(";")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::sum_case_arm(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .optional(|state| {
                                                        state
                                                            .sequence(|state| {
                                                                state
                                                                    .match_string(";")
                                                                    .and_then(|state| { super::hidden::skip(state) })
                                                                    .and_then(|state| { self::sum_case_else(state) })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { state.match_string(";") })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("end") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn sum_case_else(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::sum_case_else,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("else")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::stmt(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn sum_case_arm(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::sum_case_arm,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("(") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::bind_list(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::stmt(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn bind_list(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::bind_list,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(",")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::ident(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(",")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::ident(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn proc_call_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::proc_call_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("(") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::expr_list(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn lvalue(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::lvalue,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                self::selector(state)
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| { self::selector(state) })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn selector(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    self::deref_access(state)
                        .or_else(|state| { self::field_access(state) })
                        .or_else(|state| { self::index_access(state) })
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn deref_access(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state.rule(Rule::deref_access, |state| { state.match_string("^") })
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn field_access(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::field_access,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_string(".")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::ident(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn index_access(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::index_access,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_string("[")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(",")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::expr(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(",")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::expr(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("]") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn lvalue_list(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::lvalue_list,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::lvalue(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(",")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::lvalue(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(",")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::lvalue(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn if_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::if_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("if")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("then") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::stmt(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .optional(|state| {
                                                        state
                                                            .sequence(|state| {
                                                                state
                                                                    .match_insensitive("else")
                                                                    .and_then(|state| { super::hidden::skip(state) })
                                                                    .and_then(|state| { self::stmt(state) })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn with_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::with_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("with")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::lvalue(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(",")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::lvalue(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(",")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::lvalue(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("do") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::stmt(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn while_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::while_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("while")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("do") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::stmt(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn repeat_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::repeat_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("repeat")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::stmt_list(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("until") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn write_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::write_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("Write")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("(") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::expr_list(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn writeln_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::writeln_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("WriteLn")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .optional(|state| {
                                                        state
                                                            .sequence(|state| {
                                                                state
                                                                    .match_string("(")
                                                                    .and_then(|state| { super::hidden::skip(state) })
                                                                    .and_then(|state| {
                                                                        state.optional(|state| { self::expr_list(state) })
                                                                    })
                                                                    .and_then(|state| { super::hidden::skip(state) })
                                                                    .and_then(|state| { state.match_string(")") })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn expr_list(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::expr_list,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::expr(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(",")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::expr(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(",")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::expr(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn expr(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    self::rel(state)
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn rel(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::rel,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::add(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .optional(|state| {
                                                        state
                                                            .sequence(|state| {
                                                                self::rel_op(state)
                                                                    .and_then(|state| { super::hidden::skip(state) })
                                                                    .and_then(|state| { self::add(state) })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn rel_op(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::rel_op,
                            |state| {
                                state
                                    .match_string("<=")
                                    .or_else(|state| { state.match_string(">=") })
                                    .or_else(|state| { state.match_string("<>") })
                                    .or_else(|state| { state.match_string("=") })
                                    .or_else(|state| { state.match_string("<") })
                                    .or_else(|state| { state.match_string(">") })
                                    .or_else(|state| { state.match_insensitive("in") })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn add(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::add,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::mul(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        self::add_op(state)
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::mul(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        self::add_op(state)
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::mul(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn add_op(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::add_op,
                            |state| {
                                state
                                    .match_string("+")
                                    .or_else(|state| { state.match_string("-") })
                                    .or_else(|state| { state.match_insensitive("or") })
                                    .or_else(|state| { state.match_insensitive("xor") })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn mul(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::mul,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::unary(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        self::mul_op(state)
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::unary(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        self::mul_op(state)
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::unary(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn mul_op(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::mul_op,
                            |state| {
                                state
                                    .match_string("*")
                                    .or_else(|state| { state.match_string("/") })
                                    .or_else(|state| { state.match_insensitive("div") })
                                    .or_else(|state| { state.match_insensitive("mod") })
                                    .or_else(|state| { state.match_insensitive("and") })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn unary(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::unary,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::unary_op(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::unary(state) })
                                    })
                                    .or_else(|state| { self::primary(state) })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn unary_op(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::unary_op,
                            |state| {
                                state
                                    .match_string("-")
                                    .or_else(|state| { state.match_insensitive("not") })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn primary(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::primary,
                            |state| {
                                self::cond_expr(state)
                                    .or_else(|state| { self::nil_expr(state) })
                                    .or_else(|state| { self::none_expr(state) })
                                    .or_else(|state| { self::some_expr(state) })
                                    .or_else(|state| { self::cast_expr(state) })
                                    .or_else(|state| { self::set_lit(state) })
                                    .or_else(|state| { self::bool_lit(state) })
                                    .or_else(|state| { self::real_lit(state) })
                                    .or_else(|state| { self::number(state) })
                                    .or_else(|state| { self::string_lit(state) })
                                    .or_else(|state| { self::char_code(state) })
                                    .or_else(|state| { self::array_lit(state) })
                                    .or_else(|state| { self::array_update_expr(state) })
                                    .or_else(|state| { self::record_update_expr(state) })
                                    .or_else(|state| { self::ctor_call_named(state) })
                                    .or_else(|state| { self::func_call(state) })
                                    .or_else(|state| { self::lvalue(state) })
                                    .or_else(|state| {
                                        state
                                            .sequence(|state| {
                                                state
                                                    .match_string("(")
                                                    .and_then(|state| { super::hidden::skip(state) })
                                                    .and_then(|state| { self::expr(state) })
                                                    .and_then(|state| { super::hidden::skip(state) })
                                                    .and_then(|state| { state.match_string(")") })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn cast_expr(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::cast_expr,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("cast")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("(") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::type_ref_or_basic(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(",") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn cond_expr(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::cond_expr,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("cond")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("(") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::cond_arm(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(";")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::cond_arm(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(";")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::cond_arm(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(";") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::cond_else_arm(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn cond_arm(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::cond_arm,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .lookahead(
                                                false,
                                                |state| {
                                                    state
                                                        .sequence(|state| {
                                                            state
                                                                .match_insensitive("else")
                                                                .and_then(|state| { super::hidden::skip(state) })
                                                                .and_then(|state| { state.match_string(":") })
                                                        })
                                                },
                                            )
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::cond_block(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn cond_else_arm(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::cond_else_arm,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("else")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::cond_block(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn cond_block(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::cond_block,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("begin")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                self::cond_stmt(state)
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| { self::cond_stmt(state) })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::value_stmt(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("end") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn cond_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::cond_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::cond_stmt_inner(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(";") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn cond_stmt_inner(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    self::compound_stmt(state)
                        .or_else(|state| { self::assign_stmt(state) })
                        .or_else(|state| { self::read_stmt(state) })
                        .or_else(|state| { self::readln_stmt(state) })
                        .or_else(|state| { self::for_stmt(state) })
                        .or_else(|state| { self::write_stmt(state) })
                        .or_else(|state| { self::writeln_stmt(state) })
                        .or_else(|state| { self::sum_case_stmt(state) })
                        .or_else(|state| { self::case_stmt(state) })
                        .or_else(|state| { self::proc_call_stmt(state) })
                        .or_else(|state| { self::if_stmt(state) })
                        .or_else(|state| { self::with_stmt(state) })
                        .or_else(|state| { self::while_stmt(state) })
                        .or_else(|state| { self::repeat_stmt(state) })
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn value_stmt(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::value_stmt,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("value")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn none_expr(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::none_expr,
                            |state| { state.match_insensitive("none") },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn some_expr(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::some_expr,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_insensitive("some")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("(") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn nil_expr(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(Rule::nil_expr, |state| { state.match_insensitive("nil") })
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn set_lit(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::set_lit,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_string("[")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::set_item_list(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("]") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn set_item_list(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::set_item_list,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::set_item(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(",")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::set_item(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(",")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::set_item(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn set_item(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::set_item,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::expr(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .optional(|state| {
                                                        state
                                                            .sequence(|state| {
                                                                state
                                                                    .match_string("..")
                                                                    .and_then(|state| { super::hidden::skip(state) })
                                                                    .and_then(|state| { self::expr(state) })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn array_lit(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::array_lit,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_string("[")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::expr_list(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("]") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn record_update_expr(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::record_update_expr,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("with") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("(") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::ctor_named_args(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn array_update_expr(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::array_update_expr,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_insensitive("with") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("[") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::array_update_args(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("]") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn array_update_args(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::array_update_args,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::array_update_arg(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(",")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::array_update_arg(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(",")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::array_update_arg(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { state.match_string(",") })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn array_update_arg(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::array_update_arg,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::expr(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":=") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn ctor_call_named(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::ctor_call_named,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("(") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::ctor_named_args(state) })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn ctor_named_args(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::ctor_named_args,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ctor_named_arg(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(";")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::ctor_named_arg(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(";")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::ctor_named_arg(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { state.match_string(";") })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn ctor_named_arg(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::ctor_named_arg,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(":=") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::expr(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn func_call(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::func_call,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("(") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::expr_list(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn bool_lit(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::bool_lit,
                            |state| {
                                state
                                    .match_insensitive("false")
                                    .or_else(|state| { state.match_insensitive("true") })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn number(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::number,
                            |state| {
                                state
                                    .atomic(
                                        ::pest::Atomicity::Atomic,
                                        |state| {
                                            state
                                                .sequence(|state| {
                                                    state
                                                        .match_string("0x")
                                                        .and_then(|state| { self::ASCII_HEX_DIGIT(state) })
                                                        .and_then(|state| {
                                                            state.repeat(|state| { self::ASCII_HEX_DIGIT(state) })
                                                        })
                                                })
                                                .or_else(|state| {
                                                    state
                                                        .sequence(|state| {
                                                            state
                                                                .match_string("$")
                                                                .and_then(|state| { self::ASCII_HEX_DIGIT(state) })
                                                                .and_then(|state| {
                                                                    state.repeat(|state| { self::ASCII_HEX_DIGIT(state) })
                                                                })
                                                        })
                                                })
                                                .or_else(|state| {
                                                    state
                                                        .sequence(|state| {
                                                            self::ASCII_DIGIT(state)
                                                                .and_then(|state| {
                                                                    state.repeat(|state| { self::ASCII_DIGIT(state) })
                                                                })
                                                        })
                                                })
                                        },
                                    )
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn exp_part(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .sequence(|state| {
                            state
                                .match_string("e")
                                .or_else(|state| { state.match_string("E") })
                                .and_then(|state| { super::hidden::skip(state) })
                                .and_then(|state| {
                                    state
                                        .optional(|state| {
                                            state
                                                .match_string("+")
                                                .or_else(|state| { state.match_string("-") })
                                        })
                                })
                                .and_then(|state| { super::hidden::skip(state) })
                                .and_then(|state| { self::ASCII_DIGIT(state) })
                                .and_then(|state| { super::hidden::skip(state) })
                                .and_then(|state| {
                                    state
                                        .sequence(|state| {
                                            state
                                                .optional(|state| {
                                                    self::ASCII_DIGIT(state)
                                                        .and_then(|state| {
                                                            state
                                                                .repeat(|state| {
                                                                    state
                                                                        .sequence(|state| {
                                                                            super::hidden::skip(state)
                                                                                .and_then(|state| { self::ASCII_DIGIT(state) })
                                                                        })
                                                                })
                                                        })
                                                })
                                        })
                                })
                        })
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn real_lit(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::real_lit,
                            |state| {
                                state
                                    .atomic(
                                        ::pest::Atomicity::Atomic,
                                        |state| {
                                            state
                                                .sequence(|state| {
                                                    state
                                                        .sequence(|state| {
                                                            self::ASCII_DIGIT(state)
                                                                .and_then(|state| {
                                                                    state.repeat(|state| { self::ASCII_DIGIT(state) })
                                                                })
                                                        })
                                                        .and_then(|state| { state.match_string(".") })
                                                        .and_then(|state| {
                                                            state
                                                                .sequence(|state| {
                                                                    self::ASCII_DIGIT(state)
                                                                        .and_then(|state| {
                                                                            state.repeat(|state| { self::ASCII_DIGIT(state) })
                                                                        })
                                                                })
                                                        })
                                                        .and_then(|state| {
                                                            state.optional(|state| { self::exp_part(state) })
                                                        })
                                                })
                                                .or_else(|state| {
                                                    state
                                                        .sequence(|state| {
                                                            state
                                                                .match_string(".")
                                                                .and_then(|state| {
                                                                    state
                                                                        .sequence(|state| {
                                                                            self::ASCII_DIGIT(state)
                                                                                .and_then(|state| {
                                                                                    state.repeat(|state| { self::ASCII_DIGIT(state) })
                                                                                })
                                                                        })
                                                                })
                                                                .and_then(|state| {
                                                                    state.optional(|state| { self::exp_part(state) })
                                                                })
                                                        })
                                                })
                                                .or_else(|state| {
                                                    state
                                                        .sequence(|state| {
                                                            state
                                                                .sequence(|state| {
                                                                    self::ASCII_DIGIT(state)
                                                                        .and_then(|state| {
                                                                            state.repeat(|state| { self::ASCII_DIGIT(state) })
                                                                        })
                                                                })
                                                                .and_then(|state| { self::exp_part(state) })
                                                        })
                                                })
                                        },
                                    )
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn string_lit(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::string_lit,
                            |state| {
                                state
                                    .atomic(
                                        ::pest::Atomicity::Atomic,
                                        |state| {
                                            state
                                                .sequence(|state| {
                                                    state
                                                        .match_string("'")
                                                        .and_then(|state| {
                                                            state
                                                                .repeat(|state| {
                                                                    state
                                                                        .match_string("''")
                                                                        .or_else(|state| {
                                                                            state
                                                                                .sequence(|state| {
                                                                                    state
                                                                                        .lookahead(false, |state| { state.match_string("'") })
                                                                                        .and_then(|state| { self::ANY(state) })
                                                                                })
                                                                        })
                                                                })
                                                        })
                                                        .and_then(|state| { state.match_string("'") })
                                                })
                                        },
                                    )
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn char_code(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::char_code,
                            |state| {
                                state
                                    .sequence(|state| {
                                        state
                                            .match_string("#")
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::number(state) })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn const_expr(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    self::const_rel(state)
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn const_rel(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::const_rel,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::const_add(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .optional(|state| {
                                                        state
                                                            .sequence(|state| {
                                                                self::rel_op(state)
                                                                    .and_then(|state| { super::hidden::skip(state) })
                                                                    .and_then(|state| { self::const_add(state) })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn const_add(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::const_add,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::const_mul(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        self::add_op(state)
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::const_mul(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        self::add_op(state)
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::const_mul(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn const_mul(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::const_mul,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::const_unary(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        self::mul_op(state)
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::const_unary(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        self::mul_op(state)
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::const_unary(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn const_unary(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::const_unary,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::unary_op(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { self::const_unary(state) })
                                    })
                                    .or_else(|state| { self::const_primary(state) })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn const_primary(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::const_primary,
                            |state| {
                                self::bool_lit(state)
                                    .or_else(|state| { self::real_lit(state) })
                                    .or_else(|state| { self::number(state) })
                                    .or_else(|state| { self::string_lit(state) })
                                    .or_else(|state| { self::char_code(state) })
                                    .or_else(|state| { self::const_func_call(state) })
                                    .or_else(|state| { self::ident(state) })
                                    .or_else(|state| {
                                        state
                                            .sequence(|state| {
                                                state
                                                    .match_string("(")
                                                    .and_then(|state| { super::hidden::skip(state) })
                                                    .and_then(|state| { self::const_expr(state) })
                                                    .and_then(|state| { super::hidden::skip(state) })
                                                    .and_then(|state| { state.match_string(")") })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn const_func_call(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::const_func_call,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::ident(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string("(") })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state.optional(|state| { self::const_expr_list(state) })
                                            })
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| { state.match_string(")") })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(non_snake_case, unused_variables)]
                pub fn const_expr_list(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .rule(
                            Rule::const_expr_list,
                            |state| {
                                state
                                    .sequence(|state| {
                                        self::const_expr(state)
                                            .and_then(|state| { super::hidden::skip(state) })
                                            .and_then(|state| {
                                                state
                                                    .sequence(|state| {
                                                        state
                                                            .optional(|state| {
                                                                state
                                                                    .sequence(|state| {
                                                                        state
                                                                            .match_string(",")
                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                            .and_then(|state| { self::const_expr(state) })
                                                                    })
                                                                    .and_then(|state| {
                                                                        state
                                                                            .repeat(|state| {
                                                                                state
                                                                                    .sequence(|state| {
                                                                                        super::hidden::skip(state)
                                                                                            .and_then(|state| {
                                                                                                state
                                                                                                    .sequence(|state| {
                                                                                                        state
                                                                                                            .match_string(",")
                                                                                                            .and_then(|state| { super::hidden::skip(state) })
                                                                                                            .and_then(|state| { self::const_expr(state) })
                                                                                                    })
                                                                                            })
                                                                                    })
                                                                            })
                                                                    })
                                                            })
                                                    })
                                            })
                                    })
                            },
                        )
                }
                #[inline]
                #[allow(dead_code, non_snake_case, unused_variables)]
                pub fn ANY(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state.skip(1)
                }
                #[inline]
                #[allow(dead_code, non_snake_case, unused_variables)]
                pub fn EOI(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state.rule(Rule::EOI, |state| state.end_of_input())
                }
                #[inline]
                #[allow(dead_code, non_snake_case, unused_variables)]
                pub fn SOI(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state.start_of_input()
                }
                #[inline]
                #[allow(dead_code, non_snake_case, unused_variables)]
                pub fn ASCII_DIGIT(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state.match_range('0'..'9')
                }
                #[inline]
                #[allow(dead_code, non_snake_case, unused_variables)]
                pub fn ASCII_HEX_DIGIT(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .match_range('0'..'9')
                        .or_else(|state| state.match_range('a'..'f'))
                        .or_else(|state| state.match_range('A'..'F'))
                }
                #[inline]
                #[allow(dead_code, non_snake_case, unused_variables)]
                pub fn ASCII_ALPHA(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .match_range('a'..'z')
                        .or_else(|state| state.match_range('A'..'Z'))
                }
                #[inline]
                #[allow(dead_code, non_snake_case, unused_variables)]
                pub fn ASCII_ALPHANUMERIC(
                    state: ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                ) -> ::pest::ParseResult<
                    ::std::boxed::Box<::pest::ParserState<'_, Rule>>,
                > {
                    state
                        .match_range('a'..'z')
                        .or_else(|state| state.match_range('A'..'Z'))
                        .or_else(|state| state.match_range('0'..'9'))
                }
            }
            pub use self::visible::*;
        }
        ::pest::state(
            input,
            |state| {
                match rule {
                    Rule::WHITESPACE => rules::WHITESPACE(state),
                    Rule::COMMENT => rules::COMMENT(state),
                    Rule::ident => rules::ident(state),
                    Rule::program => rules::program(state),
                    Rule::block => rules::block(state),
                    Rule::block_item => rules::block_item(state),
                    Rule::const_section => rules::const_section(state),
                    Rule::const_decl => rules::const_decl(state),
                    Rule::type_section => rules::type_section(state),
                    Rule::type_decl => rules::type_decl(state),
                    Rule::type_spec => rules::type_spec(state),
                    Rule::basic_type => rules::basic_type(state),
                    Rule::type_ref => rules::type_ref(state),
                    Rule::pointer_type => rules::pointer_type(state),
                    Rule::option_type => rules::option_type(state),
                    Rule::result_type => rules::result_type(state),
                    Rule::enum_type => rules::enum_type(state),
                    Rule::subrange_type => rules::subrange_type(state),
                    Rule::set_type => rules::set_type(state),
                    Rule::record_type => rules::record_type(state),
                    Rule::sum_record_type => rules::sum_record_type(state),
                    Rule::sum_arm_decl => rules::sum_arm_decl(state),
                    Rule::sum_arm_fields => rules::sum_arm_fields(state),
                    Rule::field_decl_inline => rules::field_decl_inline(state),
                    Rule::variant_part => rules::variant_part(state),
                    Rule::variant_case => rules::variant_case(state),
                    Rule::array_type => rules::array_type(state),
                    Rule::array_dim => rules::array_dim(state),
                    Rule::field_decl => rules::field_decl(state),
                    Rule::type_ref_or_basic => rules::type_ref_or_basic(state),
                    Rule::var_section => rules::var_section(state),
                    Rule::imut_section => rules::imut_section(state),
                    Rule::decl_stopper => rules::decl_stopper(state),
                    Rule::var_decl => rules::var_decl(state),
                    Rule::routine_decl => rules::routine_decl(state),
                    Rule::procedure_decl => rules::procedure_decl(state),
                    Rule::function_decl => rules::function_decl(state),
                    Rule::formal_params => rules::formal_params(state),
                    Rule::formal_param_group => rules::formal_param_group(state),
                    Rule::conformant_array_param => rules::conformant_array_param(state),
                    Rule::conformant_array_dim => rules::conformant_array_dim(state),
                    Rule::compound_stmt => rules::compound_stmt(state),
                    Rule::stmt_list => rules::stmt_list(state),
                    Rule::stmt => rules::stmt(state),
                    Rule::empty_stmt => rules::empty_stmt(state),
                    Rule::assign_stmt => rules::assign_stmt(state),
                    Rule::read_stmt => rules::read_stmt(state),
                    Rule::readln_stmt => rules::readln_stmt(state),
                    Rule::for_stmt => rules::for_stmt(state),
                    Rule::for_dir => rules::for_dir(state),
                    Rule::case_stmt => rules::case_stmt(state),
                    Rule::case_arm => rules::case_arm(state),
                    Rule::case_label_list => rules::case_label_list(state),
                    Rule::case_label => rules::case_label(state),
                    Rule::sum_case_stmt => rules::sum_case_stmt(state),
                    Rule::sum_case_else => rules::sum_case_else(state),
                    Rule::sum_case_arm => rules::sum_case_arm(state),
                    Rule::bind_list => rules::bind_list(state),
                    Rule::proc_call_stmt => rules::proc_call_stmt(state),
                    Rule::lvalue => rules::lvalue(state),
                    Rule::selector => rules::selector(state),
                    Rule::deref_access => rules::deref_access(state),
                    Rule::field_access => rules::field_access(state),
                    Rule::index_access => rules::index_access(state),
                    Rule::lvalue_list => rules::lvalue_list(state),
                    Rule::if_stmt => rules::if_stmt(state),
                    Rule::with_stmt => rules::with_stmt(state),
                    Rule::while_stmt => rules::while_stmt(state),
                    Rule::repeat_stmt => rules::repeat_stmt(state),
                    Rule::write_stmt => rules::write_stmt(state),
                    Rule::writeln_stmt => rules::writeln_stmt(state),
                    Rule::expr_list => rules::expr_list(state),
                    Rule::expr => rules::expr(state),
                    Rule::rel => rules::rel(state),
                    Rule::rel_op => rules::rel_op(state),
                    Rule::add => rules::add(state),
                    Rule::add_op => rules::add_op(state),
                    Rule::mul => rules::mul(state),
                    Rule::mul_op => rules::mul_op(state),
                    Rule::unary => rules::unary(state),
                    Rule::unary_op => rules::unary_op(state),
                    Rule::primary => rules::primary(state),
                    Rule::cast_expr => rules::cast_expr(state),
                    Rule::cond_expr => rules::cond_expr(state),
                    Rule::cond_arm => rules::cond_arm(state),
                    Rule::cond_else_arm => rules::cond_else_arm(state),
                    Rule::cond_block => rules::cond_block(state),
                    Rule::cond_stmt => rules::cond_stmt(state),
                    Rule::cond_stmt_inner => rules::cond_stmt_inner(state),
                    Rule::value_stmt => rules::value_stmt(state),
                    Rule::none_expr => rules::none_expr(state),
                    Rule::some_expr => rules::some_expr(state),
                    Rule::nil_expr => rules::nil_expr(state),
                    Rule::set_lit => rules::set_lit(state),
                    Rule::set_item_list => rules::set_item_list(state),
                    Rule::set_item => rules::set_item(state),
                    Rule::array_lit => rules::array_lit(state),
                    Rule::record_update_expr => rules::record_update_expr(state),
                    Rule::array_update_expr => rules::array_update_expr(state),
                    Rule::array_update_args => rules::array_update_args(state),
                    Rule::array_update_arg => rules::array_update_arg(state),
                    Rule::ctor_call_named => rules::ctor_call_named(state),
                    Rule::ctor_named_args => rules::ctor_named_args(state),
                    Rule::ctor_named_arg => rules::ctor_named_arg(state),
                    Rule::func_call => rules::func_call(state),
                    Rule::bool_lit => rules::bool_lit(state),
                    Rule::number => rules::number(state),
                    Rule::exp_part => rules::exp_part(state),
                    Rule::real_lit => rules::real_lit(state),
                    Rule::string_lit => rules::string_lit(state),
                    Rule::char_code => rules::char_code(state),
                    Rule::const_expr => rules::const_expr(state),
                    Rule::const_rel => rules::const_rel(state),
                    Rule::const_add => rules::const_add(state),
                    Rule::const_mul => rules::const_mul(state),
                    Rule::const_unary => rules::const_unary(state),
                    Rule::const_primary => rules::const_primary(state),
                    Rule::const_func_call => rules::const_func_call(state),
                    Rule::const_expr_list => rules::const_expr_list(state),
                    Rule::EOI => rules::EOI(state),
                }
            },
        )
    }
}
fn main() {
    let src_in = read_stdin();
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let src = match preprocess_includes(&src_in, &cwd) {
        Ok(s) => s,
        Err(e) => {
            {
                ::std::io::_eprint(format_args!("error: {0}\n", e));
            };
            std::process::exit(1);
        }
    };
    let res = (|| -> Result<String, String> {
        let p = parse_program(&src).map_err(|e| with_source_hint(&src, &e))?;
        let env = build_env(&p).map_err(|e| with_source_hint(&src, &e))?;
        check_program(&env, &p).map_err(|e| with_source_hint(&src, &e))?;
        ForthGen::new(&env).gen_program(&p).map_err(|e| with_source_hint(&src, &e))
    })();
    match res {
        Ok(forth) => {
            {
                ::std::io::_print(format_args!("{0}", forth));
            };
        }
        Err(e) => {
            {
                ::std::io::_eprint(format_args!("error: {0}\n", e));
            };
            std::process::exit(1);
        }
    }
}
fn read_stdin() -> String {
    use std::io::Read;
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    s
}
fn parse_program(src: &str) -> Result<Program, String> {
    let mut pairs = PascalParser::parse(Rule::program, src)
        .map_err(|e| {
            let (line, col) = match e.line_col {
                pest::error::LineColLocation::Pos((l, c)) => (l, c),
                pest::error::LineColLocation::Span((l, c), _) => (l, c),
            };
            ::alloc::__export::must_use({
                ::alloc::fmt::format(
                    format_args!(
                        "parse error at line {0}, column {1}: {2}",
                        line,
                        col,
                        e,
                    ),
                )
            })
        })?;
    let p = pairs.next().ok_or("no program")?;
    build_program(p)
}
fn with_source_hint(src: &str, err: &str) -> String {
    if err.contains("line ") && err.contains("column ") {
        return err.to_string();
    }
    if let Some(sym) = extract_symbol_from_error(err) {
        if let Some((line, col)) = find_symbol(src, &sym) {
            return ::alloc::__export::must_use({
                ::alloc::fmt::format(
                    format_args!("{0} at line {1}, column {2}", err, line, col),
                )
            });
        }
    }
    err.to_string()
}
fn extract_symbol_from_error(err: &str) -> Option<String> {
    let prefixes = [
        "unknown type: ",
        "unknown identifier: ",
        "unknown field: ",
        "unknown var: ",
        "unknown routine in scope: ",
        "unknown const: ",
    ];
    for p in prefixes {
        if let Some(rest) = err.strip_prefix(p) {
            return Some(rest.trim().to_string());
        }
    }
    if let Some(pos) = err.find("call to ") {
        let tail = &err[pos + "call to ".len()..];
        let name = tail
            .split(|c: char| c == ':' || c.is_whitespace())
            .next()
            .unwrap_or("")
            .trim();
        if !name.is_empty() {
            return Some(name.to_string());
        }
    }
    None
}
fn find_symbol(src: &str, sym: &str) -> Option<(usize, usize)> {
    if sym.is_empty() {
        return None;
    }
    for (li, line) in src.lines().enumerate() {
        if let Some(ci) = line.find(sym) {
            return Some((li + 1, ci + 1));
        }
    }
    None
}
fn build_program(p: pest::iterators::Pair<Rule>) -> Result<Program, String> {
    let mut it = p.into_inner();
    let name = it.next().ok_or("missing program name")?.as_str().to_string();
    let block_pair = it.next().ok_or("missing block")?;
    let block = build_block(block_pair)?;
    Ok(Program { name, block })
}
fn build_block(p: pest::iterators::Pair<Rule>) -> Result<Block, String> {
    let mut b = Block::default();
    for item in p.into_inner() {
        match item.as_rule() {
            Rule::const_section => b.consts.extend(build_consts(item)?),
            Rule::type_section => b.types.extend(build_types(item)?),
            Rule::var_section => b.vars.extend(build_vars(item, false)?),
            Rule::imut_section => b.vars.extend(build_vars(item, true)?),
            Rule::procedure_decl | Rule::function_decl => {
                b.routines.push(build_routine_decl(item)?)
            }
            Rule::compound_stmt => b.body = build_compound(item)?,
            _ => {}
        }
    }
    Ok(b)
}
fn build_routine_decl(p: pest::iterators::Pair<Rule>) -> Result<RoutineDecl, String> {
    match p.as_rule() {
        Rule::procedure_decl => {
            let mut it = p.into_inner();
            let name = it.next().unwrap().as_str().to_string();
            let mut params = ::alloc::vec::Vec::new();
            let mut block: Option<Block> = None;
            for x in it {
                match x.as_rule() {
                    Rule::formal_params => params = build_formal_params(x)?,
                    Rule::block => block = Some(build_block(x)?),
                    _ => {}
                }
            }
            Ok(
                RoutineDecl::Procedure(ProcedureDecl {
                    name,
                    params,
                    block: block.ok_or("missing procedure block")?,
                }),
            )
        }
        Rule::function_decl => {
            let mut it = p.into_inner();
            let name = it.next().unwrap().as_str().to_string();
            let mut params = ::alloc::vec::Vec::new();
            let mut ret_ty: Option<TypeRef> = None;
            let mut block: Option<Block> = None;
            for x in it {
                match x.as_rule() {
                    Rule::formal_params => params = build_formal_params(x)?,
                    Rule::type_ref_or_basic | Rule::type_ref | Rule::basic_type => {
                        ret_ty = Some(build_typeref(x)?);
                    }
                    Rule::block => block = Some(build_block(x)?),
                    _ => {}
                }
            }
            Ok(
                RoutineDecl::Function(FunctionDecl {
                    name,
                    params,
                    ret_ty: ret_ty.ok_or("missing function return type")?,
                    block: block.ok_or("missing function block")?,
                }),
            )
        }
        _ => {
            Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("unexpected routine decl: {0:?}", p.as_rule()),
                    )
                }),
            )
        }
    }
}
fn build_formal_params(
    p: pest::iterators::Pair<Rule>,
) -> Result<Vec<ParamDecl>, String> {
    let mut params = ::alloc::vec::Vec::new();
    for g in p.into_inner() {
        if g.as_rule() != Rule::formal_param_group {
            continue;
        }
        let group_text = g.as_str().trim_start();
        let mut names = ::alloc::vec::Vec::new();
        let by_ref = group_text
            .get(..3)
            .map(|s| s.eq_ignore_ascii_case("var"))
            .unwrap_or(false);
        let mut ty: Option<TypeRef> = None;
        let mut conformant: Option<ConformantArrayParam> = None;
        for x in g.into_inner() {
            match x.as_rule() {
                Rule::ident => names.push(x.as_str().to_string()),
                Rule::conformant_array_param => {
                    let it = x.into_inner();
                    let mut dims = Vec::new();
                    let mut elem_ty_pair = None;
                    for item in it {
                        match item.as_rule() {
                            Rule::conformant_array_dim => {
                                let mut jt = item.into_inner();
                                let low_name = jt.next().unwrap().as_str().to_string();
                                let high_name = jt.next().unwrap().as_str().to_string();
                                let index_ty = build_typeref(jt.next().unwrap())?;
                                dims.push(ConformantArrayDim {
                                    low_name,
                                    high_name,
                                    index_ty,
                                });
                            }
                            Rule::type_ref_or_basic
                            | Rule::type_ref
                            | Rule::basic_type => {
                                elem_ty_pair = Some(build_typeref(item)?);
                            }
                            _ => {}
                        }
                    }
                    let elem_ty = elem_ty_pair
                        .ok_or("missing conformant array element type")?;
                    let mut arr_dims = Vec::new();
                    for dim in &dims {
                        arr_dims
                            .push(ArrayDim {
                                low: ConstExpr::Const(dim.low_name.clone()),
                                high: ConstExpr::Const(dim.high_name.clone()),
                            });
                    }
                    ty = Some(TypeRef::Array {
                        dims: arr_dims,
                        elem: Box::new(elem_ty.clone()),
                    });
                    conformant = Some(ConformantArrayParam {
                        dims,
                        elem_ty,
                    });
                }
                Rule::type_ref_or_basic | Rule::type_ref | Rule::basic_type => {
                    ty = Some(build_typeref(x)?);
                }
                _ => {}
            }
        }
        let ty = ty.ok_or("missing parameter type")?;
        for n in names {
            params
                .push(ParamDecl {
                    name: n,
                    ty: ty.clone(),
                    by_ref,
                    conformant: conformant.clone(),
                });
        }
    }
    Ok(params)
}
fn build_consts(p: pest::iterators::Pair<Rule>) -> Result<Vec<ConstDecl>, String> {
    let mut v = ::alloc::vec::Vec::new();
    for cd in p.into_inner() {
        if cd.as_rule() != Rule::const_decl {
            continue;
        }
        let mut it = cd.into_inner();
        let name = it.next().unwrap().as_str().to_string();
        let mut ty = None;
        let mut expr = None;
        for x in it {
            match x.as_rule() {
                Rule::type_ref_or_basic | Rule::type_ref | Rule::basic_type => {
                    ty = Some(build_typeref(x)?);
                }
                _ => expr = Some(build_const_expr(x)?),
            }
        }
        v.push(ConstDecl {
            name,
            ty,
            expr: expr.ok_or("missing const expression")?,
        });
    }
    Ok(v)
}
fn build_types(p: pest::iterators::Pair<Rule>) -> Result<Vec<TypeDecl>, String> {
    let mut v = ::alloc::vec::Vec::new();
    for td in p.into_inner() {
        if td.as_rule() != Rule::type_decl {
            continue;
        }
        let mut it = td.into_inner();
        let name = it.next().unwrap().as_str().to_string();
        let spec = build_type_spec(it.next().unwrap())?;
        v.push(TypeDecl { name, spec });
    }
    Ok(v)
}
fn build_vars(
    p: pest::iterators::Pair<Rule>,
    immutable: bool,
) -> Result<Vec<VarDecl>, String> {
    let mut v = ::alloc::vec::Vec::new();
    for vd in p.into_inner() {
        if vd.as_rule() != Rule::var_decl {
            continue;
        }
        let mut it = vd.into_inner();
        let name = it.next().unwrap().as_str().to_string();
        let ty = build_typeref(it.next().unwrap())?;
        v.push(VarDecl { name, ty, immutable });
    }
    Ok(v)
}
fn build_type_spec(p: pest::iterators::Pair<Rule>) -> Result<TypeSpec, String> {
    match p.as_rule() {
        Rule::type_spec => build_type_spec(p.into_inner().next().unwrap()),
        Rule::basic_type => Ok(TypeSpec::Basic(parse_basic(p.as_str())?)),
        Rule::type_ref => Ok(TypeSpec::Alias(TypeRef::Named(p.as_str().to_string()))),
        Rule::option_type | Rule::result_type | Rule::pointer_type => {
            Ok(TypeSpec::Alias(build_typeref(p)?))
        }
        Rule::enum_type => {
            let members = p.into_inner().map(|x| x.as_str().to_string()).collect();
            Ok(TypeSpec::Enum(members))
        }
        Rule::subrange_type => {
            let mut it = p.into_inner();
            let low = build_const_expr(it.next().unwrap())?;
            let high = build_const_expr(it.next().unwrap())?;
            Ok(TypeSpec::Subrange { low, high })
        }
        Rule::set_type => {
            let elem = build_typeref(p.into_inner().next().unwrap())?;
            Ok(TypeSpec::Set(elem))
        }
        Rule::sum_record_type => {
            let mut arms = ::alloc::vec::Vec::new();
            for arm in p.into_inner() {
                if arm.as_rule() != Rule::sum_arm_decl {
                    continue;
                }
                let mut it = arm.into_inner();
                let name = it.next().unwrap().as_str().to_string();
                let mut fields = ::alloc::vec::Vec::new();
                if let Some(sum_fields) = it.next() {
                    for fd in sum_fields.into_inner() {
                        let mut jt = fd.into_inner();
                        fields
                            .push(FieldDecl {
                                name: jt.next().unwrap().as_str().to_string(),
                                ty: build_typeref(jt.next().unwrap())?,
                            });
                    }
                }
                arms.push(SumArmDecl { name, fields });
            }
            Ok(TypeSpec::SumRecord(arms))
        }
        Rule::record_type => {
            let mut fields = ::alloc::vec::Vec::new();
            let mut variant = None;
            for fd in p.into_inner() {
                match fd.as_rule() {
                    Rule::field_decl => {
                        let mut it = fd.into_inner();
                        let name = it.next().unwrap().as_str().to_string();
                        let ty = build_typeref(it.next().unwrap())?;
                        fields.push(FieldDecl { name, ty });
                    }
                    Rule::variant_part => {
                        variant = Some(build_variant_part(fd)?);
                    }
                    _ => {}
                }
            }
            Ok(TypeSpec::Record {
                fields,
                variant,
            })
        }
        Rule::array_type => {
            let mut dims = ::alloc::vec::Vec::new();
            let mut elem: Option<TypeRef> = None;
            for x in p.into_inner() {
                match x.as_rule() {
                    Rule::type_ref_or_basic | Rule::type_ref | Rule::basic_type => {
                        elem = Some(build_typeref(x)?);
                    }
                    Rule::array_dim => {
                        let mut it = x.into_inner();
                        let first = build_const_expr(it.next().unwrap())?;
                        let (low, high) = if let Some(second) = it.next() {
                            (first, build_const_expr(second)?)
                        } else {
                            let n = match eval_const(&Env::new(), &first)? {
                                ConstVal::I32(i) if i > 0 => i,
                                _ => {
                                    return Err(
                                        "array length must be positive integer constant".into(),
                                    );
                                }
                            };
                            (ConstExpr::Int(0), ConstExpr::Int(n - 1))
                        };
                        dims.push(ArrayDim { low, high });
                    }
                    _ => {}
                }
            }
            if dims.is_empty() {
                return Err("array must have at least one dimension".into());
            }
            Ok(TypeSpec::Array {
                dims,
                elem: elem.ok_or("array elem type missing")?,
            })
        }
        _ => {
            Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("unexpected type spec: {0:?}", p.as_rule()),
                    )
                }),
            )
        }
    }
}
fn build_typeref(p: pest::iterators::Pair<Rule>) -> Result<TypeRef, String> {
    match p.as_rule() {
        Rule::type_ref_or_basic => build_typeref(p.into_inner().next().unwrap()),
        Rule::basic_type => Ok(TypeRef::Basic(parse_basic(p.as_str())?)),
        Rule::type_ref => Ok(TypeRef::Named(p.as_str().to_string())),
        Rule::pointer_type => {
            Ok(
                TypeRef::PointerNamed(
                    p.into_inner().next().unwrap().as_str().to_string(),
                ),
            )
        }
        Rule::option_type => {
            Ok(TypeRef::Option(Box::new(build_typeref(p.into_inner().next().unwrap())?)))
        }
        Rule::result_type => {
            let mut it = p.into_inner();
            let ok_ty = build_typeref(it.next().ok_or("missing result ok type")?)?;
            let err_ty = build_typeref(it.next().ok_or("missing result err type")?)?;
            Ok(TypeRef::Result(Box::new(ok_ty), Box::new(err_ty)))
        }
        Rule::subrange_type => {
            let mut it = p.into_inner();
            Ok(TypeRef::Subrange {
                low: build_const_expr(it.next().unwrap())?,
                high: build_const_expr(it.next().unwrap())?,
            })
        }
        Rule::set_type => {
            Ok(TypeRef::Set(Box::new(build_typeref(p.into_inner().next().unwrap())?)))
        }
        Rule::array_type => {
            let mut dims = ::alloc::vec::Vec::new();
            let mut elem: Option<TypeRef> = None;
            for x in p.into_inner() {
                match x.as_rule() {
                    Rule::type_ref_or_basic | Rule::type_ref | Rule::basic_type => {
                        elem = Some(build_typeref(x)?);
                    }
                    Rule::array_dim => {
                        let mut it = x.into_inner();
                        let first = build_const_expr(it.next().unwrap())?;
                        let (low, high) = if let Some(second) = it.next() {
                            (first, build_const_expr(second)?)
                        } else {
                            let n = match eval_const(&Env::new(), &first)? {
                                ConstVal::I32(i) if i > 0 => i,
                                _ => {
                                    return Err(
                                        "array length must be positive integer constant".into(),
                                    );
                                }
                            };
                            (ConstExpr::Int(0), ConstExpr::Int(n - 1))
                        };
                        dims.push(ArrayDim { low, high });
                    }
                    _ => {}
                }
            }
            if dims.is_empty() {
                return Err("array must have at least one dimension".into());
            }
            Ok(TypeRef::Array {
                dims,
                elem: Box::new(elem.ok_or("array elem type missing")?),
            })
        }
        _ => {
            Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("unexpected typeref: {0:?}", p.as_rule()),
                    )
                }),
            )
        }
    }
}
fn build_variant_case(p: pest::iterators::Pair<Rule>) -> Result<VariantCase, String> {
    let mut it = p.into_inner();
    let labels = build_case_label_list(it.next().ok_or("variant case missing labels")?)?;
    let mut fields = ::alloc::vec::Vec::new();
    let mut variant = None;
    for fd in it {
        match fd.as_rule() {
            Rule::field_decl => {
                let mut jt = fd.into_inner();
                fields
                    .push(FieldDecl {
                        name: jt.next().unwrap().as_str().to_string(),
                        ty: build_typeref(jt.next().unwrap())?,
                    });
            }
            Rule::variant_part => variant = Some(build_variant_part(fd)?),
            _ => {}
        }
    }
    Ok(VariantCase {
        labels,
        fields,
        variant,
    })
}
fn build_variant_part(p: pest::iterators::Pair<Rule>) -> Result<VariantPart, String> {
    let mut it = p.into_inner();
    let first = it.next().ok_or("variant part missing content")?;
    let (tag_name, tag_ty, first_case) = match first.as_rule() {
        Rule::ident => {
            let tag_name = Some(first.as_str().to_string());
            let tag_ty = build_typeref(it.next().ok_or("variant tag type missing")?)?;
            let first_case = it.next().ok_or("variant case missing")?;
            (tag_name, tag_ty, first_case)
        }
        Rule::type_ref_or_basic | Rule::type_ref | Rule::basic_type => {
            let tag_ty = build_typeref(first)?;
            let first_case = it.next().ok_or("variant case missing")?;
            (None, tag_ty, first_case)
        }
        Rule::variant_case => (None, TypeRef::Basic(BasicType::Integer), first),
        _ => return Err("unexpected variant part".into()),
    };
    let mut cases = <[_]>::into_vec(
        ::alloc::boxed::box_new([build_variant_case(first_case)?]),
    );
    for item in it {
        cases.push(build_variant_case(item)?);
    }
    Ok(VariantPart {
        tag_name,
        tag_ty,
        cases,
    })
}
fn parse_basic(s: &str) -> Result<BasicType, String> {
    match s.to_ascii_lowercase().as_str() {
        "integer" => Ok(BasicType::Integer),
        "boolean" => Ok(BasicType::Boolean),
        "char" => Ok(BasicType::Char),
        "real" => Ok(BasicType::Real),
        _ => {
            Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("unknown basic type: {0}", s))
                }),
            )
        }
    }
}
fn build_compound(p: pest::iterators::Pair<Rule>) -> Result<Stmt, String> {
    let mut stmts = ::alloc::vec::Vec::new();
    for it in p.into_inner() {
        if it.as_rule() == Rule::stmt_list {
            stmts = build_stmt_list(it)?;
        }
    }
    Ok(Stmt::Compound(stmts))
}
fn build_stmt_list(p: pest::iterators::Pair<Rule>) -> Result<Vec<Stmt>, String> {
    let mut v = ::alloc::vec::Vec::new();
    for s in p.into_inner() {
        v.push(build_stmt(s)?);
    }
    Ok(v)
}
fn build_stmt(p: pest::iterators::Pair<Rule>) -> Result<Stmt, String> {
    match p.as_rule() {
        Rule::compound_stmt => build_compound(p),
        Rule::assign_stmt => {
            let mut it = p.into_inner();
            let lv = build_lvalue(it.next().unwrap())?;
            let rhs = build_expr(it.next().unwrap())?;
            Ok(Stmt::Assign(lv, rhs))
        }
        Rule::read_stmt => {
            let args = build_expr_list(p.into_inner().next().unwrap())?;
            Ok(Stmt::Read(args))
        }
        Rule::readln_stmt => Ok(Stmt::ReadLn),
        Rule::for_stmt => {
            let mut it = p.into_inner();
            let var = it.next().unwrap().as_str().to_string();
            let init = build_expr(it.next().unwrap())?;
            let dir = it.next().unwrap().as_str().to_string();
            let limit = build_expr(it.next().unwrap())?;
            let body = build_stmt(it.next().unwrap())?;
            Ok(Stmt::For {
                var,
                init,
                limit,
                downto: dir == "downto",
                body: Box::new(body),
            })
        }
        Rule::case_stmt => {
            let mut it = p.into_inner();
            let expr = build_expr(it.next().unwrap())?;
            let mut arms = ::alloc::vec::Vec::new();
            let mut else_stmt = None;
            for x in it {
                match x.as_rule() {
                    Rule::case_arm => {
                        let mut jt = x.into_inner();
                        let labels = build_case_label_list(jt.next().unwrap())?;
                        let s = build_stmt(jt.next().unwrap())?;
                        arms.push((labels, s));
                    }
                    _ => else_stmt = Some(Box::new(build_stmt(x)?)),
                }
            }
            Ok(Stmt::Case {
                expr,
                arms,
                else_stmt,
            })
        }
        Rule::sum_case_stmt => {
            let mut it = p.into_inner();
            let expr = build_expr(it.next().unwrap())?;
            let mut arms = ::alloc::vec::Vec::new();
            let mut else_stmt = None;
            for x in it {
                match x.as_rule() {
                    Rule::sum_case_arm => {
                        let mut jt = x.into_inner();
                        let ctor = jt.next().unwrap().as_str().to_string();
                        let mut binds = ::alloc::vec::Vec::new();
                        let mut body = None;
                        for item in jt {
                            match item.as_rule() {
                                Rule::bind_list => {
                                    binds = item
                                        .into_inner()
                                        .map(|n| n.as_str().to_string())
                                        .collect();
                                }
                                _ => body = Some(build_stmt(item)?),
                            }
                        }
                        arms.push(SumCaseArm {
                            ctor,
                            binds,
                            body: body.ok_or("sum-case arm missing body")?,
                        });
                    }
                    Rule::sum_case_else => {
                        let stmt = x
                            .into_inner()
                            .next()
                            .ok_or("sum-case else missing body")?;
                        else_stmt = Some(Box::new(build_stmt(stmt)?));
                    }
                    _ => {}
                }
            }
            Ok(Stmt::SumCase {
                expr,
                arms,
                else_stmt,
            })
        }
        Rule::proc_call_stmt => {
            let mut it = p.into_inner();
            let name = it.next().unwrap().as_str().to_string();
            let args = if let Some(list) = it.next() {
                build_expr_list(list)?
            } else {
                ::alloc::vec::Vec::new()
            };
            Ok(Stmt::ProcCall(name, args))
        }
        Rule::if_stmt => {
            let mut it = p.into_inner();
            let cond = build_expr(it.next().unwrap())?;
            let then_s = build_stmt(it.next().unwrap())?;
            let else_s = if let Some(e) = it.next() {
                Some(Box::new(build_stmt(e)?))
            } else {
                None
            };
            Ok(Stmt::If(cond, Box::new(then_s), else_s))
        }
        Rule::with_stmt => {
            let mut it = p.into_inner();
            let mut bases = <[_]>::into_vec(
                ::alloc::boxed::box_new([build_lvalue(it.next().unwrap())?]),
            );
            let mut body = None;
            for x in it {
                if x.as_rule() == Rule::lvalue {
                    bases.push(build_lvalue(x)?);
                } else {
                    body = Some(build_stmt(x)?);
                }
            }
            Ok(Stmt::With(bases, Box::new(body.ok_or("with missing body")?)))
        }
        Rule::while_stmt => {
            let mut it = p.into_inner();
            let cond = build_expr(it.next().unwrap())?;
            let body = build_stmt(it.next().unwrap())?;
            Ok(Stmt::While(cond, Box::new(body)))
        }
        Rule::repeat_stmt => {
            let mut stmts = ::alloc::vec::Vec::new();
            let mut cond: Option<Expr> = None;
            for x in p.into_inner() {
                if x.as_rule() == Rule::stmt_list {
                    stmts = build_stmt_list(x)?;
                } else {
                    cond = Some(build_expr(x)?);
                }
            }
            Ok(Stmt::Repeat(stmts, cond.ok_or("repeat missing cond")?))
        }
        Rule::write_stmt => {
            let mut it = p.into_inner();
            let args = if let Some(list) = it.next() {
                build_expr_list(list)?
            } else {
                ::alloc::vec::Vec::new()
            };
            Ok(Stmt::Write(args))
        }
        Rule::writeln_stmt => {
            let mut it = p.into_inner();
            let args = if let Some(list) = it.next() {
                build_expr_list(list)?
            } else {
                ::alloc::vec::Vec::new()
            };
            Ok(Stmt::WriteLn(args))
        }
        Rule::empty_stmt => Ok(Stmt::Empty),
        _ => {
            Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("unexpected stmt: {0:?}", p.as_rule()),
                    )
                }),
            )
        }
    }
}
fn build_expr_list(p: pest::iterators::Pair<Rule>) -> Result<Vec<Expr>, String> {
    let mut v = ::alloc::vec::Vec::new();
    for x in p.into_inner() {
        v.push(build_expr(x)?);
    }
    Ok(v)
}
fn build_lvalue(p: pest::iterators::Pair<Rule>) -> Result<LValue, String> {
    let mut it = p.into_inner();
    let base = it.next().unwrap().as_str().to_string();
    let mut sels = ::alloc::vec::Vec::new();
    for s in it {
        match s.as_rule() {
            Rule::field_access => {
                let mut jt = s.into_inner();
                let name = jt.next().unwrap().as_str().to_string();
                sels.push(Selector::Field(name));
            }
            Rule::index_access => {
                let mut idxs = ::alloc::vec::Vec::new();
                for ie in s.into_inner() {
                    idxs.push(build_expr(ie)?);
                }
                if idxs.is_empty() {
                    return Err("index access must include at least one index".into());
                }
                sels.push(Selector::Index(idxs));
            }
            Rule::deref_access => sels.push(Selector::Deref),
            _ => {
                return Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("unexpected selector: {0:?}", s.as_rule()),
                        )
                    }),
                );
            }
        }
    }
    Ok(LValue { base, sels })
}
fn build_expr(p: pest::iterators::Pair<Rule>) -> Result<Expr, String> {
    match p.as_rule() {
        Rule::expr => build_expr(p.into_inner().next().unwrap()),
        Rule::rel => {
            let mut it = p.into_inner();
            let left = build_expr(it.next().unwrap())?;
            if let Some(op) = it.next() {
                let right = build_expr(it.next().unwrap())?;
                Ok(
                    Expr::Binary(
                        Box::new(left),
                        parse_relop(op.as_str())?,
                        Box::new(right),
                    ),
                )
            } else {
                Ok(left)
            }
        }
        Rule::add => {
            let mut it = p.into_inner();
            let mut e = build_expr(it.next().unwrap())?;
            while let Some(op) = it.next() {
                let rhs = build_expr(it.next().unwrap())?;
                let op_s = op.as_str().to_ascii_lowercase();
                let bop = match op_s.as_str() {
                    "+" => BinOp::Add,
                    "-" => BinOp::Sub,
                    "or" => BinOp::Or,
                    "xor" => BinOp::Xor,
                    _ => return Err("unknown add op".into()),
                };
                e = Expr::Binary(Box::new(e), bop, Box::new(rhs));
            }
            Ok(e)
        }
        Rule::mul => {
            let mut it = p.into_inner();
            let mut e = build_expr(it.next().unwrap())?;
            while let Some(op) = it.next() {
                let rhs = build_expr(it.next().unwrap())?;
                let op_s = op.as_str().to_ascii_lowercase();
                let bop = match op_s.as_str() {
                    "*" => BinOp::Mul,
                    "/" => BinOp::RealDiv,
                    "div" => BinOp::Div,
                    "mod" => BinOp::Mod,
                    "and" => BinOp::And,
                    _ => return Err("unknown mul op".into()),
                };
                e = Expr::Binary(Box::new(e), bop, Box::new(rhs));
            }
            Ok(e)
        }
        Rule::unary => {
            let mut it = p.clone().into_inner();
            let first = it.next().unwrap();
            if first.as_rule() == Rule::unary_op {
                let op_s = first.as_str().to_ascii_lowercase();
                let op = match op_s.as_str() {
                    "-" => UnOp::Neg,
                    "not" => UnOp::Not,
                    _ => return Err("unknown unary op".into()),
                };
                let inner = build_expr(it.next().unwrap())?;
                Ok(Expr::Unary(op, Box::new(inner)))
            } else {
                build_expr(first)
            }
        }
        Rule::primary => build_expr(p.into_inner().next().unwrap()),
        Rule::bool_lit => Ok(Expr::Bool(p.as_str().eq_ignore_ascii_case("true"))),
        Rule::nil_expr => Ok(Expr::Nil),
        Rule::none_expr => Ok(Expr::OptionNone),
        Rule::some_expr => {
            Ok(Expr::OptionSome(Box::new(build_expr(p.into_inner().next().unwrap())?)))
        }
        Rule::cast_expr => {
            let mut it = p.into_inner();
            let ty = build_typeref(it.next().unwrap())?;
            let expr = build_expr(it.next().unwrap())?;
            Ok(Expr::Cast(ty, Box::new(expr)))
        }
        Rule::cond_expr => build_cond_expr(p),
        Rule::array_lit => {
            let elems = if let Some(list) = p.into_inner().next() {
                build_expr_list(list)?
            } else {
                ::alloc::vec::Vec::new()
            };
            Ok(Expr::ArrayLit(elems))
        }
        Rule::record_update_expr => {
            let mut it = p.into_inner();
            let base = Expr::Var(it.next().unwrap().as_str().to_string());
            let mut args = ::alloc::vec::Vec::new();
            if let Some(list) = it.next() {
                for a in list.into_inner() {
                    let mut jt = a.into_inner();
                    args.push((
                        jt.next().unwrap().as_str().to_string(),
                        build_expr(jt.next().unwrap())?,
                    ));
                }
            }
            Ok(Expr::RecordUpdate(Box::new(base), args))
        }
        Rule::array_update_expr => {
            let mut it = p.into_inner();
            let base = Expr::Var(it.next().unwrap().as_str().to_string());
            let mut ups = ::alloc::vec::Vec::new();
            if let Some(list) = it.next() {
                for a in list.into_inner() {
                    let mut jt = a.into_inner();
                    ups.push((
                        build_expr(jt.next().unwrap())?,
                        build_expr(jt.next().unwrap())?,
                    ));
                }
            }
            Ok(Expr::ArrayUpdate(Box::new(base), ups))
        }
        Rule::real_lit => Ok(Expr::Real(parse_real_literal_bits(p.as_str())?)),
        Rule::number => Ok(Expr::Int(parse_int_literal(p.as_str())?)),
        Rule::string_lit => {
            let s = decode_pascal_string(p.as_str())?;
            if s.chars().count() == 1 {
                Ok(Expr::Char(s.chars().next().unwrap() as u32))
            } else {
                Ok(Expr::Str(s))
            }
        }
        Rule::char_code => {
            let mut it = p.into_inner();
            let n = it
                .next()
                .unwrap()
                .as_str()
                .parse::<u32>()
                .map_err(|e| e.to_string())?;
            if n > 0x10FFFF {
                return Err("char code > 0x10FFFF".into());
            }
            Ok(Expr::Char(n))
        }
        Rule::ctor_call_named => {
            let mut it = p.into_inner();
            let name = it.next().unwrap().as_str().to_string();
            let mut args = ::alloc::vec::Vec::new();
            if let Some(list) = it.next() {
                for a in list.into_inner() {
                    let mut jt = a.into_inner();
                    args.push((
                        jt.next().unwrap().as_str().to_string(),
                        build_expr(jt.next().unwrap())?,
                    ));
                }
            }
            Ok(Expr::Ctor(name, args))
        }
        Rule::func_call => {
            let mut it = p.into_inner();
            let name = it.next().unwrap().as_str().to_string();
            let args = if let Some(list) = it.next() {
                build_expr_list(list)?
            } else {
                ::alloc::vec::Vec::new()
            };
            Ok(Expr::Call(name, args))
        }
        Rule::set_lit => {
            let elems = if let Some(list) = p.into_inner().next() {
                build_set_items(list)?
            } else {
                ::alloc::vec::Vec::new()
            };
            Ok(Expr::SetLit(elems))
        }
        Rule::ident => Ok(Expr::Var(p.as_str().to_string())),
        Rule::lvalue => {
            let lv = build_lvalue(p)?;
            let mut e = Expr::Var(lv.base);
            for sel in lv.sels {
                e = match sel {
                    Selector::Deref => Expr::Deref(Box::new(e)),
                    Selector::Field(f) => Expr::Field(Box::new(e), f),
                    Selector::Index(ixs) => {
                        let mut acc = e;
                        for ix in ixs {
                            acc = Expr::Index(Box::new(acc), Box::new(ix));
                        }
                        acc
                    }
                };
            }
            Ok(e)
        }
        _ => {
            Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("unexpected expr node: {0:?}", p.as_rule()),
                    )
                }),
            )
        }
    }
}
fn build_set_items(p: pest::iterators::Pair<Rule>) -> Result<Vec<SetItem>, String> {
    let mut items = Vec::new();
    for x in p.into_inner() {
        if x.as_rule() != Rule::set_item {
            continue;
        }
        let mut it = x.into_inner();
        let first = build_expr(it.next().unwrap())?;
        if let Some(second) = it.next() {
            items.push(SetItem::Range(first, build_expr(second)?));
        } else {
            items.push(SetItem::Single(first));
        }
    }
    Ok(items)
}
fn build_cond_expr(p: pest::iterators::Pair<Rule>) -> Result<Expr, String> {
    let mut arms = ::alloc::vec::Vec::new();
    let mut else_block = None;
    for x in p.into_inner() {
        match x.as_rule() {
            Rule::cond_arm => {
                let mut it = x.into_inner();
                let cond = build_expr(it.next().unwrap())?;
                let block = build_cond_block(it.next().unwrap())?;
                arms.push(CondExprArm { cond, block });
            }
            Rule::cond_else_arm => {
                let mut it = x.into_inner();
                else_block = Some(build_cond_block(it.next().unwrap())?);
            }
            _ => {}
        }
    }
    Ok(Expr::Cond {
        arms,
        else_block: else_block.ok_or("cond missing else")?,
    })
}
fn build_cond_block(p: pest::iterators::Pair<Rule>) -> Result<CondValueBlock, String> {
    let mut stmts = ::alloc::vec::Vec::new();
    let mut value = None;
    for x in p.into_inner() {
        match x.as_rule() {
            Rule::cond_stmt => {
                let inner = x.into_inner().next().ok_or("empty cond stmt")?;
                stmts.push(build_stmt(inner)?);
            }
            Rule::value_stmt => {
                let mut it = x.into_inner();
                value = Some(Box::new(build_expr(it.next().unwrap())?));
            }
            _ => {}
        }
    }
    Ok(CondValueBlock {
        stmts,
        value: value.ok_or("cond block missing VALUE")?,
    })
}
fn parse_relop(s: &str) -> Result<BinOp, String> {
    match s {
        "=" => Ok(BinOp::Eq),
        "<>" => Ok(BinOp::Ne),
        "<" => Ok(BinOp::Lt),
        "<=" => Ok(BinOp::Le),
        ">" => Ok(BinOp::Gt),
        ">=" => Ok(BinOp::Ge),
        "in" | "IN" | "In" => Ok(BinOp::In),
        _ => {
            Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(format_args!("unknown relop: {0}", s))
                }),
            )
        }
    }
}
fn build_const_expr(p: pest::iterators::Pair<Rule>) -> Result<ConstExpr, String> {
    match p.as_rule() {
        Rule::const_expr => build_const_expr(p.into_inner().next().unwrap()),
        Rule::const_rel => {
            let mut it = p.into_inner();
            let left = build_const_expr(it.next().unwrap())?;
            if let Some(op) = it.next() {
                let right = build_const_expr(it.next().unwrap())?;
                Ok(
                    ConstExpr::Binary(
                        Box::new(left),
                        parse_relop(op.as_str())?,
                        Box::new(right),
                    ),
                )
            } else {
                Ok(left)
            }
        }
        Rule::const_add => {
            let mut it = p.into_inner();
            let mut e = build_const_expr(it.next().unwrap())?;
            while let Some(op) = it.next() {
                let rhs = build_const_expr(it.next().unwrap())?;
                let op_s = op.as_str().to_ascii_lowercase();
                let bop = match op_s.as_str() {
                    "+" => BinOp::Add,
                    "-" => BinOp::Sub,
                    "or" => BinOp::Or,
                    "xor" => BinOp::Xor,
                    _ => return Err("unknown const add op".into()),
                };
                e = ConstExpr::Binary(Box::new(e), bop, Box::new(rhs));
            }
            Ok(e)
        }
        Rule::const_mul => {
            let mut it = p.into_inner();
            let mut e = build_const_expr(it.next().unwrap())?;
            while let Some(op) = it.next() {
                let rhs = build_const_expr(it.next().unwrap())?;
                let op_s = op.as_str().to_ascii_lowercase();
                let bop = match op_s.as_str() {
                    "*" => BinOp::Mul,
                    "/" => BinOp::RealDiv,
                    "div" => BinOp::Div,
                    "mod" => BinOp::Mod,
                    "and" => BinOp::And,
                    _ => return Err("unknown const mul op".into()),
                };
                e = ConstExpr::Binary(Box::new(e), bop, Box::new(rhs));
            }
            Ok(e)
        }
        Rule::const_unary => {
            let mut it = p.clone().into_inner();
            let first = it.next().unwrap();
            if first.as_rule() == Rule::unary_op {
                let op_s = first.as_str().to_ascii_lowercase();
                let op = match op_s.as_str() {
                    "-" => UnOp::Neg,
                    "not" => UnOp::Not,
                    _ => return Err("unknown const unary op".into()),
                };
                let inner = build_const_expr(it.next().unwrap())?;
                Ok(ConstExpr::Unary(op, Box::new(inner)))
            } else {
                build_const_expr(first)
            }
        }
        Rule::const_primary => build_const_expr(p.into_inner().next().unwrap()),
        Rule::bool_lit => Ok(ConstExpr::Bool(p.as_str().eq_ignore_ascii_case("true"))),
        Rule::real_lit => Ok(ConstExpr::Real(parse_real_literal_bits(p.as_str())?)),
        Rule::number => Ok(ConstExpr::Int(parse_int_literal(p.as_str())?)),
        Rule::string_lit => {
            let s = decode_pascal_string(p.as_str())?;
            if s.chars().count() != 1 {
                return Err("string literal is not allowed in const expr".into());
            }
            Ok(ConstExpr::Char(s.chars().next().unwrap() as u32))
        }
        Rule::char_code => {
            let mut it = p.into_inner();
            let n = it
                .next()
                .unwrap()
                .as_str()
                .parse::<u32>()
                .map_err(|e| e.to_string())?;
            if n > 0x10FFFF {
                return Err("char code > 0x10FFFF".into());
            }
            Ok(ConstExpr::Char(n))
        }
        Rule::const_func_call => {
            let mut it = p.into_inner();
            let name = it.next().unwrap().as_str().to_string();
            let args = if let Some(list) = it.next() {
                build_const_expr_list(list)?
            } else {
                ::alloc::vec::Vec::new()
            };
            Ok(ConstExpr::Call(name, args))
        }
        Rule::ident => Ok(ConstExpr::Const(p.as_str().to_string())),
        _ => {
            Err(
                ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("unexpected const expr node: {0:?}", p.as_rule()),
                    )
                }),
            )
        }
    }
}
fn build_const_expr_list(
    p: pest::iterators::Pair<Rule>,
) -> Result<Vec<ConstExpr>, String> {
    let mut v = ::alloc::vec::Vec::new();
    for x in p.into_inner() {
        v.push(build_const_expr(x)?);
    }
    Ok(v)
}
fn decode_pascal_string(src: &str) -> Result<String, String> {
    if !src.starts_with('\'') || !src.ends_with('\'') || src.len() < 2 {
        return Err("invalid string literal".into());
    }
    let inner = &src[1..src.len() - 1];
    let mut out = String::new();
    let mut it = inner.chars().peekable();
    while let Some(ch) = it.next() {
        if ch == '\'' {
            if it.peek() == Some(&'\'') {
                it.next();
                out.push('\'');
            } else {
                return Err("invalid quote in string literal".into());
            }
        } else {
            out.push(ch);
        }
    }
    Ok(out)
}
fn parse_int_literal(s: &str) -> Result<i32, String> {
    if let Some(rest) = s.strip_prefix("0x") {
        let u = i64::from_str_radix(rest, 16).map_err(|e| e.to_string())?;
        return i32::try_from(u).map_err(|_| "hex literal out of i32 range".to_string());
    }
    if let Some(rest) = s.strip_prefix('$') {
        let u = i64::from_str_radix(rest, 16).map_err(|e| e.to_string())?;
        return i32::try_from(u).map_err(|_| "hex literal out of i32 range".to_string());
    }
    s.parse::<i32>().map_err(|e| e.to_string())
}
fn parse_real_literal_bits(s: &str) -> Result<u32, String> {
    let f = s
        .parse::<f32>()
        .map_err(|e| ::alloc::__export::must_use({
            ::alloc::fmt::format(format_args!("invalid real literal \'{0}\': {1}", s, e))
        }))?;
    Ok(f.to_bits())
}
fn build_case_label_list(
    p: pest::iterators::Pair<Rule>,
) -> Result<Vec<CaseLabel>, String> {
    let mut out = ::alloc::vec::Vec::new();
    for x in p.into_inner() {
        if x.as_rule() != Rule::case_label {
            continue;
        }
        let mut it = x.into_inner();
        let first = build_const_expr(it.next().unwrap())?;
        if let Some(second) = it.next() {
            out.push(CaseLabel::Range(first, build_const_expr(second)?));
        } else {
            out.push(CaseLabel::Single(first));
        }
    }
    Ok(out)
}
fn preprocess_includes(src: &str, base_dir: &Path) -> Result<String, String> {
    let mut stack = HashSet::new();
    expand_includes(src, base_dir, &mut stack)
}
fn expand_includes(
    src: &str,
    base_dir: &Path,
    stack: &mut HashSet<PathBuf>,
) -> Result<String, String> {
    let mut out = String::with_capacity(src.len());
    let mut pos = 0usize;
    while let Some(rel) = src[pos..].find("(*") {
        let start = pos + rel;
        out.push_str(&src[pos..start]);
        let after = start + 2;
        let Some(end_rel) = src[after..].find("*)") else {
            out.push_str(&src[start..]);
            return Ok(out);
        };
        let end = after + end_rel;
        let body = &src[after..end];
        if let Some(path) = parse_include_directive(body) {
            let full = base_dir.join(path);
            let canon = full.canonicalize().unwrap_or(full.clone());
            if stack.contains(&canon) {
                return Err(
                    ::alloc::__export::must_use({
                        ::alloc::fmt::format(
                            format_args!("include cycle detected: {0}", canon.display()),
                        )
                    }),
                );
            }
            let text = std::fs::read_to_string(&full)
                .map_err(|e| ::alloc::__export::must_use({
                    ::alloc::fmt::format(
                        format_args!("include read failed ({0}): {1}", full.display(), e),
                    )
                }))?;
            stack.insert(canon.clone());
            let parent = full.parent().unwrap_or(base_dir);
            let expanded = expand_includes(&text, parent, stack)?;
            stack.remove(&canon);
            out.push_str(&expanded);
        } else {
            out.push_str(&src[start..end + 2]);
        }
        pos = end + 2;
    }
    out.push_str(&src[pos..]);
    Ok(out)
}
fn parse_include_directive(body: &str) -> Option<String> {
    let t = body.trim();
    if t.len() < 2 {
        return None;
    }
    let u = t.to_ascii_uppercase();
    if !u.starts_with("$I") {
        return None;
    }
    let mut rest = t[2..].trim();
    if rest.is_empty() {
        return None;
    }
    if rest.len() >= 2
        && ((rest.starts_with('\'') && rest.ends_with('\''))
            || (rest.starts_with('"') && rest.ends_with('"')))
    {
        rest = &rest[1..rest.len() - 1];
    }
    if rest.is_empty() {
        return None;
    }
    Some(rest.to_string())
}
