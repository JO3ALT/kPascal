#[derive(Debug, Clone)]
pub struct Program {
    #[allow(dead_code)]
    pub name: String,
    pub block: Block,
}

#[derive(Debug, Clone, Default)]
pub struct Block {
    pub consts: Vec<ConstDecl>,
    pub types: Vec<TypeDecl>,
    pub vars: Vec<VarDecl>,
    pub routines: Vec<RoutineDecl>,
    pub body: Stmt,
}

#[derive(Debug, Clone)]
pub struct ConstDecl {
    pub name: String,
    pub ty: Option<TypeRef>,
    pub expr: ConstExpr,
}

#[derive(Debug, Clone)]
pub struct TypeDecl {
    pub name: String,
    pub spec: TypeSpec,
}

#[derive(Debug, Clone)]
pub struct VarDecl {
    pub name: String,
    pub ty: TypeRef,
    pub immutable: bool,
}

#[derive(Debug, Clone)]
pub enum RoutineDecl {
    Procedure(ProcedureDecl),
    Function(FunctionDecl),
}

#[derive(Debug, Clone)]
pub struct ProcedureDecl {
    pub name: String,
    pub params: Vec<ParamDecl>,
    pub block: Block,
}

#[derive(Debug, Clone)]
pub struct FunctionDecl {
    pub name: String,
    pub params: Vec<ParamDecl>,
    pub ret_ty: TypeRef,
    pub block: Block,
}

#[derive(Debug, Clone)]
pub struct ParamDecl {
    pub name: String,
    pub ty: TypeRef,
    pub by_ref: bool,
    pub conformant: Option<ConformantArrayParam>,
}

#[derive(Debug, Clone)]
pub enum TypeSpec {
    Basic(BasicType),
    Enum(Vec<String>),
    Record {
        fields: Vec<FieldDecl>,
        variant: Option<VariantPart>,
    },
    SumRecord(Vec<SumArmDecl>),
    Array {
        dims: Vec<ArrayDim>,
        elem: TypeRef,
    },
    Subrange {
        low: ConstExpr,
        high: ConstExpr,
    },
    Set(TypeRef),
    Alias(TypeRef),
}

#[derive(Debug, Clone)]
pub struct ConformantArrayParam {
    pub dims: Vec<ConformantArrayDim>,
    pub elem_ty: TypeRef,
}

#[derive(Debug, Clone)]
pub struct ConformantArrayDim {
    pub low_name: String,
    pub high_name: String,
    pub index_ty: TypeRef,
}

#[derive(Debug, Clone)]
pub struct ArrayDim {
    pub low: ConstExpr,
    pub high: ConstExpr,
}

#[derive(Debug, Clone)]
pub struct FieldDecl {
    pub name: String,
    pub ty: TypeRef,
}

#[derive(Debug, Clone)]
pub struct SumArmDecl {
    pub name: String,
    pub fields: Vec<FieldDecl>,
}

#[derive(Debug, Clone)]
pub struct VariantPart {
    pub tag_name: Option<String>,
    pub tag_ty: TypeRef,
    pub cases: Vec<VariantCase>,
}

#[derive(Debug, Clone)]
pub struct VariantCase {
    pub labels: Vec<CaseLabel>,
    pub fields: Vec<FieldDecl>,
    pub variant: Option<VariantPart>,
}

#[derive(Debug, Clone)]
pub enum BasicType {
    Integer,
    Boolean,
    Char,
    Real,
}

#[derive(Debug, Clone)]
pub enum TypeRef {
    Basic(BasicType),
    Named(String),
    PointerNamed(String),
    Option(Box<TypeRef>),
    Result(Box<TypeRef>, Box<TypeRef>),
    Array {
        dims: Vec<ArrayDim>,
        elem: Box<TypeRef>,
    },
    Subrange {
        low: ConstExpr,
        high: ConstExpr,
    },
    Set(Box<TypeRef>),
}

#[derive(Debug, Clone, Default)]
pub enum Stmt {
    #[default]
    Empty,
    Compound(Vec<Stmt>),
    Assign(LValue, Expr),
    Read(Vec<Expr>),
    ReadLn,
    For {
        var: String,
        init: Expr,
        limit: Expr,
        downto: bool,
        body: Box<Stmt>,
    },
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    With(Vec<LValue>, Box<Stmt>),
    While(Expr, Box<Stmt>),
    Repeat(Vec<Stmt>, Expr),
    Case {
        expr: Expr,
        arms: Vec<(Vec<CaseLabel>, Stmt)>,
        else_stmt: Option<Box<Stmt>>,
    },
    SumCase {
        expr: Expr,
        arms: Vec<SumCaseArm>,
        else_stmt: Option<Box<Stmt>>,
    },
    ProcCall(String, Vec<Expr>),
    Write(Vec<Expr>),
    WriteLn(Vec<Expr>),
}

#[derive(Debug, Clone)]
pub struct SumCaseArm {
    pub ctor: String,
    pub binds: Vec<String>,
    pub body: Stmt,
}

#[derive(Debug, Clone)]
pub struct LValue {
    pub base: String,
    pub sels: Vec<Selector>,
}

#[derive(Debug, Clone)]
pub enum Selector {
    Field(String),
    Index(Vec<Expr>),
    Deref,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Int(i32),
    Bool(bool),
    Char(u32), // UTF-32
    Real(u32), // IEEE754 binary32 bits stored in one cell
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
    Cond {
        arms: Vec<CondExprArm>,
        else_block: CondValueBlock,
    },
    Deref(Box<Expr>),
    Field(Box<Expr>, String), // left is address/value depending on context; codegen will special-case lvalues
    Index(Box<Expr>, Box<Expr>),
    Cast(TypeRef, Box<Expr>),
    Unary(UnOp, Box<Expr>),
    Binary(Box<Expr>, BinOp, Box<Expr>),
}

#[derive(Debug, Clone)]
pub struct CondExprArm {
    pub cond: Expr,
    pub block: CondValueBlock,
}

#[derive(Debug, Clone)]
pub struct CondValueBlock {
    pub stmts: Vec<Stmt>,
    pub value: Box<Expr>,
}

#[derive(Debug, Clone)]
pub enum SetItem {
    Single(Expr),
    Range(Expr, Expr),
}

#[derive(Debug, Clone)]
pub enum CaseLabel {
    Single(ConstExpr),
    Range(ConstExpr, ConstExpr),
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone, Copy)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Debug, Clone, Copy)]
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
