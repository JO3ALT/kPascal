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
}

#[derive(Debug, Clone)]
pub enum TypeSpec {
    Basic(BasicType),
    Enum(Vec<String>),
    Record(Vec<FieldDecl>),
    SumRecord(Vec<SumArmDecl>),
    Array { dims: Vec<ArrayDim>, elem: TypeRef },
    Alias(TypeRef),
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
pub enum BasicType {
    Integer,
    Boolean,
    Char,
    Float,
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
}

#[derive(Debug, Clone)]
pub struct ArrayDim {
    pub low: ConstExpr,
    pub high: ConstExpr,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Empty,
    Compound(Vec<Stmt>),
    Assign(LValue, Expr),
    Read(Vec<LValue>),
    ReadLn,
    For {
        var: String,
        init: Expr,
        limit: Expr,
        downto: bool,
        body: Box<Stmt>,
    },
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    While(Expr, Box<Stmt>),
    Repeat(Vec<Stmt>, Expr),
    Case {
        expr: Expr,
        arms: Vec<(ConstExpr, Stmt)>,
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

impl Default for Stmt {
    fn default() -> Self {
        Self::Empty
    }
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
    Char(u32),  // UTF-32
    Float(u32), // IEEE754 binary32 bits in u32 cell
    Str(String),
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
pub enum ConstExpr {
    Int(i32),
    Bool(bool),
    Char(u32),
    Float(u32),
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
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}
