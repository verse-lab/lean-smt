/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean
public meta import Lean

public meta section

/-- Returns `true` if `sub` is a substring of `s` and `false` otherwise. -/
partial def String.isSubStrOf (sub : String) (s : String) : Bool :=
  loop 0
  where
    loop i :=
    if i + sub.length > s.length then false
    else String.Pos.Raw.substrEq sub 0 s ⟨i⟩ sub.length ∨ loop (i + 1)

namespace Smt.Util

open Lean
open Lean.Expr
open Elab.Tactic

/-- Prints the given expression in AST format. -/
def exprToString : Expr → String
  | bvar id          => s!"(BVAR {id})"
  | fvar id          => s!"(FVAR {id.name})"
  | mvar id          => s!"(MVAR {id.name})"
  | sort l           => s!"(SORT {l})"
  | const id l       => s!"(CONST {id} {l})"
  | app f x          => s!"(APP {exprToString f} {exprToString x})"
  | lam id s e _     => s!"(LAM {id} {exprToString s} {exprToString e})"
  | forallE id s e _ => s!"(FORALL {id} {exprToString s} {exprToString e})"
  | letE id s v e _  => s!"(LET {id} {exprToString s} {exprToString v} {exprToString e})"
  | lit l            => s!"(LIT {literalToString l})"
  | mdata m e        => s!"(MDATA {m} {exprToString e})"
  | proj s i e       => s!"(PROJ {s} {i} {exprToString e})"
  where
    literalToString : Literal → String
      | Literal.natVal v => toString v
      | Literal.strVal v => v

/-- Count the number of occurances of the constant `c` in `e`. -/
def countConst (e : Expr) (c : Name) : Nat :=
  let rec visit : Expr → Nat
    | Expr.forallE _ d b _  => visit d + visit b
    | Expr.lam _ d b _      => visit d + visit b
    | Expr.mdata _ e        => visit e
    | Expr.letE _ t v b _   => visit t + visit v + visit b
    | Expr.app f a          => visit f + visit a
    | Expr.proj _ _ e       => visit e
    | Expr.const c' _       => if c' == c then 1 else 0
    | _                     => 0
  visit e

/-- Set of constants defined by SMT-LIB. -/
def smtConsts : Std.HashSet String :=
  Std.HashSet.ofList
  [
    "=",
    "distinct",
    "Bool",
    "true",
    "false",
    "not",
    "and",
    "or",
    "=>",
    "ite",
    "forall",
    "exists",
    "Int",
    "Real",
    "+",
    "-",
    "*",
    "/",
    "div",
    "mod",
    "abs",
    ">",
    "<",
    ">=",
    "<=",
    "str.<",
    "str.++",
    "str.len",
    "str.replace_all",
    "str.at",
    "str.contains",
    "str.to_code",
    "str.from_code"
  ]

/-- SMT-LIB 2.6 reserved words, sort names, and non-indexed operators from cvc5 1.4.2's
`src/parser/smt2/smt2_state.cpp`. These names are unavailable for user declarations. -/
def smtReservedSymbols : Std.HashSet String :=
  Std.HashSet.ofList
  [
    "BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING", "assert", "check-sat", "check-sat-assuming",
    "declare-const", "declare-datatype", "declare-datatypes", "declare-fun", "declare-sort", "define-fun",
    "define-fun-rec", "define-funs-rec", "define-sort", "echo", "exit", "get-assertions", "get-assignment",
    "get-info", "get-model", "get-option", "get-proof", "get-unsat-assumptions", "get-unsat-core",
    "get-value", "pop", "push", "reset", "reset-assertions", "set-info", "set-logic", "set-option",
    "Array", "Bag", "BitVec", "Bool", "FiniteField", "Float16", "Float32", "Float64", "Float128",
    "FloatingPoint", "Int", "Nullable", "Real", "RegLan", "Relation", "RoundingMode", "Seq", "Set",
    "String", "Table", "Tuple", "UnitTuple",
    "!", "*", "+", "-", "/", "/_total", "<", "<=", "=", "=>", ">", ">=", "@", "RNA", "RNE", "RTN",
    "RTP", "RTZ", "^", "_", "abs", "and", "arccos", "arccot", "arccsc", "arcsec", "arcsin",
    "arctan", "as", "bag", "bag.all", "bag.card", "bag.choose", "bag.count",
    "bag.difference_remove", "bag.difference_subtract", "bag.empty", "bag.filter", "bag.fold",
    "bag.inter_min", "bag.map", "bag.member", "bag.partition", "bag.setof", "bag.some",
    "bag.subbag", "bag.union_disjoint", "bag.union_max", "bv2nat", "bvadd", "bvand", "bvashr",
    "bvcomp", "bvite", "bvlshr", "bvmul", "bvnand", "bvneg", "bvnego", "bvnor", "bvnot", "bvor",
    "bvredand", "bvredor", "bvsaddo", "bvsdiv", "bvsdivo", "bvsge", "bvsgt", "bvshl", "bvsle",
    "bvslt", "bvsmod", "bvsmulo", "bvsrem", "bvssubo", "bvsub", "bvuaddo", "bvudiv", "bvuge",
    "bvugt", "bvule", "bvult", "bvumulo", "bvurem", "bvusubo", "bvxnor", "bvxor", "concat", "cos",
    "cot", "csc", "distinct", "div", "div_total", "eqrange", "exists", "exp", "false", "ff.add",
    "ff.bitsum", "ff.mul", "ff.neg", "forall", "fp", "fp.abs", "fp.add", "fp.div", "fp.eq",
    "fp.fma", "fp.geq", "fp.gt", "fp.isInfinite", "fp.isNaN", "fp.isNegative", "fp.isNormal",
    "fp.isPositive", "fp.isSubnormal", "fp.isZero", "fp.leq", "fp.lt", "fp.max", "fp.min", "fp.mul",
    "fp.neg", "fp.rem", "fp.roundToIntegral", "fp.sqrt", "fp.sub", "fp.to_real", "int.log2",
    "int.pow2", "is_int", "ite", "lambda", "let", "match", "mod", "mod_total", "not",
    "nullable.is_null", "nullable.is_some", "nullable.lift", "nullable.null", "nullable.some",
    "nullable.val", "or", "par", "piand", "pto", "re.*", "re.+", "re.++", "re.all", "re.allchar",
    "re.comp", "re.diff", "re.inter", "re.none", "re.opt", "re.range", "re.union", "real.pi",
    "rel.aggr", "rel.group", "rel.iden", "rel.join", "rel.join_image", "rel.product", "rel.project",
    "rel.table_join", "rel.tclosure", "rel.transpose", "roundNearestTiesToAway",
    "roundNearestTiesToEven", "roundTowardNegative", "roundTowardPositive", "roundTowardZero",
    "sbv_to_int", "sec", "select", "sep", "sep.emp", "sep.nil", "seq.++", "seq.at", "seq.contains",
    "seq.empty", "seq.extract", "seq.indexof", "seq.len", "seq.nth", "seq.prefixof", "seq.replace",
    "seq.replace_all", "seq.rev", "seq.suffixof", "seq.unit", "seq.update", "set.all", "set.card",
    "set.choose", "set.complement", "set.comprehension", "set.empty", "set.filter", "set.fold",
    "set.insert", "set.inter", "set.is_empty", "set.is_singleton", "set.map", "set.member",
    "set.minus", "set.singleton", "set.some", "set.subset", "set.union", "set.universe", "sin",
    "sqrt", "store", "str.++", "str.<", "str.<=", "str.at", "str.contains", "str.from_code",
    "str.from_int", "str.in_re", "str.indexof", "str.indexof_re", "str.is_digit", "str.len",
    "str.prefixof", "str.replace", "str.replace_all", "str.replace_re", "str.replace_re_all",
    "str.rev", "str.substr", "str.suffixof", "str.to_code", "str.to_int", "str.to_lower",
    "str.to_re", "str.to_upper", "str.update", "table.aggr", "table.group", "table.join",
    "table.product", "table.project", "tan", "to_int", "to_real", "true", "tuple", "tuple.project",
    "tuple.unit", "ubv_to_int", "wand", "xor"
  ]

private def roundtrips (n : Name) (s : String) : Bool :=
  !n.isAnonymous && s.toName == n && !s.startsWith "$" && !s.startsWith "@" && !s.startsWith "." &&
    !s.any (fun c => c == '|' || c == '\\' || c.toNat < 32 || c.toNat == 127)

/-- Keep round-tripping constant names readable. Mangle the rest before SMT quoting can lose
information. A leading dollar sign is reserved for symbols generated by the translator. -/
def constSymbol (n : Name) : String :=
  let s := n.toString
  if smtConsts.contains s || (roundtrips n s && !smtReservedSymbols.contains s) then s
  else n.mangle "$const!"

/-- Choose a variable name whose spelling survives both SMT quoting and reconstruction. -/
def freshVarName [Monad m] [MonadEnv m] (n : Name) (taken : String → m Bool) : m Name := do
  let s := n.toString
  let base := if roundtrips n s then n else `v
  let env ← getEnv
  let mut candidate := base
  let mut i := 1
  while smtReservedSymbols.contains candidate.toString || env.contains candidate ||
      (← taken candidate.toString) do
    candidate := base.appendIndexAfter i
    i := i + 1
  return candidate

/-- Like `unfoldProjInst?`, but iterated in case a typeclass projection
is defined in terms of another. -/
partial def unfoldProjInsts? (e : Expr) : MetaM (Option Expr) := do
  let some e' ← Meta.unfoldProjInst? e | return none
  let some e'' ← unfoldProjInsts? e' | return e'
  return e''

/-- Returns an expression equivalent to `e` with all typeclass projections
    unfolded. -/
def unfoldAllProjInsts : Expr → MetaM Expr :=
  Meta.transform (pre := pre)
where
  pre e : MetaM TransformStep := return match ← Meta.unfoldProjInst? e with
    | some e => .visit e
    | none   => .continue

end Smt.Util
