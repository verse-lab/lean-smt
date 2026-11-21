/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp
public import Smt.Preprocess.Basic
public meta import Smt.Preprocess.Basic
public import Smt.Preprocess.Normalize.Attribute
public meta import Smt.Preprocess.Normalize.Attribute

public meta section

namespace Smt.Preprocess

open Lean

def normalizeWithFin (enableFin : Bool) (mv : MVarId) (hs : Array Expr) : MetaM Result := mv.withContext do
  let (hintIds, originalToLocal, mv) ← assertHints mv hs
  -- Revert all hypotheses in `mv`'s context.
  let fvs ← Meta.sortFVarIds hintIds
  let (fvs', mv) ← mv.revert fvs true
  -- Simplify the goal using the smt_normalize theorems.
  let mv ← simpTargetWithExtensions mv `smt_normalize `fin_normalize enableFin
  -- Re-introduce all free vars.
  let (fvs'', mv) ← mv.introNP fvs'.size
  -- Compose the final map from new free vars to old ones.
  let localToNew := Std.HashMap.ofList ((fvs'.zip fvs'').map fun (of, to) => (.fvar of, .fvar to)).toList
  let (hs', map) := restoreHints hs originalToLocal localToNew
  return { map := map, hs := hs', mv }

def normalize := normalizeWithFin true

end Smt.Preprocess
