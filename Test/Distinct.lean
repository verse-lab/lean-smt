import Smt

universe u

-- Empty and singleton literals are translated to SMT-LIB `true`.
example : distinctN ([] : List Nat) := by
  smt

example (x : Nat) : distinctN [x] := by
  smt

-- The public definition ranges over `Type`, including `Prop : Type`.
example {α : Type u} (xs : List α) : Prop :=
  distinctN xs

/--
error: Application type mismatch: The argument
  h
has type
  P
of sort `Prop` but is expected to have type
  ?m.5 h
of sort `Type ?u.5` in the application
  List.cons h
-/
#guard_msgs in
#check fun {P : Prop} (h : P) => distinctN [h]

-- SMT disequality itself remains available over arbitrary `Sort`; only the
-- compact public `distinctN` connective is restricted to `Type`.
example {α : Sort u} (a b : α) (h : a ≠ b) : a ≠ b := by
  smt [h]

example (p q : Prop) (h : distinctN [p, q]) : p ≠ q := by
  smt [h]

-- Basic n-ary translation and reconstruction of a compact `distinctN` proof.
example {U : Type} [Nonempty U] (a b c : U)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : distinctN [a, b, c] := by
  smt [hab, hac, hbc]

-- Reconstruct a selected pair without expanding the full pairwise conjunction.
example {U : Type} [Nonempty U] (a b c : U) (h : distinctN [a, b, c]) : a ≠ c := by
  smt [h]

-- Equal expressions at distinct positions must remain distinct positions.
example {U : Type} [Nonempty U] (a b : U) (h : distinctN [a, b, a]) : a ≠ a := by
  smt [h]

open Lean Elab Term in
syntax:max "distinctRange% " num : term

axiom LargeEnum : Type
axiom v000 : LargeEnum
axiom v001 : LargeEnum
axiom v002 : LargeEnum
axiom v003 : LargeEnum
axiom v004 : LargeEnum
axiom v005 : LargeEnum
axiom v006 : LargeEnum
axiom v007 : LargeEnum
axiom v008 : LargeEnum
axiom v009 : LargeEnum
axiom v010 : LargeEnum
axiom v011 : LargeEnum
axiom v012 : LargeEnum
axiom v013 : LargeEnum
axiom v014 : LargeEnum
axiom v015 : LargeEnum
axiom v016 : LargeEnum
axiom v017 : LargeEnum
axiom v018 : LargeEnum
axiom v019 : LargeEnum
axiom v020 : LargeEnum
axiom v021 : LargeEnum
axiom v022 : LargeEnum
axiom v023 : LargeEnum
axiom v024 : LargeEnum
axiom v025 : LargeEnum
axiom v026 : LargeEnum
axiom v027 : LargeEnum
axiom v028 : LargeEnum
axiom v029 : LargeEnum
axiom v030 : LargeEnum
axiom v031 : LargeEnum
axiom v032 : LargeEnum
axiom v033 : LargeEnum
axiom v034 : LargeEnum
axiom v035 : LargeEnum
axiom v036 : LargeEnum
axiom v037 : LargeEnum
axiom v038 : LargeEnum
axiom v039 : LargeEnum
axiom v040 : LargeEnum
axiom v041 : LargeEnum
axiom v042 : LargeEnum
axiom v043 : LargeEnum
axiom v044 : LargeEnum
axiom v045 : LargeEnum
axiom v046 : LargeEnum
axiom v047 : LargeEnum
axiom v048 : LargeEnum
axiom v049 : LargeEnum
axiom v050 : LargeEnum
axiom v051 : LargeEnum
axiom v052 : LargeEnum
axiom v053 : LargeEnum
axiom v054 : LargeEnum
axiom v055 : LargeEnum
axiom v056 : LargeEnum
axiom v057 : LargeEnum
axiom v058 : LargeEnum
axiom v059 : LargeEnum
axiom v060 : LargeEnum
axiom v061 : LargeEnum
axiom v062 : LargeEnum
axiom v063 : LargeEnum
axiom v064 : LargeEnum
axiom v065 : LargeEnum
axiom v066 : LargeEnum
axiom v067 : LargeEnum
axiom v068 : LargeEnum
axiom v069 : LargeEnum
axiom v070 : LargeEnum
axiom v071 : LargeEnum
axiom v072 : LargeEnum
axiom v073 : LargeEnum
axiom v074 : LargeEnum
axiom v075 : LargeEnum
axiom v076 : LargeEnum
axiom v077 : LargeEnum
axiom v078 : LargeEnum
axiom v079 : LargeEnum
axiom v080 : LargeEnum
axiom v081 : LargeEnum
axiom v082 : LargeEnum
axiom v083 : LargeEnum
axiom v084 : LargeEnum
axiom v085 : LargeEnum
axiom v086 : LargeEnum
axiom v087 : LargeEnum
axiom v088 : LargeEnum
axiom v089 : LargeEnum
axiom v090 : LargeEnum
axiom v091 : LargeEnum
axiom v092 : LargeEnum
axiom v093 : LargeEnum
axiom v094 : LargeEnum
axiom v095 : LargeEnum
axiom v096 : LargeEnum
axiom v097 : LargeEnum
axiom v098 : LargeEnum
axiom v099 : LargeEnum
axiom v100 : LargeEnum
axiom v101 : LargeEnum
axiom v102 : LargeEnum
axiom v103 : LargeEnum
axiom v104 : LargeEnum
axiom v105 : LargeEnum
axiom v106 : LargeEnum
axiom v107 : LargeEnum
axiom v108 : LargeEnum
axiom v109 : LargeEnum
axiom v110 : LargeEnum
axiom v111 : LargeEnum
axiom v112 : LargeEnum
axiom v113 : LargeEnum
axiom v114 : LargeEnum
axiom v115 : LargeEnum
axiom v116 : LargeEnum
axiom v117 : LargeEnum
axiom v118 : LargeEnum
axiom v119 : LargeEnum
axiom v120 : LargeEnum
axiom v121 : LargeEnum
axiom v122 : LargeEnum
axiom v123 : LargeEnum
axiom v124 : LargeEnum
axiom v125 : LargeEnum
axiom v126 : LargeEnum
axiom v127 : LargeEnum
axiom v128 : LargeEnum
axiom v129 : LargeEnum
axiom v130 : LargeEnum
axiom v131 : LargeEnum
axiom v132 : LargeEnum
axiom v133 : LargeEnum
axiom v134 : LargeEnum
axiom v135 : LargeEnum
axiom v136 : LargeEnum
axiom v137 : LargeEnum
axiom v138 : LargeEnum
axiom v139 : LargeEnum
axiom v140 : LargeEnum
axiom v141 : LargeEnum
axiom v142 : LargeEnum
axiom v143 : LargeEnum
axiom v144 : LargeEnum
axiom v145 : LargeEnum
axiom v146 : LargeEnum
axiom v147 : LargeEnum
axiom v148 : LargeEnum
axiom v149 : LargeEnum
axiom v150 : LargeEnum
axiom v151 : LargeEnum
axiom v152 : LargeEnum
axiom v153 : LargeEnum
axiom v154 : LargeEnum
axiom v155 : LargeEnum
axiom v156 : LargeEnum
axiom v157 : LargeEnum
axiom v158 : LargeEnum
axiom v159 : LargeEnum
axiom v160 : LargeEnum
axiom v161 : LargeEnum
axiom v162 : LargeEnum
axiom v163 : LargeEnum
axiom v164 : LargeEnum
axiom v165 : LargeEnum
axiom v166 : LargeEnum
axiom v167 : LargeEnum
axiom v168 : LargeEnum
axiom v169 : LargeEnum
axiom v170 : LargeEnum
axiom v171 : LargeEnum
axiom v172 : LargeEnum
axiom v173 : LargeEnum
axiom v174 : LargeEnum
axiom v175 : LargeEnum
axiom v176 : LargeEnum
axiom v177 : LargeEnum
axiom v178 : LargeEnum
axiom v179 : LargeEnum
axiom v180 : LargeEnum
axiom v181 : LargeEnum
axiom v182 : LargeEnum
axiom v183 : LargeEnum
axiom v184 : LargeEnum
axiom v185 : LargeEnum
axiom v186 : LargeEnum
axiom v187 : LargeEnum
axiom v188 : LargeEnum
axiom v189 : LargeEnum
axiom v190 : LargeEnum
axiom v191 : LargeEnum
axiom v192 : LargeEnum
axiom v193 : LargeEnum
axiom v194 : LargeEnum
axiom v195 : LargeEnum
axiom v196 : LargeEnum
axiom v197 : LargeEnum
axiom v198 : LargeEnum
axiom v199 : LargeEnum
axiom v200 : LargeEnum
axiom v201 : LargeEnum
axiom v202 : LargeEnum
axiom v203 : LargeEnum
axiom v204 : LargeEnum
axiom v205 : LargeEnum
axiom v206 : LargeEnum
axiom v207 : LargeEnum
axiom v208 : LargeEnum
axiom v209 : LargeEnum
axiom v210 : LargeEnum
axiom v211 : LargeEnum
axiom v212 : LargeEnum
axiom v213 : LargeEnum
axiom v214 : LargeEnum
axiom v215 : LargeEnum
axiom v216 : LargeEnum
axiom v217 : LargeEnum
axiom v218 : LargeEnum
axiom v219 : LargeEnum
axiom v220 : LargeEnum
axiom v221 : LargeEnum
axiom v222 : LargeEnum
axiom v223 : LargeEnum
axiom v224 : LargeEnum
axiom v225 : LargeEnum
axiom v226 : LargeEnum
axiom v227 : LargeEnum
axiom v228 : LargeEnum
axiom v229 : LargeEnum
axiom v230 : LargeEnum
axiom v231 : LargeEnum
axiom v232 : LargeEnum
axiom v233 : LargeEnum
axiom v234 : LargeEnum
axiom v235 : LargeEnum
axiom v236 : LargeEnum
axiom v237 : LargeEnum
axiom v238 : LargeEnum
axiom v239 : LargeEnum

instance : Nonempty LargeEnum := ⟨v000⟩

open Lean Elab Term in
elab_rules : term
  | `(distinctRange% $n:num) => do
    let count := n.getNat
    let elems : Array (TSyntax `term) ← (Array.range count).mapM fun i => do
      let suffix :=
        if i < 10 then s!"00{i}"
        else if i < 100 then s!"0{i}"
        else toString i
      `(term| $(mkIdent s!"v{suffix}".toName):ident)
    elabTerm (← `(distinctN [$[$elems],*])) none

-- Lean's list macro chunks this literal behind lets. Translation and compact
-- reconstruction must both retain the source hypothesis.
set_option maxRecDepth 1024 in
example (h : distinctRange% 80) : v000 ≠ v079 := by
  smt [h]

-- Veil's large-enumeration macro produces list literals of this size. This
-- simultaneously exercises let-chunk literal translation and scalable
-- `AND_ELIM` reconstruction for a selected subtree.
set_option maxRecDepth 1024 in
example (h : distinctRange% 240) :
    ((v000 ≠ v239 ∧ v000 ≠ v001) ∧ v001 ≠ v002) ∧
      (v160 ≠ v194 ∧ v025 ≠ v026) := by
  smt (timeout := some 30) [h]
