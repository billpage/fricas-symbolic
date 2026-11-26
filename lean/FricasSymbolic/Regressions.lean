import FricasSymbolic.Rewriting
import Mathlib.Tactic.NormNum

/-!
# Part 1: regressions

**L7** (plan §3.4). Without the completion rule (AN), the normaliser is not
confluent: the step `x + (1+2) → (x+1)+2` by (A) joins two terms whose normal
forms differ, `x+3` and `(x+1)+2`. With (AN) both normalise to `x+3`.

**L10** (found 2026-11-26 while writing part 1). Spec Theorem 3 claims that every
union of the groups of `A_P` is confluent. With Id but without Num it is not:
`0 - 0` rewrites to `0` by `x - 0 → x` and to `-0` by `0 - x → -x`, and both are
normal forms. The proof of Theorem 3 joins them with Num (`-0 → 0`). FriCAS
agrees: in `GeneralSymbolicExpression(Integer, [identities])`, `0 - 0` has form
`0` and `-0` has form `(- 0)` (run `20261126-184235-id-zero-minus-zero`).
-/

namespace FricasSymbolic

open Term

/-- `A_P` with associativity: the groups of the regression. -/
def AP : Ax := {id := true, ann := true, inv := true, num := true, assoc := true}

theorem sAdd_num (A : Ax) (h : A.num = true) (p q : ℚ) :
    sAdd A (.num p) (.num q) = .num (p + q) := by
  rw [sAdd]; simp [h, isNum, nv]

/-- L7: without (AN), a single (A) step separates two normal forms. -/
theorem L7_without_AN :
    let A : Ax := {AP with an := false}
    let s := Term.add (.var "x") (.add (.num 1) (.num 2))
    let t := Term.add (.add (.var "x") (.num 1)) (.num 2)
    Step A s t ∧ nf A s = .add (.var "x") (.num 3) ∧ nf A t = t := by
  intro A s t
  have h12 : sAdd A (.num 1) (.num 2) = .num 3 := by rw [sAdd_num A rfl]; norm_num
  refine ⟨Step.root (Root.assoc_add _ _ _ rfl), ?_, ?_⟩
  · simp only [s, nf, h12]
    rw [sAdd]; simp [A, AP, isNum, isLit, nv, isAdd]
  · simp only [t, nf]
    rw [sAdd]; simp [A, AP, isNum, isLit, nv, isAdd]
    rw [sAdd]; simp [isNum, isLit, nv, isAdd, snd]

/-- L7, the other half: with (AN), both sides of the step normalise to `x+3`. -/
theorem L7_with_AN :
    let s := Term.add (.var "x") (.add (.num 1) (.num 2))
    let t := Term.add (.add (.var "x") (.num 1)) (.num 2)
    nf AP s = .add (.var "x") (.num 3) ∧ nf AP t = .add (.var "x") (.num 3) := by
  intro s t
  have h12 : sAdd AP (.num 1) (.num 2) = .num 3 := by rw [sAdd_num AP rfl]; norm_num
  constructor
  · simp only [s, nf, h12]
    rw [sAdd]; simp [AP, isNum, isLit, nv, isAdd]
  · simp only [t, nf]
    have h1 : sAdd AP (.var "x") (.num 1) = .add (.var "x") (.num 1) := by
      rw [sAdd]; simp [AP, isNum, isLit, nv, isAdd]
    rw [h1, sAdd]; simp [AP, isNum, isLit, nv, isAdd, snd, fst]; norm_num
    rw [sAdd]; simp [isNum, isLit, nv, isAdd]

theorem isNF_num (A : Ax) (q : ℚ) : IsNF A (.num q) := by
  intro t h
  cases h with
  | root r => cases r

/-- L10: with Id and without Num, `0 - 0` has two distinct normal forms. -/
theorem L10_id_without_num :
    let A : Ax := {id := true}
    Step A (.sub (.num 0) (.num 0)) (.num 0) ∧
    Step A (.sub (.num 0) (.num 0)) (.neg (.num 0)) ∧
    IsNF A (.num 0) ∧ IsNF A (.neg (.num 0)) ∧
    (Term.num 0) ≠ .neg (.num 0) := by
  refine ⟨Step.root (Root.id_sub_r _ rfl), Step.root (Root.id_sub_l _ rfl), isNF_num _ _, ?_, ?_⟩
  · intro t h
    cases h with
    | root r =>
      cases r with
      | num_neg _ h => exact absurd h (by decide)
    | neg h' => exact isNF_num _ _ _ h'
  · intro h; cases h

/-- L10, consequence: for `A = {Id}`, terms equal under the axioms can have
different normal forms, so Theorem 3's "every union of its groups" fails. -/
theorem L10_not_confluent :
    ¬ ∀ s t, EqA {id := true} s t → nf {id := true} s = nf {id := true} t := by
  intro h
  have e : EqA {id := true} (.num 0) (.neg (.num 0)) :=
    Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Step.root (Root.id_sub_r _ rfl))))
      (Relation.EqvGen.rel _ _ (Step.root (Root.id_sub_l _ rfl)))
  have := h _ _ e
  simp [nf, sNeg] at this

end FricasSymbolic
