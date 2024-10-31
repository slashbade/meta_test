import Lean
import Mathlib

open Lean Lean.Expr Lean.Meta Lean.Elab Lean.Elab.Command

open ZMod

private lemma cube_of_castHom_ne_zero {n : ZMod 9} :
    castHom (show 3 ∣ 9 by norm_num) (ZMod 3) n ≠ 0 → n ^ 3 = 1 ∨ n ^ 3 = 8 := by
  revert n; decide

/-- If `a b c : ℤ` are such that `¬ 3 ∣ a * b * c`, then `a ^ 3 + b ^ 3 ≠ c ^ 3`. -/
lemma cube_of_not_dvd {n : ℤ} (h : ¬ 3 ∣ n) :
    (n : ZMod 9) ^ 3 = 1 ∨ (n : ZMod 9) ^ 3 = 8 := by
  apply cube_of_castHom_ne_zero
  rw [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  assumption
-- `R` is the domain of the characters
variable {R : Type u} [CommRing R] [Fintype R]

-- `R'` is the target of the characters
variable {R' : Type v} [CommRing R']

/-- Replacing `ψ` by `mulShift ψ a` and multiplying the Gauss sum by `χ a` does not change it. -/
theorem gaussSum_mulShift1 (χ : MulChar R R') (ψ : AddChar R R') (a : Rˣ) :
    χ a * gaussSum χ (AddChar.mulShift ψ a) = gaussSum χ ψ := by
  simp only [gaussSum, AddChar.mulShift_apply, Finset.mul_sum]
  simp_rw [← mul_assoc, ← map_mul]
  exact Fintype.sum_bijective _ a.mulLeft_bijective _ _ fun x ↦ rfl

/-- Replacing `ψ` by `mulShift ψ a` and multiplying the Gauss sum by `χ a` does not change it. -/
theorem gaussSum_mulShift2 (χ : MulChar R R') (ψ : AddChar R R') (a : Rˣ) :
    χ a * gaussSum χ (AddChar.mulShift ψ a) = gaussSum χ ψ := by
  simp only [gaussSum, AddChar.mulShift_apply, Finset.mul_sum]
  simp_rw [← mul_assoc, ← map_mul]
  -- apply Fintype.sum_bijective
  -- pick_goal 3
  -- exact fun x ↦ x

  exact Fintype.sum_bijective _ a.mulLeft_bijective _ _ fun x ↦ rfl


#check cube_of_not_dvd


namespace Lean.Syntax

def setArgr (stx: Syntax) (locs: List ℕ) (arg: Syntax) : Syntax :=
  match locs with
  | .nil => arg
  | .cons i it => stx.setArg i $ stx[i].setArgr it arg


def setArgsr (stx: Syntax) (locs: List ℕ) (args: Array Syntax) : Syntax :=
  match locs with
  | .nil => stx.setArgs args
  | .cons i it => stx.setArg i $ stx[i].setArgsr it args

end Lean.Syntax

open Lean.Syntax Lean.Parser Lean.Elab

elab "#rwSplitter" cmd:command : command => do
  elabCommand cmd
  let tactic_seq := cmd.raw[1][3][1][1][0][0].getArgs
  let tac_sep := tactic_seq[1]!
  let mut new_seq : Array Syntax := #[]
  for tac in tactic_seq do
    if tac.isOfKind ``Tactic.rwSeq then
      let rw_seq := tac[2][1].getArgs.filter (·.isOfKind ``Tactic.rwRule)
      for rw_rule in rw_seq do
        let trule : TSyntax `term := TSyntax.mk rw_rule
        let testrww ← `(tactic | rw [$trule: term])
        -- let testrww := testrww.raw.setKind ``Tactic.rwSeq
        new_seq := (new_seq.push testrww).push tac_sep
    else if tac == tac_sep then pure ()
    else new_seq := (new_seq.push tac).push tac_sep
  new_seq := new_seq.pop
  let processed := cmd.raw.setArgsr [1,3,1,1,0,0] new_seq
  logInfo m!"The normalized proof is\n{processed}."
  -- logInfo m!"The position is {tree}."

elab "#info " c:command : command => do
  let initInfoTrees ← getResetInfoTrees
  try
    elabCommand c
    let trees ← getInfoTrees
    for tree in trees do
      let fm := tree.getCompletionInfos
      -- logInfo m!"{fm}"
      logInfo m!"{← tree.format}"
  finally
    modify fun st =>
      { st with infoState := { st.infoState with trees := initInfoTrees ++ st.infoState.trees } }




set_option pp.rawOnError true

#info
lemma cube_o2f_not_dvd {n : ℤ} (h : ¬ 3 ∣ n) :
    (n : ZMod 9) ^ 3 = 1 ∨ (n : ZMod 9) ^ 3 = 8 := by
  apply cube_of_castHom_ne_zero
  rw [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  assumption
  <;> linarith


#info
lemma cube_o2f_not_dvd1 {n : ℤ} (h : ¬3 ∣ n) : (n : ZMod 9) ^ 3 = 1 ∨ (n : ZMod 9) ^ 3 = 8 :=
  by
  apply cube_of_castHom_ne_zero
  rw [map_intCast]
  rw [Ne]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  assumption
