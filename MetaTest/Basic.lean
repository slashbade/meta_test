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


#check cube_of_not_dvd
-- open Lean.Elab.Tactic


def parseExpr (v : Expr) : CommandElabM Unit := do
  match v with
  | const _ _ => pure ()
    -- logInfo s!"const {v}"
  | Expr.mdata md v' =>
    logInfo s!"Transformed proof:\n{md}"
    parseExpr v'
  | Expr.app f a => do
    parseExpr f
    parseExpr a
    -- logInfo s!"{a}"
  | Expr.lam _ l1 l2 _ => do
    parseExpr l1
    parseExpr l2
  | lit _ => pure ()
  | proj _ _ s =>
    parseExpr s
  | info =>
    logInfo s!"{info}"


def decompose_rw (thm_name : Name) : CommandElabM Unit := do
  let scope ← getScope
  let info := toString scope.header
  let env ← getEnv
  let info := env.constants.find? thm_name
  -- let info := scope.varDecls
  -- logInfo s!"{info}"
  match info with
  | none => throwError "Theorem '{thm_name}' not found"
  | some aa =>
    let value := aa.value!
    logInfo s!"{value}"
    parseExpr value


-- #eval decompose_rw `gaussSum_mulShift1
open Lean Elab Parser Command
elab "getName " cmd:command : command => do
  elabCommand cmd
  match cmd.raw.find? (·.isOfKind ``declId) with
    | some nm => logInfo m!"The name is '{nm}'."
    | none => logInfo m!"No given name."

elab "getProof" cmd:command : command => do
  elabCommand cmd
  let allArgs := cmd.raw[1][3][1][1][0][0][2][2]
  logInfo m!"The proof is '{allArgs}'."

elab "getInfo" cmd:command : command => do
  elabCommand cmd
  match cmd.raw.find? (·.isOfKind ``Lean.Parser.Tactic.rwSeq) with
    | some nm =>
      let rw_seq := nm[2][1].getArgs.filter (·.isOfKind ``Lean.Parser.Tactic.rwRule)
      -- let nm := nm.setArg 2 $ nm[2].setArg 1 (nm[2][1].setArg 0 nm[2][1][2])
      -- let nm := nm.setArg 2 $ nm[2][1].setArgs (#[nm[2][1][0]])
      let nm :=  rw [abs]
      logInfo m!"The tactic sequence is '{nm}'."
    | none => logInfo m!"No given name."

def split_rw (stx : Syntax) : Syntax := Id.run do
  let mut newStx := #[]
  for rwRule in stx[1].getArgs do
    let rwRule := rwRule[1]
    let rwRule := rwRule.setArg 1 $ mkAtom "⬝"
    newStx := newStx.setArg 1 $ newStx[1].setArg 0 rwRule
  newStx

set_option pp.rawOnError true

getInfo
lemma cube_o2f_not_dvd {n : ℤ} (h : ¬ 3 ∣ n) :
    (n : ZMod 9) ^ 3 = 1 ∨ (n : ZMod 9) ^ 3 = 8 := by
  apply cube_of_castHom_ne_zero
  rw [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  assumption
