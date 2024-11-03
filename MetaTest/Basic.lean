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





namespace Lean.Syntax

def setArgr (stx: Syntax) (locs: List ℕ) (arg: Syntax) : Syntax :=
  match locs with
  | .nil => arg
  | .cons i it => stx.setArg i $ stx[i].setArgr it arg


def setArgsr (stx: Syntax) (locs: List ℕ) (args: Array Syntax) : Syntax :=
  match locs with
  | .nil => stx.setArgs args
  | .cons i it => stx.setArg i $ stx[i].setArgsr it args


partial def findall (stx: Syntax) (p: Syntax → Bool) : List Syntax :=
  match stx with
  | stx@(Syntax.node _ _ args) =>
    (if p stx then [stx] else []) ++ args.toList.bind (findall · p)
  | _ => if p stx then [stx] else []


def dedup_syntax : List Syntax → List Syntax :=
  List.pwFilter (toString · ≠ toString ·)


def getProofAfter (stx : Syntax) (pos: String.Pos) : Syntax := Id.run do
  let tactic_seq := stx[1][3][1][1][0][0].getArgs
  let tac_sep := tactic_seq[1]!
  let mut after_seq : Array Syntax := #[]
  for tac in tactic_seq do
    let tac_pos := tac.getPos?.getD 0
    if tac_pos > pos then
      after_seq := (after_seq.push tac).push tac_sep
  (stx.setArgsr [1,3,1,1,0,0] after_seq)[1][3]


def getProofWithin (stx : Syntax) (pos : String.Pos) (endPos : String.Pos) : Syntax := Id.run do
  let tactic_seq := stx[1][3][1][1][0][0].getArgs
  let tac_sep := tactic_seq[1]!
  let mut within_seq : Array Syntax := #[]
  for tac in tactic_seq do
    let tac_pos := tac.getPos?.getD 0
    if tac_pos > pos && tac_pos <= endPos then
      within_seq := (within_seq.push tac).push tac_sep
  (stx.setArgsr [1,3,1,1,0,0] within_seq)[1][3]


def pushTactic (stx : Syntax) (tac : Syntax) : Syntax := Id.run do
  let tactic_seq := stx[1][1][0][0].getArgs
  let tac_sep := tactic_seq[1]!
  let new_seq := (tactic_seq.push tac).push tac_sep
  stx.setArgsr [1,1,0,0] new_seq


def getNearestNoGoalsPos (stx : Syntax) (pos : String.Pos) : String.Pos := Id.run do
  let tactic_seq := stx[1][3][1][1][0][0].getArgs
  let mut nearest_pos := 0
  for tac in tactic_seq do
    let tac_pos := tac.getPos?.getD 0
    if tac_pos > pos then
      break
    nearest_pos := tac_pos
  nearest_pos


end Lean.Syntax


namespace Lean.Elab.Info

/-- The type of a `Lean.Elab.Info`, as a string. -/
def kind : Info → String
  | .ofTacticInfo         _ => "TacticInfo"
  | .ofTermInfo           _ => "TermInfo"
  | .ofCommandInfo        _ => "CommmandInfo"
  | .ofMacroExpansionInfo _ => "MacroExpansionInfo"
  | .ofOptionInfo         _ => "OptionInfo"
  | .ofFieldInfo          _ => "FieldInfo"
  | .ofCompletionInfo     _ => "CompletionInfo"
  | .ofUserWidgetInfo     _ => "UserWidgetInfo"
  | .ofCustomInfo         _ => "CustomInfo"
  | .ofFVarAliasInfo      _ => "FVarAliasInfo"
  | .ofFieldRedeclInfo    _ => "FieldRedeclInfo"
  | .ofOmissionInfo       _ => "OmmisionInfo"

/-- The `Syntax` for a `Lean.Elab.Info`, if there is one. -/
def stx? : Info → Option Syntax
  | .ofTacticInfo         info => info.stx
  | .ofTermInfo           info => info.stx
  | .ofCommandInfo        info => info.stx
  | .ofMacroExpansionInfo info => info.stx
  | .ofOptionInfo         info => info.stx
  | .ofFieldInfo          info => info.stx
  | .ofCompletionInfo     info => info.stx
  | .ofUserWidgetInfo     info => info.stx
  | .ofCustomInfo         info => info.stx
  | .ofFVarAliasInfo      _    => none
  | .ofFieldRedeclInfo    info => info.stx
  | .ofOmissionInfo       info => info.stx

/-- Is the `Syntax` for this `Lean.Elab.Info` original, or synthetic? -/
def isOriginal (i : Info) : Bool :=
  match i.stx? with
  | none => true   -- Somewhat unclear what to do with `FVarAliasInfo`, so be conservative.
  | some stx => match stx.getHeadInfo with
    | .original .. => true
    | _ => false

end Lean.Elab.Info

namespace Lean.Elab.ContextInfo

/-- Pretty print an expression in the given `ContextInfo` with the given `LocalContext`. -/
def ppExpr (ctx : ContextInfo) (lctx : LocalContext) (e : Expr) : IO Format :=
  ctx.runMetaM lctx (do Meta.ppExpr (← instantiateMVars e))

end Lean.Elab.ContextInfo

namespace Lean.Elab.TacticInfo

/-- Find the name for the outermost `Syntax` in this `TacticInfo`. -/
def name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none

/-- Decide whether a tactic is "substantive",
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def isSubstantive (t : TacticInfo) : Bool :=
  match t.name? with
  | none => false
  | some `null => false
  | some ``cdot => false
  | some ``cdotTk => false
  | some ``Lean.Parser.Term.byTactic => false
  | some ``Lean.Parser.Tactic.tacticSeq => false
  | some ``Lean.Parser.Tactic.tacticSeq1Indented => false
  | some ``Lean.Parser.Tactic.«tactic_<;>_» => false
  | some ``Lean.Parser.Tactic.paren => false
  | _ => true

end Lean.Elab.TacticInfo

namespace Lean.Elab.InfoTree

-- /--
-- Keep `.node` nodes and `.hole` nodes satisfying predicates.

-- Returns a `List InfoTree`, although in most situations this will be a singleton.
-- -/
-- partial def filter (p : Info → Bool) (m : MVarId → Bool := fun _ => false) :
--     InfoTree → List InfoTree
--   | .context ctx tree => tree.filter p m |>.map (.context ctx)
--   | .node info children =>
--     if p info then
--       [.node info (children.toList.map (filter p m)).join.toPArray']
--     else
--       (children.toList.map (filter p m)).join
--   | .hole mvar => if m mvar then [.hole mvar] else []

-- /-- Discard all nodes besides `.context` nodes and `TacticInfo` nodes. -/
-- partial def retainTacticInfo (tree : InfoTree) : List InfoTree :=
--   tree.filter fun | .ofTacticInfo _ => true | _ => false

-- /-- Retain only nodes with "original" syntax. -/
-- partial def retainOriginal (tree : InfoTree) : List InfoTree :=
--   tree.filter Info.isOriginal

-- /-- Discard all TacticInfo nodes that are tactic combinators or structuring tactics. -/
-- -- There is considerable grey area here: what to do with `classical`?
-- partial def retainSubstantive (tree : InfoTree) : List InfoTree :=
--   tree.filter fun | .ofTacticInfo i => i.isSubstantive | _ => true

/-- Discard any enclosing `InfoTree.context` layers. -/
def consumeContext : InfoTree → InfoTree
  | .context _ t => t.consumeContext
  | t => t

/-- Is this `InfoTree` a `TermInfo` for some `Expr`? -/
def ofExpr? (i : InfoTree) : Option Expr := match i with
  | .node (.ofTermInfo i) _ => some i.expr
  | _ => none

/-- Is this `InfoTree` a `TermInfo` for some `Name`? -/
def ofName? (i : InfoTree) : Option Name := i.ofExpr?.bind Expr.constName?

/-- Check if the `InfoTree` is the top level `InfoTree` for a declaration,
if so, return it along with the declaration name. -/
def elabDecl? (t : InfoTree) : Option Name :=
  match t.consumeContext with
  | .node (.ofCommandInfo i) c =>
    if i.elaborator == `Lean.Elab.Command.elabDeclaration
    then
      -- this is hacky: we are relying on the ordering of the child nodes.
      c.toList.foldr (fun cc acc => match (cc.consumeContext.ofName?, acc) with
                       | (_, some r) => some r
                       | (some n, none) => some n
                       | (none, none) => none )
                     none
    else
      none
  | _ => none

/-- Analogue of `Lean.Elab.InfoTree.findInfo?`, but that returns a list of all results. -/
partial def findAllInfo (t : InfoTree) (ctx? : Option ContextInfo) (p : Info → Bool) :
    List (Info × Option ContextInfo × PersistentArray InfoTree) :=
  match t with
  | context ctx t => t.findAllInfo (ctx.mergeIntoOuter? ctx?) p
  | node i ts  =>
      (if p i then [(i, ctx?, ts)] else []) ++ ts.toList.bind (fun t => t.findAllInfo ctx? p)
  | _ => []

/-- Return all `TacticInfo` nodes in an `InfoTree` corresponding to tactics,
each equipped with its relevant `ContextInfo`, and any children info trees. -/
def findTacticNodes (t : InfoTree) : List (TacticInfo × ContextInfo × PersistentArray InfoTree) :=
  let infos := t.findAllInfo none fun i => match i with
    | .ofTacticInfo _ => true
    | _ => false
  infos.filterMap fun p => match p with
  | (.ofTacticInfo i, some ctx, children) => (i, ctx, children)
  | _ => none


def findTacticNodes' (t : InfoTree) : List (TacticInfo × ContextInfo × PersistentArray InfoTree) :=
  let infos := t.findAllInfo none fun i => match i with
    | .ofTacticInfo _ => true
    | _ => false
  let infos := infos.filterMap fun p => match p with
  | (.ofTacticInfo i, some ctx, children) => (i, ctx, children)
  | _ => none
  let infos := infos.pwFilter fun (i1, c1, _) (i2, c2, _) =>
    let l1 := c1.fileMap.toPosition (i1.toElabInfo.stx.getPos?.getD 0)
    let l2 := c2.fileMap.toPosition (i2.toElabInfo.stx.getPos?.getD 0)
    ¬l1.line == l2.line
  infos

end Lean.Elab.InfoTree

def addLine (fmt : Format) : Format :=
  if fmt.isNil then fmt else fmt ++ Format.line


def Lean.Meta.ppGoalasDecl_aux (lctx : LocalContext) (linst : LocalInstances) (type : Expr) : MetaM Format := do
    let indent         := 2 -- Use option
    let showLetValues  := pp.showLetValues.get (← getOptions)
    let ppAuxDecls     := pp.auxDecls.get (← getOptions)
    let ppImplDetailHyps := pp.implementationDetailHyps.get (← getOptions)
    let lctx           := lctx
    let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) }
    withLCtx lctx linst do
      -- The following two `let rec`s are being used to control the generated code size.
      -- Then should be remove after we rewrite the compiler in Lean
      let rec pushPending (ids : List Name) (type? : Option Expr) (fmt : Format) : MetaM Format := do
        if ids.isEmpty then
          return fmt
        else
          let fmt := addLine fmt
          match type? with
          | none      => return fmt
          | some type =>
            let typeFmt ← ppExpr type
            return fmt ++ ("(" ++ Format.joinSep ids.reverse (format " ") ++ " :" ++ Format.nest indent (Format.line ++ typeFmt) ++ ")").group
      let rec ppVars (varNames : List Name) (prevType? : Option Expr) (fmt : Format) (localDecl : LocalDecl) : MetaM (List Name × Option Expr × Format) := do
        match localDecl with
        | .cdecl _ _ varName type _ _ =>
          let varName := varName.simpMacroScopes
          let type ← instantiateMVars type
          if prevType? == none || prevType? == some type then
            return (varName :: varNames, some type, fmt)
          else do
            let fmt ← pushPending varNames prevType? fmt
            return ([varName], some type, fmt)
        | .ldecl _ _ varName type val _ _ => do
          let varName := varName.simpMacroScopes
          let fmt ← pushPending varNames prevType? fmt
          let fmt  := addLine fmt
          let type ← instantiateMVars type
          let typeFmt ← ppExpr type
          let mut fmtElem  := format varName ++ " : " ++ typeFmt
          if showLetValues then
            let val ← instantiateMVars val
            let valFmt ← ppExpr val
            fmtElem := fmtElem ++ " :=" ++ Format.nest indent (Format.line ++ valFmt)
          let fmt := fmt ++ fmtElem.group
          return ([], none, fmt)
      let (varNames, type?, fmt) ← lctx.foldlM (init := ([], none, Format.nil)) fun (varNames, prevType?, fmt) (localDecl : LocalDecl) =>
         if !ppAuxDecls && localDecl.isAuxDecl || !ppImplDetailHyps && localDecl.isImplementationDetail then
           return (varNames, prevType?, fmt)
         else
           ppVars varNames prevType? fmt localDecl
    --   return fmt
      let fmt ← pushPending varNames type? fmt
    --   return fmt
      let fmt := addLine fmt
      let typeFmt ← ppExpr (← instantiateMVars type)
      -- let typeFmt1 := mvarDecl.type.coeTypeSet?.getD mvarDecl.type
      let fmt := fmt ++ ": " ++ Format.nest indent typeFmt
      return "lemma aug " ++ fmt


def Lean.Meta.ppGoalasDecl (mvarId: MVarId) : MetaM Format := do
  match (← getMCtx).findDecl? mvarId with
  | none          => return "unknown goal"
  | some mvarDecl => return ← ppGoalasDecl_aux mvarDecl.lctx mvarDecl.localInstances mvarDecl.type


def Lean.Meta.ppGoalStartEndasDecl (mvarId1 mvarId2 : MVarId) : MetaM Format := do
  match (← getMCtx).findDecl? mvarId1, (← getMCtx).findDecl? mvarId2 with
  | none, _       => return "unknown goal"
  | (some _), none       => return "unknown goal"
  | some mvarDec1, some mvarDec2 =>
    let lctx := mvarDec1.lctx.mkLocalDecl (← mkFreshFVarId) `hg2 mvarDec2.type
    return ← ppGoalasDecl_aux lctx mvarDec1.localInstances mvarDec1.type


def Lean.Elab.ContextInfo.ppGoals_as_decl (ctx : ContextInfo) (goals : List MVarId) : IO Format :=
  if goals.isEmpty then
    return "no goals"
  else
    ctx.runMetaM {} (return Std.Format.prefixJoin "\n" (← goals.mapM (Meta.ppGoalasDecl ·)))


def Lean.Elab.ContextInfo.ppGoalsStartEnd_as_decl (ctx : ContextInfo) (goalsStart goalsEnd : List MVarId) : IO Format :=
  if goalsStart.isEmpty then
    return "no goals"
  else if goalsEnd.isEmpty then
    ctx.runMetaM {} (return Std.Format.prefixJoin "\n" (← goalsStart.mapM (Meta.ppGoalasDecl ·)))
  else
    ctx.runMetaM {} (return ← Meta.ppGoalStartEndasDecl goalsStart.head! goalsEnd.head!)


namespace Augmenter


end Augmenter



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
    let stxs := c.raw.findall (·.isOfKind identKind)
    -- logInfo m!"{c.raw[1][3][1][1][0][0][0][1].getKind}"
    logInfo m!"Syntax references: {dedup_syntax stxs}"
    let trees ← getInfoTrees
    for tree in trees do
      let tac_nodes := tree.findTacticNodes' -- Get non-duplicate tactic nodes
      let bi_enumerator := (List.product tac_nodes.enum tac_nodes.enum).filter fun ((i, _), (j, _)) => i < j
      logInfo m!"{tac_nodes.length}"
      logInfo m!"{bi_enumerator.length}"
      for ((_, infoStart, ctxStart, _), (_, infoEnd, ctxEnd, _))
        in bi_enumerator do

        let ctxB := { ctxStart with mctx := infoStart.mctxBefore }
        let ctxA := { ctxEnd with mctx := infoEnd.mctxAfter }
        -- let goalsBefore ← ctxB.ppGoals_as_decl infoStart.goalsBefore
        let statement ← ctxA.ppGoalsStartEnd_as_decl infoStart.goalsBefore infoEnd.goalsAfter
        -- let goalsAfter  ← ctxA.ppGoals_as_decl infoStart.goalsAfter
        let goalsBPos := infoStart.toElabInfo.stx.getPos?.getD 0
        let goalsAPos := infoEnd.toElabInfo.stx.getPos?.getD 0

        -- let nearestNoGoalsPos := c.raw.getNearestNoGoalsPos goalsBPos
        -- let proofAfter := c.raw.getProofAfter goalsBPos
        let proofWithin := c.raw.getProofWithin goalsBPos goalsAPos
        let added_assump := mkIdent `hg2
        let xx ← `(tactic | exact $added_assump)
        let proofWithin := proofWithin.pushTactic xx.raw
        logInfo m!"Augmented Proof No.{goalsBPos}\n{statement}{proofWithin}"
        -- logInfo m!"{proofAfter}"
        -- logInfo m!"{}"
    --   logInfo m!"{← tree.format}"
  finally
    modify fun st =>
      { st with infoState := { st.infoState with trees := initInfoTrees ++ st.infoState.trees } }




set_option pp.rawOnError true

-- set_option pp.coercions false
set_option pp.fullNames true
set_option pp.mvars.withType true
set_option pp.sanitizeNames false

@[coe] def intToZmod (n : ℤ) : ZMod 3 := n

#rwSplitter
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


lemma aug1 (n : ℤ)
(h : ¬3 ∣ n)
(hg2 : ¬(n : ZMod 3) = 0)
: (n : ZMod 3) ≠ 0 := by rw [Ne]; exact hg2


lemma aug2 (n : ℤ)
(h : ¬3 ∣ n)
: (n: ZMod 3) ≠ 0 := by
  rw [Ne]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  assumption

lemma aug3 (n : ℤ)
(h : ¬3 ∣ n)
: ¬(n: ZMod 3) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  assumption


example (a n : ℤ) (h : ¬3 ∣ n) : ↑n ≠ 0 := sorry
