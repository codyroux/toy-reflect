import Qq
import Mathlib.Tactic.ToExpr
import Aesop

open Lean Qq


inductive BoolTree :=
| trueLeaf : BoolTree
| falseLeaf : BoolTree
| andNode : BoolTree → BoolTree → BoolTree
| orNode : BoolTree → BoolTree → BoolTree
| negNode : BoolTree → BoolTree
deriving Repr, ToExpr

def evalsToTrue (b : BoolTree) : Bool :=
match b with
| .trueLeaf => true
| .falseLeaf => false
| .andNode a b => (evalsToTrue a) && (evalsToTrue b)
| .orNode a b => (evalsToTrue a) || (evalsToTrue b)
| .negNode a => !(evalsToTrue a)

#eval evalsToTrue (.negNode (.andNode .trueLeaf .falseLeaf))

def interp (b : BoolTree) : Prop :=
match b with
| .trueLeaf => True
| .falseLeaf => False
| .andNode a b => (interp a) ∧ (interp b)
| .orNode a b => (interp a) ∨ (interp b)
| .negNode a => ¬ (interp a)

theorem bool_and_false : (b₁ && b₂) = false → b₁ = false ∨ b₂ = false :=
by
  cases b₁ <;> cases b₂ <;> simp

theorem bool_or_false : (b₁ || b₂) = false → b₁ = false ∧ b₂ = false :=
by
  cases b₁ <;> cases b₂ <;> simp

-- tedious but straightforward
theorem evalsToTrue_interp_aux : (evalsToTrue b → interp b) ∧ (evalsToTrue b = false → ¬ interp b) :=
by
  induction b <;> simp [interp, evalsToTrue]
  case andNode ih₁ ih₂ =>
    constructor
    . intros; aesop
    . intro h; have h' := bool_and_false h
      aesop
  case orNode ih =>
    constructor
    . intros; aesop
    . intros h; have h' := bool_or_false h; aesop
  case negNode ih =>
    constructor <;> aesop

theorem evalsToTrue_interp_true : evalsToTrue b → interp b := evalsToTrue_interp_aux.1

-- FIXME: find a better way to do this
def map₂ (f : α → β → γ) (a : Option α) (b : Option β) : Option γ :=
match a, b with
| .some av, .some bv => .some (f av bv)
| _, _ => .none

partial def toInterp (e : Q(Prop)) : MetaM (Option BoolTree) := do
match e with
| ~q(True) => return .some .trueLeaf
| ~q(False) => return .some .falseLeaf
| ~q($a ∧ $b) =>
  let av ← toInterp a
  let bv ← toInterp b
  return map₂ BoolTree.andNode av bv
| ~q($a ∨ $b) =>
  let av ← toInterp a
  let bv ← toInterp b
  return map₂ BoolTree.orNode av bv
| ~q(¬ $a) =>
  let av ← toInterp a
  return Option.map BoolTree.negNode av
| _ => return .none

#eval (toInterp q(True ∧ True ∨ False))

elab "reflect_tac" : tactic =>
 Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let goalTy ← goal.getType
  match ← toInterp goalTy with
  | .none => throwError "Failed to reify"
  | .some tree =>
    let qtree : Q(BoolTree) := q($tree)
    let newGoal ← MVarId.replaceTargetDefEq goal q(interp $qtree)
    let [newGoal] ← newGoal.applyConst ``evalsToTrue_interp_true | throwError "Failure applying lemma"
    newGoal.refl

theorem bar : True ∧ True ∨ False := by
  reflect_tac
