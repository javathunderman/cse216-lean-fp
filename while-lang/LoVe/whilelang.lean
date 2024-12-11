import LoVe.LoVelib

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

#print State

inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt

infixr:90 "; " => Stmt.seq


/- The program

  while x > y do
    skip;
    x := x - 1

is modeled as -/

def sillyLoop : Stmt :=
  Stmt.whileDo (fun s ↦ s "x" > s "y")
    (Stmt.skip;
     Stmt.assign "x" (fun s ↦ s "x" - 1))

inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq (S T s t u) (hS : BigStep (S, s) t)
      (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true (B S T s t) (hcond : B s)
      (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | if_false (B S T s t) (hcond : ¬ B s)
      (hbody : BigStep (T, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | while_true (B S s t u) (hcond : B s)
      (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.whileDo B S, t) u) :
    BigStep (Stmt.whileDo B S, s) u
  | while_false (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.whileDo B S, s) s

infix:110 " ⟹ " => BigStep

/- What does this theorem actually say? -/
theorem silly_from_1_BigStep :
  (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ⟹ (fun _ ↦ 0) :=
    by
      rw [sillyLoop] /- what does the rw tactic do? rewrite -/
      apply BigStep.while_true
      { simp }
      { apply BigStep.seq
        { apply BigStep.skip }
        { apply BigStep.assign } }
      simp
      apply BigStep.while_false
      simp

theorem BigStep_deterministic {Ss l r} (hl: Ss ⟹ l)
  (hr: Ss ⟹ r):
    l = r := by
      induction hl with
        | skip => cases hr with
          | skip => rfl
        | assign =>
          cases hr with
            | assign => rfl
        | seq S T s t l hS hT ihS ihT => cases hr with
          | seq _ _ _ t' _ hS' hT' => cases ihS hS' with
            | refl => cases ihT hT' with
              | refl => rfl
        | if_true B S T s l bProp hS iH => cases hr with
          | if_true _ _ _ _ r _ hS' => apply iH hS'
          | if_false => aesop
        | if_false B S T s l hB hS iH => cases hr with
          | if_false B' S T s r hB hS' => apply iH hS'
          | if_true => aesop
        | while_false => cases hr with
          | while_false => rfl
          | while_true => aesop
        | while_true B S s t l hCondS hStepS hRestS ihS iHRestS => cases hr with
          | while_true _ _ _ t' _ hCondT hStepT hRestT => cases ihS hStepT with
            | refl => cases iHRestS hRestT with
              | refl => rfl
          | while_false => aesop

def PartialHoare (P : State → Prop) (S : Stmt)
  (Q : State → Prop) : Prop :=
    ∀s t, P s → (S, s) ⇒ t → Q t
-- Type issue with (S,s), may need 2 define as variable
-- ask prof fremont?

theorem skip_intro {P} :
  {* P *}(Stmt.skip){* P *}
-- Lean issue? may need to define/dig thru lovelib


theorem assign_intro (P) {x a} :
  {* P (s[x ↦ a s])*}(Stmt.assign x a){* P *}

theorem seq_intro {P Q R S T}
  (hS: {*P*}(S){*R*})
  (hT: {*R*}(T){*Q*}) :
  {* P *} (S; T) {* Q *}

theorem if_intro {P B S Q T}
  (h: {fun s ↦ P s ∧ B s} (S) {Q})
  (hb:{fun s ↦ P s ∧ ¬B s} (S) {Q}) :
  {* P *} (Stmt.ifThenElse B S T) {* Q *}

theorem while_intro (P) {B S}
  (hS: {* fun s ↦ P s ∧ B s *} (S) {* P *}) :
    {* P *} (Stmt.whileDo B S) {* fun s ↦ P s ∧ ¬ B s *}

theorem consequence {P P' Q Q' S}
  (hP: P' s → P s)
  (hQ: Q → Q')
  (hS: {*P*} (S) {*Q*}) :
  {* P' *} (S) {* Q' *}

-- maybe try lovelib with deeper arithmetic embeddings?
-- see if it helps
-- maybe ask on zulip or consult documentation

end LoVe
