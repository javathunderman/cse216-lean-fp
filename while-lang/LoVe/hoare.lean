import LoVe.LoVelib
import LoVe.whilelang

set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace LoVe


-- inductive Stmt : Type where
--   | skip       : Stmt
--   | assign     : String → (State → ℕ) → Stmt
--   | seq        : Stmt → Stmt → Stmt
--   | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
--   | whileDo    : (State → Prop) → Stmt → Stmt
-- infixr:90 "; " => Stmt.seq




def PartialHoare (P : State → Prop) (S : Stmt)
  (Q : State → Prop) : Prop :=
    ∀s t, P s → (S, s) ⟹ t → Q t
-- Type issue with (S,s), may need 2 define as variable
-- ask prof fremont?
-- for some reason importing the demo file fixes this

macro "{*" P:term " *} " "(" S:term ")" " {* " Q:term " *}" : term =>
  `(PartialHoare $P $S $Q)

namespace PartialHoare

theorem skip_intro {P} :
  {* P *}(Stmt.skip){* P *} :=
  by
    intro s t hs hst
    cases hst
    assumption

theorem assign_intro (P) {x} :
  {*fun s ↦ P (s[x ↦ (fun _ ↦ DataType.natural 0) s])*}(Stmt.assign x (fun _ ↦ DataType.natural 0)){* P *} :=
  by
    intro s t P' hst
    cases hst with
    | assign => assumption

-- TODO: Show a case where this clearly does not follow

theorem seq_intro {P Q R S T}
  (hS: {*P*}(S){*R*})
  (hT: {*R*}(T){*Q*}) :
  {* P *} (S; T) {* Q *} :=
  by
    intro s t hs hst
    cases hst with
    | seq _ _ _ u d hS' hT' =>
      apply hT
      { apply hS
        { exact hs }
        { assumption } }
      { assumption }

theorem if_intro {B P Q S T}
  (hS: {* fun s ↦ P s ∧ B s *} (S) {* Q*})
  (hT:{* fun s ↦ P s ∧ ¬B s *} (T) {* Q *}) :
  {* P *} (Stmt.ifThenElse B S T) {* Q *} :=
  by
    intro s t hs hst
    cases hst with
    | if_true _ _ _ _ _ hB hS' =>
      apply hS
      exact And.intro hs hB
      assumption
    | if_false _ _ _ _ _ hB hT' =>
      apply hT
      exact And.intro hs hB
      assumption

end PartialHoare
end LoVe
