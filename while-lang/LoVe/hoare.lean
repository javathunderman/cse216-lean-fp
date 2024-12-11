import LoVe.LoVelib
import LoVe.Demo9

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



theorem assign_intro (P) {x a} :
  {*fun s ↦ P (s[x ↦ a s])*}(Stmt.assign x a){* P *} :=
  by
    intro s t P' hst
    cases hst with
    | assign => assumption

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

theorem if_intro {P B S Q T}
  (h: {* fun s ↦ P s ∧ B s *} (S) {* Q*})
  (hb:{* fun s ↦ P s ∧ ¬B s *} (S) {* Q *}) :
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

theorem while_intro (P) {B S}
    (h : {* fun s ↦ P s ∧ B s *} (S) {* P *}) :
  {* P *} (Stmt.whileDo B S) {* fun s ↦ P s ∧ ¬ B s *} :=
  by
    intro s t hs hst
    generalize ws_eq : (Stmt.whileDo B S, s) = Ss
    rw [ws_eq] at hst
    induction hst generalizing s with
    | skip s'                       => cases ws_eq
    | assign x a s'                 => cases ws_eq
    | seq S T s' t' u hS hT ih      => cases ws_eq
    | if_true B S T s' t' hB hS ih  => cases ws_eq
    | if_false B S T s' t' hB hT ih => cases ws_eq
    | while_true B' S' s' t' u hB' hS hw ih_hS ih_hw =>
      cases ws_eq
      apply ih_hw
      { apply h
        { apply And.intro <;>
            assumption }
        { exact hS } }
      { rfl }
    | while_false B' S' s' hB'      =>
      cases ws_eq
      aesop

theorem consequence {P P' Q Q' S}
    (h : {* P *} (S) {* Q *}) (hp : ∀s, P' s → P s)
    (hq : ∀s, Q s → Q' s) :
  {* P' *} (S) {* Q' *} :=
  fix s t : State
  assume hs : P' s
  assume hst : (S, s) ⟹ t
  show Q' t from
    hq _ (h s t (hp s hs) hst)


end PartialHoare
end LoVe
