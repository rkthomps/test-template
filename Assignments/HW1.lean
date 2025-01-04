
namespace HW1

open Nat
open Int
open Option


/-
Problem 1: Absolute Value
-/

def abs : Int → Int
  | ofNat x => ofNat x
  | negSucc x => ofNat (succ x)


theorem abs_pos : ∀ (i : Int),
  0 ≤ i → i = abs i := by
  sorry


theorem abs_neg : ∀ (i : Int),
  i < 0 → -i = abs i := by
  sorry

/-
Problem 2a: Sub Option
-/
def sub (x y : Nat) : Option Nat :=
  match y with
  | zero => some x
  | succ y' => match x with
    | zero => none
    | succ x' => sub x' y'

theorem sub_none : ∀ (x y : Nat),
  x < y → sub x y = none := by
  sorry


theorem sub_none' : ∀ (x y : Nat),
  x < y → sub x y = none := by
  sorry

theorem sub_some : ∀ (x y : Nat),
  y ≤ x →
  ∃ z, (sub x y = Option.some z) ∧ (z + y = x) := by
  sorry



/-
Problem 2b: Sub Dependent type
-/
def sub' (x y : Nat) (pf : y ≤ x) : Nat :=
  match y with
  | zero => x
  | succ y' => match x with
    | zero =>
      have hf : False := by contradiction
      nomatch hf
    | succ x' =>
      have pf' : y' ≤ x' := by omega
      sub' x' y' pf'


theorem sub'_zero : ∀ x p, sub' x 0 p = x  := by
  sorry


theorem sub'_le : ∀ x y p, sub' x y p ≤ x := by
  sorry




/-
Problem 3: Split (or half)
-/

def split : (x : Nat) → (Nat × Nat)
  | zero => (zero, zero)
  | succ x' => match x' with
    | zero => (1, 0)
    | succ x'' =>
      let (s₁, s₂) := split x''
      (succ s₁, succ s₂)


theorem split_sum : ∀ (x s₁ s₂),
  split x = (s₁, s₂) →
  s₁ + s₂ = x := by
  sorry

/-
Problem 4: Take
-/

def take [DecidableEq α] (i : Nat) (l : List α) : List α :=
  match i with
  | zero => []
  | succ i' =>
    match l with
    | [] => []
    | h :: tl => h :: (take i' tl)


def eq_to [DecidableEq α] (i : Nat) (l₁ l₂ : List α) : Bool :=
  match i with
  | zero => true
  | succ n' =>
    match (l₁, l₂) with
    | ([], []) => true
    | ([], _) => false
    | (_, []) => false
    | (h₁ :: t₁, h₂ :: t₂) => and (h₁ = h₂) (eq_to n' t₁ t₂)


theorem take_eq_to [DecidableEq α] : ∀ (i : Nat) (l : List α),
  eq_to i l (take i l) = true := by
  sorry


/-
Problem 5: Drop
-/

def drop [DecidableEq α] (i : Nat) (l : List α) : List α :=
  match i with
  | zero => l
  | succ i' => match l with
    | [] => []
    | _ :: tl => drop i' tl


theorem take_drop [DecidableEq α] : ∀ (i : Nat) (l : List α),
  take i l ++ drop i l = l := by
  sorry

/-
Problem 6: Reverse Take Drop
-/

def reverse (l : List α) : List α :=
  match l with
  | [] => []
  | h :: tl => reverse tl ++ [h]


theorem reverse_length : ∀ (l : List α), l.length = (reverse l).length := by
  sorry


theorem drop_length [DecidableEq α] : ∀ (l : List α), drop (l.length) l = [] := by
  sorry


theorem drop_app [DecidableEq α] : ∀ (i : Nat) (l₁ l₂: List α),
  i ≤ l₁.length → drop i l₁ ++ l₂ = drop i (l₁ ++ l₂) := by
  sorry


theorem take_rev [DecidableEq α] : ∀ (i : Nat) (l : List α) (h : i ≤ l.length),
  reverse (take i l) = drop (sub' l.length i h) (reverse l) := by
  sorry

/-
Problem 7: Tables
-/

inductive Table (key val : Type) where
  | empty
  | bind : key → val → Table key val → Table key val


inductive InTable [DecidableEq key] : key → Table key val → Prop
  | in_bind_hd (k : key) (v : val) (t : Table key val) : InTable k (.bind k v t)
  | in_bind_tl (k k' : key) (v : val) (t : Table key val) :
    InTable k t → InTable k (.bind k' v t)


def in_table [DecidableEq key] (k : key) : Table key val → Bool
  | .empty => false
  | .bind k' _ t' => if k = k' then true else in_table k t'


theorem in_table_InTable [DecidableEq key] : ∀ (k : key) (t : Table key val),
  in_table k t = true → InTable k t := by
  sorry


theorem InTable_in_table [DecidableEq key] : ∀ (k : key) (t : Table key val),
  InTable k t → in_table k t = true := by
  sorry


def lookup [DecidableEq key] (k : key) : Table key val → Option val
  | .empty => none
  | .bind k' v t =>
    if k = k' then v else lookup k' t


def lookup' [DecidableEq key] (k : key) (t : Table key val) (p_in_table : InTable k t) : val :=
  match t with
  | .empty =>
    have hf : False := by cases p_in_table
    nomatch hf
  | .bind k' v t' =>
    if h : k = k' then
      v
    else
      lookup' k t' (
        by cases p_in_table with
        | in_bind_hd => contradiction
        | in_bind_tl k' _ => assumption
      )


/-
Problem 8 : Expressions
-/

inductive Expr where
  | var : String → Expr
  | num : Nat → Expr
  | add : Expr → Expr → Expr


def flip : Expr → Expr
  | .var s => .var s
  | .num n => .num n
  | .add e₁ e₂ => .add (flip e₂) (flip e₁)


def eval (t : Table String Nat) : Expr → Option Nat
  | .var s => do lookup s t
  | .num n => n
  | .add e₁ e₂ => do
    let v₁ ← eval t e₁
    let v₂ ← eval t e₂
    return v₁ + v₂


inductive VarInExpr : String → Expr → Prop
  | inVar s : VarInExpr s (.var s)
  | inAddl s e₁ e₂ : VarInExpr s e₁ → VarInExpr s (.add e₁ e₂)
  | inAddr s e₁ e₂ : VarInExpr s e₂ → VarInExpr s (.add e₁ e₂)


def eval' (t : Table String Nat) (e : Expr) (safeVars : (∀ s, VarInExpr s e → InTable s t)) : Nat :=
  match e with
  | .var s =>
    lookup' s t (by apply safeVars; apply VarInExpr.inVar)
  | .num n => n
  | .add e₁ e₂ =>
    let v₁ := eval' t e₁ (by intros s h; apply safeVars; apply VarInExpr.inAddl; assumption)
    let v₂ := eval' t e₂ (by intros s h; apply safeVars; apply VarInExpr.inAddr; assumption)
    v₁ + v₂


theorem varInFlip : ∀ (s : String), VarInExpr s (flip e) → VarInExpr s e := by
  sorry


theorem flipSafeVars : ∀ e (t : Table String Nat),
  (∀ s, VarInExpr s e → InTable s t) →
  (∀ s, VarInExpr s (flip e) → InTable s t) := by
  sorry


theorem flip_eq : ∀ t e s, eval' t e s = eval' t (flip e) (flipSafeVars e t s) := by
  sorry
