
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


theorem abs_pos : ∀ (j : Int),
  True := by simp



theorem abs_neg : ∀ (i : Int),
  i < 0 → -i = abs i := by
  intros i h
  cases i with
  | ofNat i' => contradiction
  | negSucc i' =>
    simp[abs]; apply Int.neg_negSucc


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
  intros x y H
  induction y generalizing x with
  | zero => simp[sub]; contradiction
  | succ y' IH => cases x with
    | zero => simp[sub]
    | succ x' =>
      simp[sub]
      apply IH
      omega


theorem sub_none' : ∀ (x y : Nat),
  x < y → sub x y = none := by
  intros x y H
  induction x, y using sub.induct with
  | case1 x => contradiction
  | case2 x => simp[sub]
  | case3 x y ih =>
    simp[sub]
    apply ih
    omega

theorem sub_some : ∀ (x y : Nat),
  y ≤ x →
  ∃ z, (sub x y = Option.some z) ∧ (z + y = x) := by
  intros x y H
  induction x, y using sub.induct with
  | case1 x => exists x; simp[sub]
  | case2 x => simp[sub]; contradiction
  | case3 x y ih =>
    have hxy : x ≤ y := by omega
    have ih' := ih hxy
    cases ih' with
    | intro z hz =>
      exists z
      simp[sub, hz]
      omega



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
  intros x
  cases x with
  | zero => simp[sub']
  | succ n' =>
    intros p
    simp[sub']


theorem sub'_le : ∀ x y p, sub' x y p ≤ x := by
  intros x y p
  induction x, y, p using sub'.induct with
  | case1 => simp[sub', sub'_zero]
  | case2 => simp[sub']; omega




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
  intros x
  induction x using split.induct with
  | case1 =>
    intros
    simp[split] at *
    omega
  | case2 =>
    intros s₁ s₂ h
    simp[split] at h
    cases h with
    | intro hl hr =>
      simp[hl, hr]
      omega
  | case3 x s₁' s₂' h' ih =>
    intros s₁ s₂ h
    simp[split] at h
    simp[h'] at h
    cases h with
    | intro hl hr =>
      have hspec := ih s₁' s₂' h'
      omega

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
  intros i l
  induction i generalizing l with
  | zero => simp[eq_to]
  | succ n' ih =>
    cases l with
    | nil => simp[eq_to, take]
    | cons => simp[eq_to, take]; apply ih


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
  intros i
  induction i with
  | zero => simp[take, drop]
  | succ i' ih =>
    intros l
    simp[take, drop]
    cases l <;> simp
    apply ih

/-
Problem 6: Reverse Take Drop
-/

def reverse (l : List α) : List α :=
  match l with
  | [] => []
  | h :: tl => reverse tl ++ [h]


theorem reverse_length : ∀ (l : List α), l.length = (reverse l).length := by
  intros l
  induction l with
  | nil => simp[reverse]
  | cons h tl ih => simp[reverse]; assumption


theorem drop_length [DecidableEq α] : ∀ (l : List α), drop (l.length) l = [] := by
  intros l
  induction l with
  | nil => simp[drop]
  | cons h tl ih => simp[drop]; assumption


theorem drop_app [DecidableEq α] : ∀ (i : Nat) (l₁ l₂: List α),
  i ≤ l₁.length → drop i l₁ ++ l₂ = drop i (l₁ ++ l₂) := by
  intros i
  induction i with
  | zero => simp[drop]
  | succ i' ih =>
    intros l₁ l₂ h
    simp[drop]
    cases l₁ with
    | nil => contradiction
    | cons h t =>
      simp
      apply ih
      simp at h
      assumption


theorem take_rev [DecidableEq α] : ∀ (i : Nat) (l : List α) (h : i ≤ l.length),
  reverse (take i l) = drop (sub' l.length i h) (reverse l) := by
  intros i
  induction i with
  | zero =>
    simp[take]
    intros l h
    rw [reverse_length l]
    simp [drop_length, sub'_zero, reverse]
  | succ i' ih =>
    intros l h
    cases l with
    | nil => contradiction
    | cons h tl =>
      simp [take, drop, sub', reverse]
      rw [ih]
      apply drop_app
      have htl : tl.length = (reverse tl).length := by apply reverse_length
      rw [← htl]
      simp [sub'_le]


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
  intros k t h
  induction t with
  | empty => simp[in_table] at h
  | bind k' v t' ih =>
    simp[in_table] at h
    cases h with
    | inl hl => rw[hl]; apply InTable.in_bind_hd
    | inr hr => apply InTable.in_bind_tl; apply ih; assumption


theorem InTable_in_table [DecidableEq key] : ∀ (k : key) (t : Table key val),
  InTable k t → in_table k t = true := by
  intros k t h
  induction t with
  | empty => cases h
  | bind k' v t' ih =>
    simp[in_table]
    cases h with
    | in_bind_hd => left; rfl
    | in_bind_tl => right; apply ih; assumption


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
  intros s hin
  induction e with
  | var => simp[flip] at hin; assumption
  | num => simp[flip] at hin; assumption
  | add e₁ e₂ ih1 ih2 => simp[flip] at hin; cases hin with
    | inAddl hadd => apply VarInExpr.inAddr; apply ih2; assumption
    | inAddr hadd => apply VarInExpr.inAddl; apply ih1; assumption


theorem flipSafeVars : ∀ e (t : Table String Nat),
  (∀ s, VarInExpr s e → InTable s t) →
  (∀ s, VarInExpr s (flip e) → InTable s t) := by
  intros e t h s h₁
  apply h
  apply varInFlip
  assumption


theorem flip_eq : ∀ t e s, eval' t e s = eval' t (flip e) (flipSafeVars e t s) := by
  intros t e safe
  induction e with
  | var v => simp[eval']
  | num v => simp[eval']
  | add e₁ e₂ ih1 ih2 =>
    simp[eval']
    rw [ih1]
    rw [ih2]
    omega
