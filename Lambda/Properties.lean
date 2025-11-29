import Lambda.Basic
import Mathlib.Tactic

open Lambda

lemma exists_notFree_var (N : Λ') : ∃ x, x ♯ N := Infinite.exists_notMem_finset (fv N)

@[simp]
lemma subst_fresh {N M : Λ'} {x : ℕ} : (x ♯ N) → N[x := M] = N := by
  intro h₁; simp at h₁
  induction N <;> (unfold fv at h₁; simp_all)

lemma subst_intro {N M : Λ'} {x k : ℕ} : (x ♯ N) → N{k ⇒ M} = (N{k ⇒ x})[x := M] := by
  intro h₁; simp at h₁
  induction N generalizing k
  case bvar => simp; split <;> simp
  all_goals unfold fv at h₁; simp_all

theorem substitution {M N L : Λ'} {x y : ℕ} (xny : x ≠ y) (xnfv : x ♯ L) :
  M[x := N][y := L] = M[y := L][x := N[y := L]] := by
  induction M
  case fvar => repeat (first | simp_all | split)
  all_goals simp_all

lemma subst_opening {N M : Λ'} {k : ℕ} (x : ℕ) : (x ♯ N) → N{k ⇒ M} = N{k ⇒ x}[x := M] := by
  intro h; simp at h
  induction N generalizing k
  case bvar => simp; split <;> simp
  all_goals (unfold fv at h); aesop

lemma subst_open₀ {N M : Λ'} {x : ℕ} : (x ♯ N) → N ↑ M = (N ↑ x)[x := M] := by
  simp; apply subst_opening

lemma notFree_open_conservation {N M : Λ'} {k : ℕ} (x : ℕ) :
  (x ♯ M) → (x ♯ N) → (x ♯ M{k ⇒ N}) := by
  induction M generalizing k <;> repeat (first | simp_all | split)

lemma open_comm {x₁ x₂ y₁ y₂ : ℕ} {M : Λ'} :
    x₁ ≠ x₂ → M{x₁ ⇒ y₁}{x₂ ⇒ y₂} = M{x₂ ⇒ y₂}{x₁ ⇒ y₁} := by
  intro h
  induction M generalizing x₁ x₂ with
  | bvar n => repeat (first | simp_all | split)
  | fvar => simp
  | app => simp; constructor <;> aesop
  | abs => simp; aesop

lemma open_close_var {n m x y z : ℕ} {N : Λ'}:
    n ≠ m → x ≠ y → (y ♯ N) → N{n ⇐ x}{n ⇒ z}{m ⇒ y} = N{m ⇒ y}{n ⇐ x}{n ⇒ z} := by
  intro hnm hxy hy; simp at hy
  induction N generalizing n m
  -- The cases of bvar and fvar are followed by making cases on the equalities of n,m,x and y
  -- The cases of app and abs are followed by simplificantion
  all_goals repeat (first | simp_all | split)

@[simp]
lemma opening_lc_lemma {M N L : Λ'} {i j : ℕ} :
  i ≠ j → M{j ⇒ N}{i ⇒ L} = M{j ⇒ N} → M{i ⇒ L} = M := by
  intro hij h₁
  induction M generalizing i j with
  | bvar => simp_all; intros; split at h₁ <;> simp_all
  | fvar => simp
  | app =>
    simp_all; have ⟨h₁, h₂⟩ := h₁; constructor <;> aesop
  | abs => simp_all; aesop

@[simp]
lemma close_open {x k : ℕ} {N : Λ'} :
    (x ♯ N) → N{k ⇒ x}{k ⇐ x} = N := by
  intro hx; simp at hx
  induction N generalizing k
  all_goals repeat (first | simp_all | split)

@[simp]
lemma close_open_var {x : ℕ} {N : Λ'} :
  (x ♯ N) → (N ↑ x) ↓ x = N := by
  intro hx; simp_all

@[simp]
lemma open₀_injective {x : ℕ} {N M : Λ'} :
    (x ♯ N) → (x ♯ M) → (N ↑ x = M ↑ x) → N = M := by
  intro hn hm h
  rw [← @close_open_var x N hn, ← @close_open_var x M hm, h]
