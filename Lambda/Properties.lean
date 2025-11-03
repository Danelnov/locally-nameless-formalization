import Lambda.Basic
import Mathlib.Tactic

open Lambda

lemma exists_notFree_var (N : Λ) : ∃ x, x ♯ N := Infinite.exists_notMem_finset (fv N)

lemma lc_abs_iff_body (N : Λ) : Lc (λ N) ↔ body N := by
  constructor <;> simp_all
  . intro h
    cases h; expose_names; exists L
  . intro L h
    apply Lc.lc_abs
    assumption

@[simp]
lemma close_open {k x : ℕ} {N : Λ} : (x ♯ N) → N{k ⇒ x}{k ⇐ x} = N := by
  intro h₁; simp at h₁
  induction N generalizing k
  case bvar => simp; split <;> simp; omega
  all_goals (unfold fv at h₁; simp_all)

lemma close_open_var {N : Λ} {x : ℕ} : (x ♯ N) → (N ↑ x) ↓ x = N := by exact close_open

@[simp]
lemma subst_fresh {N M : Λ} {x : ℕ} : (x ♯ N) → N[x := M] = N := by
  intro h₁; simp at h₁
  induction N <;> (unfold fv at h₁; simp_all)

lemma subst_intro {N M : Λ} {x k : ℕ} : (x ♯ N) → N{k ⇒ M} = (N{k ⇒ x})[x := M] := by
  intro h₁; simp at h₁
  induction N generalizing k
  case bvar => simp; split <;> simp
  all_goals unfold fv at h₁; simp_all

theorem substitution {M N L : Λ} {x y : ℕ} (xny : x ≠ y) (xnfv : x ♯ L) :
  M[x := N][y := L] = M[y := L][x := N[y := L]] := by
  induction M
  case fvar => repeat (first | simp_all | split)
  all_goals simp_all

@[simp]
lemma opening_lc_lemma {M N L : Λ} {i j : ℕ} :
  i ≠ j → M{j ⇒ N}{i ⇒ L} = M{j ⇒ N} → M{i ⇒ L} = M := by
  intro hij h₁
  induction M generalizing i j with
  | bvar => simp_all; intros; split at h₁ <;> simp_all
  | fvar => simp
  | app =>
    simp_all; have ⟨h₁, h₂⟩ := h₁; constructor <;> aesop
  | abs => simp_all; aesop


@[simp]
lemma open_rec_lc {M N : Λ} {k : ℕ} : Lc M → M{k ⇒ N} = M := by
  intro h
  induction h generalizing k with
  | lc_var => simp
  | lc_app => simp_all
  | lc_abs L _ ih  =>
    simp_all
    have ⟨x, hx⟩ : ∃ x, x ∉ L := Infinite.exists_notMem_finset L
    apply opening_lc_lemma
    exact Ne.symm (Nat.zero_ne_add_one k)
    apply ih; assumption

lemma subst_opening {N M : Λ} {k : ℕ} (x : ℕ) : (x ♯ N) → N{k ⇒ M} = N{k ⇒ x}[x := M] := by
  intro h; simp at h
  induction N generalizing k
  case bvar => simp; split <;> simp
  all_goals (unfold fv at h); aesop

lemma subst_open₀ {N M : Λ} {x : ℕ} : (x ♯ N) → N ↑ M = (N ↑ x)[x := M] := by
  simp; apply subst_opening

lemma subst_open {M N L : Λ} {x k : ℕ} :
  Lc L → M{k ⇒ N}[x := L] = M[x := L]{k ⇒ N[x := L]} := by
  intro h
  induction M generalizing k with
  | bvar => simp; split; rfl; simp
  | fvar => simp_all; split <;> simp_all
  | _ => simp_all

lemma notFree_open_conservation {N M : Λ} {k : ℕ} (x : ℕ) :
  (x ♯ M) → (x ♯ N) → (x ♯ M{k ⇒ N}) := by
  induction M generalizing k <;> repeat (first | simp_all | split)
