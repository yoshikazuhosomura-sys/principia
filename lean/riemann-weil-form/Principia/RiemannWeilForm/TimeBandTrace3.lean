import Mathlib

/-!
# The cluster identity for the `1/k` law: the general `k`

Let `oddH n = 1 + 1/3 + ⋯ + 1/(2n-1)` and `harm n = 1 + 1/2 + ⋯ + 1/n`.
The `1/k` law for the trace of a time-band operator was reduced (in the accompanying
notes) to the binomial identity

  `∑_{n ≥ 1} (k.choose (2 n)) * oddH n = 2 ^ (k - 2) * harm (k - 1)`,

previously verified only for `k ≤ 12`.  Here it is proved for every `k`, in the
subtraction-free form

  `4 * ∑_{n} ((k+1).choose (2 n)) * oddH n = 2 ^ (k+1) * harm k`.

The proof is a simultaneous induction on the three binomial transforms

  `S k = ∑_n (k.choose (2n)) * oddH n`,
  `T k = ∑_n (k.choose (2n+1)) * oddH (n+1)`,
  `U k = ∑_n (k.choose (2n)) / (2n+1) = 2 ^ k / (k+1)`,

whose Pascal recursions are `S (k+1) = S k + T k` and `T (k+1) = T k + S k + U k`.
No integral is used.
-/

namespace TimeBand

open Finset

/-- `oddH n = 1 + 1/3 + ⋯ + 1/(2n-1)`. -/
def oddH (n : ℕ) : ℚ := ∑ i ∈ range n, (1 : ℚ) / (2 * (i : ℚ) + 1)

/-- `harm n = 1 + 1/2 + ⋯ + 1/n`. -/
def harm (n : ℕ) : ℚ := ∑ i ∈ range n, (1 : ℚ) / ((i : ℚ) + 1)

@[simp] lemma oddH_zero : oddH 0 = 0 := by simp [oddH]

@[simp] lemma harm_zero : harm 0 = 0 := by simp [harm]

lemma oddH_succ (n : ℕ) : oddH (n + 1) = oddH n + 1 / (2 * (n : ℚ) + 1) := by
  simp [oddH, Finset.sum_range_succ]

lemma harm_succ (n : ℕ) : harm (n + 1) = harm n + 1 / ((n : ℚ) + 1) := by
  simp [harm, Finset.sum_range_succ]

/-- Shrinking the range of a sum whose tail vanishes. -/
lemma sum_ext_zero {M : Type*} [AddCommMonoid M] {a b : ℕ} (h : a ≤ b) (f : ℕ → M)
    (hf : ∀ x, a ≤ x → f x = 0) : ∑ n ∈ range b, f n = ∑ n ∈ range a, f n := by
  refine (Finset.sum_subset (Finset.range_subset_range.mpr h) ?_).symm
  intro x hx hnx
  simp only [Finset.mem_range, not_lt] at hnx
  exact hf x hnx

/-- Dropping a vanishing first term. -/
lemma sum_shift (g : ℕ → ℚ) (N : ℕ) (h0 : g 0 = 0) :
    ∑ n ∈ range (N + 1), g n = ∑ i ∈ range N, g (i + 1) := by
  rw [Finset.sum_range_succ']
  simp [h0]

def S (k : ℕ) : ℚ := ∑ n ∈ range (k + 2), (k.choose (2 * n) : ℚ) * oddH n
def T (k : ℕ) : ℚ := ∑ n ∈ range (k + 2), (k.choose (2 * n + 1) : ℚ) * oddH (n + 1)
def U (k : ℕ) : ℚ := ∑ n ∈ range (k + 2), (k.choose (2 * n) : ℚ) / (2 * (n : ℚ) + 1)

lemma S_ext (k M : ℕ) (h : k + 2 ≤ M) :
    ∑ n ∈ range M, (k.choose (2 * n) : ℚ) * oddH n = S k := by
  refine sum_ext_zero h _ ?_
  intro x hx
  have : k.choose (2 * x) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [this]

lemma T_ext (k M : ℕ) (h : k + 2 ≤ M) :
    ∑ n ∈ range M, (k.choose (2 * n + 1) : ℚ) * oddH (n + 1) = T k := by
  refine sum_ext_zero h _ ?_
  intro x hx
  have : k.choose (2 * x + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [this]

lemma U_ext (k M : ℕ) (h : k + 2 ≤ M) :
    ∑ n ∈ range M, (k.choose (2 * n) : ℚ) / (2 * (n : ℚ) + 1) = U k := by
  refine sum_ext_zero h _ ?_
  intro x hx
  have : k.choose (2 * x) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [this]

lemma S_succ (k : ℕ) : S (k + 1) = S k + T k := by
  have e1 : S (k + 1)
      = ∑ i ∈ range (k + 2), (((k+1).choose (2 * (i + 1)) : ℚ) * oddH (i + 1)) := by
    unfold S
    rw [show k + 1 + 2 = (k + 2) + 1 from rfl]
    exact sum_shift _ _ (by simp)
  have e2 : ∀ i ∈ range (k + 2),
      (((k+1).choose (2 * (i + 1)) : ℚ) * oddH (i + 1))
        = (k.choose (2 * i + 1) : ℚ) * oddH (i + 1)
          + (k.choose (2 * (i + 1)) : ℚ) * oddH (i + 1) := by
    intro i _
    have hp : (k+1).choose (2 * i + 1 + 1) = k.choose (2 * i + 1) + k.choose (2 * i + 1 + 1) :=
      Nat.choose_succ_succ k (2 * i + 1)
    have h2 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    rw [h2, hp]
    push_cast
    ring
  have hsh := sum_shift (fun n => (k.choose (2 * n) : ℚ) * oddH n) (k + 2) (by simp)
  have e3 : ∑ i ∈ range (k + 2), (k.choose (2 * (i + 1)) : ℚ) * oddH (i + 1) = S k := by
    rw [← S_ext k (k + 3) (by omega), show k + 3 = (k + 2) + 1 from rfl]
    exact hsh.symm
  rw [e1, Finset.sum_congr rfl e2, Finset.sum_add_distrib, e3]
  have : ∑ i ∈ range (k + 2), (k.choose (2 * i + 1) : ℚ) * oddH (i + 1) = T k := rfl
  rw [this]
  ring

lemma T_succ (k : ℕ) : T (k + 1) = T k + S k + U k := by
  have e1 : T (k + 1)
      = ∑ n ∈ range (k + 3), (((k+1).choose (2 * n + 1) : ℚ) * oddH (n + 1)) := rfl
  have e2 : ∀ n ∈ range (k + 3),
      (((k+1).choose (2 * n + 1) : ℚ) * oddH (n + 1))
        = ((k.choose (2 * n) : ℚ) * oddH n + (k.choose (2 * n) : ℚ) / (2 * (n : ℚ) + 1))
          + (k.choose (2 * n + 1) : ℚ) * oddH (n + 1) := by
    intro n _
    have hp : (k+1).choose (2 * n + 1) = k.choose (2 * n) + k.choose (2 * n + 1) :=
      Nat.choose_succ_succ k (2 * n)
    have hpos : (2 * (n : ℚ) + 1) ≠ 0 := by positivity
    rw [hp, oddH_succ]
    push_cast
    ring
  rw [e1, Finset.sum_congr rfl e2, Finset.sum_add_distrib, Finset.sum_add_distrib,
      S_ext k (k + 3) (by omega), U_ext k (k + 3) (by omega), T_ext k (k + 3) (by omega)]
  ring

/-! ### The sums of the even and the odd binomial coefficients -/

def Ev (k : ℕ) : ℕ := ∑ n ∈ range (k + 2), k.choose (2 * n)
def Od (k : ℕ) : ℕ := ∑ n ∈ range (k + 2), k.choose (2 * n + 1)

lemma Ev_ext (k M : ℕ) (h : k + 2 ≤ M) : ∑ n ∈ range M, k.choose (2 * n) = Ev k := by
  refine sum_ext_zero h _ ?_
  intro x hx
  exact Nat.choose_eq_zero_of_lt (by omega)

lemma Od_ext (k M : ℕ) (h : k + 2 ≤ M) : ∑ n ∈ range M, k.choose (2 * n + 1) = Od k := by
  refine sum_ext_zero h _ ?_
  intro x hx
  exact Nat.choose_eq_zero_of_lt (by omega)

lemma Ev_succ (k : ℕ) : Ev (k + 1) = Od k + Ev k := by
  have e1 : Ev (k + 1) = ∑ n ∈ range (k + 3), (k+1).choose (2 * n) := rfl
  rw [e1, Finset.sum_range_succ' (fun n => (k+1).choose (2 * n)) (k + 2)]
  have e2 : ∀ i ∈ range (k + 2),
      (k+1).choose (2 * (i + 1)) = k.choose (2 * i + 1) + k.choose (2 * (i + 1)) := by
    intro i _
    have hp : (k+1).choose (2 * i + 1 + 1) = k.choose (2 * i + 1) + k.choose (2 * i + 1 + 1) :=
      Nat.choose_succ_succ k (2 * i + 1)
    have h2 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    rw [h2, hp]
  rw [Finset.sum_congr rfl e2, Finset.sum_add_distrib]
  have e3 : ∑ i ∈ range (k + 2), k.choose (2 * (i + 1)) = Ev k - 1 := by
    have := Ev_ext k (k + 3) (by omega)
    rw [show k + 3 = (k + 2) + 1 from rfl,
        Finset.sum_range_succ' (fun n => k.choose (2 * n)) (k + 2)] at this
    simp at this
    omega
  have hEv1 : 1 ≤ Ev k := by
    have : k.choose (2 * 0) ≤ Ev k := Finset.single_le_sum
      (f := fun n => k.choose (2 * n)) (fun i _ => Nat.zero_le _) (by simp)
    simpa using this
  have e4 : ∑ i ∈ range (k + 2), k.choose (2 * i + 1) = Od k := rfl
  simp [e3, e4]
  omega

lemma Od_succ (k : ℕ) : Od (k + 1) = Ev k + Od k := by
  have e1 : Od (k + 1) = ∑ n ∈ range (k + 3), (k+1).choose (2 * n + 1) := rfl
  have e2 : ∀ n ∈ range (k + 3),
      (k+1).choose (2 * n + 1) = k.choose (2 * n) + k.choose (2 * n + 1) := by
    intro n _
    exact Nat.choose_succ_succ k (2 * n)
  rw [e1, Finset.sum_congr rfl e2, Finset.sum_add_distrib,
      Ev_ext k (k + 3) (by omega), Od_ext k (k + 3) (by omega)]

lemma EvOd (k : ℕ) : Ev (k + 1) = 2 ^ k ∧ Od (k + 1) = 2 ^ k := by
  induction k with
  | zero => constructor <;> decide
  | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [Ev_succ (n + 1), ih.1, ih.2, pow_succ]; ring
      · rw [Od_succ (n + 1), ih.1, ih.2, pow_succ]; ring

/-- `∑_{n} (k.choose (2n)) / (2n+1) = 2 ^ k / (k+1)`. -/
lemma U_eq (k : ℕ) : U k = 2 ^ k / ((k : ℚ) + 1) := by
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have key : ∀ n ∈ range (k + 2),
      (k.choose (2 * n) : ℚ) / (2 * (n : ℚ) + 1)
        = ((k+1).choose (2 * n + 1) : ℚ) / ((k : ℚ) + 1) := by
    intro n _
    have h := Nat.add_one_mul_choose_eq k (2 * n)
    have h' : ((k + 1) * k.choose (2 * n) : ℚ) = (((k+1).choose (2 * n + 1)) * (2 * n + 1) : ℚ) := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ℚ)) h
    have hpos : (2 * (n : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    push_cast at h' ⊢
    linarith [h']
  unfold U
  rw [Finset.sum_congr rfl key, ← Finset.sum_div]
  have : ∑ n ∈ range (k + 2), ((k+1).choose (2 * n + 1) : ℚ)
      = ((Od (k + 1) : ℕ) : ℚ) := by
    have h1 : ∑ n ∈ range (k + 3), (k+1).choose (2 * n + 1) = Od (k + 1) := rfl
    have h2 : ∑ n ∈ range (k + 2), (k+1).choose (2 * n + 1) = Od (k + 1) := by
      rw [← h1]
      refine (sum_ext_zero (by omega) _ ?_).symm
      intro x hx
      exact Nat.choose_eq_zero_of_lt (by omega)
    rw [← h2]
    push_cast
    rfl
  rw [this, (EvOd k).2]
  push_cast
  ring

/-! ### The main identity -/

lemma main_aux (k : ℕ) :
    4 * S (k + 1) = 2 ^ (k + 1) * harm k ∧
    4 * T (k + 1) = 2 ^ (k + 1) * harm k + 2 ^ (k + 2) / ((k : ℚ) + 1) := by
  induction k with
  | zero =>
      have c12 : Nat.choose 1 2 = 0 := by decide
      have c13 : Nat.choose 1 3 = 0 := by decide
      have c14 : Nat.choose 1 4 = 0 := by decide
      have c15 : Nat.choose 1 5 = 0 := by decide
      constructor
      · norm_num [S, oddH, harm, Finset.sum_range_succ, c12, c13, c14, c15]
      · norm_num [T, oddH, harm, Finset.sum_range_succ, c12, c13, c14, c15]
  | succ n ih =>
      have hS := S_succ (n + 1)
      have hT := T_succ (n + 1)
      have hU := U_eq (n + 1)
      have hh := harm_succ n
      have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
      constructor
      · rw [hS]
        rw [show (4 : ℚ) * (S (n+1) + T (n+1)) = 4 * S (n+1) + 4 * T (n+1) by ring,
            ih.1, ih.2, hh]
        field_simp
        ring
      · rw [hT]
        rw [show (4 : ℚ) * (T (n+1) + S (n+1) + U (n+1)) = 4 * T (n+1) + 4 * S (n+1) + 4 * U (n+1)
              by ring, ih.1, ih.2, hU, hh]
        push_cast
        field_simp
        ring

/-- **The cluster identity for every `k`.**  With `oddH n = 1 + 1/3 + ⋯ + 1/(2n-1)`
and `harm n = 1 + 1/2 + ⋯ + 1/n`,
`4 * ∑_n ((k+1).choose (2n)) * oddH n = 2 ^ (k+1) * harm k`, i.e.
`∑_{n ≥ 1} (K.choose (2n)) * oddH n = 2 ^ (K-2) * harm (K-1)` for `K = k+1`. -/
theorem binom_oddH_identity (k : ℕ) :
    4 * ∑ n ∈ range (k + 3), (((k+1).choose (2 * n) : ℚ) * oddH n) = 2 ^ (k + 1) * harm k :=
  (main_aux k).1

end TimeBand

#print axioms TimeBand.binom_oddH_identity
#print axioms TimeBand.U_eq
#print axioms TimeBand.EvOd
