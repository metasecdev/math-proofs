/-
  Residue (small-number) form of the guard-agreement check, 2026-10-28.

  The kernel check `decide +kernel` of `bbpGuardAgrees n` evaluates `bbpGuardedSum n g`, a sum of
  ~`n` floors of numbers with ~`4n` bits. That makes kernel memory grow like `n^3` bits over a range
  of `n` and is what stopped the bound at 2000 (docs/PBBP01_EXTENSION_ANALYSIS.md §3).

  But `bbpGuardedLo n g = bbpGuardedHi n g` only depends on `S mod 16^g` (`S = bbpGuardedSum n g`).
  With `M = 16^g` and the Nat identity `(X / d) % M = (X % (d * M)) / d`
  (`Nat.mod_mul_right_div_self`) every floor term reduces mod `M` using only numbers of
  `~ log₂(d·M)` bits, after one modular reduction of `c·16^(N-k)`.

  Everything here is natural-number arithmetic. No reals, no π, no `native_decide`, no `sorry`.

  * `termMod`, `blkSum`, `fsum`  : residue form of the sum (blocks of 128 terms, so the kernel
    recursion depth stays small).
  * `fsum_eq`                    : `fsum N M ((N+128)/128) = bbpGuardedSum.. % M` (proved).
  * `fastAgreeAt n g : Bool`     : `E ≤ s ∧ s + E < M`, `s = fsum ..`.
  * `fastAgreeAt_sound`          : `fastAgreeAt n g = true → BBPGuardAgreesAt-style equality
                                   bbpGuardedLo n g = bbpGuardedHi n g` (proved, no hypothesis on n).
  * `bbpGuardAgrees_of_fast`     : `fastAgreeAt n g` for some `g ∈ {4,8,…,68}` ⇒ `bbpGuardAgrees n`.
-/
import Thoughts.Proved.BBPTail
import Thoughts.Proved.BBPGuarded

namespace FinitistProved

/-- Residue mod `M` of `bbp_term k N` (`0` for `k > N`), computed from small numbers. -/
def termMod (k N M : ℕ) : ℕ :=
  if k ≤ N then
    let m := N - k
    let a1 := (4 * 16 ^ m % ((8 * k + 1) * M)) / (8 * k + 1)
    let a4 := (2 * 16 ^ m % ((8 * k + 4) * M)) / (8 * k + 4)
    let a5 := (16 ^ m % ((8 * k + 5) * M)) / (8 * k + 5)
    let a6 := (16 ^ m % ((8 * k + 6) * M)) / (8 * k + 6)
    (a1 + 3 * M - (a4 + a5 + a6)) % M
  else 0

/-- Sum of `termMod (a+i) N M` for `i < j`, reduced mod `M` at every step. -/
def blkSum (N M a : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (blkSum N M a j + termMod (a + j) N M) % M

/-- Block-wise residue sum: blocks `[128·b, 128·b + 128)`, `b < nb`. -/
def fsum (N M : ℕ) : ℕ → ℕ
  | 0 => 0
  | b + 1 => (fsum N M b + blkSum N M (128 * b) 128) % M

/-! ### The floor terms, written with the common factor `16^k` cancelled -/

private lemma div_cancel (k m c d : ℕ) :
    (c * 16 ^ (k + m)) / (16 ^ k * d) = (c * 16 ^ m) / d := by
  have : c * 16 ^ (k + m) = 16 ^ k * (c * 16 ^ m) := by ring
  rw [this, Nat.mul_div_mul_left _ _ (by positivity)]

/-- The four floors of `bbp_term k N` and their non-truncation (`f4+f5+f6 ≤ f1`). -/
private lemma term_split (k N : ℕ) :
    bbp_term k N =
      (4 * 16 ^ N) / (16 ^ k * (8 * k + 1)) -
        ((2 * 16 ^ N) / (16 ^ k * (8 * k + 4)) + (16 ^ N) / (16 ^ k * (8 * k + 5)) +
          (16 ^ N) / (16 ^ k * (8 * k + 6))) ∧
    ((2 * 16 ^ N) / (16 ^ k * (8 * k + 4)) + (16 ^ N) / (16 ^ k * (8 * k + 5)) +
          (16 ^ N) / (16 ^ k * (8 * k + 6))) ≤ (4 * 16 ^ N) / (16 ^ k * (8 * k + 1)) := by
  have hle :
      (2 * 16 ^ N) / (16 ^ k * (8 * k + 4)) + (16 ^ N) / (16 ^ k * (8 * k + 5)) +
          (16 ^ N) / (16 ^ k * (8 * k + 6)) ≤
        (4 * 16 ^ N) / (16 ^ k * (8 * k + 1)) := by
    -- same real-number argument as in `bbp_term_cast_bounds` (BBPGuarded.lean)
    have hd1 : (0 : ℝ) < ((16 ^ k * (8 * k + 1) : ℕ) : ℝ) := by positivity
    have hd4 : (0 : ℝ) < ((16 ^ k * (8 * k + 4) : ℕ) : ℝ) := by positivity
    have hd5 : (0 : ℝ) < ((16 ^ k * (8 * k + 5) : ℕ) : ℝ) := by positivity
    have hd6 : (0 : ℝ) < ((16 ^ k * (8 * k + 6) : ℕ) : ℝ) := by positivity
    have hsc : 0 ≤ (16 : ℝ) ^ N * bbpSummand k :=
      mul_nonneg (by positivity) (bbpSummand_nonneg k)
    have hscal :
        (16 : ℝ) ^ N * bbpSummand k =
          ((4 * 16 ^ N : ℕ) : ℝ) / ((16 ^ k * (8 * k + 1) : ℕ) : ℝ) -
            ((2 * 16 ^ N : ℕ) : ℝ) / ((16 ^ k * (8 * k + 4) : ℕ) : ℝ) -
            ((16 ^ N : ℕ) : ℝ) / ((16 ^ k * (8 * k + 5) : ℕ) : ℝ) -
            ((16 ^ N : ℕ) : ℝ) / ((16 ^ k * (8 * k + 6) : ℕ) : ℝ) := by
      unfold bbpSummand bbpCoeff
      push_cast
      field_simp
    rw [hscal] at hsc
    rw [Nat.le_div_iff_mul_le (by positivity)]
    have f4 : (((2 * 16 ^ N) / (16 ^ k * (8 * k + 4)) : ℕ) : ℝ) ≤
        ((2 * 16 ^ N : ℕ) : ℝ) / ((16 ^ k * (8 * k + 4) : ℕ) : ℝ) := Nat.cast_div_le
    have f5 : (((16 ^ N) / (16 ^ k * (8 * k + 5)) : ℕ) : ℝ) ≤
        ((16 ^ N : ℕ) : ℝ) / ((16 ^ k * (8 * k + 5) : ℕ) : ℝ) := Nat.cast_div_le
    have f6 : (((16 ^ N) / (16 ^ k * (8 * k + 6)) : ℕ) : ℝ) ≤
        ((16 ^ N : ℕ) : ℝ) / ((16 ^ k * (8 * k + 6) : ℕ) : ℝ) := Nat.cast_div_le
    have h' :
        (((2 * 16 ^ N) / (16 ^ k * (8 * k + 4)) + (16 ^ N) / (16 ^ k * (8 * k + 5)) +
            (16 ^ N) / (16 ^ k * (8 * k + 6)) : ℕ) : ℝ) ≤
          ((4 * 16 ^ N : ℕ) : ℝ) / ((16 ^ k * (8 * k + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_add]
      linarith
    rw [le_div_iff₀ hd1] at h'
    exact_mod_cast h'
  refine ⟨?_, hle⟩
  show (4 * 16 ^ N) / (16 ^ k * (8 * k + 1)) - (2 * 16 ^ N) / (16 ^ k * (8 * k + 4)) -
      16 ^ N / (16 ^ k * (8 * k + 5)) - 16 ^ N / (16 ^ k * (8 * k + 6)) = _
  rw [Nat.sub_sub, Nat.sub_sub, Nat.add_assoc]

/-- **Residue of one term:** `bbp_term k N % M = termMod k N M`. -/
theorem bbp_term_mod (k N M : ℕ) (hM : 0 < M) : bbp_term k N % M = termMod k N M := by
  by_cases hk : k ≤ N
  · obtain ⟨m, rfl⟩ : ∃ m, N = k + m := ⟨N - k, by omega⟩
    obtain ⟨hsplit, hle⟩ := term_split k (k + m)
    have e1 := div_cancel k m 4 (8 * k + 1)
    have e4 := div_cancel k m 2 (8 * k + 4)
    have e5 := div_cancel k m 1 (8 * k + 5)
    have e6 := div_cancel k m 1 (8 * k + 6)
    simp only [one_mul] at e5 e6
    rw [e1, e4, e5, e6] at hsplit hle
    have h1 : ((4 * 16 ^ m) / (8 * k + 1)) % M = (4 * 16 ^ m % ((8 * k + 1) * M)) / (8 * k + 1) := by
      rw [← Nat.mod_mul_right_div_self]
    have h4 : ((2 * 16 ^ m) / (8 * k + 4)) % M = (2 * 16 ^ m % ((8 * k + 4) * M)) / (8 * k + 4) := by
      rw [← Nat.mod_mul_right_div_self]
    have h5 : ((16 ^ m) / (8 * k + 5)) % M = (16 ^ m % ((8 * k + 5) * M)) / (8 * k + 5) := by
      rw [← Nat.mod_mul_right_div_self]
    have h6 : ((16 ^ m) / (8 * k + 6)) % M = (16 ^ m % ((8 * k + 6) * M)) / (8 * k + 6) := by
      rw [← Nat.mod_mul_right_div_self]
    have hN : k + m - k = m := by omega
    unfold termMod
    rw [if_pos (by omega)]
    simp only [hN]
    rw [← h1, ← h4, ← h5, ← h6]
    -- abbreviations
    generalize (4 * 16 ^ m) / (8 * k + 1) = f1 at *
    generalize (2 * 16 ^ m) / (8 * k + 4) = f4 at *
    generalize (16 ^ m) / (8 * k + 5) = f5 at *
    generalize (16 ^ m) / (8 * k + 6) = f6 at *
    rw [hsplit]
    have hmod : ∀ x : ℕ, x % M < M := fun x => Nat.mod_lt _ hM
    have a4 := hmod f4
    have a5 := hmod f5
    have a6 := hmod f6
    -- (f1 - (f4+f5+f6)) % M = (f1 % M + 3M - (f4%M + f5%M + f6%M)) % M
    have key : (f1 - (f4 + f5 + f6)) + (f4 + f5 + f6) = f1 := Nat.sub_add_cancel hle
    have hm : (f1 - (f4 + f5 + f6)) + (f4 % M + f5 % M + f6 % M) ≡ f1 % M [MOD M] := by
      have h1' : (f1 - (f4 + f5 + f6)) + (f4 + f5 + f6) ≡ f1 [MOD M] := by rw [key]
      have h2' : f4 % M + f5 % M + f6 % M ≡ f4 + f5 + f6 [MOD M] :=
        ((Nat.mod_modEq f4 M).add (Nat.mod_modEq f5 M)).add (Nat.mod_modEq f6 M)
      have h3' : (f1 - (f4 + f5 + f6)) + (f4 % M + f5 % M + f6 % M) ≡
          (f1 - (f4 + f5 + f6)) + (f4 + f5 + f6) [MOD M] := Nat.ModEq.add_left _ h2'
      exact h3'.trans (h1'.trans (Nat.mod_modEq f1 M).symm)
    have hm2 : (f1 % M + 3 * M - (f4 % M + f5 % M + f6 % M)) + (f4 % M + f5 % M + f6 % M)
        ≡ f1 % M [MOD M] := by
      have : (f1 % M + 3 * M - (f4 % M + f5 % M + f6 % M)) + (f4 % M + f5 % M + f6 % M)
          = f1 % M + 3 * M := by omega
      rw [this]
      unfold Nat.ModEq
      rw [show 3 * M = M * 3 from by ring, Nat.add_mul_mod_self_left]
    have := hm.trans hm2.symm
    exact Nat.ModEq.add_right_cancel' _ this
  · have h0 : bbp_term k N = 0 := bbpSpigotTerm_eq_zero_of_gt k N (by omega)
    unfold termMod
    rw [if_neg hk, h0]
    simp

/-- Prefix sums: `(S_a + blkSum a j) % M = S_{a+j} % M`. -/
theorem blkSum_eq (N M a : ℕ) (hM : 0 < M) :
    ∀ j, (bbpSpigotSum N a + blkSum N M a j) % M = bbpSpigotSum N (a + j) % M := by
  intro j
  induction j with
  | zero => simp [blkSum]
  | succ j ih =>
    have e : bbpSpigotSum N (a + (j + 1)) = bbpSpigotSum N (a + j) + bbp_term (a + j) N := rfl
    have hb : blkSum N M a (j + 1) = (blkSum N M a j + termMod (a + j) N M) % M := rfl
    rw [e, hb, Nat.add_mod_mod, ← Nat.add_assoc, Nat.add_mod, ih,
      ← bbp_term_mod _ _ _ hM]
    rw [Nat.mod_mod]
    exact (Nat.add_mod _ _ _).symm

/-- Block sums agree with the prefix sums at multiples of 128. -/
theorem fsum_eq (N M : ℕ) (hM : 0 < M) :
    ∀ b, fsum N M b = bbpSpigotSum N (128 * b) % M := by
  intro b
  induction b with
  | zero => simp [fsum, bbpSpigotSum]
  | succ b ih =>
    have hb : fsum N M (b + 1) = (fsum N M b + blkSum N M (128 * b) 128) % M := rfl
    rw [hb, ih, Nat.mod_add_mod, blkSum_eq N M (128 * b) hM 128,
      show 128 * (b + 1) = 128 * b + 128 from by ring]

/-! ### Kernel-friendly versions (raw `Nat.*`, no instance layers; ~3.5x faster in the kernel).
They are proved equal to the readable definitions above (`fsumR_eq`). -/

/-- `termMod` written with raw `Nat` operations. -/
def termModR (k N M : ℕ) : ℕ :=
  cond (Nat.ble k N)
    (Nat.mod (Nat.sub (Nat.add
      (Nat.div (Nat.mod (Nat.mul 4 (Nat.pow 16 (Nat.sub N k)))
        (Nat.mul (Nat.add (Nat.mul 8 k) 1) M)) (Nat.add (Nat.mul 8 k) 1))
      (Nat.mul 3 M))
      (Nat.add (Nat.add
        (Nat.div (Nat.mod (Nat.mul 2 (Nat.pow 16 (Nat.sub N k)))
          (Nat.mul (Nat.add (Nat.mul 8 k) 4) M)) (Nat.add (Nat.mul 8 k) 4))
        (Nat.div (Nat.mod (Nat.pow 16 (Nat.sub N k))
          (Nat.mul (Nat.add (Nat.mul 8 k) 5) M)) (Nat.add (Nat.mul 8 k) 5)))
        (Nat.div (Nat.mod (Nat.pow 16 (Nat.sub N k))
          (Nat.mul (Nat.add (Nat.mul 8 k) 6) M)) (Nat.add (Nat.mul 8 k) 6)))) M)
    0

theorem termModR_eq (k N M : ℕ) : termModR k N M = termMod k N M := by
  unfold termModR termMod
  by_cases h : k ≤ N
  · have : Nat.ble k N = true := Nat.ble_eq_true_of_le h
    rw [this, if_pos h]; rfl
  · have : Nat.ble k N = false := by
      cases hb : Nat.ble k N
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) h
    rw [this, if_neg h]; rfl

def blkSumR (N M a : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => Nat.mod (Nat.add (blkSumR N M a j) (termModR (Nat.add a j) N M)) M

def fsumR (N M : ℕ) : ℕ → ℕ
  | 0 => 0
  | b + 1 => Nat.mod (Nat.add (fsumR N M b) (blkSumR N M (Nat.mul 128 b) 128)) M

theorem blkSumR_eq (N M a : ℕ) : ∀ j, blkSumR N M a j = blkSum N M a j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    show Nat.mod (Nat.add (blkSumR N M a j) (termModR (Nat.add a j) N M)) M =
      (blkSum N M a j + termMod (a + j) N M) % M
    rw [ih, termModR_eq]; rfl

theorem fsumR_eq (N M : ℕ) : ∀ b, fsumR N M b = fsum N M b := by
  intro b
  induction b with
  | zero => rfl
  | succ b ih =>
    show Nat.mod (Nat.add (fsumR N M b) (blkSumR N M (Nat.mul 128 b) 128)) M =
      (fsum N M b + blkSum N M (128 * b) 128) % M
    rw [ih, blkSumR_eq]; rfl

/-- Fast agreement test: residue `s` of the guarded sum is at distance `≥ E` from both ends. -/
def fastAgreeAt (n g : ℕ) : Bool :=
  let N := n + g
  let M := 16 ^ g
  let s := fsumR N M (Nat.div (Nat.add N 128) 128)
  decide (bbpGuardErr n g ≤ s ∧ s + bbpGuardErr n g < M)

theorem fastAgreeAt_sound (n g : ℕ) (h : fastAgreeAt n g = true) :
    bbpGuardedLo n g = bbpGuardedHi n g := by
  unfold fastAgreeAt at h
  simp only [fsumR_eq] at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hM : 0 < 16 ^ g := by positivity
  have hK : n + g + 1 ≤ 128 * ((n + g + 128) / 128) := by omega
  have hs : fsum (n + g) (16 ^ g) ((n + g + 128) / 128) = bbpGuardedSum n g % 16 ^ g := by
    rw [fsum_eq _ _ hM, bbpSpigotSum_eq_of_ge _ _ hK]
    rfl
  have hd : Nat.div (Nat.add (n + g) 128) 128 = (n + g + 128) / 128 := rfl
  rw [hd] at h1 h2
  rw [hs] at h1 h2
  unfold bbpGuardedLo bbpGuardedHi
  set S := bbpGuardedSum n g
  set E := bbpGuardErr n g
  set M := 16 ^ g
  have hS : S = M * (S / M) + S % M := (Nat.div_add_mod S M).symm
  set q := S / M
  set s := S % M
  have e1 : (S - E) / M = q := by
    rw [show S - E = (s - E) + M * q from by rw [hS]; omega]
    rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt (by omega)]; simp
  have e2 : (S + E) / M = q := by
    rw [show S + E = (s + E) + M * q from by rw [hS]; omega]
    rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt (by omega)]; simp
  rw [e1, e2]

/-- Any fast-agreeing guard depth in `{4, 8, …, 68}` gives `bbpGuardAgrees`. -/
theorem bbpGuardSearch_of_agree (n : ℕ) :
    ∀ (fuel g : ℕ) (t : ℕ), t < fuel → g + 4 * t ≤ 100000 →
      bbpGuardedLo n (g + 4 * t) = bbpGuardedHi n (g + 4 * t) →
      bbpGuardedLo n (bbpGuardSearch n fuel g) = bbpGuardedHi n (bbpGuardSearch n fuel g) := by
  intro fuel
  induction fuel with
  | zero => intro g t ht; omega
  | succ f ih =>
    intro g t ht _ hag
    unfold bbpGuardSearch
    by_cases hc : bbpGuardedLo n g = bbpGuardedHi n g
    · rw [if_pos hc]; exact hc
    · rw [if_neg hc]
      cases t with
      | zero => exact absurd hag (by simpa using hc)
      | succ t =>
        exact ih (g + 4) t (by omega) (by omega)
          (by rwa [show g + 4 + 4 * t = g + 4 * (t + 1) from by ring])

theorem bbpGuardAgrees_of_fast (n t : ℕ) (ht : t < 16)
    (h : fastAgreeAt n (4 + 4 * t) = true) : bbpGuardAgrees n := by
  unfold bbpGuardAgrees bbpCertGuard bbpGuardDigits
  exact bbpGuardSearch_of_agree n 16 4 t ht (by omega) (fastAgreeAt_sound _ _ h)

/-- Per-`n` kernel check: guard depth `g` is in the search grid `{4,…,64}` and fast-agrees. -/
def fastOK (n g : ℕ) : Bool :=
  decide (4 ≤ g ∧ g % 4 = 0 ∧ g ≤ 64) && fastAgreeAt n g

/-- Check consecutive `n = a, a+1, …` with the supplied guard depths. -/
def chkFrom : ℕ → List ℕ → Bool
  | _, [] => true
  | n, g :: gs => fastOK n g && chkFrom (n + 1) gs

theorem fastOK_sound (n g : ℕ) (h : fastOK n g = true) : bbpGuardAgrees n := by
  unfold fastOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  have : g = 4 + 4 * (g / 4 - 1) := by omega
  rw [this] at h4
  exact bbpGuardAgrees_of_fast n (g / 4 - 1) (by omega) h4

theorem chkFrom_sound : ∀ (gs : List ℕ) (a : ℕ), chkFrom a gs = true →
    ∀ i, i < gs.length → bbpGuardAgrees (a + i) := by
  intro gs
  induction gs with
  | nil => intro a _ i hi; simp at hi
  | cons g gs ih =>
    intro a h i hi
    unfold chkFrom at h
    simp only [Bool.and_eq_true] at h
    cases i with
    | zero => exact fastOK_sound _ _ h.1
    | succ i =>
      have := ih (a + 1) h.2 i (by simpa using hi)
      rwa [show a + 1 + i = a + (i + 1) from by ring] at this

end FinitistProved
