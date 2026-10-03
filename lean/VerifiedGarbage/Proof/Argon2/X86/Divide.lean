import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Argon2.Divide
import VerifiedGarbage.Impl.Argon2.X86.Divide

/-!
# Fixed-time division on x86 (32-bit)

`code_ok`: `Impl.Argon2.X86.Divide.code d` leaves `n / D` in `ecx` and
`n mod D` in `eax`, for the numerator `n` in `ecx` and the divisor `D` at
`[ebp + d]`, `0 < D < 2³¹`. After `k` bits (`bits_ok`) `ecx` holds the `32 - k`
bits of `n` not yet consumed above the quotient of the `k` consumed ones,
and `eax` their remainder: each bit is one step of binary long division
(`Proof.Argon2.divide_step`).
-/

namespace VG.Proof.Argon2.X86.Divide

open VG VG.X86 VG.X86.Wp
open VG.Impl.Argon2.X86.Divide (bit bits code)
open VG.Impl.Sha512.X86 (at_)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `adc d, r`, and the carry. -/
theorem wp_adc {d r : Reg} {c : Bool} (hc : s.cf = some c)
    (k : ∀ s', Upd s s' d (s.gpr d + s.gpr r + (BitVec.ofBool c).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .adc d (.reg r) :: is)) s Q :=
  cons (by simp [exec, execAlu, readSrc, hc]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

/-- `sub d, [b + o]`, and the borrow. -/
theorem wp_subm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d - s.mem.readW (addr B o) 32) →
      s'.cf = some (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (by simp [exec, execAlu, readSrc_mem hb hin]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `and d, [b + o]` -/
theorem wp_andm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d &&& s.mem.readW (addr B o) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (by simp [exec, execAlu, readSrc_mem hb hin]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

end

/-- Only `eax`, `ecx` and `edx` change. -/
structure Keep (s t : State) : Prop where
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s t u : State} (h : Keep s t) (h' : Keep t u) : Keep s u :=
  ⟨fun r a b c => (h'.other r a b c).trans (h.other r a b c), h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr⟩

theorem Keep.of_upd {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v)
    (hd : d = .eax ∨ d = .ecx ∨ d = .edx) : Keep s t :=
  ⟨fun r a b c => u.other r (by rcases hd with rfl | rfl | rfl <;> assumption), u.mem, u.rd, u.wr⟩

/-- The numbers after `k` bits of `n`. -/
def Stage (n D k : Nat) (s : State) : Prop :=
  (s.gpr .ecx).toNat = (n % 2 ^ (32 - k)) * 2 ^ k + n / 2 ^ (32 - k) / D ∧
    (s.gpr .eax).toNat = n / 2 ^ (32 - k) % D

theorem toNat_allOnes32 : (BitVec.allOnes 32).toNat = 2 ^ 32 - 1 := by decide

/-- One bit. -/
theorem bit_ok {s : State} {D : BitVec 32} (hD : 0 < D.toNat) (hD2 : D.toNat < 2 ^ 31) {B : BitVec 32} {d : Nat}
    (hb : s.gpr .ebp = B) (hin : InRegions (s.rd ++ s.wr) (addr B d) 4)
    (hDv : s.mem.readW (addr B d) 32 = D) {n k : Nat} (hn : n < 2 ^ 32) (hk : k < 32)
    (h : Stage n D.toNat k s) {is : List Instr} {Q : State → Prop}
    (hq : ∀ t, Stage n D.toNat (k + 1) t → Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (bit d ++ is)) s Q := by
  obtain ⟨hc, ha⟩ := h
  have hm : k + (31 - k) = 31 := by omega
  have pos : ∀ j, 0 < 2 ^ j := fun j => Nat.two_pow_pos j
  have e32 : 32 - k = 31 - k + 1 := by omega
  have p31 : 2 ^ (31 - k) * 2 ^ k = 2 ^ 31 := by rw [← Nat.pow_add, Nat.add_comm, hm]
  have hRlt : n % 2 ^ (32 - k) < 2 ^ (32 - k) := Nat.mod_lt _ (pos _)
  have hRb := (Nat.div_add_mod' (n % 2 ^ (32 - k)) (2 ^ (31 - k))).symm
  have hb1 : n % 2 ^ (32 - k) / 2 ^ (31 - k) ≤ 1 := by
    have h' : 2 ^ (32 - k) = 2 ^ (31 - k) * 2 := by rw [e32, Nat.pow_succ]
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
  have hR'lt : n % 2 ^ (32 - k) % 2 ^ (31 - k) < 2 ^ (31 - k) := Nat.mod_lt _ (pos _)
  have hqlt : n / 2 ^ (32 - k) / D.toNat < 2 ^ k := by
    refine Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.div_lt_of_lt_mul ?_)
    rw [← Nat.pow_add, show 32 - k + k = 32 by omega]; exact hn
  have hrlt : n / 2 ^ (32 - k) % D.toNat < D.toNat := Nat.mod_lt _ hD
  -- Abbreviations, as numbers.
  generalize hN : n / 2 ^ (32 - k) = N at hc ha hqlt hrlt
  generalize hRR : n % 2 ^ (32 - k) = R at hc hRlt hRb hb1 hR'lt
  generalize hbb : R / 2 ^ (31 - k) = b at hRb hb1
  generalize hR' : R % 2 ^ (31 - k) = R' at hRb hR'lt
  -- The next stage's numbers.
  have N' : n / 2 ^ (32 - (k + 1)) = 2 * N + b := by
    rw [← hN, ← hbb, ← hRR, show 32 - (k + 1) = 31 - k by omega, e32, Nat.pow_succ,
      Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (n / 2 ^ (31 - k)) 2
    omega
  have R'' : n % 2 ^ (32 - (k + 1)) = R' := by
    rw [← hR', ← hRR, show 32 - (k + 1) = 31 - k by omega, e32, Nat.pow_succ, Nat.mod_mul_right_mod]
  have step := Proof.Argon2.divide_step (n := N) (d := D.toNat) (q := N / D.toNat) (r := N % D.toNat)
    (bit := b) (Nat.div_add_mod' N _).symm hrlt hb1
  dsimp only at step
  obtain ⟨st₁, st₂⟩ := step
  have res := Proof.Argon2.divide_result hD st₁ st₂
  -- The instructions, with `K = 2 ^ k` and `P = R' · K`.
  have pk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hP : R' * 2 ^ (k + 1) = 2 * (R' * 2 ^ k) := by rw [pk, Nat.mul_left_comm]
  have hPb : R' * 2 ^ k + 2 ^ k ≤ 2 ^ 31 := by
    have := Nat.mul_le_mul_right (2 ^ k) (show R' + 1 ≤ 2 ^ (31 - k) by omega)
    rw [Nat.add_mul, Nat.one_mul, p31] at this
    exact this
  have hecx : (s.gpr .ecx).toNat = b * 2 ^ 31 + R' * 2 ^ k + N / D.toNat := by
    rw [hc, hRb, Nat.add_mul, Nat.mul_assoc, p31]
  generalize hPP : R' * 2 ^ k = P at hP hPb hecx
  generalize hKK : 2 ^ k = K at hPb hqlt pk
  have hDv' : (s.mem.readW (addr B d) 32).toNat = D.toNat := by rw [hDv]
  simp only [bit, List.cons_append, List.nil_append]
  refine wp_add fun s₁ u₁ c₁ => ?_
  have cb : decide (2 ^ 32 ≤ (s.gpr .ecx).toNat + (s.gpr .ecx).toNat) = decide (b = 1) := by
    rw [hecx]; rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp <;> omega
  have v₁ : (s₁.gpr .ecx).toNat = 2 * P + 2 * (N / D.toNat) := by
    rw [u₁.gpr, BitVec.toNat_add, hecx]
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [show 1 * 2 ^ 31 + P + N / D.toNat + (1 * 2 ^ 31 + P + N / D.toNat) =
        (2 * P + 2 * (N / D.toNat)) + 2 ^ 32 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  refine wp_adc (c := decide (b = 1)) (by rw [c₁, cb]) fun s₂ u₂ => ?_
  have v₂ : (s₂.gpr .eax).toNat = 2 * (N % D.toNat) + b := by
    rw [u₂.gpr, u₁.other _ (by decide), BitVec.toNat_add, BitVec.toNat_add, ha]
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp <;> omega
  refine wp_subm (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin) fun s₃ u₃ c₃ => ?_
  rw [u₂.mem, u₁.mem, hDv] at u₃ c₃
  rw [v₂] at c₃
  refine wp_sbb_self c₃ fun s₄ u₄ => ?_
  refine wp_addi fun s₅ u₅ => ?_
  refine wp_add fun s₆ u₆ _ => ?_
  refine wp_andm (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin)
    fun s₇ u₇ => ?_
  rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hDv] at u₇
  refine wp_add fun s₈ u₈ _ => hq s₈ ⟨?_, ?_⟩ ?_
  · -- `ecx`: the remaining bits above the quotient.
    rw [R'', hP, N', ← res.1, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr,
      u₅.other _ (by decide), u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide)]
    by_cases hv : 2 * (N % D.toNat) + b < D.toNat
    · simp only [hv, decide_true, ite_true]
      rw [BitVec.add_assoc, show (1 : BitVec 32) + BitVec.allOnes 32 = 0#32 by decide, BitVec.add_zero, v₁]
      omega
    · simp only [hv, decide_false, ite_false, Bool.false_eq_true]
      rw [BitVec.toNat_add, BitVec.toNat_add, v₁]
      simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.zero_mod, Nat.add_zero]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · -- `eax`: the remainder.
    rw [N', ← res.2, u₈.gpr, u₇.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₄.gpr, u₃.gpr]
    by_cases hv : 2 * (N % D.toNat) + b < D.toNat
    · simp only [hv, decide_true, ite_true, BitVec.allOnes_and, BitVec.sub_add_cancel]
      rw [v₂]
    · simp only [hv, decide_false, ite_false, Bool.false_eq_true]
      rw [show (0 : BitVec 32) &&& D = 0#32 by simp, BitVec.add_zero,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, v₂]; omega), v₂]
  · exact (Keep.of_upd u₁ (by simp)).trans ((Keep.of_upd u₂ (by simp)).trans ((Keep.of_upd u₃ (by simp)).trans
      ((Keep.of_upd u₄ (by simp)).trans ((Keep.of_upd u₅ (by simp)).trans ((Keep.of_upd u₆ (by simp)).trans
        ((Keep.of_upd u₇ (by simp)).trans (Keep.of_upd u₈ (by simp))))))))

theorem bits_ok {D : BitVec 32} (hD : 0 < D.toNat) (hD2 : D.toNat < 2 ^ 31) {B : BitVec 32} {d n : Nat}
    (hn : n < 2 ^ 32) {is : List Instr} {Q : State → Prop} :
    ∀ k ≤ 32, ∀ s : State, s.gpr .ebp = B → InRegions (s.rd ++ s.wr) (addr B d) 4 →
      s.mem.readW (addr B d) 32 = D → Stage n D.toNat 0 s →
      (∀ t, Stage n D.toNat k t → Keep s t → WP isa (.block is) t Q) →
      WP isa (.block (bits d k ++ is)) s Q
  | 0, _, s, _, _, _, h, hq => hq s h (Keep.refl s)
  | k + 1, hk, s, hb, hin, hDv, h, hq => by
    simp only [bits, List.append_assoc]
    refine bits_ok hD hD2 hn k (by omega) s hb hin hDv h fun t ht kt => ?_
    refine bit_ok hD hD2 (by rw [kt.other _ (by decide) (by decide) (by decide), hb])
      (by rw [kt.rd, kt.wr]; exact hin) (by rw [kt.mem]; exact hDv) hn (by omega) ht
      fun u hu ku => hq u hu (kt.trans ku)

/-- The division: `ecx := n / D`, `eax := n mod D`. -/
theorem code_ok {s : State} {D : BitVec 32} (hD : 0 < D.toNat) (hD2 : D.toNat < 2 ^ 31) {B : BitVec 32}
    {d : Nat} (hb : s.gpr .ebp = B) (hin : InRegions (s.rd ++ s.wr) (addr B d) 4)
    (hDv : s.mem.readW (addr B d) 32 = D) {is : List Instr} {Q : State → Prop}
    (hq : ∀ t, (t.gpr .ecx).toNat = (s.gpr .ecx).toNat / D.toNat →
      (t.gpr .eax).toNat = (s.gpr .ecx).toNat % D.toNat → Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (code d ++ is)) s Q := by
  have hn := (s.gpr .ecx).isLt
  simp only [code, List.cons_append]
  refine wp_movi fun s₁ u₁ => ?_
  refine bits_ok hD hD2 hn 32 (Nat.le_refl _) s₁ (by rw [u₁.other _ (by decide), hb])
    (by rw [u₁.rd, u₁.wr]; exact hin) (by rw [u₁.mem]; exact hDv) ⟨?_, ?_⟩ fun t ⟨hc, ha⟩ kt => ?_
  · rw [u₁.other _ (by decide), Nat.mod_eq_of_lt hn, Nat.div_eq_of_lt hn, Nat.zero_div]; simp
  · rw [u₁.gpr, Nat.div_eq_of_lt hn, Nat.zero_mod]; rfl
  · refine hq t (by rw [hc]; simp [Nat.mod_one]) (by rw [ha]; simp) ((Keep.of_upd u₁ (by simp)).trans kt)

end VG.Proof.Argon2.X86.Divide
