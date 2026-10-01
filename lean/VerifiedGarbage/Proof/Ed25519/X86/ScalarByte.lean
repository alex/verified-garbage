import VerifiedGarbage.Proof.Ed25519.X86.ScalarStep

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Spec.Ed25519 (L)

def scalarFrame (x : BitVec 32) : List Region := [sub x scalarR 32, sub x T 32]

theorem scalarFrame_word {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (hf : Frame (scalarFrame x) m m') : wd m' x 32 = wd m x 32 := by
  apply wd_frame hf
  intro r hr
  simp only [scalarFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_disj (by omega_using [hx]) (by simp only [scalarR]; omega_using [hx]) (Or.inl (by decide))
  · exact sub_disj (by omega_using [hx]) (by simp only [T]; omega_using [hx]) (Or.inl (by decide))

theorem scalarBitLoad_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {j : Nat} (hj : j < 8) :
    WP isa (.block (scalarBitLoad j)) s fun t => Keep s t ∧ t.mem = s.mem ∧
      acc t = (wv s.mem x 32 / 2 ^ (j + 1)) % 2 := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun u₁ h₁ => ?_
  refine Wp.wp_shr (by omega_using [hj]) fun u₂ h₂ _ => ?_
  refine Wp.wp_andi fun u₃ h₃ => Wp.wp_movi fun u₄ h₄ => Wp.wp_movi fun t h₅ => WP.block_nil ?_
  refine ⟨(updKeep h₁).trans ((updKeep h₂).trans ((updKeep h₃).trans ((updKeep h₄).trans (updKeep h₅)))),
    by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_⟩
  simp only [acc, v, h₅.gpr, h₅.other .ebx (by decide), h₅.other .ecx (by decide),
    h₄.gpr, h₄.other .ebx (by decide), toNat_zero32, Nat.mul_zero, Nat.add_zero]
  rw [h₃.gpr, h₂.gpr, h₁.gpr, BitVec.toNat_and]
  change (wd s.mem x 32 >>> (j + 1)).toNat &&& (2 ^ 1 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem scalarBit_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {j : Nat} (hj : j < 8)
    (hr : fe s.mem x scalarR < L) :
    WP isa (.block (scalarBit j)) s fun t => Keep s t ∧ Frame (scalarFrame x) s.mem t.mem ∧
      fe t.mem x scalarR = (2 * fe s.mem x scalarR + (wv s.mem x 32 / 2 ^ (j + 1)) % 2) % L := by
  refine WP.block_append (WP.mono (scalarBitLoad_ok hc hj) fun u ⟨ku, mu, au⟩ => ?_)
  refine WP.mono (scalarRound_ok (ku.ctx hc) (by rw [mu]; exact hr)
    (by rw [au]; exact Nat.mod_lt _ (by decide))) fun t ⟨kt, ft, et⟩ => ?_
  rw [mu] at ft
  exact ⟨ku.trans kt, ft, by rw [et, mu, au]⟩

/-- Pure bit recurrence, kept independent from machine states. -/
def scalarConsume (b : Nat) : Nat → Nat → Nat
  | 0, r => r
  | n + 1, r => scalarConsume b n ((2 * r + b / 2 ^ n % 2) % L)

theorem scalarConsume_eq (b n r : Nat) (hr : r < L) :
    scalarConsume b n r = (2 ^ n * r + b % 2 ^ n) % L := by
  induction n generalizing r with
  | zero => simp only [scalarConsume, Nat.pow_zero, Nat.one_mul, Nat.mod_one, Nat.add_zero,
      Nat.mod_eq_of_lt hr]
  | succ n ih =>
    rw [scalarConsume, ih _ (Nat.mod_lt _ order_pos)]
    have hmod (a y z : Nat) : (a * (y % L) + z) % L = (a * y + z) % L := by
      rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
    rw [hmod, Nat.pow_succ, Nat.mod_mul, Nat.mul_add, Nat.mul_assoc]
    congr 1
    omega_using []

theorem scalarBits_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {n : Nat} (hn : n ≤ 8)
    (hr : fe s.mem x scalarR < L) :
    WP isa (.block (scalarBits n)) s fun t => Keep s t ∧ Frame (scalarFrame x) s.mem t.mem ∧
      fe t.mem x scalarR = scalarConsume (wv s.mem x 32 / 2) n (fe s.mem x scalarR) := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨Keep.refl _, Frame.refl _ _, rfl⟩
  | succ n ih =>
    have ec : scalarBits (n + 1) = scalarBit n ++ scalarBits n := by
      simp only [scalarBits, List.range_succ, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.flatMap_append, List.flatMap_singleton]
    rw [ec]
    refine WP.block_append (WP.mono (scalarBit_ok hc (by omega_using [hn]) hr)
      fun u ⟨ku, fu, eu⟩ => ?_)
    refine WP.mono (ih (ku.ctx hc) (by omega_using [hn])
      (by rw [eu]; exact Nat.mod_lt _ order_pos)) fun t ⟨kt, ft, et⟩ => ?_
    refine ⟨ku.trans kt, fu.trans ft, ?_⟩
    rw [et, wv, scalarFrame_word hc.fit fu, scalarConsume, eu]
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2 (2 ^ n)]

theorem scalarEight_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hr : fe s.mem x scalarR < L) (hb : wv s.mem x 32 / 2 < 256) :
    WP isa (.block (scalarBits 8)) s fun t => Keep s t ∧ Frame (scalarFrame x) s.mem t.mem ∧
      fe t.mem x scalarR = (256 * fe s.mem x scalarR + wv s.mem x 32 / 2) % L := by
  refine WP.mono (scalarBits_ok hc (by decide) hr) fun t ⟨kt, ft, et⟩ => ⟨kt, ft, ?_⟩
  rw [et, scalarConsume_eq _ _ _ hr, show 2 ^ 8 = 256 by decide, Nat.mod_eq_of_lt hb]
end VG.Proof.Ed25519.X86
