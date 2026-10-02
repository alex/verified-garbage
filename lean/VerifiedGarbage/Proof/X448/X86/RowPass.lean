import VerifiedGarbage.Proof.X448.X86.Field

/-!
# X448 on x86 (32-bit): multiplication-row carry propagation

A pass stores one digit at a time and preserves the remaining coefficients for
the next step.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

structure CarryInv (base : Addr) (o : Nat) (s0 : State) (c : Nat → Nat) (k : Nat) (s : State) : Prop where
  regs : Keeps [.eax, .ebx, .edx] s0 s
  carry : (s.gpr .ebx).toNat = Radix16.carry c k
  mem : Outside base o (4 * k) s0.mem s.mem
  outs : ∀ j < k, limbs s.mem base o j = digit c j

theorem carryPass_ok {base : Addr} {o d : Nat} {rb : Reg} {src : Nat → List Instr} {s0 : State}
    {c : Nat → Nat} (hrb : rb ∉ [.eax, .ebx, .edx]) (ho : o + 112 ≤ 8192)
    (hea : ∀ k < 28, s0.ea (at_ rb (d + 4 * k)) = off base (o + 4 * k))
    (hw : ∀ k < 28, InRegions s0.wr (off base (o + 4 * k)) 4)
    (hzero : (s0.gpr .ebx).toNat = 0) (hc : ∀ k < 28, c k ≤ 2 ^ 32 - radix)
    (hsrc : ∀ k < 28, ∀ s, CarryInv base o s0 c k s →
      WP isa (.block (src k)) s fun t =>
        (t.gpr .eax).toNat = c k ∧ Keeps [.eax, .edx] s t ∧ t.mem = s.mem) :
    WP isa (.block (carryPass rb d src)) s0 (CarryInv base o s0 c 28) := by
  refine wp_range_flatMap (M := isa) (CarryInv base o s0 c) (fun k s hk h => ?_) 28 (Nat.le_refl _) s0
    ⟨Keeps.refl _ _, hzero, Outside.refl _ _ _ _, fun j hj => by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (hsrc k hk s h) fun t ⟨tv, tk, tm⟩ => ?_
  have tb : t.gpr .ebx = s.gpr .ebx := tk.1 _ (by decide)
  have tk' : Keeps [.eax, .ebx, .edx] s t := tk.mono (by decide)
  have trb : t.gpr rb = s0.gpr rb := (tk'.1 rb hrb).trans (h.regs.1 rb hrb)
  have ea : t.ea (at_ rb (d + 4 * k)) = off base (o + 4 * k) := by
    simpa only [State.ea, at_, trb] using hea k hk
  have bound : c k + Radix16.carry c k < 2 ^ 32 := by
    have a := hc k hk
    have b := carry_bound (n := k) (fun j hj => hc j (by omega))
    simp only [radix] at a
    omega
  refine WP.mono (carryRaw_ok hrb ea (by rw [tk.2.2, h.regs.2.2]; exact hw k hk)
    (by rw [tv, tb, h.carry]; exact bound)) fun u ⟨uc, um, uk⟩ => ?_
  rw [tv, tb, h.carry] at uc um
  rw [tm] at um
  refine ⟨h.regs.trans ((tk.mono (by decide)).trans uk), uc, ?_, ?_⟩
  · rw [um]
    exact (h.mem.mono (by omega) (by omega)).trans
      ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · intro j hj
    change (word u.mem base (o + 4 * j)).toNat = _
    rw [um, word_write s.mem base (by omega) (by omega)]
    by_cases he : j = k
    · rw [ite_eq_left he, he, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_trans (digit_lt c k) (by decide : radix < 2 ^ 32))
    · rw [ite_eq_right he]; exact h.outs j (by omega)

end VG.Proof.X448.X86
