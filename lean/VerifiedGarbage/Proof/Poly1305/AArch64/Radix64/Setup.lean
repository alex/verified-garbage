import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Absorb
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Reduce
import VerifiedGarbage.Proof.Poly1305.AArch64.Blocks

namespace VG.Proof.Poly1305.AArch64.Radix64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.AArch64 VG.PowLit
open VG.Spec.Poly1305 (P)

def Keys (R : Nat) (s : State) : Prop :=
  ∃ q, (s.gpr .x7).toNat < 2 ^ 60 ∧ (s.gpr .x8).toNat = 4 * q ∧ q < 2 ^ 58 ∧
    (s.gpr .x17).toNat = 5 * q ∧ (s.gpr .x7).toNat + 2 ^ 64 * (s.gpr .x8).toNat = R

def Bounds (s : State) : Prop := (s.gpr .x6).toNat ≤ 4

abbrev hv := hval

theorem key0_lt (k : BitVec 64) : (k &&& M0).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem key1_lt (k : BitVec 64) : (k &&& M1).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem key1_mod (k : BitVec 64) : (k &&& M1).toNat % 4 = 0 := by
  rw [BitVec.toNat_and, show (4 : Nat) = 2 ^ 2 from rfl,
    ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show M1.toNat &&& 2 ^ 2 - 1 = 0 by decide, Nat.and_zero]

theorem s1_toNat (k : BitVec 64) :
    (((k &&& M1) >>> 2) + (k &&& M1)).toNat = 5 * ((k &&& M1).toNat / 4) := by
  have h1 := key1_lt k
  have h2 := key1_mod k
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega_using [h1, h2]

set_option simprocs false in
theorem setup_regs (s : State) (hw : sR (s.gpr .x0) ∈ s.rd ++ s.wr) :
    WP isa (.block setup) s fun s' =>
      s'.gpr .x7 = s.mem.readW (off (s.gpr .x0) 24) 64 &&& M0 ∧
      s'.gpr .x8 = s.mem.readW (off (s.gpr .x0) 32) 64 &&& M1 ∧
      (s'.gpr .x17).toNat = 5 * ((s'.gpr .x8).toNat / 4) ∧
      s'.gpr .x4 = s.mem.readW (off (s.gpr .x0) 0) 64 ∧
      s'.gpr .x5 = s.mem.readW (off (s.gpr .x0) 8) 64 ∧
      s'.gpr .x6 = s.mem.readW (off (s.gpr .x0) 16) 64 ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x16, .x17] s s' := by
  have i : ∀ d, d + 8 ≤ 128 →
      InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega_using [hd])⟩
  have i0 := i 0 (by decide)
  have i8 := i 8 (by decide)
  have i16 := i 16 (by decide)
  have i24 := i 24 (by decide)
  have i32 := i 32 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [setup, VG.Impl.Poly1305.AArch64.const64,
    List.cons_append, List.nil_append, runBlock_cons, runBlock_nil, isa, runStep_some,
    exec, addr, Size.bytes, State.load, i0, i8, i16, i24, i32, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [movz_movk64']; rfl
  · rw [movz_movk64']; rfl
  · rw [movz_movk64', s1_toNat]
  · rfl
  · rfl
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

theorem setup_ok (s : State) (hw : sR (s.gpr .x0) ∈ s.wr) :
    WP isa (.block setup) s fun s' =>
      Keys (Rk s.mem (s.gpr .x0)) s' ∧
      (A0 s < P → hval s' = A0 s ∧ Bounds s') ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x16, .x17] s s' := by
  refine (setup_regs s (List.mem_append_right _ hw)).mono fun s' ⟨r0, r1, t, h0, h1, h2, k⟩ => ?_
  refine ⟨?_, ?_, k⟩
  · refine ⟨(s'.gpr .x8).toNat / 4, ?_, ?_, ?_, t, ?_⟩
    · rw [r0]; exact key0_lt _
    · have e := key1_mod (s.mem.readW (off (s.gpr .x0) 32) 64)
      rw [← r1] at e
      omega_using [e]
    · have e := key1_lt (s.mem.readW (off (s.gpr .x0) 32) 64)
      rw [← r1] at e
      omega_using [e]
    · rw [r0, r1]
  · intro hA
    have e : hval s' = A0 s := by
      simp only [hval, h0, h1, h2, A0, leNum_acc, w64, off]
    refine ⟨e, ?_⟩
    have a0 := (s'.gpr .x4).isLt
    have a1 := (s'.gpr .x5).isLt
    simp only [Bounds, hval, P] at e hA ⊢
    omega_using [e, hA, a0, a1]

theorem Keys.of_regs {R : Nat} {s s' : State} (hk : Keys R s)
    (h : ∀ r ∈ [Reg.x7, .x8, .x17], s'.gpr r = s.gpr r) : Keys R s' := by
  simpa only [Keys, h .x7 (by simp), h .x8 (by simp), h .x17 (by simp)] using hk

theorem bounds_eq {s s' : State}
    (h : ∀ r ∈ [Reg.x4, .x5, .x6], s'.gpr r = s.gpr r) :
    hval s' = hval s ∧ (Bounds s → Bounds s') := by
  simp only [hval, Bounds, h .x4 (by simp), h .x5 (by simp), h .x6 (by simp)]
  exact ⟨trivial, id⟩

theorem absorb_key_ok (s : State) (pad : Bool) {R : Nat} (hk : Keys R s)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 8) 8) :
    WP isa (.block (absorb pad)) s fun s' =>
      (Bounds s → hval s' % P =
        ((hval s + (word s.mem (s.gpr .x1) 0 + 2 ^ 64 * word s.mem (s.gpr .x1) 8 +
          2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps absorbRegs s s' := by
  obtain ⟨q, hr0, hr1, hq, hs1, hr⟩ := hk
  simpa only [← hr, Bounds] using absorb_ok s pad hr0 hr1 hq hs1 h0 h8

end VG.Proof.Poly1305.AArch64.Radix64
