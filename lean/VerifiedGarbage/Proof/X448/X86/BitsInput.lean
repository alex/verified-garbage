import VerifiedGarbage.Proof.X448.X86.Bits
import VerifiedGarbage.Proof.X448.X86.Frame

/-!
# X448 on x86 (32-bit): loading the scalar argument

Scratch-only setup leaves the scalar pointer and input bytes available for
expansion.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448

def bitsRegs : List Reg := [.esi, .eax, .edx]

theorem bits_ok {s₀ s : State} (pre : Pre s₀)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr)
    {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base)
    (hm : Outside base 0 8192 s₀.mem s.mem) (hs : Scr s base)
    (hkd : ∀ i < 56, 8192 ≤ ofs base (off ((arg s₀ 1).setWidth 64) i)) :
    WP isa bits s fun t =>
      Keeps bitsRegs s t ∧ Outside base BITS 448 s.mem t.mem ∧
      ∀ j < 448, t.mem (off base (BITS + j)) =
        BitVec.ofNat 8 (bit (Spec.X448.decodeScalar448
          (Spec.X448.bytesAt s.mem ((arg s₀ 1).setWidth 64) 56)) j) := by
  change WP isa (.block (.mov .esi (.mem (at_ .esp 8)) :: (expandBits ++ clamp))) s _
  refine loadArg_ok pre hsp hr hw (hbase ▸ hm) (by decide : 1 < 4) fun u hu => ?_
  refine WP.mono (bitsData_ok (hs.of_upd hu (by decide)) (by rw [hu.gpr])
    (by rw [hu.gpr]; exact pre.scalar_fit)
    (by intro i hi; rw [hu.rd, hu.wr, hr, hw]; exact ⟨scalarR s₀,
      by rw [pre.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩)
    hkd) fun t ⟨tg, tr, tw, tm, tb⟩ => ?_
  rw [hu.mem] at tm tb
  exact ⟨(hu.rest (by decide)).trans ((show Keeps bitRegs u t from ⟨tg, tr, tw⟩).mono
    (by simp [bitRegs, bitsRegs])), tm, tb⟩

end VG.Proof.X448.X86
