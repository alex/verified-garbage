import VerifiedGarbage.Proof.X448.X86.Fill
import VerifiedGarbage.Proof.X448.X86.RowMem

/-!
# X448 on x86 (32-bit): initializing multiplication

Untrusted: everything here is checked by Lean. The initial 28 zero digits
represent the empty product prefix; each row adds its final carry word.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem zeroAcc_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block zeroAcc) s fun t =>
      (∀ i < 28, accw t.mem base i = 0) ∧ Outside base ACC 112 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold zeroAcc
  rw [WP.block_append_iff]
  refine WP.mono (zeroEax_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  have hf := fill_ok (hs.of_keeps tk (by decide)) (by decide : ACC + 4 * 28 ≤ 4096) tz
  rw [List.map_eq_flatMap] at hf
  refine WP.mono hf fun u ⟨uf, um, uk⟩ => ⟨uf, ?_, tk.trans (uk.mono (by simp))⟩
  rw [← tm]; exact um

theorem mulPre_ok {s : State} {base : Addr} (hs : Scr s base) (a b : Nat) :
    WP isa (.block mulPre) s (RowInv base a b s 0) := by
  unfold mulPre
  rw [WP.block_append_iff]
  refine WP.mono (zeroAcc_ok hs) fun t ⟨tf, tm, tk⟩ => ?_
  refine wp_mov rfl fun u hu => WP.block_nil ?_
  have uk : Keeps clob s u := (tk.mono (by decide)).trans (hu.rest (by decide))
  refine ⟨hs.of_keeps uk (by decide), uk, ?_, ?_, ?_, ?_⟩
  · change u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 0
    rw [BitVec.add_zero, hu.gpr, hu.other .edi (by decide)]
  · rw [hu.mem]; exact tm.mono (by decide) (by decide)
  · intro i hi; rw [hu.mem, tf i hi]; decide
  · rw [hu.mem, valN_congr tf, valN_zero]
    exact (Nat.zero_mul _).symm

end VG.Proof.X448.X86
