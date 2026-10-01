import VerifiedGarbage.Proof.X448.X86.ByteMem
import VerifiedGarbage.Proof.X448.Radix16Bytes

/-!
# X448 on x86 (32-bit): encoding a limb

Untrusted: everything here is checked by Lean. Two byte stores encode each
16-bit limb in little-endian order without requiring output alignment.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

def packMem (m : Mem) (p : Addr) (i : Nat) (v : BitVec 32) : Mem :=
  (m.writeW (off p (2 * i)) (v.setWidth 8)).writeW (off p (2 * i + 1)) ((v >>> 8).setWidth 8)

theorem packStep_ok {s : State} {base p : Addr} (hs : Scr s base) {i : Nat} (hi : i < 28)
    (hp : (s.gpr .esi).setWidth 64 = p) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hw : ∀ j < 2, InRegions s.wr (off p (2 * i + j)) 1) :
    WP isa (.block (packLimb i)) s fun t =>
      t.mem = packMem s.mem p i (word s.mem base (X2 + 4 * i)) ∧ Keeps [.eax] s t := by
  have ea : ∀ j < 2, addr (s.gpr .esi) (2 * i + j) = off p (2 * i + j) := by
    intro j hj; rw [addr_eq (by omega), hp]
  unfold packLimb
  refine load_ok hs (by simp only [X2, slot]; omega) fun t ht => ?_
  refine wp_store8 (a := off p (2 * i)) (by change addr (t.gpr .esi) _ = _; rw [ht.other .esi (by decide)]; exact ea 0 (by decide))
    (by rw [ht.wr]; exact hw 0 (by decide)) fun u hu => ?_
  refine wp_shift (by decide) fun v hv => ?_
  refine wp_store8 (a := off p (2 * i + 1)) (by change addr (v.gpr .esi) _ = _; rw [hv.other .esi (by decide), hu.gpr, ht.other .esi (by decide)]; exact ea 1 (by decide))
    (by rw [hv.wr, hu.wr, ht.wr]; exact hw 1 (by decide)) fun w hw' => WP.block_nil ⟨?_, ?_⟩
  · rw [hw'.mem, hv.mem, hu.mem, ht.mem, Reg8.reg, hv.gpr, hu.gpr, ht.gpr]; rfl
  · exact ((ht.rest (by decide)).trans ((hu.rest _).trans
      ((hv.rest (by decide)).trans (hw'.rest _))))

theorem packMem_decoded (m : Mem) (p : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32)
    (hv : v.toNat < radix) : decoded (packMem m p i v) p i = v.toNat := by
  have hn : off p (2 * i) ≠ off p (2 * i + 1) := by
    rw [ne_eq, off_eq_iff p (by omega) (by omega)]; omega
  simp only [decoded, byteN, packMem, writeW8_apply, hn, ite_false, ite_true,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [radix] at hv
  omega

theorem packMem_outside (m : Mem) (p : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32) :
    Outside p (2 * i) 2 m (packMem m p i v) := by
  intro x hx
  rw [packMem, writeW8_outside _ _ _ (by omega) (by omega),
    writeW8_outside _ _ _ (by omega) (by omega)]

theorem packLimb_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    {i : Nat} (hi : i < 28) (hp : (s.gpr .esi).setWidth 64 = p)
    (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hw : ∀ j < 2, InRegions s.wr (off p (2 * i + j)) 1) :
    WP isa (.block (packLimb i)) s fun t =>
      decoded t.mem p i = limbs s.mem base X2 i ∧ Outside p (2 * i) 2 s.mem t.mem ∧ Keeps clob s t := by
  refine WP.mono (packStep_ok hs hi hp hfit hw) fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, tk.mono ?_⟩
  · rw [tm]; exact packMem_decoded _ _ hi _ (hb i hi)
  · rw [tm]; exact packMem_outside _ _ hi _
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide

end VG.Proof.X448.X86
