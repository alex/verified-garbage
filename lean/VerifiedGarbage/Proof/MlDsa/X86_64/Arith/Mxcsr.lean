import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic

/-!
# ML-DSA on x86-64: MXCSR through the end of a polynomial

`withMxcsr r 1016 c` (ML-KEM's, see `Impl/MlKem/X86_64/Vec.lean`) through the
last 8 bytes `mxH` of a writable polynomial at `r` (`withMxcsrH_ok`), as
ML-KEM's `withMxcsr_ok` through `scratch + 768`.
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ldmxcsr_ok)

/-- The last 8 bytes of the polynomial at `p`. -/
abbrev mxH (p : Addr) : Region := ⟨p + BitVec.ofNat 64 1016, 8⟩

theorem mxH_in {p : Addr} {rs : List Region} (hw : pR p ∈ rs) (d : Nat) (hd : 1016 ≤ d ∧ d ≤ 1020) :
    InRegions rs (p + BitVec.ofNat 64 d) 4 :=
  ⟨_, hw, Offset.contains_base p (by omega) (by omega)⟩

theorem mxH_sub (p : Addr) : Region.Sub (mxH p) (pR p) := Offset.sub_base p (by decide)

/-- `withMxcsr` through `mxH`: `c` runs from `s` but for `rax`, `r11` and
those bytes, and nothing more than they and MXCSR change after it. -/
theorem withMxcsrH_ok {c : Prog isa} {r : Reg} (hr : r ≠ .r11 ∧ r ≠ .rax) (rs : List Reg)
    (hrs : r ∉ rs ∧ Reg.r11 ∉ rs) {p : Addr} {s : State} {Q : State → Prop}
    (hsi : s.gpr r = p) (hw : pR p ∈ s.wr) (hk : writesOnly rs c = true)
    (hc : ∀ s1, Keep [.rax, .r11] s s1 → Frame [mxH p] s.mem s1.mem → s1.xmm = s.xmm → s1.ymmHi = s.ymmHi →
      WP isa c s1 Q) :
    WP isa (withMxcsr r 1016 c) s fun s' =>
      ∃ s2, Q s2 ∧ Frame [mxH p] s2.mem s'.mem ∧ Keep [] s2 s' ∧ s'.xmm = s2.xmm ∧ s'.ymmHi = s2.ymmHi := by
  have h0 := mxH_in hw 1016 (by decide)
  have h0' := mxH_in (List.mem_append_right s.rd hw) 1016 (by decide)
  have h4 := mxH_in hw 1020 (by decide)
  simp only [withMxcsr]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r11 = (s.mxcsr &&& 0xFFFF).setWidth 64 ∧ Keep [.r11] s s1 ∧
    Frame [mxH p] s.mem s1.mem ∧ s1.xmm = s.xmm ∧ s1.ymmHi = s.ymmHi) (by
      vrunm [hsi, h0, h0', Mem.readW_writeW_self32, hr.1]
      refine ⟨by rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq],
        ⟨fun r hr => ?_, rfl, rfl⟩, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains p (by decide) (by decide) (by decide)),
        by simp only [RegUpd.ymmHi_setReg, RegUpd.ymmHi_setFlags]⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h11, k1, f1, x1, y1⟩ => ?_)
  have hsi1 : s1.gpr r = p := by rw [k1.gpr (by simpa using hr.1), hsi]
  have h4' : InRegions s1.wr (p + BitVec.ofNat 64 (1016 + 4)) 4 := by rw [k1.2.2]; exact h4
  have h4'' : InRegions (s1.rd ++ s1.wr) (p + BitVec.ofNat 64 (1016 + 4)) 4 :=
    let ⟨r, hr, hc⟩ := h4'; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.seq (WP.seq (WP.mono (Q := fun (s2 : State) => Keep [.rax] s1 s2 ∧ Frame [mxH p] s1.mem s2.mem ∧
      s2.xmm = s1.xmm ∧ s2.ymmHi = s1.ymmHi)
    (by
      vrunm [hsi1, h4', h4'', Mem.readW_writeW_self32, hr.2]
      refine ⟨⟨fun r hr => ?_, rfl, rfl⟩, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains p (by decide) (by decide) (by decide)), by simp only [RegUpd.ymmHi_setReg]⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s2 ⟨k2, f2, x2, y2⟩ => ?_))
  refine WP.seq (WP.mono (WP.keep _ (hc s2 ((k1.trans k2).mono (by simp)) (f1.trans f2) (x2.trans x1)
    (y2.trans y1)) hk)
    fun s3 ⟨hq, k3⟩ => ?_)
  have k23 := k2.trans k3
  have hsi3 : s3.gpr r = p := by rw [k23.gpr (by simp [hr.2, hrs.1]), hsi1]
  have h113 : s3.gpr .r11 = BitVec.setWidth 64 (s.mxcsr &&& 65535) := by rw [k23.gpr (by simp [hrs.2]), h11]
  have h03 : InRegions s3.wr (p + BitVec.ofNat 64 1016) 4 := by rw [k23.2.2, k1.2.2]; exact h0
  have h03' : InRegions (s3.rd ++ s3.wr) (p + BitVec.ofNat 64 1016) 4 :=
    let ⟨r, hr, hc⟩ := h03; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (Q := fun s4 => s4 = s3) (by vrunm) fun s4 h4 => ?_
  subst h4
  vrunm [hsi3, h113, h03, h03', Mem.readW_writeW_self32, ldmxcsr_ok]
  exact ⟨_, hq, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains p (by decide) (by decide) (by decide)), ⟨fun _ _ => rfl, rfl, rfl⟩, rfl, rfl⟩

end VG.Proof.MlDsa.X86_64.Arith
