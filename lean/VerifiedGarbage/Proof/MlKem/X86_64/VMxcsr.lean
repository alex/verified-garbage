import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/-!
# ML-KEM on x86-64: code with MXCSR `0x1FBF`

Untrusted: everything here is checked by Lean. `withMxcsr r 768 c` (see
`Impl/MlKem/X86_64/Vec.lean`) runs `c` from a state that differs from its
own only in `rax`, `r11` and the eight bytes `mxR` of `scratch`, and after
it changes only those bytes and MXCSR (`withMxcsr_ok`). That it keeps
MXCSR's control bits is `ctlOk` (`Proof/Framework/X86_64/Mxcsr.lean`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-! ## MXCSR -/

/-- The bytes of `scratch` through which `withMxcsr` loads MXCSR. -/
abbrev mxR (sP : Addr) : Region := ⟨sP + BitVec.ofNat 64 768, 8⟩

theorem mx_in {sP : Addr} {rs : List Region} (hw : pR sP ∈ rs) (d : Nat) (hd : 768 ≤ d ∧ d ≤ 772) :
    InRegions rs (sP + BitVec.ofNat 64 d) 4 :=
  ⟨_, hw, Offset.contains_base sP (by omega) (by omega)⟩

theorem mx_sub (sP : Addr) : Region.Sub (mxR sP) (pR sP) := Offset.sub_base sP (by decide)

theorem ldmxcsr_ok (v : BitVec 32) :
    BitVec.extractLsb' 16 16 (BitVec.setWidth 32 (BitVec.setWidth 64 (v &&& 0xFFFF))) = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_and, hi, decide_true,
    Bool.true_and]
  rw [show (0xFFFF : BitVec 32).getLsbD (16 + i) = false by revert i; decide]
  simp

/-- `withMxcsr` runs `c` from `s` but for `rax`, `r11` and `mxR`, and
changes nothing more than `mxR` and MXCSR after it. -/
theorem withMxcsr_ok {c : Prog isa} {r : Reg} (hr : r ≠ .r11 ∧ r ≠ .rax) (rs : List Reg)
    (hrs : r ∉ rs ∧ Reg.r11 ∉ rs) {sP : Addr} {s : State} {Q : State → Prop}
    (hsi : s.gpr r = sP) (hw : pR sP ∈ s.wr) (hk : writesOnly rs c = true)
    (hc : ∀ s1, Keep [.rax, .r11] s s1 → Frame [mxR sP] s.mem s1.mem → WP isa c s1 Q) :
    WP isa (withMxcsr r 768 c) s fun s' => ∃ s2, Q s2 ∧ Frame [mxR sP] s2.mem s'.mem ∧ Keep [] s2 s' := by
  have h0 := mx_in hw 768 (by decide)
  have h0' := mx_in (List.mem_append_right s.rd hw) 768 (by decide)
  have h4 := mx_in hw 772 (by decide)
  simp only [withMxcsr]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r11 = (s.mxcsr &&& 0xFFFF).setWidth 64 ∧ Keep [.r11] s s1 ∧
    Frame [mxR sP] s.mem s1.mem) (by
      vrunm [hsi, h0, h0', Mem.readW_writeW_self32, hr.1]
      refine ⟨by rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq],
        ⟨fun r hr => ?_, rfl, rfl⟩, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Offset.contains sP (by decide) (by decide) (by decide))⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h11, k1, f1⟩ => ?_)
  have hsi1 : s1.gpr r = sP := by rw [k1.gpr (by simpa using hr.1), hsi]
  have h4' : InRegions s1.wr (sP + BitVec.ofNat 64 (768 + 4)) 4 := by rw [k1.2.2]; exact h4
  have h4'' : InRegions (s1.rd ++ s1.wr) (sP + BitVec.ofNat 64 (768 + 4)) 4 :=
    let ⟨r, hr, hc⟩ := h4'; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.seq (WP.seq (WP.mono (Q := fun (s2 : State) => Keep [.rax] s1 s2 ∧ Frame [mxR sP] s1.mem s2.mem)
    (by
      vrunm [hsi1, h4', h4'', Mem.readW_writeW_self32, hr.2]
      refine ⟨⟨fun r hr => ?_, rfl, rfl⟩, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains sP (by decide) (by decide) (by decide))⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s2 ⟨k2, f2⟩ => ?_))
  refine WP.seq (WP.mono (WP.keep _ (hc s2 ((k1.trans k2).mono (by simp)) (f1.trans f2)) hk)
    fun s3 ⟨hq, k3⟩ => ?_)
  have k23 := k2.trans k3
  have hsi3 : s3.gpr r = sP := by rw [k23.gpr (by simp [hr.2, hrs.1]), hsi1]
  have h113 : s3.gpr .r11 = BitVec.setWidth 64 (s.mxcsr &&& 65535) := by rw [k23.gpr (by simp [hrs.2]), h11]
  have h03 : InRegions s3.wr (sP + BitVec.ofNat 64 768) 4 := by rw [k23.2.2, k1.2.2]; exact h0
  have h03' : InRegions (s3.rd ++ s3.wr) (sP + BitVec.ofNat 64 768) 4 :=
    let ⟨r, hr, hc⟩ := h03; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (Q := fun s4 => s4 = s3) (by vrunm) fun s4 h4 => ?_
  subst h4
  vrunm [hsi3, h113, h03, h03', Mem.readW_writeW_self32, ldmxcsr_ok]
  exact ⟨_, hq, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains sP (by decide) (by decide) (by decide)), fun _ _ => rfl, rfl, rfl⟩

/-! ## Regions of `scratch` -/

theorem pR_sub_tab (sP : Addr) : Region.Sub ⟨sP, 256⟩ (pR sP) := Region.sub_prefix (by decide)

theorem pR_sub_S (sP : Addr) : Region.Sub (sR (spW sP)) (pR sP) := Offset.sub_base sP (by decide)

/-- The regions of `scratch` within it, and `f`. -/
theorem frame_fs {fP sP : Addr} {m m' : Mem} {rs : List Region} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (pR fP) ∨ Region.Sub r (pR sP)) : Frame [pR fP, pR sP] m m' :=
  h.sub fun r hr => (hs r hr).elim (fun h => ⟨_, List.mem_cons_self .., h⟩)
    fun h => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩

end VG.Proof.MlKem.X86_64
