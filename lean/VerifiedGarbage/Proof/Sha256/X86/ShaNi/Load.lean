import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Block

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86 VG.Impl.Sha256.X86.ShaNi
open VG.Proof.Sha256.X86 (Pre st scr esp₀ stR scrR H₀ stAddr workRegion work_sub saved_frame
  contains_sub stateAt_eq stateAt_get)
open VG.Spec.Sha256 (stateAt compressBlocks)

theorem loadPointer_ok (s : State) (p : BitVec 32)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4)
    (hv : s.mem.readW (addr (s.gpr .esp) 4) 32 = p) :
    WP isa (.block [.mov .ebx (.mem (at_ .esp 4))]) s fun s' =>
      s'.gpr .ebx = p ∧ (∀ r, r ≠ .ebx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, State.load32,
    ea_at, hin, ite_true, hv, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg]
  exact ⟨trivial, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, trivial, trivial, trivial, trivial⟩

theorem storeMask_ok (s : State)
    (hout : InRegions s.wr (addr (s.gpr .esi) 16) 16) :
    WP isa (.block [.movdquStore (at_ .esi 16) .xmm0]) s fun s' =>
      s'.mem = s.mem.writeW (addr (s.gpr .esi) 16) (s.xmm .xmm0) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128, ea_at,
    hout, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State}
    (hc : VG.Proof.Sha256.X86.Common s₀ 0 s) :
    WP isa (.block load) s fun s' =>
      Common s₀ 0 s' ∧ (∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r) ∧ s'.zf = s.zf := by
  have shape : load = [.mov .ebx (.mem (at_ .esp 4))] ++
      (const bswapMask ++ (([.movdquStore (at_ .esi 16) .xmm0] : List Instr) ++ loadState)) := by
    simp only [load, List.append_assoc]
  rw [shape, WP.block_append_iff]
  refine WP.mono (loadPointer_ok s (st s₀)
    (by rw [hc.esp, hc.rd, hc.wr]; exact hp.in_arg (by decide) (by decide))
    (by rw [hc.esp]; exact hp.arg_frame hc.frame (i := 0) (by decide)))
    fun s₁ ⟨hb₁, hg₁, hm₁, hrd₁, hwr₁, hz₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok bswapMask s₁)
    fun s₂ ⟨h0, hx₂, hg₂, hm₂, hrd₂, hwr₂, hz₂⟩ => ?_
  have hsi₂ : s₂.gpr .esi = scr s₀ := (hg₂ _ (by decide)).trans ((hg₁ _ (by decide)).trans hc.esi)
  rw [WP.block_append_iff]
  refine WP.mono (storeMask_ok s₂
    (by rw [hsi₂, hwr₂, hwr₁, hc.wr]; exact Pre.scr_vec hp (by decide)))
    fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃, hz₃⟩ => ?_
  have hmem : s₃.mem = s.mem.writeW (addr (scr s₀) 16) bswapMask := by
    rw [hm₃, hm₂, hm₁, hsi₂, h0]
  have hframe : Frame [workRegion (scr s₀)] s.mem s₃.mem := by
    rw [hmem]; exact work_write128 _ hp.scr_fits _ _ (by decide)
  have hframeFull : Frame [stR s₀, scrR s₀] s.mem s₃.mem := hframe.sub
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨scrR s₀, by simp, work_sub _⟩)
  have state : stateAt s₃.mem ((st s₀).setWidth 64) =
      compressBlocks (H₀ s₀) s₀.mem ((VG.Proof.Sha256.X86.bp s₀).setWidth 64) 0 := by
    apply stateAt_eq hp
    intro k hk
    rw [hframe.readW (contains_sub (len := 32) (off := 4 * k) (by omega) (by omega)
      (hp.stAddr_eq hk)) (by simpa using hp.st_scr.sub_right (work_sub _)) (by decide),
      ← stateAt_get hp s.mem hk, hc.state]
  have hb₃ : s₃.gpr .ebx = st s₀ := by rw [hg₃, hg₂ _ (by decide), hb₁]
  have rd₃ : s₃.rd = s₀.rd := hrd₃.trans (hrd₂.trans (hrd₁.trans hc.rd))
  have wr₃ : s₃.wr = s₀.wr := hwr₃.trans (hwr₂.trans (hwr₁.trans hc.wr))
  have out0 : InRegions s₀.wr ((st s₀).setWidth 64) 16 :=
    ⟨stR s₀, by simp [hp.wr], by simpa only [BitVec.add_zero] using
      (Offset.contains_base ((st s₀).setWidth 64) (d := 0) (n := 16) (k := 32) (by decide) (by decide))⟩
  have out16 : InRegions s₀.wr ((st s₀).setWidth 64 + BitVec.ofNat 64 16) 16 :=
    ⟨stR s₀, by simp [hp.wr], Offset.contains_base _ (by decide) (by decide)⟩
  refine WP.mono (loadState_ok s₃ (by rw [hb₃]; exact hp.st_fits)
    (by rw [hb₃, rd₃, wr₃]; exact in_read_of_write out0)
    (by rw [hb₃, rd₃, wr₃]; exact in_read_of_write out16))
    fun s₄ ⟨x1, x2, hz₄, hg₄, hm₄, hrd₄, hwr₄⟩ => ?_
  have regs : ∀ r, r ≠ .eax → r ≠ .ebx → s₄.gpr r = s.gpr r :=
    fun r ha hb => (congrFun hg₄ r).trans ((congrFun hg₃ r).trans ((hg₂ r ha).trans (hg₁ r hb)))
  refine ⟨⟨?_, ?_, (regs _ (by decide) (by decide)).trans hc.esi,
    (regs _ (by decide) (by decide)).trans hc.esp, ?_, hrd₄.trans rd₃, hwr₄.trans wr₃,
    ?_, ?_, ?_⟩, regs, hz₄.trans (hz₃.trans (hz₂.trans hz₁))⟩
  · rw [x1, hb₃, state]
  · rw [x2, hb₃, state]
  · rw [hg₄]; exact hb₃
  · rw [hm₄]; exact hc.frame.trans hframeFull
  · rw [hm₄]; exact saved_frame hp hc.saved (.inl hframe)
  · rw [hm₄, hmem]; exact Mem.readW_writeW_self _ _ 16 _ (by decide)

end VG.Proof.Sha256.X86.ShaNi
