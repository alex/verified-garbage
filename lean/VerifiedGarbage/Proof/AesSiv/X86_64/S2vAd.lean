import VerifiedGarbage.Proof.AesSiv.X86_64.CmacOf

/-!
# AES-SIV on x86-64: `vg_aes_siv_s2v_ad`

The code saves the callee-saved registers in the working space and keeps the
arguments in them, computes the CMAC of the string into the working space
(`cmacOf_wp`), doubles `D` in place, XORs the CMAC into it and restores the
registers: `D` is then `dbl(D) ⊕ CMAC(S)` (`Spec.Siv.s2vStep`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 dblMem dbl_ok dblMem_bytes)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem Env.ofAd {s₀ : State} (h : s2vAdX86_64.pre s₀) :
    Env s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .rsi).toNat (s₀.gpr .r8).toNat := by
  obtain ⟨sp, rd, wr, _, c_s, p_d, p_s, d_s, ret_c, ret_p, ret_d, ret_s, stk_c, stk_p, stk_d, stk_s, wC, wP, wD,
    wS, rounds⟩ := h
  exact ⟨sp, rounds, by rw [rd, wr]; simp, by rw [rd, wr]; simp, by rw [rd, wr]; simp, by rw [wr]; simp, c_s,
    p_d.symm, d_s, p_s, ret_c, ret_d, ret_p, ret_s, stk_c, stk_d, stk_p, stk_s, wC, wD, wP, wS, (s₀.gpr .r8).isLt⟩

theorem saved_le : ∀ p ∈ saved, p.2 + 8 ≤ 208 := by decide

theorem saved_ge : ∀ p ∈ saved, 160 ≤ p.2 := by decide

theorem saved_slots : Spill.Slots saved := by decide

theorem saved_all : ∀ r ∈ calleeSaved, r ≠ .rsp → r ∈ saved.map Prod.fst := by decide

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## The save -/

/-- The registers of the arguments, by name. -/
structure ArgRegs (s₀ : State) (C D P W : Addr) (R L : Nat) : Prop where
  rdi : s₀.gpr .rdi = C
  rsi : s₀.gpr .rsi = BitVec.ofNat 64 R
  rdx : s₀.gpr .rdx = D
  rcx : s₀.gpr .rcx = P
  r8 : s₀.gpr .r8 = BitVec.ofNat 64 L
  r9 : s₀.gpr .r9 = W

theorem adPre_ok (h : Env s₀ C D P W R L) (ha : ArgRegs s₀ C D P W R L) :
    ∃ s₁, runBlock isa adPre s₀ = some s₁ ∧ Regs s₀ C D P W R L s₁ ∧
      s₁.mem = Spill.saveMem s₀.mem W s₀.gpr saved := by
  have hrun := Spill.save_run .r9 saved s₀ (fun p hp => by
    rw [ha.r9]; have := saved_le p hp; exact h.inW rfl (by omega))
  refine ⟨_, by
    rw [adPre, show save .r9 = Spill.saveCode .r9 saved from rfl, runBlock_append, hrun, Option.bind_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
    rfl, ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩, by rw [← ha.r9]; rfl⟩ <;>
    simp (config := {decide := true}) only [gpr_setReg, ite_true, ite_false, ha.rdi, ha.rsi, ha.rdx, ha.rcx,
      ha.r8, ha.r9]

theorem adPre_wp (h : Env s₀ C D P W R L) (ha : ArgRegs s₀ C D P W R L) :
    WP isa (.block adPre) s₀ fun s₁ => Regs s₀ C D P W R L s₁ ∧
      s₁.mem = Spill.saveMem s₀.mem W s₀.gpr saved := by
  obtain ⟨s₁, run, hr, m⟩ := adPre_ok h ha
  exact WP.of_runBlock ⟨s₁, run, hr, m⟩

/-! ## After the CMAC -/

theorem xorD_ok {s : State} (h12 : s.gpr .r12 = D) (h15 : s.gpr .r15 = W)
    (w₀ : InRegions s.wr D 8) (w₁ : InRegions s.wr (D + BitVec.ofNat 64 8) 8)
    (r₀ : InRegions (s.rd ++ s.wr) D 8) (r₁ : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 8) 8)
    (q₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 128) 8)
    (q₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 136) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .r12 0)), .alu .xor .rax (.mem (at_ .r15 stOff)),
        .store (at_ .r12 0) .rax, .mov .rax (.mem (at_ .r12 8)), .alu .xor .rax (.mem (at_ .r15 (stOff + 8))),
        .store (at_ .r12 8) .rax] s = some s' ∧
      s'.mem = (s.mem.writeW D (s.mem.readW D 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 128) 64)).writeW
        (D + BitVec.ofNat 64 8)
        ((s.mem.writeW D (s.mem.readW D 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 128) 64)).readW
            (D + BitVec.ofNat 64 8) 64 ^^^
          (s.mem.writeW D (s.mem.readW D 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 128) 64)).readW
            (W + BitVec.ofNat 64 136) 64) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [stOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, k0, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      ite_true, ite_false, h12, h15, w₀, w₁, r₀, r₁, q₀, q₁]
    rfl, ?_⟩
  refine ⟨rfl, fun r hr => ?_, rfl, rfl⟩
  simp [gpr_setReg, hr]

/-- `dbl(D)` in place, then the CMAC state XORed into it, then the registers
restored from the slots. -/
theorem adPost_wp {s : State} {g : Reg → BitVec 64} (h12 : s.gpr .r12 = D) (h15 : s.gpr .r15 = W)
    (hDw : (⟨D, 16⟩ : Region) ∈ s.wr) (hWw : (⟨W, 2560⟩ : Region) ∈ s.wr)
    (hDW : (⟨D, 16⟩ : Region).Disjoint ⟨W, 2560⟩) (_wD : D.toNat + 16 ≤ 2 ^ 64) (_wW : W.toNat + 2560 ≤ 2 ^ 64)
    (hsv : Spill.Saved s.mem W g saved) :
    WP isa (.block adPost) s fun s' => (∀ r ∈ saved.map Prod.fst, s'.gpr r = g r) ∧
      s'.gpr .rsp = s.gpr .rsp ∧
      Spec.Aes.bytesAt s'.mem D 16 =
        Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 128) 16) ∧
      Frame [⟨D, 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (D + BitVec.ofNat 64 d) 8 :=
    ⟨_, hDw, Offset.contains_base D hd (by omega)⟩
  have inW (d : Nat) (hd : d + 8 ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 :=
    ⟨_, List.mem_append_right _ hWw, Offset.contains_base W hd (by omega)⟩
  have rr {a : Addr} (h : InRegions s.wr a 8) : InRegions (s.rd ++ s.wr) a 8 :=
    let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩
  have cD (d : Nat) (hd : d + 8 ≤ 16) : (⟨D, 16⟩ : Region).Contains (D + BitVec.ofNat 64 d) 8 :=
    Offset.contains_base D hd (by omega)
  -- The doubling.
  have hb : (s.setReg .rbx (s.gpr .r12)).gpr .rbx = D := by rw [gpr_setReg_self, h12]
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ := dbl_ok (s.setReg .rbx (s.gpr .r12)) hb (src := 0) (dst := 0)
    (by rw [rd_setReg, wr_setReg]; exact rr (inD 0 (by decide)))
    (by rw [rd_setReg, wr_setReg]; exact rr (inD (0 + 8) (by decide)))
    (by rw [wr_setReg]; exact inD 0 (by decide)) (by rw [wr_setReg]; exact inD (0 + 8) (by decide))
  rw [mem_setReg] at m₂
  rw [rd_setReg] at rd₂
  rw [wr_setReg] at wr₂
  have r12₂ : s₂.gpr .r12 = D := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), gpr_setReg_of_ne _ _
    (by decide), h12]
  have r15₂ : s₂.gpr .r15 = W := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), gpr_setReg_of_ne _ _
    (by decide), h15]
  have i₀ := inD 0 (by decide)
  rw [k0] at i₀
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := xorD_ok r12₂ r15₂ (by rw [wr₂]; exact i₀) (by rw [wr₂]; exact inD 8 (by decide))
    (by rw [rd₂, wr₂]; exact rr i₀) (by rw [rd₂, wr₂]; exact rr (inD 8 (by decide)))
    (by rw [rd₂, wr₂]; exact inW 128 (by decide)) (by rw [rd₂, wr₂]; exact inW 136 (by decide))
  -- What the doubling and the XOR write.
  have fd : Frame [⟨D, 16⟩] s.mem s₂.mem := by
    rw [m₂, dblMem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cD 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (cD (0 + 8) (by decide))
  have f₃ : Frame [⟨D, 16⟩] s.mem s₃.mem := by
    have c₀ := cD 0 (by decide)
    rw [k0] at c₀
    rw [m₃]
    exact (fd.writeW (List.mem_singleton_self _) _ c₀).writeW (List.mem_singleton_self _) _ (cD 8 (by decide))
  have dW {d n : Nat} (hd : d + n ≤ 2560) (r : Region) (hr : r ∈ [(⟨D, 16⟩ : Region)]) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact hDW.symm.sub_left (Offset.sub_base W hd)
  have hsv₃ : Spill.Saved s₃.mem W g saved :=
    hsv.frame f₃ fun p hp r hr => dW (by have := saved_le p hp; omega) r hr
  have r15₃ : s₃.gpr .r15 = W := by rw [g₃ _ (by decide), r15₂]
  have run₁ : runBlock isa [.mov .rbx (.reg .r12)] s = some (s.setReg .rbx (s.gpr .r12)) := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
  have run : runBlock isa ([.mov .rbx (.reg .r12)] ++ Impl.CmacAes.X86_64.dbl 0 0 ++
      [.mov .rax (.mem (at_ .r12 0)), .alu .xor .rax (.mem (at_ .r15 stOff)), .store (at_ .r12 0) .rax,
       .mov .rax (.mem (at_ .r12 8)), .alu .xor .rax (.mem (at_ .r15 (stOff + 8))), .store (at_ .r12 8) .rax])
      s = some s₃ := by
    rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃]
  rw [show adPost = ([.mov .rbx (.reg .r12)] ++ Impl.CmacAes.X86_64.dbl 0 0 ++
      [.mov .rax (.mem (at_ .r12 0)), .alu .xor .rax (.mem (at_ .r15 stOff)), .store (at_ .r12 0) .rax,
       .mov .rax (.mem (at_ .r12 8)), .alu .xor .rax (.mem (at_ .r15 (stOff + 8))), .store (at_ .r12 8) .rax]) ++
      restore from rfl]
  refine WP.block_append (WP.of_runBlock ⟨s₃, run, ?_⟩)
  refine WP.mono (Spill.restore_ok .r15 saved g s₃ (by decide) (fun p hp => by
      rw [r15₃, rd₃, wr₃, rd₂, wr₂]; exact inW p.2 (by have := saved_le p hp; omega))
    (by rw [r15₃]; exact hsv₃)) fun s₄ ⟨h₄a, h₄b, m₄, rd₄, wr₄⟩ => ?_
  refine ⟨h₄a, ?_, ?_, by rw [m₄]; exact f₃, by rw [rd₄, rd₃, rd₂], by rw [wr₄, wr₃, wr₂]⟩
  · rw [h₄b _ (by decide), g₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide),
      gpr_setReg_of_ne _ _ (by decide)]
  · -- The XOR, a word at a time, of `dbl(D)` and the state.
    have sep : Mem.Sep (D + BitVec.ofNat 64 8) (64 / 8) D (64 / 8) := by
      simpa using Offset.sep D (d := 8) (n := 8) (e := 0) (k := 8) (by decide) (by decide) (by decide)
    have fw : Frame [⟨D, 16⟩] s₂.mem (s₂.mem.writeW D (s₂.mem.readW D 64 ^^^
        s₂.mem.readW (W + BitVec.ofNat 64 128) 64)) := by
      have c₀ := cD 0 (by decide)
      rw [k0] at c₀
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₀
    have e136 : W + BitVec.ofNat 64 136 = W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8 := by
      rw [Offset.add_add]
    rw [m₄, m₃, Proof.Cmac.bytesAt_store2, Mem.readW_writeW_sep sep (by decide),
      fw.readW (Region.contains_self _ _) (fun r hr => dW (d := 136) (n := 8) (by decide) r hr) (by decide), e136,
      Proof.Cmac.xor_words]
    have hd := dblMem_bytes s.mem D 0 0
    rw [k0] at hd
    rw [bytesAt_frame fd (fun r hr => dW (d := 128) (n := 16) (by decide) r hr) (by decide), m₂, hd,
      Spec.Siv.dbl, Siv.xor_eq]

/-! ## The whole function -/

theorem ArgRegs.of {s₀ : State} (h : s2vAdX86_64.pre s₀) :
    ArgRegs s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .rsi).toNat (s₀.gpr .r8).toNat where
  rdi := rfl
  rsi := BitVec.eq_of_toNat_eq (by
    rw [toNat_ofNat (by have := (Env.ofAd h).rounds; rcases this with h | h | h <;> omega)])
  rdx := rfl
  rcx := rfl
  r8 := BitVec.eq_of_toNat_eq (by rw [toNat_ofNat (s₀.gpr .r8).isLt])
  r9 := rfl

theorem s2v_ad_wp (v : Ctr32Impl) {s₀ : State} (h0 : s2vAdX86_64.pre s₀) :
    WP isa (s2vAd v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ s2vAdX86_64.post s₀ s' := by
  have h := Env.ofAd h0
  have ha := ArgRegs.of h0
  have hwr : s₀.wr = [⟨s₀.gpr .rdx, 16⟩, ⟨s₀.gpr .r9, 2560⟩] := h0.2.2.1
  show WP isa (s2vAd v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧
    Spec.Aes.bytesAt s'.mem (s₀.gpr .rdx) 16 =
      Spec.Siv.s2vStep (Spec.Siv.ctxMac s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)
        (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdx) 16) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat)
  generalize s₀.gpr .rdi = C at h ha ⊢
  generalize s₀.gpr .rdx = D at h ha hwr ⊢
  generalize s₀.gpr .rcx = P at h ha ⊢
  generalize s₀.gpr .r9 = W at h ha hwr
  generalize (s₀.gpr .rsi).toNat = R at h ha ⊢
  generalize (s₀.gpr .r8).toNat = L at h ha ⊢
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  obtain ⟨s₁, run₁, hr₁, m₁⟩ := adPre_ok h ha
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (cmacOf_wp v h hr₁) fun s₂ h₂ => ?_)
  have f₁ : Frame [⟨W, 2560⟩] s₀.mem s₁.mem := by
    rw [m₁]; exact Spill.saveMem_frame_base _ _ _ _ (fun p hp => by have := saved_le p hp; omega) (by have := h.wW; omega)
  have hsv₂ : Spill.Saved s₂.mem W s₀.gpr saved := by
    refine (m₁ ▸ Spill.saveMem_saved s₀.mem W s₀.gpr saved saved_slots).frame h₂.frame fun p hp r hr => ?_
    have h1 := saved_le p hp
    have h2 := saved_ge p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base W (by omega) (by have := h.wW; omega)
    · exact Offset.disjoint W (by omega) (by have := h.wW; omega) (by have := h.wW; omega)
    · exact (h.stk_w.sub_right (h.sW (by omega))).symm
  have hr₂ := h₂.regs
  refine WP.mono (adPost_wp hr₂.r12 hr₂.r15 (by rw [hr₂.wr, hwr]; simp) (by rw [hr₂.wr, hwr]; simp) h.d_w h.wD h.wW
    hsv₂) fun s₃ ⟨g₃, rsp₃, out₃, f₃, _, _⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hsp : r = .rsp
    · subst hsp; rw [rsp₃, hr₂.rsp]
    · exact g₃ r (saved_all r hr hsp)
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    rw [f₃.readW c (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.ret_d) (by decide),
      h₂.frame.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.ret_w.sub_right (Region.sub_prefix (by decide))
        · exact h.ret_w.sub_right (h.sW (by decide))
        · exact Offset.base_disjoint_below _ (by decide)) (by decide),
      f₁.readW c (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.ret_w) (by decide)]
  · have dD : Spec.Aes.bytesAt s₂.mem D 16 = Spec.Aes.bytesAt s₀.mem D 16 := by
      rw [bytesAt_frame h₂.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.d_w.sub_right (Region.sub_prefix (by decide))
          · exact h.d_w.sub_right (h.sW (by decide))
          · exact h.stk_d.symm) (by decide),
        bytesAt_frame f₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.d_w) (by decide)]
    have dP : Spec.Aes.bytesAt s₁.mem P L = Spec.Aes.bytesAt s₀.mem P L :=
      bytesAt_frame f₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.p_w)
        (by have := h.lt; omega)
    have dC : Spec.Siv.ctxMac s₁.mem C R = Spec.Siv.ctxMac s₀.mem C R :=
      ctxMac_frame f₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.c_w) hRb
    rw [out₃, h₂.out, dD, dP, dC]
    rfl

/-! ## Constant time -/

theorem s2v_ad_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : s2vAdX86_64.pre s₀) (h0' : s2vAdX86_64.pre s₀')
    (hq : s2vAdX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (s2vAd v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have h := Env.ofAd h0
  have ha := ArgRegs.of h0
  have h' : Env s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .rsi).toNat
      (s₀.gpr .r8).toNat := by
    rw [q2, q3, q4, q5, q6, q7]; exact Env.ofAd h0'
  have ha' : ArgRegs s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .rsi).toNat
      (s₀.gpr .r8).toNat := by
    rw [q2, q3, q4, q5, q6, q7]; exact ArgRegs.of h0'
  generalize s₀.gpr .rdi = C at h ha h' ha'
  generalize s₀.gpr .rdx = D at h ha h' ha'
  generalize s₀.gpr .rcx = P at h ha h' ha'
  generalize s₀.gpr .r9 = W at h ha h' ha'
  generalize (s₀.gpr .rsi).toNat = R at h ha h' ha'
  generalize (s₀.gpr .r8).toNat = L at h ha h' ha'
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (.block adPre)
      hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) (.block adPost)
      hc).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L) fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨WP.mono (adPre_wp h ha) fun _ h => h.1, WP.mono (adPre_wp h' ha') fun _ h => h.1⟩
  have p := RelCT.taint (A := taint) (P := fun a b => Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b) _
    (fun a b hab => regs_agree q1 hab.1 hab.2) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((cmacOf_rel v h h' q1).seq p)

theorem s2v_ad_ct (v : Ctr32Impl) :
    ConstantTime isa s2vAdX86_64.pre s2vAdX86_64.pub (s2vAd v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (s2v_ad_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesSiv.X86_64
