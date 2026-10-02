import VerifiedGarbage.Proof.AesGcm.X86.Fn

/-!
# AES-GCM on x86: the tag (`tag`)

Untrusted: everything here is checked by Lean. `tag o …` absorbs the
lengths block (`lens 16`), copies the accumulator to `W + o` and encrypts
it there with `vg_aes_ctr32` from the counter block `J₀` (at the state's
first block): `GHASH ⊕ CIPH_K(J₀)` (`tag_pc`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ofBytes toBytes)
open VG.Proof.Gcm (lensBlock)
open VG.Proof.Cmac (le4 store4)

theorem bytesAt_toBytes (m : Mem) (p : Addr) : bytesAt m p 16 = toBytes (blockAt m p) :=
  (Cmac.toBytes_ofBytes (length_bytesAt _ _ _)).symm

theorem bytesAt16 (m : Mem) (p : Addr) : bytesAt m p 16 = bytesAt m p 4 ++ bytesAt m (p + BitVec.ofNat 64 4) 4 ++
    bytesAt m (p + BitVec.ofNat 64 8) 4 ++ bytesAt m (p + BitVec.ofNat 64 12) 4 := by
  rw [show (16 : Nat) = 4 + 12 from rfl, bytesAt_add, show (12 : Nat) = 4 + 8 from rfl, bytesAt_add,
    show (8 : Nat) = 4 + 4 from rfl, bytesAt_add, add_ofNat_assoc, add_ofNat_assoc, List.append_assoc,
    List.append_assoc]

/-- The regions `tag o` writes. -/
abbrev tagFrame (St W SP : BitVec 32) (o : Nat) : List Region :=
  [⟨w64 St, 32⟩, ⟨w64 W + BitVec.ofNat 64 96, 16⟩, ⟨w64 W + BitVec.ofNat 64 o, 16⟩, wsR W, below SP 28]

/-- Before `tag o al ah tl th`. -/
structure TagIn (Ctx St W SP : BitVec 32) (R : Nat) (al ah tl th : Nat) (alo ahi tlo thi : BitVec 32) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  sl : LensSlots W al ah tl th alo ahi tlo thi s.mem
  rounds : RoundsAt s.mem W R

/-- After: the tag at `W + o`, from `m₀`. -/
structure TagOut (Ctx St W SP : BitVec 32) (R o aN tN : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  rounds : RoundsAt s.mem W R
  out : bytesAt s.mem (w64 W + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom (Hk m₀ Ctx) (blockAt m₀ (w64 St + BitVec.ofNat 64 16)) [ofBytes (lensBlock aN tN)] ^^^
      ciphOf m₀ Ctx R (blockAt m₀ (w64 St)))
  frame : Frame (tagFrame St W SP o) m₀ s.mem

/-- After the lengths block and the copy, from `m₀`. -/
structure TagMid (Ctx St W SP : BitVec 32) (R o aN tN : Nat) (m₀ : Mem) (s : State) : Prop where
  ready : CtrReady Ctx St W SP R St (W + BitVec.ofNat 32 o) 1 s
  acc : blockAt s.mem (w64 W + BitVec.ofNat 64 o) =
    ghashFrom (Hk m₀ Ctx) (blockAt m₀ (w64 St + BitVec.ofNat 64 16)) [ofBytes (lensBlock aN tN)]
  j : blockAt s.mem (w64 St) = blockAt m₀ (w64 St)
  ciph : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R
  frame : Frame (tagFrame St W SP o) m₀ s.mem

section
variable {Ctx St W SP : BitVec 32} (L : Lay Ctx St W SP 28)
include L

omit L in
theorem t_tagFrame {o : Nat} {m m' : Mem} (h : Frame (tFrame St W SP 28 16) m m') :
    Frame (tagFrame St W SP o) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base (w64 St) (show 16 + 16 ≤ 32 by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨wsR W, by simp, fun _ h => h⟩
    · exact ⟨below SP 28, by simp, fun _ h => h⟩

/-- The copy of the accumulator to `W + o`, and the arguments of `vg_aes_ctr32`. -/
theorem tagCopy_ok {R o aN tN : Nat} (ho : o = 0 ∨ o = 112) {m₀ : Mem} {s : State}
    (he : Env Ctx St W SP s) (hR : RoundsAt s.mem W R)
    (hacc : blockAt s.mem (w64 St + BitVec.ofNat 64 16) =
      ghashFrom (Hk m₀ Ctx) (blockAt m₀ (w64 St + BitVec.ofNat 64 16)) [ofBytes (lensBlock aN tN)])
    (hj : blockAt s.mem (w64 St) = blockAt m₀ (w64 St)) (hc : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R)
    (hf : Frame (tagFrame St W SP o) m₀ s.mem) :
    WP isa (.block [.mov .eax (.mem (at_ .esi 16)), .mov .ecx (.mem (at_ .esi 20)), .mov .edx (.mem (at_ .esi 24)),
      .mov .ebx (.mem (at_ .esi 28)), .store (at_ .ebp o) .eax, .store (at_ .ebp (o + 4)) .ecx,
      .store (at_ .ebp (o + 8)) .edx, .store (at_ .ebp (o + 12)) .ebx, .mov .ebx (.reg .ebp),
      .alu .add .ebx (imm o), .mov .edi (imm 1), .mov .eax (slot ctxO), .mov .ecx (slot roundsO),
      .mov .edx (.reg .esi), .alu .add .ebp (imm scrO)]) s (TagMid Ctx St W SP R o aN tN m₀) := by
  have r₁ := hR.1
  rw [slotv_eq] at r₁
  have ho' : o + 16 ≤ 128 := by omega
  generalize hw0 : s.mem.readW (w64 St + BitVec.ofNat 64 16) 32 = w0
  generalize hw1 : s.mem.readW (w64 St + BitVec.ofNat 64 20) 32 = w1
  generalize hw2 : s.mem.readW (w64 St + BitVec.ofNat 64 24) 32 = w2
  generalize hw3 : s.mem.readW (w64 St + BitVec.ofNat 64 28) 32 = w3
  have hctx := he.ctx
  have hm4 : ∀ v : BitVec 32, store4 s.mem (w64 W + BitVec.ofNat 64 o) w0 w1 w2 v =
      (((s.mem.writeW (w64 W + BitVec.ofNat 64 o) w0).writeW (w64 W + BitVec.ofNat 64 (o + 4)) w1).writeW
        (w64 W + BitVec.ofNat 64 (o + 8)) w2).writeW (w64 W + BitVec.ofNat 64 (o + 12)) v := fun v => by
    simp only [store4, add_ofNat_assoc]
  refine WP.of_runBlock ⟨_, by xrun [he.esi, he.ebp, L.aS, L.aW, he.stIn', he.wIn, he.wIn', readW_writeW_off,
    hctx, r₁, hw0, hw1, hw2, hw3, ← hm4], ?_⟩
  generalize hM : store4 s.mem (w64 W + BitVec.ofNat 64 o) w0 w1 w2 w3 = M
  have f₄ : Frame [⟨w64 W + BitVec.ofNat 64 o, 16⟩] s.mem M := by rw [← hM]; exact Cmac.frame_store4 _ _ _ _ _
  have sK : ∀ {q}, 128 ≤ q → q + 4 ≤ 2560 → slotv M W q = slotv s.mem W q := fun h₁ h₂ =>
    slot_frame f₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by omega)
  have dS : ∀ {a k : Nat}, a + k ≤ 80 → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 o, 16⟩ : Region)],
      (⟨w64 St + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r := fun hak r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rcases ho with rfl | rfl
    · exact L.st_w hak (.inl (by decide))
    · exact L.st_w hak (.inr ⟨by decide, by decide⟩)
  have hR' : RoundsAt M W R := ⟨by rw [sK (by decide) (by decide)]; exact hR.1, hR.2⟩
  have eW := L.aW (o := o) (by omega)
  have eS : w64 (St + BitVec.ofNat 32 0) = w64 St := by rw [L.aS (by decide)]; exact BitVec.add_zero _
  refine ⟨⟨by regs []; exact (sK (q := 144) (by decide) (by decide)).trans hctx,
    by regs []; exact (sK (q := 148) (by decide) (by decide)).trans hR.1, by regs [he.esi], by regs [he.ebp], by regs [], by regs [he.ebp],
    by regs [he.esi], by regs [he.esp], he.ctxR, he.stW, he.wW, by simp only [mem_setReg, mem_arithFlags, mem_setMem]; exact (sK (q := 144) (by decide) (by decide)).trans hctx,
    by simp only [mem_setReg, mem_arithFlags, mem_setMem]; exact hR', by have := L.fs; omega, by rw [L.nW (by omega)]; have := L.fw; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (by simpa using he.stC (d := 0) (n := 16) (by decide) : Covers [⟨w64 St, 16⟩] s.wr)
  · rw [eW]; exact (he.wC (d := o) (n := 16 * 1) (by omega) : Covers _ s.wr)
  · rw [eW]; have := dS (a := 0) (k := 16) (by decide) _ (List.mem_singleton_self _); simpa using this
  · exact L.cs.sub_right (Region.sub_prefix (by decide))
  · rw [eW]; exact L.ctx_w (a := 0) (n := 256) (d := o) (k := 16 * 1) (by decide) (by omega) |> fun h => by simpa using h
  · simpa using L.st_w (a := 0) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)
  · rw [eW]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · simpa using L.stk_st (a := 0) (n := 16) (by decide)
  · rw [eW]; exact L.stk_w (by omega)
  · simpa using (L.st_w (a := 0) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · rw [eW]; exact Lay.w_w (.inr (by omega)) (by decide) (by omega)
  · simp only [mem_setReg, mem_arithFlags, mem_setMem]
    rw [← hM, blockAt, Cmac.bytesAt_store4, ← hw0, ← hw1, ← hw2, ← hw3, Cmac.le4_readW, Cmac.le4_readW,
      Cmac.le4_readW, Cmac.le4_readW, ← hacc, blockAt]
    congr 1
    rw [bytesAt16, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]
  · simp only [mem_setReg, mem_arithFlags, mem_setMem]
    have := blockAt_frame f₄ (dS (a := 0) (k := 16) (by decide))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this, hj]
  · simp only [mem_setReg, mem_arithFlags, mem_setMem]
    rw [ciph_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.ctx_w (a := 0) (n := 256) (d := o) (k := 16) (by decide) (by omega) |> fun h => by simpa using h)
      hR.2, hc]
  · simp only [mem_setReg, mem_arithFlags, mem_setMem]
    exact hf.trans (f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩)

theorem kept_tFrame : ∀ r ∈ tFrame St W SP 28 16, (keptR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem ctx_tFrame' : ∀ r ∈ tFrame St W SP 28 16, (⟨w64 Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw.sub_right (Lay.wSub (by decide))
  · exact L.cw.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

theorem tag_pc {R o al ah tl th : Nat} (ho : o = 0 ∨ o = 112) (hc : LensAt 16 al ah tl th)
    {alo ahi tlo thi : BitVec 32} :
    Pc (fun (m₀ : Mem) s => TagIn Ctx St W SP R al ah tl th alo ahi tlo thi s ∧ s.mem = m₀) (tag vg.callees o al ah tl th)
      (TagOut Ctx St W SP R o (val64 alo ahi) (val64 tlo thi) ·) := by
  refine Pc.seq (Pc.lift (lens_pc L hc) (fun m₀ _ => m₀) fun m₀ s ⟨h, hm⟩ => ⟨⟨h.env, h.sl⟩, hm⟩) ?_
  have hw : ∀ (m₀ : Mem) s', (∃ s, (TagIn Ctx St W SP R al ah tl th alo ahi tlo thi s ∧ s.mem = m₀) ∧
      LensOut Ctx St W SP 28 16 (val64 alo ahi) (val64 tlo thi) m₀ s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr) →
      WP isa (.block [.mov .eax (.mem (at_ .esi 16)), .mov .ecx (.mem (at_ .esi 20)), .mov .edx (.mem (at_ .esi 24)),
        .mov .ebx (.mem (at_ .esi 28)), .store (at_ .ebp o) .eax, .store (at_ .ebp (o + 4)) .ecx,
        .store (at_ .ebp (o + 8)) .edx, .store (at_ .ebp (o + 12)) .ebx, .mov .ebx (.reg .ebp),
        .alu .add .ebx (imm o), .mov .edi (imm 1), .mov .eax (slot ctxO), .mov .ecx (slot roundsO),
        .mov .edx (.reg .esi), .alu .add .ebp (imm scrO)]) s' (TagMid Ctx St W SP R o (val64 alo ahi) (val64 tlo thi) m₀) :=
    fun m₀ s' ⟨s, ⟨h, hm⟩, lo, _, _⟩ => by
      subst hm
      have hj : blockAt s'.mem (w64 St) = blockAt s.mem (w64 St) := by
        have := blockAt_frame lo.frame (p := w64 St + BitVec.ofNat 64 0) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
          · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
          · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
          · exact (L.stk_st (by decide)).symm
        simpa using this
      exact tagCopy_ok L ho lo.env (rounds_frame lo.frame (kept_tFrame L) h.rounds) lo.out hj
        (ciph_frame lo.frame (ctx_tFrame' L) h.rounds.2) (t_tagFrame lo.frame)
  have hr : ∀ (m₀ m₁ : Mem) s₁ s₂, (∃ s, (TagIn Ctx St W SP R al ah tl th alo ahi tlo thi s ∧ s.mem = m₀) ∧
      LensOut Ctx St W SP 28 16 (val64 alo ahi) (val64 tlo thi) m₀ s₁ ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr) →
      (∃ s, (TagIn Ctx St W SP R al ah tl th alo ahi tlo thi s ∧ s.mem = m₁) ∧
      LensOut Ctx St W SP 28 16 (val64 alo ahi) (val64 tlo thi) m₁ s₂ ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr) →
      ∀ r ∈ [Reg.esi, .ebp], s₁.gpr r = s₂.gpr r := fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.env.esi, h₂.env.esi]
    · rw [h₁.env.ebp, h₂.env.ebp]
  refine Pc.seq (Q := TagMid Ctx St W SP R o (val64 alo ahi) (val64 tlo thi)) ?_ ?_
  · rcases ho with rfl | rfl
    · exact Pc.taint [.esi, .ebp] hw hr (by taint_decide)
    · exact Pc.taint [.esi, .ebp] hw hr (by taint_decide)
  refine Pc.mono (Pc.of (I := CtrReady Ctx St W SP R St (W + BitVec.ofNat 32 o) 1) (fun _ h => ctrW_ok L rfl h)
    (ctrW_ct L rfl) _ fun _ _ h => h.ready) (fun _ _ h => h) fun m₀ s' ⟨s, h, g⟩ => ?_
  have eW := L.aW (o := o) (by omega)
  have eS : w64 St = w64 St := rfl
  have go := g.out
  rw [eW, blocksAt_one, blocksAt_one, h.ciph] at go
  have hb := congrArg (fun l => List.getD l 0 0) go
  simp only [List.getD_cons_zero] at hb
  rw [Proof.Gcm.ctr32_getD _ _ _ (by simp)] at hb
  simp only [List.getD_cons_zero, Nat.repeat] at hb
  have gf := g.frame
  rw [eW] at gf
  refine ⟨g.env, g.rounds, by rw [bytesAt_toBytes, hb, h.acc, h.j], h.frame.trans (gf.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨below SP 28, by simp, fun _ h => h⟩

end

end VG.Proof.AesGcm.X86
