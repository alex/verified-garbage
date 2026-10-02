import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Squeeze

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4_avx2`, correctness

Untrusted: everything here is checked by Lean. The pieces, in order: the
prologue, the round constants and the padded seeds (`M4Absorb.lean`), five
squeezes (`M4Squeeze.lean`), which leave the first 680 bytes of SHAKE256 of
each seed in its buffer, the branch on `γ₁`, the four unpackings, each the
loop of `vg_mldsa_expand_mask_poly` (`emBody_ok`) on the output of a seed
(`unpack_ok`), and the epilogue.
-/

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Impl.MlKem.X86_64.Sample4 (oRc oBuf)
open VG.Impl.MlDsa.X86_64.Sample (emBody)
open VG.Proof.MlKem.X86_64
open VG.Proof.MlDsa.X86_64.Sample (GPre emBody_ok emOk emV gOf)
open VG.Proof.MlDsa.Sample (emC emC_eq expandMask_getElem polyIs_of_coeffAt)
open VG.Spec.MlDsa (H coeffAt)
open VG.Proof.MlDsa.Sample (coeffAddr)
open VG.Proof.Sha3.X86_64.X4 (la)

/-- The first 640 bytes of SHAKE256 of seed `k`. -/
abbrev X (σ : State) (k : Nat) : List Byte := H (B σ k) 640

/-- After the squeezes, and the unpackings of the first `K` seeds, `c` bits a coefficient. -/
structure UI (σ : State) (c K : Nat) (s : State) : Prop where
  env : Env σ s
  buf : ∀ k < 4, ∀ p < 680, s.mem (at' σ (oBuf + 680 * k + p)) = hByte (B σ k) p
  st : ∀ k < K, ∀ i < 256, coeffAt s.mem (poly4 (aP σ) k) i = emV (X σ k) c i

/-- During the unpacking of seed `K`: `g` groups of four. -/
structure EI (σ : State) (c K g : Nat) (s : State) : Prop where
  ui : UI σ c K s
  rsi : s.gpr .rsi = at' σ (oBuf + 680 * K) + BitVec.ofNat 64 (c / 2 * g)
  rdi : s.gpr .rdi = poly4 (aP σ) K + BitVec.ofNat 64 (16 * g)
  cur : ∀ i < 4 * g, coeffAt s.mem (poly4 (aP σ) K) i = emV (X σ K) c i

section
variable {σ : State} (hp : Pre σ)
include hp

/-- The prologue, the round constants and the padded seeds. -/
theorem start_ok : WP isa (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4)) σ (SqInv σ 0) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pro_ok hp) fun s₁ h₁ => WP.mono (rc_ok hp h₁) fun s₂ h₂ => ?_
  have he₂ : Env σ s₂ := Env.low h₁ (rs := [⟨at' σ oRc, 768⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by simp only [oRc, oSave]; omega))
    h₂.frame h₂.keep.2.1 h₂.keep.2.2 fun r hr => h₂.keep.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.mono (absorb_ok hp (m₁ := s₂.mem) ⟨he₂, Frame.refl _ _⟩)
    fun s₃ ⟨a₃, b₃⟩ => ⟨a₃.env, fun r hr k hk => ?_, lanes_A0 b₃, fun _ _ p hp' => absurd hp' (by omega)⟩
  rw [a₃.frame.readW (Region.contains_self _ _) (by
    simpa using Offset.disjoint_base (scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega) (by omega))
    (by decide)]
  exact h₂.rc r hr k hk

/-- `Env` after writes to polynomial `K`. -/
theorem Env.poly {K : Nat} (hK : K < 4) {s s' : State} (he : Env σ s)
    (hf : Frame [⟨poly4 (aP σ) K, 1024⟩] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp, .r15], s'.gpr r = s.gpr r) : Env σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .r14 (by simp), he.r14], by rw [hg .rsp (by simp), he.rsp],
    by rw [hg .r15 (by simp), he.r15], fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using ((hp.a_scr.sub_left (sub_poly hK)).sub_right (sub_scr (σ := σ) (a := oSave + 8 * i) (n := 8)
          (by simp only [oSave]; omega))).symm) (by decide)]
    exact he.saved i hi
  · exact he.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨aR σ, by simp, sub_poly hK⟩)

/-- The facts a group of the unpacking of seed `K` needs. -/
theorem gpre {c K g : Nat} (hK : K < 4) (hg : g < 64) {s : State} (h : EI σ c K g s) :
    GPre c (X σ K) (at' σ (oBuf + 680 * K)) (poly4 (aP σ) K) g s := by
  refine ⟨h.rsi, h.rdi, hg, fun j hj => ?_, fun j hj => ?_, fun i hi => ?_, fun j hj hc => ?_⟩
  · rw [at', Offset.add_add, ← at', h.ui.buf K hK j (by omega)]; exact (H_getD _ hj).symm
  · rw [at', Offset.add_add, ← at']
    exact in_scr' hp h.ui.env.rd h.ui.env.wr (by simp only [oBuf]; omega)
  · rw [h.ui.env.wr, hp.wr]
    refine ⟨aR σ, by simp, ?_⟩
    rw [coeffAddr, poly4, Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega)
  · rw [at', Offset.add_add] at hc
    exact (hp.a_scr.sub_left (sub_poly hK)) _ hc
      (Offset.contains_base _ (by simp only [oBuf]; omega) (by simp only [oBuf]; omega))

/-- An iteration of the unpacking of seed `K`. -/
theorem ei_step {c K g : Nat} (hc : emOk c) (hK : K < 4) (hg : g < 64) {s : State} (h : EI σ c K g s) :
    WP isa (.block (emBody c)) s fun s' => EI σ c K (g + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  refine WP.mono (emBody_ok hc (gpre hp hK hg h)) fun s' ⟨hk, hf, hst, hsame, hsi, hdi, hcx, hz⟩ => ?_
  refine ⟨⟨⟨Env.poly hp hK h.ui.env hf hk.2.1 hk.2.2 fun r hr => hk.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), fun k hk' p hp' => ?_, fun k hk' i hi => ?_⟩,
    hsi, hdi, fun i hi => ?_⟩, hcx, hz⟩
  · rw [buf_frame (by simpa using ((hp.a_scr.sub_left (sub_poly hK)).sub_right (sub_scr (σ := σ) (a := oBuf)
        (n := 2720) (by simp only [oBuf]; omega))).symm) hf hk' hp']
    exact h.ui.buf k hk' p hp'
  · rw [show coeffAt s'.mem (poly4 (aP σ) k) i = coeffAt s.mem (poly4 (aP σ) k) i from
      hf.readW (VG.Proof.MlDsa.Sample.coeff_contains _ hi) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have hd := Offset.disjoint (aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega)
          (by omega) (by omega)
        simpa [poly4] using hd) (by decide)]
    exact h.ui.st k hk' i hi
  · by_cases hlo : i < 4 * g
    · rw [hsame i (by omega) (.inl hlo)]; exact h.cur i hlo
    · have := hst (i - 4 * g) (by omega)
      rwa [show 4 * g + (i - 4 * g) = i by omega] at this

/-- The unpacking of seed `K`. -/
theorem unpack_ok {c K : Nat} (hc : emOk c) (hK : K < 4) {s : State} (h : UI σ c K s) :
    WP isa (unpack c K) s (UI σ c (K + 1)) := by
  unfold unpack
  refine WP.seq (WP.mono (WP.keep [.rsi, .rdi, .rcx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = at' σ (oBuf + 680 * K) ∧ s'.gpr .rdi = poly4 (aP σ) K ∧ s'.gpr .rcx = BitVec.ofNat 64 64)
    (by xrun [h.env.rbx, h.env.r13, sx_ofNat (show oBuf + 680 * K < 2 ^ 31 by simp only [oBuf]; omega),
      sx_ofNat (show 1024 * K < 2 ^ 31 by omega)]) (by rfl)) fun s1 ⟨⟨hm1, hsi1, hdi1, hcx1⟩, k1⟩ => ?_)
  have he1 : Env σ s1 := Env.low h.env (rs := []) (by simp) (by rw [hm1]; exact Frame.refl _ _) k1.2.1 k1.2.2
    fun r hr => k1.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine wp_countdown (N := 64) (by decide) (by decide) (EI σ c K) (fun g hg s hI _ =>
    WP.mono (ei_step hp hc hK hg hI) fun s' ⟨hI', hc', hz⟩ => ⟨hI', hc', hz⟩) (fun s' hI =>
      ⟨hI.ui.env, hI.ui.buf, fun k hk i hi => ?_⟩)
    ⟨⟨he1, fun k hk p hp' => by rw [hm1]; exact h.buf k hk p hp', fun k hk i hi => by rw [hm1]; exact h.st k hk i hi⟩,
      by rw [hsi1]; simp, by rw [hdi1]; simp, fun i hi => absurd hi (by omega)⟩ hcx1
  by_cases e : k = K
  · subst e; exact hI.cur i (by omega)
  · exact hI.ui.st k (by omega) i hi

/-- The four unpackings. -/
theorem unpack4_ok {c : Nat} (hc : emOk c) {s : State} (h : UI σ c 0 s) : WP isa (unpack4 c) s (UI σ c 4) :=
  WP.seq (WP.mono (unpack_ok hp hc (by decide) h) fun _ h₁ => WP.seq (WP.mono (unpack_ok hp hc (by decide) h₁)
    fun _ h₂ => WP.seq (WP.mono (unpack_ok hp hc (by decide) h₂) fun _ h₃ => unpack_ok hp hc (by decide) h₃)))

omit hp in
theorem sx17 : BitVec.signExtend 64 (0x20000 : BitVec 32) = BitVec.ofNat 64 0x20000 := by decide

/-- The branch on `γ₁`, and the unpackings for it. -/
theorem sel_ok {s : State} (h : SqInv σ 5 s) {Q : State → Prop} (kont : ∀ s', UI σ (emC (gOf σ)) 4 s' →
    WP isa (.block epi) s' Q) :
    WP isa (.seq (.block [.vop .vzeroupper, .alu32 .cmp .r14 (.imm 0x20000)])
      (.seq (.ite .e (unpack4 18) (unpack4 20)) (.block epi))) s Q := by
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = s.gpr .r14 ∧
      s'.zf = some (BitVec.setWidth 32 (s.gpr .r14) - 0x20000 == 0)) (by xrun; exact ⟨rfl, rfl, rfl⟩) (by decide))
    fun s1 ⟨⟨hm1, h14, hz1⟩, k1'⟩ => ?_)
  have k1 : Keep [] s s1 := ⟨fun r _ => by
    by_cases e : r = .r14
    · subst e; exact h14
    · exact k1'.gpr (by simp [e]), k1'.2⟩
  have hr14 : BitVec.setWidth 32 (s.gpr .r14) = BitVec.ofNat 32 (gOf σ) := by
    rw [h.env.r14, gOf, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hU : ∀ c, UI σ c 0 s1 := fun c => ⟨Env.low h.env (rs := []) (by simp) (by rw [hm1]; exact Frame.refl _ _)
      k1.2.1 k1.2.2 fun r _ => k1.gpr (List.not_mem_nil),
    fun k hk p hp' => by rw [hm1]; exact h.buf k hk p (by omega), fun _ hk => absurd hk (by omega)⟩
  refine WP.seq (WP.mono (?_ : WP isa (.ite .e (unpack4 18) (unpack4 20)) s1 (UI σ (emC (gOf σ)) 4)) kont)
  rcases hp.gamma with he | he
  · refine WP.ite true (by show s1.zf = _; rw [hz1, hr14, he]; rfl) (fun _ => ?_) (fun hb => absurd hb (by decide))
    rw [show emC (gOf σ) = 18 by rw [he]; rfl]; exact unpack4_ok hp (.inl rfl) (hU 18)
  · refine WP.ite false (by show s1.zf = _; rw [hz1, hr14, he]; rfl) (fun hb => absurd hb (by decide)) (fun _ => ?_)
    rw [show emC (gOf σ) = 20 by rw [he]; rfl]; exact unpack4_ok hp (.inr rfl) (hU 20)

omit hp in
theorem epi_eq : epi = [.mov .r14 (.mem (at_ .rbx 5120)), .mov .r13 (.mem (at_ .rbx 5112)),
    .mov .r12 (.mem (at_ .rbx 5104)), .mov .rbp (.mem (at_ .rbx 5096)), .mov .rbx (.mem (at_ .rbx 5088))] := rfl

/-- The postcondition, and the callee-saved registers restored. -/
theorem end_ok {s : State} (h : UI σ (emC (gOf σ)) 4 s) :
    WP isa (.block epi) s fun s' => em4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega)
  rw [epi_eq]
  refine WP.mono (WP.keep [.r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .r14 = s.mem.readW (at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  obtain ⟨_, _, hγ⟩ := emC_eq hp.gamma
  refine ⟨fun K hK => polyIs_of_coeffAt fun i hi => ?_, fun r hr => ?_, ?_⟩
  · rw [expandMask_getElem _ hp.gamma hi, hm, h.st K hK i (by omega)]
    simp only [emV]
    congr 3
    rw [← hγ]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega)⟩)
      (by decide)

end

theorem correct (σ : State) (hs : em4K.pre σ) :
    ∃ t s', Exec isa expandMask4Avx2 σ t s' ∧ abiPreserved σ s' ∧ em4K.post σ s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (start_ok hp) fun _ h₀ =>
    WP.seq (WP.mono (sq_ok hp (by decide) h₀) fun _ h₁ => WP.seq (WP.mono (sq_ok hp (by decide) h₁) fun _ h₂ =>
      WP.seq (WP.mono (sq_ok hp (by decide) h₂) fun _ h₃ => WP.seq (WP.mono (sq_ok hp (by decide) h₃) fun _ h₄ =>
        WP.seq (WP.mono (sq_ok hp (by decide) h₄) fun _ h₅ => sel_ok hp h₅ fun _ hu => end_ok hp hu))))))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Mask4
