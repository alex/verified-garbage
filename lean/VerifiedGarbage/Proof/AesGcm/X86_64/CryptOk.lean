import VerifiedGarbage.Proof.AesGcm.X86_64.Crypt

/-!
# AES-GCM on x86-64: `crypt`

Untrusted: everything here is checked by Lean (see `Crypt.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

/-- `[D, D + j)` and `[D + j, D + n)` are apart. -/
theorem split_disj {D : Addr} {j n : Nat} (hj : j ≤ n) (hn : n < 2 ^ 64) :
    (⟨D, j⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 j, n - j⟩ := by
  have := Offset.disjoint D (d := 0) (n := j) (e := j) (k := n - j) (.inl (by omega)) (by omega) (by omega)
  simpa using this

/-- The bytes done so far and the next ones. -/
theorem done_append {m m₀ : Mem} {ciph : Block → Block} {icb : Block} {P : Nat} {D : Addr} {j l : Nat}
    (h₁ : bytesAt m D j = xorKs ciph icb P (bytesAt m₀ D j))
    (h₂ : bytesAt m (D + BitVec.ofNat 64 j) l = xorKs ciph icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) l)) :
    bytesAt m D (j + l) = xorKs ciph icb P (bytesAt m₀ D (j + l)) := by
  rw [bytesAt_add, bytesAt_add, Proof.Gcm.xorKs_append, h₁, h₂, length_bytesAt]

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

omit L in
/-- The rest of the keystream block. -/
theorem cryptHead_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {s : State}
    (h : CrIn Ctx St W SP R icb P D n s) (hn : n ≠ 0) (hP : P % 16 ≠ 0) :
    WP isa cryptHead s (fun s' => ∃ j, CrMid Ctx St W SP R icb P D n s.mem j s') := by
  have hlt : P % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.ok.lt
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.rbx h.rbp (by omega) hn') fun s₁ ⟨hcx, hg, hm, hrd, hwr⟩ => ?_)
  generalize hk : min (16 - P % 16) n = k at hcx
  have hk1 : 1 ≤ k := by omega
  have hk16 : P % 16 + k ≤ 16 := by omega
  have hkn : k ≤ n := by omega
  obtain ⟨s₂, run₂, hdi, hsi, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rdi (.reg .r12),
      .mov .rsi (.reg .r14), .alu .add .rsi (.reg .rbx), .alu .add .rsi (imm 64)] s₁ = some s₂ ∧
      s₂.gpr .rdi = D ∧ s₂.gpr .rsi = St + BitVec.ofNat 64 (64 + P % 16) ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg _ (by decide : Reg.r12 ≠ .rcx), h.r12]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        hg _ (by decide : Reg.r14 ≠ .rcx), hg _ (by decide : Reg.rbx ≠ .rcx), he.r14, h.rbx,
        add_ofNat_assoc, Nat.add_comm]
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have lp : LoopPre s₂ (St + BitVec.ofNat 64 (64 + P % 16)) D k := by
    refine ⟨hsi, hdi, by rw [hg₂ _ (by decide) (by decide), hcx], hk1, by omega, ?_, ?_, ?_⟩
    · rw [hrd₂, hwr₂, hrd, hwr]; exact covers_left (he.perm.stC (by omega))
    · rw [hwr₂, hwr]; exact (h.data.take hkn).wr
    · exact ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by omega))).symm
  refine WP.seq (WP.mono (xorLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_)
  rw [hm₂, hm] at hm₃
  rw [hrd₂, hrd] at hrd₃
  rw [hwr₂, hwr] at hwr₃
  have hreg : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₃.gpr r = s.gpr r :=
    fun r a b c d e f => by rw [hg₃ r a b c, hg₂ r d e, hg r f]
  have h3rcx : s₃.gpr .rcx = BitVec.ofNat 64 k := by
    rw [hg₃ _ (by decide) (by decide) (by decide), hg₂ _ (by decide) (by decide), hcx]
  have hxl := length_xorBytes s.mem D (St + BitVec.ofNat 64 (64 + P % 16)) k
  have fw : Frame [⟨D, k⟩] s.mem s₃.mem := by rw [hm₃]; exact writeBytes_frame' _ hxl
  have hdisjst : ∀ r ∈ [(⟨D, k⟩ : Region)], (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨St + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨((h.data.take hkn).ok.st.sub_right (Lay.stSub (by decide))).symm,
      ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  obtain ⟨s₄, run₄, h12, hbp, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
      [.alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx)] s₃ = some s₄ ∧
      s₄.gpr .r12 = D + BitVec.ofNat 64 k ∧ s₄.gpr .rbp = BitVec.ofNat 64 (n - k) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    have e12 := hreg .r12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have ebp := hreg .rbp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e12, h3rcx, h.r12]
    · simp [gpr_setReg, ebp, h3rcx, h.rbp, ofNat_sub hkn hn']
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
    all_goals rfl
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have he₄ : Env Ctx St W SP s₄ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [hg₄ _ (by decide) (by decide),
        hreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    (hrd₄.trans hrd₃) (hwr₄.trans hwr₃)
  have hc₄ : ciphOf s₄.mem Ctx R = ciphOf s.mem Ctx R := by
    rw [hm₄]; exact ciph_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.data.take hkn).ctx) h.rounds.2
  refine ⟨k, he₄, hkn, h12, hbp, h.data.of_eq (hrd₄.trans hrd₃) (hwr₄.trans hwr₃), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm₄]; exact rounds_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((h.data.take hkn).ok.w.sub_right (Lay.wSub (by decide))).symm) h.rounds
  · intro hc₀
    rw [hm₄]
    refine (hc₀.head hP hk16).congr (blockAt_frame fw fun r hr => (hdisjst r hr).1)
      (blockAt_frame fw fun r hr => (hdisjst r hr).2)
  · intro hc₀
    have e := bytesAt_writeBytes_self s.mem D (xorBytes s.mem D (St + BitVec.ofNat 64 (64 + P % 16)) k)
      (by rw [hxl]; omega)
    rw [hxl] at e
    rw [hm₄, hm₃, e, xorBytes]
    have := Proof.Gcm.ctr_head hc₀ hP (d := bytesAt s.mem D k) (by rw [length_bytesAt]; exact hk16)
    rw [length_bytesAt, add_ofNat_assoc] at this
    exact this
  · rw [hm₄]
    exact bytesAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (split_disj hkn hn').symm) (by omega)
  · by_cases hkk : k = n
    · left; omega
    · right; omega
  · rw [hm₄]; exact fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hkn⟩

omit L in
/-- The arguments of a call of `vg_aes_ctr32`, from `W + 176` and the state. -/
theorem ctrArgs_ok {R : Nat} {s : State} (he : Env Ctx St W SP s) (hR : RoundsAt s.mem W R) :
    ∃ s', runBlock isa ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r14 48 ++
        ptr .r9 .r15 scrO) s = some s' ∧
      s'.gpr .rdi = Ctx ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧ s'.gpr .rdx = St + BitVec.ofNat 64 48 ∧
      s'.gpr .r9 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h13 := he.r13; have h14 := he.r14; have h15 := he.r15
  have r₁ := he.perm.wR (show 176 + 8 ≤ 2560 by decide)
  refine ⟨_, by xrun [h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h13]
  · simp [gpr_setReg, hR.1]
  · simp [gpr_setReg, h14]
  · simp [gpr_setReg, h15]
  · intro r a b c d; simp [gpr_setReg, a, b, c, d]
  all_goals rfl

omit L in
theorem CrMid.data_eq {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid Ctx St W SP R icb P D n m₀ j s) : bytesAt s.mem D n =
      bytesAt s.mem D j ++ bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) := by
  rw [← bytesAt_add, Nat.add_sub_cancel' h.le]

/-- Whole blocks. -/
theorem cryptWhole_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid Ctx St W SP R icb P D n m₀ j s) (hc : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R) :
    WP isa (cryptWhole v.callees) s (fun s' => ∃ j', CrMid Ctx St W SP R icb P D n m₀ j' s' ∧ n - j' < 16) := by
  have hn' := h.data.ok.lt
  have he := h.env
  generalize hnb : (n - j) / 16 = nb
  have h16 : 16 * nb ≤ n - j := by omega
  obtain ⟨s₁, run₁, hcx, h8, h12, hbp, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      (splitWhole .rcx .r8 ++ [.alu .test .r8 (.reg .r8)]) s = some s₁ ∧
      s₁.gpr .rcx = D + BitVec.ofNat 64 j ∧ s₁.gpr .r8 = BitVec.ofNat 64 nb ∧
      s₁.gpr .r12 = D + BitVec.ofNat 64 (j + 16 * nb) ∧ s₁.gpr .rbp = BitVec.ofNat 64 (n - (j + 16 * nb)) ∧
      s₁.zf = some (decide (nb = 0)) ∧
      (∀ r, r ≠ .rcx → r ≠ .r8 → r ≠ .rax → r ≠ .r12 → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have hand := and15 (BitVec.ofNat 64 (n - j))
    rw [toNat_ofNat_of_lt (by omega), imm_eq (by decide)] at hand
    have hsub : BitVec.ofNat 64 (n - j) - BitVec.ofNat 64 ((n - j) % 16) = BitVec.ofNat 64 (16 * nb) := by
      rw [ofNat_sub (Nat.mod_le _ _) (by omega)]; congr 1; omega
    refine ⟨_, by simp only [splitWhole]; xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_setFlags, h.r12]
    · simp [gpr_setReg, gpr_setFlags, h.rbp, shr4 _ (show n - j < 2 ^ 64 by omega), hnb]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h.r12, h.rbp,
        hand, hsub, BitVec.add_assoc, ofNat_add_ofNat]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h.rbp, hand]
      congr 1
      omega
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq,
        h.rbp, shr4 _ (show n - j < 2 ^ 64 by omega), hnb]
      rw [and_self_beq (by omega)]
    · intro r h₁ h₂ h₃ h₄ h₅; simp [gpr_setReg, gpr_setFlags, h₁, h₂, h₃, h₄, h₅]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    hrd₁ hwr₁
  have hd₁ : DataW Ctx St W SP s₁ D n := h.data.of_eq hrd₁ hwr₁
  refine WP.ite (decide (nb = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, ⟨he₁, h.le, by rw [h12]; rfl, by rw [hbp]; rfl, hd₁, by rw [hm₁]; exact h.rounds,
      fun hc₀ => by rw [hm₁]; exact h.ctr hc₀, fun hc₀ => by rw [hm₁]; exact h.done hc₀, by rw [hm₁]; exact h.rest, h.whole,
      by rw [hm₁]; exact h.frame⟩, by omega⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hw : (P + j) % 16 = 0 := h.whole.resolve_left (by omega)
    have hdj := (h.data.drop h.le).take (k := 16 * nb) h16
    obtain ⟨s₂, run₂, hdi, hsi, hdx, h9, hg₂, hm₂, hrd₂, hwr₂⟩ := ctrArgs_ok he₁ (by rw [hm₁]; exact h.rounds)
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
      hrd₂ hwr₂
    have hk := he₂.rsp
    have hcall : CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (W + BitVec.ofNat 64 512) R nb := by
      refine ⟨hdi, hsi, hdx, by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), hcx],
        by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h8], h9, h.rounds.2, hdj.ok.wrap,
        (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
        hdj.ctx.sub_left (Region.sub_prefix (by decide)),
        L.cw'.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Lay.wSub (by decide)),
        (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm, L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
        hdj.ok.w.sub_right (Lay.wSub (by decide)), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
      · rw [hk]; exact L.stk_st (by decide)
      · rw [hk]; exact hdj.ok.stk
      · rw [hk]; exact L.stk_w (by decide)
      · refine covers_cons ?_ (covers_cons (covers_left (he₂.perm.stC (by decide))) (covers_cons ?_
          (covers_left (he₂.perm.wC (by decide)))))
        · exact fun a m' ⟨r, hr, hc'⟩ => by
            simp only [List.mem_singleton] at hr; subst hr
            exact he₂.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
        · rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact covers_left hdj.wr
      · refine covers_cons (he₂.perm.stC (by decide)) (covers_cons ?_ (he₂.perm.wC (by decide)))
        rw [hwr₂, hwr₁]; exact hdj.wr
    refine WP.mono (ctr_call v.ctr hcall) fun s₃ g => ?_
    have gout := g.out; have gctr := g.ctr; have gframe := g.frame
    rw [hm₂, hm₁] at gout gctr gframe
    have hcw := fun hc₀ => Proof.Gcm.ctr_whole (h.ctr hc₀) hw (m' := s₃.mem) (dp := D + BitVec.ofNat 64 j)
      (nb := nb) (by rw [gout, ← hc]) gctr
    refine ⟨j + 16 * nb, ⟨he₂.of_saved g.saved g.rd g.wr, by omega, ?_, ?_, hd₁.of_eq (g.rd.trans hrd₂) (g.wr.trans hwr₂),
      ?_, ?_, ?_, ?_, .inr (by omega), ?_⟩, by omega⟩
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h12]
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), hbp]
    · refine rounds_frame gframe (fun r hr => ?_) h.rounds
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact (hdj.ok.w.sub_right (Lay.wSub (by decide))).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rw [hk]; exact (L.stk_w (by decide)).symm
    · intro hc₀; rw [← Nat.add_assoc]; exact (hcw hc₀).2
    · -- The bytes done.
      intro hc₀
      have hj16 : bytesAt s₃.mem (D + BitVec.ofNat 64 j) (16 * nb) =
          xorKs (ciphOf m₀ Ctx R) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * nb)) := by
        rw [(hcw hc₀).1]
        congr 1
        have e := congrArg (List.take (16 * nb)) h.rest
        rwa [show n - j = 16 * nb + (n - j - 16 * nb) by omega, bytesAt_add, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _), List.take_left' (length_bytesAt _ _ _)] at e
      have hjd : bytesAt s₃.mem D j = bytesAt s.mem D j := bytesAt_frame gframe (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
        · exact split_disj (D := D) (j := j) (n := n) h.le hn' |>.sub_right (Region.sub_prefix (by omega))
        · exact (h.data.take h.le).ok.w.sub_right (Lay.wSub (by decide))
        · rw [hk]; exact (h.data.take h.le).ok.stk.symm) (by omega)
      exact done_append (hjd.trans (h.done hc₀)) hj16
    · -- The bytes left.
      have hdis : ∀ r ∈ [⟨St + BitVec.ofNat 64 48, 16⟩, ⟨D + BitVec.ofNat 64 j, 16 * nb⟩,
          ⟨W + BitVec.ofNat 64 512, 2048⟩, below (s₂.gpr .rsp) 8],
          (⟨D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ : Region).Disjoint r := by
        have hrest := (h.data.drop (k := j + 16 * nb) (by omega))
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hrest.ok.st.sub_right (Lay.stSub (by decide))
        · rw [← add_ofNat_assoc]
          have := split_disj (D := D + BitVec.ofNat 64 j) (j := 16 * nb) (n := n - j) h16 (by omega)
          rw [show n - j - 16 * nb = n - (j + 16 * nb) by omega] at this
          exact this.symm
        · exact hrest.ok.w.sub_right (Lay.wSub (by decide))
        · rw [hk]; exact hrest.ok.stk.symm
      rw [bytesAt_frame gframe hdis (by omega)]
      have e := congrArg (List.drop (16 * nb)) h.rest
      have e₂ : ∀ m : Mem, (bytesAt m (D + BitVec.ofNat 64 j) (n - j)).drop (16 * nb) =
          bytesAt m (D + BitVec.ofNat 64 (j + 16 * nb)) (n - (j + 16 * nb)) := fun m => by
        rw [show n - j = 16 * nb + (n - (j + 16 * nb)) by omega, bytesAt_add,
          List.drop_left' (length_bytesAt _ _ _), add_ofNat_assoc]
      simpa only [e₂] using e
    · refine h.frame.trans (gframe.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., (Offset.sub_base D (by omega))⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
      · rw [hk]; exact ⟨_, by simp, fun _ h => h⟩

/-- The last bytes, with a new keystream block. -/
theorem cryptTail_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid Ctx St W SP R icb P D n m₀ j s) (hj : n - j < 16) (hc : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R) :
    WP isa (cryptTail v.callees) s (CrOut Ctx St W SP R icb P D n m₀) := by
  have hn' := h.data.ok.lt
  have he := h.env
  obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp h.rbp (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (n - j = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega
    subst h0
    exact WP.block_nil ⟨he₁, by rw [hm₁]; exact h.rounds, fun hc₀ => by rw [hm₁]; exact h.ctr hc₀,
      fun hc₀ => by rw [hm₁]; exact h.done hc₀,
      by rw [hm₁]; exact h.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    have hw : (P + j) % 16 = 0 := h.whole.resolve_left h0
    have hdj := h.data.drop h.le
    have h13 := he₁.r13; have h14 := he₁.r14; have h15 := he₁.r15
    have r₁ := he₁.perm.wR (show 176 + 8 ≤ 2560 by decide)
    have w₁ := he₁.perm.stW (show 64 + 8 ≤ 80 by decide)
    have w₂ := he₁.perm.stW (show 72 + 8 ≤ 80 by decide)
    obtain ⟨s₂, run₂, hm₂, hdi, hsi, hdx, hcx, h8, h9, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        ([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
          .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] ++ ptr .rdx .r14 48 ++
          ptr .rcx .r14 64 ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO) s₁ = some s₂ ∧
        s₂.mem = (s.mem.writeW (St + BitVec.ofNat 64 64) (0 : BitVec 64)).writeW
          (St + BitVec.ofNat 64 64 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
        s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = St + BitVec.ofNat 64 48 ∧
        s₂.gpr .rcx = St + BitVec.ofNat 64 64 ∧ s₂.gpr .r8 = BitVec.ofNat 64 1 ∧
        s₂.gpr .r9 = W + BitVec.ofNat 64 512 ∧
        (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → s₂.gpr r = s.gpr r) ∧
        s₂.rd = s.rd ∧ s₂.wr = s.wr := by
      have hR := h.rounds.1
      rw [← hm₁] at hR
      have hsep : ∀ (m : Mem) (x y : BitVec 64), ((m.writeW (St + BitVec.ofNat 64 64) x).writeW
          (St + BitVec.ofNat 64 72) y).readW (W + BitVec.ofNat 64 176) 64 = m.readW (W + BitVec.ofNat 64 176) 64 := by
        intro m x y
        rw [Mem.readW_writeW_sep (Region.Disjoint.sep (L.st_w (a := 72) (n := 8) (by decide)
            (.inr ⟨by decide, by decide⟩)).symm (Region.contains_self _ _) (Region.contains_self _ _)) (by decide),
          Mem.readW_writeW_sep (Region.Disjoint.sep (L.st_w (a := 64) (n := 8) (by decide)
            (.inr ⟨by decide, by decide⟩)).symm (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
      refine ⟨_, by xrun [h13, h14, h15, w₁, w₂, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [mem_setReg, mem_arithFlags, add_ofNat_assoc, hm₁]; rfl
      · simp [gpr_setReg, h13]
      · simp [gpr_setReg, hsep, hR]
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg]
      · simp [gpr_setReg, h15]
      · intro r a b c d e f g; simp [gpr_setReg, a, b, c, d, e, f, g, hg₁]
      · simp [rd_setReg, rd_arithFlags, hrd₁]
      · simp [wr_setReg, wr_arithFlags, hwr₁]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hrd₂ hwr₂
    have hk := he₂.rsp
    have fz : Frame [⟨St + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by rw [hm₂]; exact Cmac.frame_store2 _ _ _
    have hKS0 : blockAt s₂.mem (St + BitVec.ofNat 64 64) = 0 := by
      rw [blockAt, hm₂, zeroT_bytes]; decide
    have hCB : blockAt s₂.mem (St + BitVec.ofNat 64 48) = blockAt s.mem (St + BitVec.ofNat 64 48) :=
      blockAt_frame fz fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by decide)) (by decide) (by decide)
    have hc₂ : ciphOf s₂.mem Ctx R = ciphOf m₀ Ctx R := by
      rw [ciph_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.cs.sub_right (Lay.stSub (by decide))) h.rounds.2, hc]
    have hcall : CtrCall s₂ Ctx (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 512) R 1 := by
      refine ⟨hdi, hsi, hdx, hcx, h8, h9, h.rounds.2, by have := L.sw; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
        (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
        (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
        L.cw'.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Lay.wSub (by decide)),
        L.st_st (.inl (by decide)) (by decide) (by decide), L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
        L.st_w (by decide) (.inr ⟨by decide, by decide⟩), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
      · rw [hk]; exact L.stk_st (by decide)
      · rw [hk]; exact L.stk_st (by decide)
      · rw [hk]; exact L.stk_w (by decide)
      · refine covers_cons ?_ (covers_cons (covers_left (he₂.perm.stC (by decide))) (covers_cons
          (covers_left (he₂.perm.stC (by decide))) (covers_left (he₂.perm.wC (by decide)))))
        exact fun a m' ⟨r, hr, hc'⟩ => by
          simp only [List.mem_singleton] at hr; subst hr
          exact he₂.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
      · exact covers_cons (he₂.perm.stC (by decide)) (covers_cons (he₂.perm.stC (by decide))
          (he₂.perm.wC (by decide)))
    refine WP.seq (WP.mono (ctr_call v.ctr hcall) fun s₃ g => ?_)
    have gout := g.out; have gctr := g.ctr; have gframe := g.frame
    rw [blocksAt_one, blocksAt_one, hKS0, Cmac.ctr32_one, List.cons.injEq] at gout
    have hKS : blockAt s₃.mem (St + BitVec.ofNat 64 64) = ciphOf m₀ Ctx R (blockAt s.mem (St + BitVec.ofNat 64 48)) := by
      rw [gout.1, ← hc₂, hCB]
    have hCB₃ : blockAt s₃.mem (St + BitVec.ofNat 64 48) = Spec.Gcm.inc32 (blockAt s.mem (St + BitVec.ofNat 64 48)) := by
      rw [gctr, hCB]; rfl
    have he₃ : Env Ctx St W SP s₃ := he₂.of_saved g.saved g.rd g.wr
    obtain ⟨s₄, run₄, hdi₄, hsi₄, hcx₄, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
        ([.mov .rdi (.reg .r12)] ++ ptr .rsi .r14 64 ++ [.mov .rcx (.reg .rbp)]) s₃ = some s₄ ∧
        s₄.gpr .rdi = D + BitVec.ofNat 64 j ∧ s₄.gpr .rsi = St + BitVec.ofNat 64 64 ∧
        s₄.gpr .rcx = BitVec.ofNat 64 (n - j) ∧
        (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧
        s₄.wr = s₃.wr := by
      have e12 : s₃.gpr .r12 = D + BitVec.ofNat 64 j := by
        rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h.r12]
      have ebp : s₃.gpr .rbp = BitVec.ofNat 64 (n - j) := by
        rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h.rbp]
      refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, e12]
      · simp [gpr_setReg, he₃.r14]
      · simp [gpr_setReg, ebp]
      · intro r a b c; simp [gpr_setReg, a, b, c]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
    have lp : LoopPre s₄ (St + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 j) (n - j) := by
      refine ⟨hsi₄, hdi₄, hcx₄, by omega, by omega, ?_, ?_, ?_⟩
      · rw [hrd₄, hwr₄, g.rd, g.wr]; exact covers_left (he₂.perm.stC (by omega))
      · rw [hwr₄, g.wr, hwr₂]; exact hdj.wr
      · exact (hdj.ok.st.sub_right (Lay.stSub (by omega))).symm
    refine WP.mono (xorLoop_ok s₄ lp) fun s₅ ⟨hm₅, hg₅, hrd₅, hwr₅⟩ => ?_
    rw [hm₄] at hm₅
    have hxl := length_xorBytes s₃.mem (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 64) (n - j)
    have fw : Frame [⟨D + BitVec.ofNat 64 j, n - j⟩] s₃.mem s₅.mem := by rw [hm₅]; exact writeBytes_frame' _ hxl
    have hd₃ : bytesAt s₃.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
      rw [← h.rest, bytesAt_frame gframe (fun r hr => ?_) (by omega), bytesAt_frame fz (fun r hr => ?_) (by omega)]
      · simp only [List.mem_singleton] at hr; subst hr; exact hdj.ok.st.sub_right (Lay.stSub (by decide))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdj.ok.st.sub_right (Lay.stSub (by decide))
        · exact hdj.ok.st.sub_right (Lay.stSub (by decide))
        · exact hdj.ok.w.sub_right (Lay.wSub (by decide))
        · rw [hk]; exact hdj.ok.stk.symm
    have ht := fun hc₀ => Proof.Gcm.ctr_tail (h.ctr hc₀) hw (m₁ := s₃.mem) hKS (by rw [hCB₃]) (d := bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j))
      (by rw [length_bytesAt]; omega) (by rw [length_bytesAt]; omega)
    rw [length_bytesAt] at ht
    have dW : ∀ r ∈ [(⟨D + BitVec.ofNat 64 j, n - j⟩ : Region)], (⟨W + BitVec.ofNat 64 176, 8⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact (hdj.ok.w.sub_right (Lay.wSub (by decide))).symm
    have dS : ∀ r ∈ [(⟨D + BitVec.ofNat 64 j, n - j⟩ : Region)], ∀ k, k + 16 ≤ 80 →
        (⟨St + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint r := by
      intro r hr k hk; simp only [List.mem_singleton] at hr; subst hr
      exact (hdj.ok.st.sub_right (Lay.stSub hk)).symm
    have hrd₅' : s₅.rd = s.rd := by rw [hrd₅, hrd₄, g.rd, hrd₂]
    have hwr₅' : s₅.wr = s.wr := by rw [hwr₅, hwr₄, g.wr, hwr₂]
    refine ⟨he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [hg₅ _ (by decide) (by decide) (by decide), hg₄ _ (by decide) (by decide) (by decide)])
      (by rw [hrd₅, hrd₄]) (by rw [hwr₅, hwr₄]), ?_, ?_, ?_, ?_⟩
    · refine rounds_frame fw dW (rounds_frame gframe (fun r hr => ?_) (rounds_frame fz (fun r hr => ?_) h.rounds))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
        · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · rw [hk]; exact (L.stk_w (by decide)).symm
      · simp only [List.mem_singleton] at hr; subst hr
        exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · intro hc₀
      rw [show P + n = P + j + (n - j) by omega]
      exact (ht hc₀).2.congr (blockAt_frame fw fun r hr => dS r hr 48 (by decide))
        (blockAt_frame fw fun r hr => dS r hr 64 (by decide))
    · intro hc₀
      have hdone : bytesAt s₅.mem D j = bytesAt s.mem D j := by
        rw [bytesAt_frame fw (fun r hr => ?_) (by omega), bytesAt_frame gframe (fun r hr => ?_) (by omega),
          bytesAt_frame fz (fun r hr => ?_) (by omega)]
        · simp only [List.mem_singleton] at hr; subst hr
          exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
          · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
          · exact (h.data.take h.le).ok.w.sub_right (Lay.wSub (by decide))
          · rw [hk]; exact (h.data.take h.le).ok.stk.symm
        · simp only [List.mem_singleton] at hr; subst hr; exact split_disj (D := D) h.le hn'
      have hpiece : bytesAt s₅.mem (D + BitVec.ofNat 64 j) (n - j) =
          xorKs (ciphOf m₀ Ctx R) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)) := by
        have e := bytesAt_writeBytes_self s₃.mem (D + BitVec.ofNat 64 j)
          (xorBytes s₃.mem (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 64) (n - j)) (by rw [hxl]; omega)
        rw [hxl] at e
        rw [hm₅, e, xorBytes, hd₃, (ht hc₀).1]
      rw [show n = j + (n - j) by omega]
      exact done_append (hdone.trans (h.done hc₀)) hpiece
    · refine h.frame.trans (Frame.trans (Frame.trans (fz.sub fun r hr => ?_) (gframe.sub fun r hr => ?_))
        (fw.sub fun r hr => ?_))
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
        · rw [hk]; exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Offset.sub_base D (by omega)⟩

theorem CrMid.ciph {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid Ctx St W SP R icb P D n m₀ j s) : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R :=
  ciph_frame h.frame (ctx_crFrame L h.data) h.rounds.2

/-- `crypt`. -/
theorem crypt_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {s : State}
    (h : CrIn Ctx St W SP R icb P D n s) :
    WP isa (crypt v.callees) s (CrOut Ctx St W SP R icb P D n s.mem) := by
  have hn' := h.data.ok.lt
  have he := h.env
  obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp h.rbp hn'
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨he₁, by rw [hm₁]; exact h.rounds, fun hc₀ => by rw [hm₁]; exact hc₀,
      fun _ => by simp [bytesAt]; rfl, by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    have h₁ : CrIn Ctx St W SP R icb P D n s₁ := ⟨he₁, by rw [hg₁]; exact h.r12, by rw [hg₁]; exact h.rbp,
      by rw [hg₁]; exact h.rbx, h.data.of_eq hrd₁ hwr₁, by rw [hm₁]; exact h.rounds⟩
    obtain ⟨s₂, run₂, hzf₂, hg₂, hm₂, hrd₂, hwr₂⟩ := test_ok s₁ .rbx h₁.rbx
      (by have := Nat.mod_lt P (show 16 > 0 by decide); omega)
    have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r _ => by rw [hg₂]) hrd₂ hwr₂
    have h₂ : CrIn Ctx St W SP R icb P D n s₂ := ⟨he₂, by rw [hg₂]; exact h₁.r12, by rw [hg₂]; exact h₁.rbp,
      by rw [hg₂]; exact h₁.rbx, h₁.data.of_eq hrd₂ hwr₂, by rw [hm₂]; exact h₁.rounds⟩
    have hm₀ : s₂.mem = s.mem := hm₂.trans hm₁
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.seq (WP.mono (Q := fun s' => ∃ j, CrMid Ctx St W SP R icb P D n s.mem j s')
      (WP.ite (decide (P % 16 = 0)) (eval_e hzf₂) (fun ht => ?_) (fun hf => ?_)) fun s' hj => ?_)
    · have ho : P % 16 = 0 := by simpa using ht
      exact WP.block_nil ⟨0, he₂, by omega, by rw [h₂.r12]; simp, by rw [h₂.rbp, Nat.sub_zero], h₂.data,
        h₂.rounds, fun hc₀ => by rw [hm₀]; simpa using hc₀, fun _ => by simp [bytesAt]; rfl, by rw [hm₀],
        .inr (by omega), by rw [← hm₀]; exact Frame.refl _ _⟩
    · have := cryptHead_ok h₂ h0 (by simpa using hf)
      rw [hm₀] at this; exact this
    · obtain ⟨j, hj⟩ := hj
      refine WP.seq (WP.mono (cryptWhole_ok v L hj (hj.ciph L)) fun s'' ⟨j', hj', hlt⟩ => ?_)
      exact cryptTail_ok v L hj' hlt (hj'.ciph L)

end

end VG.Proof.AesGcm.X86_64
