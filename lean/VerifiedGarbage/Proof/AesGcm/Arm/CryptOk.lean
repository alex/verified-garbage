import VerifiedGarbage.Proof.AesGcm.Arm.Crypt

/-!
# AES-GCM on ARMv7: `crypt`

Untrusted: everything here is checked by Lean (see `Crypt.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

/-- The rest of the keystream block. -/
theorem cryptHead_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s : State}
    (h : CrIn c st w sp k7 k8 R icb P D n s) (hn : n ≠ 0) (hP : P % 16 ≠ 0) :
    WP isa cryptHead s (fun s' => ∃ j, CrMid c st w sp k7 k8 R icb P D n s.mem j s') := by
  have hlt : P % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.ok.lt32
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.r6 h.r5 (by omega) hn') fun s₁ ⟨h3, hg, hk⟩ => ?_)
  obtain ⟨k, hk'⟩ : ∃ k, min (16 - P % 16) n = k := ⟨_, rfl⟩
  rw [hk'] at h3
  have hk1 : 1 ≤ k := by omega
  have hk16 : P % 16 + k ≤ 16 := by omega
  have hkn : k ≤ n := by omega
  obtain ⟨s₂, run₂, h1, h2, h4, h5, h3', hg₂, hk₂⟩ : ∃ s₂, runBlock isa [addI .r1 .r10 64,
      .dp .add .r1 .r1 (.reg .r6), .mov .r2 (.reg .r4), .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)]
      s₁ = some s₂ ∧
      s₂.gpr .r1 = st + BitVec.ofNat 32 (64 + P % 16) ∧ s₂.gpr .r2 = D ∧
      s₂.gpr .r4 = D + BitVec.ofNat 32 k ∧ s₂.gpr .r5 = BitVec.ofNat 32 (n - k) ∧
      s₂.gpr .r3 = BitVec.ofNat 32 k ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → r ≠ .r5 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    have e10 := hg .r10 (by decide) (by decide)
    have e4 := hg .r4 (by decide) (by decide)
    have e5 := hg .r5 (by decide) (by decide)
    have e6 := hg .r6 (by decide) (by decide)
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e10, e6, he.r10, h.r6, add32_ofNat_assoc]
    · simp [gpr_setReg, e4, h.r4]
    · simp [gpr_setReg, e4, h.r4, h3]
    · simp [gpr_setReg, e5, h.r5, h3, ofNat_sub32 hkn hn']
    · simp [gpr_setReg, h3]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hk₂' := hk.trans hk₂
  have eK : State.addr (st + BitVec.ofNat 32 (64 + P % 16)) = State.addr st + BitVec.ofNat 64 (64 + P % 16) :=
    L.stA (by omega)
  have lp : LoopPre s₂ (st + BitVec.ofNat 32 (64 + P % 16)) D k := by
    refine ⟨h1, h2, h3', hk1, by omega, by rw [L.stN (by omega)]; have := L.sw; omega,
      by have := h.data.ok.fit; omega, ?_, ?_, ?_⟩
    · rw [hk₂'.rd, hk₂'.wr, eK]; exact covers_left (he.perm.stC (by omega))
    · rw [hk₂'.wr]; exact (h.data.take hkn).wr
    · rw [eK]; exact ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by omega))).symm
  refine WP.mono (xorLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  rw [eK, hk₂'.mem] at hm₃
  have hxl := length_xorBytes s.mem (State.addr D) (State.addr st + BitVec.ofNat 64 (64 + P % 16)) k
  have fw : Frame [⟨State.addr D, k⟩] s.mem s₃.mem := by rw [hm₃]; exact writeBytes_frame' _ hxl
  have hdisjst : ∀ r ∈ [(⟨State.addr D, k⟩ : Region)],
      (⟨State.addr st + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨State.addr st + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨((h.data.take hkn).ok.st.sub_right (Lay.stSub (by decide))).symm,
      ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .r4 → r ≠ .r5 → s₃.gpr r = s.gpr r :=
    fun r a b c d e f i => by rw [lo.other r a b c d e, hg₂ r b c f i, hg r d e]
  have he₃ : Env c st w sp k7 k8 s₃ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lo.sp.trans hk₂'.sp) (lo.rd.trans hk₂'.rd) (lo.wr.trans hk₂'.wr)
  have hc₃ : ciphOf s₃.mem (State.addr c) R = ciphOf s.mem (State.addr c) R :=
    ciph_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.data.take hkn).ctx) h.rounds
  refine ⟨k, he₃, hkn, by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h4],
    by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h5],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8],
    h.rounds, h.data.of_eq (lo.rd.trans hk₂'.rd) (lo.wr.trans hk₂'.wr), ?_, ?_, ?_, ?_, ?_⟩
  · intro hc₀
    refine (hc₀.head hP hk16).congr (blockAt_frame fw fun r hr => (hdisjst r hr).1)
      (blockAt_frame fw fun r hr => (hdisjst r hr).2)
  · intro hc₀
    have e := bytesAt_writeBytes_self s.mem (State.addr D)
      (xorBytes s.mem (State.addr D) (State.addr st + BitVec.ofNat 64 (64 + P % 16)) k) (by rw [hxl]; omega)
    rw [hxl] at e
    rw [hm₃, e, xorBytes]
    have := Proof.Gcm.ctr_head hc₀ hP (d := bytesAt s.mem (State.addr D) k) (by rw [length_bytesAt]; exact hk16)
    rw [length_bytesAt, add_ofNat_assoc] at this
    exact this
  · exact bytesAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (split_disj hkn h.data.ok.lt).symm) (by omega)
  · by_cases hkk : k = n
    · left; omega
    · right; omega
  · exact fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hkn⟩

omit L in
theorem CrMid.data_eq {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid c st w sp k7 k8 R icb P D n m₀ j s) : bytesAt s.mem (State.addr D) n =
      bytesAt s.mem (State.addr D) j ++ bytesAt s.mem (State.addr D + BitVec.ofNat 64 j) (n - j) := by
  rw [← bytesAt_add, Nat.add_sub_cancel' h.le]

omit L in
/-- The split of the rest into whole blocks for `vg_aes_ctr32` and the last bytes. -/
theorem splitCtr_ok {s : State} {D : BitVec 32} {n j : Nat} (hj : j ≤ n) (hn : n < 2 ^ 32)
    (h4 : s.gpr .r4 = D + BitVec.ofNat 32 j) (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)) :
    ∃ s', runBlock isa splitCtr s = some s' ∧
      s'.gpr .r3 = D + BitVec.ofNat 32 j ∧ s'.gpr .r12 = BitVec.ofNat 32 ((n - j) / 16) ∧
      s'.gpr .r4 = D + BitVec.ofNat 32 (j + 16 * ((n - j) / 16)) ∧
      s'.gpr .r5 = BitVec.ofNat 32 (n - (j + 16 * ((n - j) / 16))) ∧
      s'.z = decide ((n - j) / 16 = 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have hand := and15 (BitVec.ofNat 32 (n - j))
  rw [toNat32 (by omega)] at hand
  have hsub : BitVec.ofNat 32 (n - j) - BitVec.ofNat 32 ((n - j) % 16) = BitVec.ofNat 32 (16 * ((n - j) / 16)) := by
    rw [ofNat_sub32 (Nat.mod_le _ _) (by omega)]; congr 1; omega
  refine ⟨_, by simp only [splitCtr]; arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h4]
  · simp [gpr_setReg, h5, shr4 (show n - j < 2 ^ 32 by omega)]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h4, h5, hand, hsub, add32_ofNat_assoc]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, hand]
    congr 1; omega
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5,
      shr4 (show n - j < 2 ^ 32 by omega)]
    rw [z_cmp (by omega) (by decide)]
  · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
  · exact ⟨rfl, rfl, rfl, rfl⟩

omit L in
/-- The arguments of `vg_aes_ctr32` for the whole blocks. -/
theorem wholeArgs_ok {s : State} (he : Env c st w sp k7 k8 s) :
    ∃ s', runBlock isa [.mov .r0 (.reg .r9), .mov .r1 (.reg .r8), addI .r2 .r10 48, addI .lr .r11 scrO] s = some s' ∧
      s'.gpr .r0 = c ∧ s'.gpr .r1 = s.gpr .r8 ∧ s'.gpr .r2 = st + BitVec.ofNat 32 48 ∧
      s'.gpr .lr = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg, h11]
  · intro r a b d e; simp [gpr_setReg, a, b, d, e]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- Whole blocks. -/
theorem cryptWhole_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid c st w sp k7 k8 R icb P D n m₀ j s) (hc : ciphOf s.mem (State.addr c) R = ciphOf m₀ (State.addr c) R) :
    WP isa cryptWhole s (fun s' => ∃ j', CrMid c st w sp k7 k8 R icb P D n m₀ j' s' ∧ n - j' < 16) := by
  have hn' := h.data.ok.lt32
  have he := h.env
  obtain ⟨s₁, run₁, h3, h12, h4, h5, hz, hg₁, hk₁⟩ := splitCtr_ok h.le hn' h.r4 h.r5
  generalize hnb : (n - j) / 16 = nb at h12 h4 h5 hz
  have h16 : 16 * nb ≤ n - j := by omega
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) hk₁.sp hk₁.rd hk₁.wr
  have hd₁ : DataW c st w sp k7 k8 s₁ D n := h.data.of_eq hk₁.rd hk₁.wr
  have r8₁ : s₁.gpr .r8 = BitVec.ofNat 32 R := by
    rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8]
  refine WP.ite (decide (nb = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, ⟨he₁, h.le, by rw [h4]; rfl, by rw [h5]; rfl, r8₁, h.rounds, hd₁,
      fun hc₀ => by rw [hk₁.mem]; exact h.ctr hc₀, fun hc₀ => by rw [hk₁.mem]; exact h.done hc₀,
      by rw [hk₁.mem]; exact h.rest, h.whole, by rw [hk₁.mem]; exact h.frame⟩, by omega⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hw : (P + j) % 16 = 0 := h.whole.resolve_left (by omega)
    have hdj := h.data.sub (j := j) (k := 16 * nb) (by omega) (by omega)
    have eD := h.data.ok.addr (j := j) (by omega)
    obtain ⟨s₂, run₂, h0', h1', h2', hlr', hg₂, hk₂⟩ := wholeArgs_ok he₁
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : Env c st w sp k7 k8 s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
      hk₂.sp hk₂.rd hk₂.wr
    have eC := L.stA (d := 48) (by decide)
    have eS := L.wA (d := 512) (by decide)
    have hk := he₂.sp
    have hcall : CtrCall s₂ c (st + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) (w + BitVec.ofNat 32 512) R nb := by
      refine ⟨h0', by rw [h1', r8₁], h2', by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h3],
        by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h12], hlr', h.rounds,
        by rw [hk]; exact L.sp8, by have := L.cw; omega, by rw [L.stN (by decide)]; have := L.sw; omega,
        by have := hdj.ok.fit; omega, by rw [L.wN (by decide)]; have := L.ww; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_⟩
      all_goals try simp only [eC, eS, hk]
      · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
      · exact hdj.ctx.sub_left (Region.sub_prefix (by decide))
      · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
      · exact (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact hdj.ok.w.sub_right (Lay.wSub (by decide))
      · exact L.kc.sub_right (Region.sub_prefix (by decide))
      · exact L.stk_st (by decide)
      · exact hdj.ok.stk
      · exact L.stk_w (by decide)
      · exact covers_prefix he₂.perm.ctx (by decide)
      · refine covers_cons (he₂.perm.stC (by decide)) (covers_cons ?_ (he₂.perm.wC (by decide)))
        rw [hk₂.wr, hk₁.wr]; exact hdj.wr
    refine WP.mono (ctr_call hcall) fun s₃ g => ?_
    have gout := g.out; have gctr := g.ctr; have gframe := g.frame
    simp only [hk₂.mem, hk₁.mem, eC, eS, eD, hk] at gout gctr gframe
    have hcw := fun hc₀ => Proof.Gcm.ctr_whole (h.ctr hc₀) hw (m' := s₃.mem)
      (dp := State.addr D + BitVec.ofNat 64 j) (nb := nb) (by rw [gout, ← hc]) gctr
    refine ⟨j + 16 * nb, ⟨he₂.of_saved g.saved g.sp g.rd g.wr, by omega, ?_, ?_, ?_, h.rounds,
      hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr), ?_, ?_, ?_, .inr (by omega), ?_⟩, by omega⟩
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h4]
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h5]
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), r8₁]
    · intro hc₀; rw [← Nat.add_assoc]; exact (hcw hc₀).2
    · -- The bytes done.
      intro hc₀
      have hj16 : bytesAt s₃.mem (State.addr D + BitVec.ofNat 64 j) (16 * nb) =
          xorKs (ciphOf m₀ (State.addr c) R) icb (P + j) (bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (16 * nb)) := by
        rw [(hcw hc₀).1]
        congr 1
        have e := congrArg (List.take (16 * nb)) h.rest
        rwa [show n - j = 16 * nb + (n - j - 16 * nb) by omega, bytesAt_add, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _), List.take_left' (length_bytesAt _ _ _)] at e
      have hjd : bytesAt s₃.mem (State.addr D) j = bytesAt s.mem (State.addr D) j := bytesAt_frame gframe (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
        · exact split_disj (D := State.addr D) (j := j) (n := n) h.le h.data.ok.lt |>.sub_right
            (Region.sub_prefix (by omega))
        · exact (h.data.take h.le).ok.w.sub_right (Lay.wSub (by decide))
        · exact (h.data.take h.le).ok.stk.symm) (by omega)
      exact done_append (hjd.trans (h.done hc₀)) hj16
    · -- The bytes left.
      have hdis : ∀ r ∈ [⟨State.addr st + BitVec.ofNat 64 48, 16⟩, ⟨State.addr D + BitVec.ofNat 64 j, 16 * nb⟩,
          ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, below sp],
          (⟨State.addr D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ : Region).Disjoint r := by
        have hst := h.data.ok.st; have hW := h.data.ok.w; have hK := h.data.ok.stk
        have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ ⟨State.addr D, n⟩ :=
          Offset.sub_base _ (by omega)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hst.sub_left hs).sub_right (Lay.stSub (by decide))
        · rw [← add_ofNat_assoc]
          have := split_disj (D := State.addr D + BitVec.ofNat 64 j) (j := 16 * nb) (n := n - j) h16 (by omega)
          rw [show n - j - 16 * nb = n - (j + 16 * nb) by omega] at this
          exact this.symm
        · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
        · exact (hK.sub_right hs).symm
      rw [bytesAt_frame gframe hdis (by omega)]
      have e := congrArg (List.drop (16 * nb)) h.rest
      have e₂ : ∀ m : Mem, (bytesAt m (State.addr D + BitVec.ofNat 64 j) (n - j)).drop (16 * nb) =
          bytesAt m (State.addr D + BitVec.ofNat 64 (j + 16 * nb)) (n - (j + 16 * nb)) := fun m => by
        rw [show n - j = 16 * nb + (n - (j + 16 * nb)) by omega, bytesAt_add,
          List.drop_left' (length_bytesAt _ _ _), add_ofNat_assoc]
      simpa only [e₂] using e
    · refine h.frame.trans (gframe.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., (Offset.sub_base _ (by omega))⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- The keystream block zeroed and the arguments of `vg_aes_ctr32` on it. -/
theorem tailArgs_ok {s : State} (he : Env c st w sp k7 k8 s) :
    ∃ s', runBlock isa tailArgs s = some s' ∧
      s'.mem = Cmac.store4 s.mem (State.addr st + BitVec.ofNat 64 64) 0 0 0 0 ∧
      s'.gpr .r0 = c ∧ s'.gpr .r1 = s.gpr .r8 ∧ s'.gpr .r2 = st + BitVec.ofNat 32 48 ∧
      s'.gpr .r3 = st + BitVec.ofNat 32 64 ∧ s'.gpr .r12 = BitVec.ofNat 32 1 ∧
      s'.gpr .lr = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
  have w₀ := he.perm.stW (show 64 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 68 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 72 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 76 + 4 ≤ 80 by decide)
  refine ⟨_, by simp only [tailArgs]; arun [h10, L.stA, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]; rfl
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg]
  · simp [gpr_setReg, h11]
  · intro r a b d e f i; simp [gpr_setReg, a, b, d, e, f, i]
  all_goals rfl

/-- The last bytes' keystream block, from `vg_aes_ctr32`. -/
structure TailKs (c st w sp k7 k8 : BitVec 32) (R : Nat) (icb : Block) (P : Nat) (D : BitVec 32) (n : Nat) (m₀ : Mem)
    (j : Nat) (s₀ s : State) : Prop where
  mid : CrMid c st w sp k7 k8 R icb P D n m₀ j s₀
  env : Env c st w sp k7 k8 s
  r4 : s.gpr .r4 = D + BitVec.ofNat 32 j
  r5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)
  r8 : s.gpr .r8 = BitVec.ofNat 32 R
  ks : blockAt s.mem (State.addr st + BitVec.ofNat 64 64) =
    ciphOf m₀ (State.addr c) R (blockAt s₀.mem (State.addr st + BitVec.ofNat 64 48))
  cb : blockAt s.mem (State.addr st + BitVec.ofNat 64 48) =
    Spec.Gcm.inc32 (blockAt s₀.mem (State.addr st + BitVec.ofNat 64 48))
  frame : Frame [⟨State.addr st + BitVec.ofNat 64 48, 32⟩, ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, below sp]
    s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The new keystream block. -/
theorem tailKs_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid c st w sp k7 k8 R icb P D n m₀ j s) (hc : ciphOf s.mem (State.addr c) R = ciphOf m₀ (State.addr c) R) :
    WP isa (.seq (.block tailArgs) ctrFrame) s (TailKs c st w sp k7 k8 R icb P D n m₀ j s) := by
  have he := h.env
  obtain ⟨s₂, run₂, hm₂, h0, h1, h2, h3, h12, hlr, hg₂, hrd₂, hwr₂, hsp₂⟩ := tailArgs_ok L he
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ : Env c st w sp k7 k8 s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂
  have hk := he₂.sp
  have eC := L.stA (d := 48) (by decide)
  have eK := L.stA (d := 64) (by decide)
  have eS := L.wA (d := 512) (by decide)
  have fz : Frame [⟨State.addr st + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hKS0 : blockAt s₂.mem (State.addr st + BitVec.ofNat 64 64) = 0 := by
    rw [blockAt, hm₂, store4_zero_bytes]; decide
  have hCB : blockAt s₂.mem (State.addr st + BitVec.ofNat 64 48) = blockAt s.mem (State.addr st + BitVec.ofNat 64 48) :=
    blockAt_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  have hc₂ : ciphOf s₂.mem (State.addr c) R = ciphOf m₀ (State.addr c) R := by
    rw [ciph_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cs.sub_right (Lay.stSub (by decide))) h.rounds, hc]
  have hcall : CtrCall s₂ c (st + BitVec.ofNat 32 48) (st + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 512) R 1 := by
    refine ⟨h0, by rw [h1, h.r8], h2, h3, h12, hlr, h.rounds, by rw [hk]; exact L.sp8, by have := L.cw; omega,
      by rw [L.stN (by decide)]; have := L.sw; omega, by rw [L.stN (by decide)]; have := L.sw; omega,
      by rw [L.wN (by decide)]; have := L.ww; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [eC, eK, eS, hk]
    · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
    · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
    · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
    · exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
    · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · exact L.kc.sub_right (Region.sub_prefix (by decide))
    · exact L.stk_st (by decide)
    · exact L.stk_st (by decide)
    · exact L.stk_w (by decide)
    · exact covers_prefix he₂.perm.ctx (by decide)
    · exact covers_cons (he₂.perm.stC (by decide)) (covers_cons (he₂.perm.stC (by decide))
        (he₂.perm.wC (by decide)))
  refine WP.mono (ctr_call hcall) fun s₃ g => ?_
  have gout := g.out; have gctr := g.ctr; have gframe := g.frame
  simp only [eC, eK, eS, hk] at gout gctr gframe
  rw [blocksAt_one, blocksAt_one, hKS0, Cmac.ctr32_one, List.cons.injEq] at gout
  refine ⟨h, he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_, ?_, ?_, ?_, ?_, by rw [g.rd, hrd₂], by rw [g.wr, hwr₂]⟩
  · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r4]
  · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r5]
  · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r8]
  · rw [gout.1, ← hc₂, hCB]
  · rw [gctr, hCB]; rfl
  · refine (fz.sub fun r hr => ?_).trans (gframe.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- The last bytes XORed with the new keystream block. -/
theorem tailXor_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s₀ s : State}
    (h : TailKs c st w sp k7 k8 R icb P D n m₀ j s₀ s) (hj : n - j < 16) (h0 : n - j ≠ 0) :
    WP isa (.seq (.block [addI .r1 .r10 64, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)]) xorLoop) s
      (CrOut c st w sp k7 k8 R icb P D n m₀) := by
  have hm := h.mid
  have hn' := hm.data.ok.lt32
  have hw : (P + j) % 16 = 0 := hm.whole.resolve_left h0
  have hdj := hm.data.sub (j := j) (k := n - j) (by omega) (by omega)
  have eD := hm.data.ok.addr (j := j) (by omega)
  have he₃ := h.env
  obtain ⟨s₄, run₄, h1, h2, h3, hg₄, hk₄⟩ : ∃ s₄, runBlock isa
      [addI .r1 .r10 64, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)] s = some s₄ ∧
      s₄.gpr .r1 = st + BitVec.ofNat 32 64 ∧ s₄.gpr .r2 = D + BitVec.ofNat 32 j ∧
      s₄.gpr .r3 = BitVec.ofNat 32 (n - j) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₄.gpr r = s.gpr r) ∧ Keeps s s₄ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he₃.r10]
    · simp [gpr_setReg, h.r4]
    · simp [gpr_setReg, h.r5]
    · intro r a b d; simp [gpr_setReg, a, b, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have eK := L.stA (d := 64) (by decide)
  have lp : LoopPre s₄ (st + BitVec.ofNat 32 64) (D + BitVec.ofNat 32 j) (n - j) := by
    refine ⟨h1, h2, h3, by omega, by omega, by rw [L.stN (by decide)]; have := L.sw; omega, hdj.ok.fit, ?_, ?_, ?_⟩
    · rw [hk₄.rd, hk₄.wr, eK]; exact covers_left (he₃.perm.stC (by omega))
    · rw [hk₄.wr, h.wr]; exact hdj.wr
    · rw [eK]; exact (hdj.ok.st.sub_right (Lay.stSub (by omega))).symm
  refine WP.mono (xorLoop_ok s₄ lp) fun s₅ ⟨hm₅, lo⟩ => ?_
  rw [hk₄.mem, eK, eD] at hm₅
  have hxl := length_xorBytes s.mem (State.addr D + BitVec.ofNat 64 j) (State.addr st + BitVec.ofNat 64 64) (n - j)
  have fw : Frame [⟨State.addr D + BitVec.ofNat 64 j, n - j⟩] s.mem s₅.mem := by
    rw [hm₅]; exact writeBytes_frame' _ hxl
  have dst := hdj.ok.st; have dw := hdj.ok.w; have dk := hdj.ok.stk
  rw [eD] at dst dw dk
  have hd₃ : bytesAt s.mem (State.addr D + BitVec.ofNat 64 j) (n - j) =
      bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j) := by
    rw [← hm.rest, bytesAt_frame h.frame (fun r hr => ?_) (by omega)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dst.sub_right (Lay.stSub (by decide))
    · exact dw.sub_right (Lay.wSub (by decide))
    · exact dk.symm
  have ht := fun hc₀ => Proof.Gcm.ctr_tail (hm.ctr hc₀) hw (m₁ := s.mem) h.ks (by rw [h.cb])
    (d := bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j)) (by rw [length_bytesAt]; omega)
    (by rw [length_bytesAt]; omega)
  rw [length_bytesAt] at ht
  have dS : ∀ r ∈ [(⟨State.addr D + BitVec.ofNat 64 j, n - j⟩ : Region)], ∀ k, k + 16 ≤ 80 →
      (⟨State.addr st + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint r := by
    intro r hr k hk; simp only [List.mem_singleton] at hr; subst hr
    exact (dst.sub_right (Lay.stSub hk)).symm
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₅.gpr r = s.gpr r :=
    fun r a b c d e => by rw [lo.other r a b c d e, hg₄ r b c d]
  refine ⟨he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (lo.sp.trans hk₄.sp) (lo.rd.trans hk₄.rd) (lo.wr.trans hk₄.wr),
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r8], ?_, ?_, ?_⟩
  · intro hc₀
    rw [show P + n = P + j + (n - j) by omega]
    exact (ht hc₀).2.congr (blockAt_frame fw fun r hr => dS r hr 48 (by decide))
      (blockAt_frame fw fun r hr => dS r hr 64 (by decide))
  · intro hc₀
    have hdone : bytesAt s₅.mem (State.addr D) j = bytesAt s₀.mem (State.addr D) j := by
      have hdt := (hm.data.take hm.le).ok
      rw [bytesAt_frame fw (fun r hr => ?_) (by omega), bytesAt_frame h.frame (fun r hr => ?_) (by omega)]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hdt.st.sub_right (Lay.stSub (by decide))
        · exact hdt.w.sub_right (Lay.wSub (by decide))
        · exact hdt.stk.symm
      · simp only [List.mem_singleton] at hr; subst hr; exact split_disj hm.le hm.data.ok.lt
    have hpiece : bytesAt s₅.mem (State.addr D + BitVec.ofNat 64 j) (n - j) =
        xorKs (ciphOf m₀ (State.addr c) R) icb (P + j) (bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j)) := by
      have e := bytesAt_writeBytes_self s.mem (State.addr D + BitVec.ofNat 64 j)
        (xorBytes s.mem (State.addr D + BitVec.ofNat 64 j) (State.addr st + BitVec.ofNat 64 64) (n - j))
        (by rw [hxl]; omega)
      rw [hxl] at e
      rw [hm₅, e, xorBytes, hd₃, (ht hc₀).1]
    rw [show n = j + (n - j) by omega]
    exact done_append (hdone.trans (hm.done hc₀)) hpiece
  · refine hm.frame.trans (Frame.trans (h.frame.sub fun r hr => ?_) (fw.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega)⟩

/-- The last bytes, with a new keystream block. -/
theorem cryptTail_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid c st w sp k7 k8 R icb P D n m₀ j s) (hj : n - j < 16)
    (hc : ciphOf s.mem (State.addr c) R = ciphOf m₀ (State.addr c) R) :
    WP isa cryptTail s (CrOut c st w sp k7 k8 R icb P D n m₀) := by
  have hn' := h.data.ok.lt32
  have he := h.env
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 h.r5 (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁
  have h₁ : CrMid c st w sp k7 k8 R icb P D n m₀ j s₁ :=
    ⟨he₁, h.le, (by rw [hg₁]; exact h.r4), (by rw [hg₁]; exact h.r5), (by rw [hg₁]; exact h.r8), h.rounds,
      h.data.of_eq hrd₁ hwr₁, (fun hc₀ => by rw [hm₁]; exact h.ctr hc₀), (fun hc₀ => by rw [hm₁]; exact h.done hc₀),
      (by rw [hm₁]; exact h.rest), h.whole, (by rw [hm₁]; exact h.frame)⟩
  refine WP.ite (decide (n - j = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega
    subst h0
    exact WP.block_nil ⟨he₁, h₁.r8, fun hc₀ => h₁.ctr hc₀, fun hc₀ => h₁.done hc₀, h₁.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    exact WP.seq (WP.mono (tailKs_ok L h₁ (by rw [hm₁]; exact hc)) fun _ ht => tailXor_ok L ht hj h0)

theorem CrMid.ciph {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid c st w sp k7 k8 R icb P D n m₀ j s) : ciphOf s.mem (State.addr c) R = ciphOf m₀ (State.addr c) R :=
  ciph_frame h.frame (ctx_crFrame L h.data) h.rounds

omit L in
theorem CrIn.keep {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s s' : State}
    (h : CrIn c st w sp k7 k8 R icb P D n s) (hg : s'.gpr = s.gpr) (hk : Keeps s s') : CrIn c st w sp k7 k8 R icb P D n s' :=
  ⟨h.env.keep (fun r _ => by rw [hg]) hk.sp hk.rd hk.wr, by rw [hg]; exact h.r4, by rw [hg]; exact h.r5,
    by rw [hg]; exact h.r6, by rw [hg]; exact h.r8, h.rounds, h.data.of_eq hk.rd hk.wr⟩

/-- The rest of the keystream block first, if there is one. -/
theorem cryptFill_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s : State}
    (h : CrIn c st w sp k7 k8 R icb P D n s) (h0 : n ≠ 0) :
    WP isa cryptFill s (fun s' => ∃ j, CrMid c st w sp k7 k8 R icb P D n s.mem j s') := by
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂, hsp₂⟩ := cmp0_ok s .r6 h.r6
    (by have := Nat.mod_lt P (show 16 > 0 by decide); omega)
  have h₂ := h.keep hg₂ ⟨hm₂, hrd₂, hwr₂, hsp₂⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.ite (decide (P % 16 = 0)) (eval_eq' hz₂) (fun ht => ?_) (fun hf => ?_)
  · have ho : P % 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨0, h₂.env, by omega, by rw [h₂.r4, add_ofNat_zero], by rw [h₂.r5, Nat.sub_zero], h₂.r8,
      h₂.rounds, h₂.data, fun hc₀ => by rw [hm₂]; simpa using hc₀, fun _ => by simp [bytesAt]; rfl,
      by rw [hm₂, add_ofNat_zero], .inr (by omega), by rw [hm₂]; exact Frame.refl _ _⟩
  · have := cryptHead_ok L h₂ h0 (by simpa using hf)
    rw [hm₂] at this; exact this

/-- `crypt`. -/
theorem crypt_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s : State}
    (h : CrIn c st w sp k7 k8 R icb P D n s) :
    WP isa crypt s (CrOut c st w sp k7 k8 R icb P D n s.mem) := by
  have hn' := h.data.ok.lt32
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 h.r5 hn'
  have h₁ := h.keep hg₁ ⟨hm₁, hrd₁, hwr₁, hsp₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨h₁.env, h₁.r8, fun hc₀ => by rw [hm₁]; exact hc₀,
      fun _ => by simp [bytesAt]; rfl, by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    rw [← hm₁]
    refine WP.seq (WP.mono (cryptFill_ok L h₁ h0) fun s' ⟨j, hj⟩ => ?_)
    refine WP.seq (WP.mono (cryptWhole_ok L hj (hj.ciph L)) fun s'' ⟨j', hj', hlt⟩ => ?_)
    exact cryptTail_ok L hj' hlt (hj'.ciph L)

end

end VG.Proof.AesGcm.Arm
