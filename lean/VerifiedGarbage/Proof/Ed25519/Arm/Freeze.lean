import VerifiedGarbage.Proof.Ed25519.Arm.FreezeSelect
import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg

/-! Untrusted: canonical reduction preserves all working field elements. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.X25519 (P)
variable {b : BitVec 32}

theorem freezeCore_ok {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) FR) :
    WP isa (.block freezeCore) s fun t => Rest clob s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) FR ∧ V t.mem (State.addr b) FR = V s.mem (State.addr b) FR % P := by
  have hX : FR = 1472 := rfl
  have hFY : FY = 1536 := rfl
  obtain ⟨tA, tFY, hS, hR, hv⟩ := freeze_facts hl
  obtain ⟨-, -, lm, c1⟩ := mask15_facts hl
  simp only [freezeCore, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (freezeA_ok hc hl) fun s1 ⟨h6, h5, hl1, hf1, hr1⟩ => ?_
  have hc1 : Ctx b s1 := hc.of_rest hr1 (by decide)
  refine WP.append (pass_ok (rb := .r0) (o := FR) (s0 := s1) (c := mask15 (limb s.mem (State.addr b) FR))
    (cin := 19 * (limb s.mem (State.addr b) FR 15 / 32768)) (by decide) (by decide)
    (by rw [hc1.r0]; have := hc.fit; omega) (fun k hk => by rw [hc1.r0]; exact hc1.inW (by omega)) h6 h5
    (fun k hk => by have := lm k hk; omega) (by omega) ?_) fun s2 hp2 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc1.of_rest hp.rest (by decide)) (o := FR) (k := k) (by omega)) fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc1 hp.frame (by omega) (by omega) (by omega)]
    exact hl1 k hk
  have hc2 : Ctx b s2 := hc1.of_rest hp2.rest (by decide)
  have hpo2 : ∀ j < 16, wd s2.mem (State.addr b) (FR + 4 * j) = frA (limb s.mem (State.addr b) FR) j :=
    fun j hj => by have := hp2.outs j hj; rwa [hc1.r0] at this
  have hpf2 : Frame [⟨State.addr b + BitVec.ofNat 64 FR, 64⟩] s1.mem s2.mem := by
    have := hp2.frame; rwa [hc1.r0] at this
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := [.r5]) (by decide)) (by decide)
  refine WP.append (pass_ok (rb := .r0) (o := FY) (s0 := s3) (c := frA (limb s.mem (State.addr b) FR))
    (cin := 19) (by decide) (by decide)
    (by rw [hc3.r0]; have := hc.fit; omega) (fun k hk => by rw [hc3.r0]; exact hc3.inW (by omega))
    (by rw [u3.other _ (by decide), hp2.rest.gpr _ (by decide)]; exact h6)
    (by rw [u3.gpr]; rfl) (fun k hk => by have := out_lt (mask15 (limb s.mem (State.addr b) FR)) (19 * (limb s.mem (State.addr b) FR 15 / 32768)) k; unfold frA; omega) (by decide) ?_) fun s4 hp4 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc3.of_rest hp.rest (by decide)) (o := FR) (k := k) (by omega)) fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc3 hp.frame (by omega) (by omega) (by omega), u3.mem]
    exact hpo2 k hk
  have hc4 : Ctx b s4 := hc3.of_rest hp4.rest (by decide)
  have hpo4 : ∀ j < 16, wd s4.mem (State.addr b) (FY + 4 * j) = frY (limb s.mem (State.addr b) FR) j :=
    fun j hj => by have := hp4.outs j hj; rwa [hc3.r0] at this
  have hpf4 : Frame [⟨State.addr b + BitVec.ofNat 64 FY, 64⟩] s3.mem s4.mem := by
    have := hp4.frame; rwa [hc3.r0] at this
  have hx4 : ∀ k < 16, limb s4.mem (State.addr b) FR k = frA (limb s.mem (State.addr b) FR) k := by
    intro k hk
    rw [limb, wd_frame hpf4 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega),
      u3.mem, hpo2 k hk]
  refine WP.append (freezeB_ok hc4) fun s5 ⟨h9, hy5, hf5, hr5⟩ => ?_
  have hc5 : Ctx b s5 := hc4.of_rest hr5 (by decide)
  have hx5 : ∀ k < 16, limb s5.mem (State.addr b) FR k = frA (limb s.mem (State.addr b) FR) k := by
    intro k hk
    rw [limb, wd_frame hf5 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)]
    exact hx4 k hk
  have hy5' : ∀ k < 16, limb s5.mem (State.addr b) FY k = mask15 (frY (limb s.mem (State.addr b) FR)) k := by
    intro k hk
    rw [hy5 k hk]
    simp only [mask15]
    split
    · rename_i h; subst h; rw [limb, hpo4 15 (by decide)]
    · rw [limb, hpo4 k hk]
  have h9' : s5.gpr .r9 = 0 - BitVec.ofNat 32 (frS (limb s.mem (State.addr b) FR)) := by
    rw [h9, limb, hpo4 15 (by decide)]; rfl
  have hr45 : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r9] s s5 :=
    (hr1.mono (by decide)).trans ((hp2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((hp4.rest.mono (by decide)).trans (hr5.mono (by decide)))))
  refine WP.mono (freezeSelect_ok hc5 hS h9') fun s6 h6' => ?_
  have hr : ∀ k < 16, limb s6.mem (State.addr b) FR k = frR (limb s.mem (State.addr b) FR) k :=
    fun k hk => by rw [h6'.2.2 k hk, hx5 k hk, hy5' k hk]; rfl
  refine ⟨(hr45.mono (by decide)).trans (h6'.1.mono (by decide)), ?_,
    fun k hk => by rw [hr k hk]; exact hR k hk, ?_⟩
  · have hfa : ∀ z, ACC ≤ z → z + 64 ≤ ACC + 128 →
        Region.Sub ⟨State.addr b + BitVec.ofNat 64 z, 64⟩
          ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩ :=
      fun z h1 h2 => Offset.sub _ h1 h2
    have extend : ∀ {z m m'}, (z = FR ∨ z = FY) →
        Frame [⟨State.addr b + BitVec.ofNat 64 z, 64⟩] m m' →
        Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] m m' := by
      intro z m m' hz hf
      refine hf.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩
      rw [List.mem_singleton.mp hmem]
      rcases hz with rfl | rfl <;> exact hfa _ (by decide) (by decide)
    refine (extend (.inl rfl) hf1).trans ((extend (.inl rfl) hpf2).trans ?_)
    rw [← u3.mem]
    exact (extend (.inr rfl) hpf4).trans ((extend (.inr rfl) hf5).trans (extend (.inl rfl) h6'.2.1))
  · rw [V, val16_congr hr, hv]
    rfl

theorem freeze_ok {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) (a : Slot) :
    WP isa (.block (freeze a)) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = env s.mem b ∧ Lim t.mem (State.addr b) FR ∧
      V t.mem (State.addr b) FR = (env s.mem b a).val := by
  rw [freeze, WP.block_append_iff]
  refine WP.mono (freezeCopy_ok hc a) fun u ⟨hr, hf, he⟩ => ?_
  refine WP.mono (freezeCore_ok (hc.of_rest hr (by decide))
    (fun k hk => by rw [he k hk]; exact hl a k hk)) fun t ⟨hr', hf', hl', hv⟩ => ?_
  have hframe : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem :=
    (hf.sub fun r hm => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hm]; exact Region.sub_prefix (by decide)⟩).trans hf'
  have hs : ∀ (i : Slot) k, k < 16 →
      limb t.mem (State.addr b) (offset i) k = limb s.mem (State.addr b) (offset i) k := by
    intro i k hk
    have hi := slot_range i
    refine limb_frame hframe (fun r hm j hj => ?_) k hk
    rw [List.mem_singleton.mp hm]
    exact Offset.disjoint _ (.inl (by omega)) (by rw [ACC_eq] at hi; omega) (by decide)
  refine ⟨⟨(hr.mono (by decide)).trans hr', ?_⟩,
    fun i k hk => by rw [hs i k hk]; exact hl i k hk,
    funext fun i => congrArg VG.Proof.X25519.toFe (val16_congr (hs i)), hl', ?_⟩
  · exact hframe.sub fun r hm => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hm]; exact Offset.sub _ (by decide) (by decide)⟩
  · rw [hv, V, val16_congr he]
    rfl

end VG.Proof.Ed25519.Arm
