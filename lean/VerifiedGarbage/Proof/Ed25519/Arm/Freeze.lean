import VerifiedGarbage.Impl.Ed25519.Arm.Freeze
import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg

/-! Merged from `Proof.Ed25519.Arm.FreezeSteps`. -/
section
/-! Canonical reduction of the two temporary field elements. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem low15_val (x : BitVec 32) : ((x <<< 17) >>> 17).toNat = x.toNat % 32768 := by
  rw [toNat_shr, toNat_shl, show (2 : Nat) ^ 32 = 32768 * 2 ^ 17 from rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem sel0r (a c : BitVec 32) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 32 0)) = a := by simp

theorem sel1r (a c : BitVec 32) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 32 1)) = c := by
  have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
  rw [this, BitVec.and_allOnes, BitVec.xor_comm c, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

variable {b : BitVec 32}

/-- The start of `freeze`: bit 255 of `[FR]` cleared, 19 times it in `r5`. -/
theorem freezeA_ok {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) FR) :
    WP isa (.block freezeA) s fun s' =>
      s'.gpr .r6 = mask16 ∧ (s'.gpr .r5).toNat = 19 * (limb s.mem (State.addr b) FR 15 / 32768) ∧
      (∀ k < 16, limb s'.mem (State.addr b) FR k = mask15 (limb s.mem (State.addr b) FR) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 FR, 64⟩] s.mem s'.mem ∧
      Rest [.r2, .r3, .r5, .r6] s s' := by
  have hX : FR = 1472 := rfl
  simp only [freezeA, low15, List.cons_append, List.nil_append]
  refine wp_movw fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r6]) (by decide)) (by decide)
  refine ldr0_ok hc1 (d := FR + 60) (by decide) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => wp_mov (op2_lsl (by decide)) fun s4 u4 =>
    wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  have hr5 : Rest [.r3, .r5, .r6] s s5 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  refine str0_ok hc5 (d := FR + 60) (by decide) fun s6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun s7 u7 => wp_mul fun s8 u8 => WP.block_nil ?_
  have hl15 := hl 15 (by decide)
  have e2 : (s2.gpr .r3).toNat = limb s.mem (State.addr b) FR 15 := by rw [u2.gpr, u1.mem]; rfl
  have e5 : (s5.gpr .r3).toNat = limb s.mem (State.addr b) FR 15 % 32768 := by
    rw [u5.gpr, u4.gpr, low15_val, u3.other .r3 (by decide), e2]
  have e3 : (s3.gpr .r5).toNat = limb s.mem (State.addr b) FR 15 / 32768 := by
    rw [u3.gpr, toNat_shr, e2]
  have hm6 : s6.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (FR + 60)) (s5.gpr .r3) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr, u5.other .r6 (by decide),
      u4.other .r6 (by decide), u3.other .r6 (by decide), u2.other .r6 (by decide), u1.gpr]
  · rw [u8.gpr, u7.other _ (by decide), u7.gpr, u6.gpr, u5.other _ (by decide), u4.other _ (by decide),
      toNat_mul_lt (by rw [e3]; show _ * 19 < _; omega), e3]
    show _ * 19 = _
    omega
  · rw [limb, u8.mem, u7.mem, hm6]
    rcases Nat.lt_or_ge k 15 with h | h
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      simp only [mask15, show k ≠ 15 by omega, ite_false]; rfl
    · rw [show FR + 4 * k = FR + 60 by omega, wd_write_self, e5, show k = 15 by omega]; rfl
  · rw [u8.mem, u7.mem, hm6]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := FR + 60) (n := 4) (Nat.le_add_right _ _) (by omega) (by omega))
  · exact (hr5.mono (by decide)).trans ((u6.rest _).trans ((u7.rest (by decide)).trans (u8.rest (by decide))))

/-- `freezeB`: the mask `-(bit 255 of [FY])` in `r9`, and bit 255 of `[FY]` cleared. -/
theorem freezeB_ok {s : State} (hc : Ctx b s) :
    WP isa (.block freezeB) s fun s' =>
      s'.gpr .r9 = 0 - BitVec.ofNat 32 (limb s.mem (State.addr b) FY 15 / 32768) ∧
      (∀ k < 16, limb s'.mem (State.addr b) FY k = mask15 (limb s.mem (State.addr b) FY) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 FY, 64⟩] s.mem s'.mem ∧ Rest [.r1, .r3, .r9] s s' := by
  have hFY : FY = 1536 := rfl
  simp only [freezeB, low15, List.cons_append, List.nil_append]
  refine ldr0_ok hc (d := FY + 60) (by decide) fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => wp_mov (op2_imm (by decide)) fun s3 u3 =>
    wp_dp (op2_reg _ _) fun s4 u4 => wp_mov (op2_lsl (by decide)) fun s5 u5 =>
    wp_mov (op2_lsr (by decide)) fun s6 u6 => ?_
  have hr6 : Rest [.r1, .r3, .r9] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  refine str0_ok (hc.of_rest hr6 (by decide)) (d := FY + 60) (by decide) fun s7 u7 => WP.block_nil ?_
  have e1 : (s1.gpr .r3).toNat = limb s.mem (State.addr b) FY 15 := by rw [u1.gpr]; rfl
  have hm7 : s7.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (FY + 60)) (s6.gpr .r3) := by
    rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, fun k hk => ?_, ?_, hr6.trans (u7.rest _)⟩
  · rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.gpr]
    show s3.gpr .r1 - s3.gpr .r9 = _
    rw [u3.gpr, u3.other _ (by decide), u2.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shr, e1, toNat_imm (by have := wd_lt s.mem (State.addr b) (FY + 4 * 15); unfold limb; omega)]
  · rw [limb, hm7]
    rcases Nat.lt_or_ge k 15 with h | h
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      simp only [mask15, show k ≠ 15 by omega, ite_false]; rfl
    · rw [show FY + 4 * k = FY + 60 by omega, wd_write_self, u6.gpr, u5.gpr, low15_val, u4.other .r3 (by decide),
        u3.other .r3 (by decide), u2.other .r3 (by decide), e1, show k = 15 by omega]; rfl
  · rw [hm7]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := FY + 60) (n := 4) (Nat.le_add_right _ _) (by omega) (by omega))

theorem freezeCopy_ok {s : State} (hc : Ctx b s) (a : Slot) :
    WP isa (.block (freezeCopy a)) s fun t => Rest [.r3] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 FR, 64⟩] s.mem t.mem ∧
      ∀ k < 16, limb t.mem (State.addr b) FR k = limb s.mem (State.addr b) (offset a) k := by
  have ha := slot_range a
  rw [ACC_eq] at ha
  refine WP.mono (fill_ok (src := fun k => [.ldr .r3 .r0 (offset a + 4 * k)])
    (f := limb s.mem (State.addr b) (offset a)) hc (by decide)
    (fun k hk t ht => ldr0_ok (hc.of_rest ht.rest (by decide)) (by omega)
      fun u hu => WP.block_nil ⟨?_, hu.rest (by decide), hu.mem⟩))
    fun t ht => ⟨ht.rest, ht.frame, ht.outs⟩
  rw [hu.gpr]
  exact wd_frame ht.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by change _ ≤ 1472; omega)) (by omega) (by change 1472 + _ ≤ _; omega)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.FreezeSelect`. -/
section
/-! Select the reduced limbs without a data-dependent branch. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem freezeSelect_ok {b : BitVec 32} {s0 : State} (hc : Ctx b s0) {sw : Nat}
    (hsw : sw ≤ 1) (h9 : s0.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block freezeSelect) s0 fun t => Rest [.r2, .r3] s0 t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 FR, 64⟩] s0.mem t.mem ∧
      ∀ k < 16, limb t.mem (State.addr b) FR k =
        sel sw (limb s0.mem (State.addr b) FR k) (limb s0.mem (State.addr b) FY k) := by
  have hR : FR = 1472 := rfl
  have hY : FY = 1536 := rfl
  refine WP.mono (fill_regs_ok (ws := [.r2, .r3]) (by decide) (src := selectSrc)
    (f := fun k => sel sw (limb s0.mem (State.addr b) FR k) (limb s0.mem (State.addr b) FY k))
    hc (by decide) (fun k hk s h => ?_)) fun t ht => ⟨ht.rest, ht.frame, ht.outs⟩
  have hcs := hc.of_rest h.rest (by decide)
  unfold selectSrc
  refine ldr0_ok hcs (d := FR + 4 * k) (by omega) fun t1 v1 => ?_
  refine ldr0_ok (hcs.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide))
    (d := FY + 4 * k) (by omega) fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 =>
    wp_dp (op2_reg _ _) fun t5 v5 => WP.block_nil ?_
  have ex : t2.gpr .r3 = s.mem.readW (State.addr b + BitVec.ofNat 64 (FR + 4 * k)) 32 := by
    rw [v2.other _ (by decide), v1.gpr]
  have ey : t2.gpr .r2 = s.mem.readW (State.addr b + BitVec.ofNat 64 (FY + 4 * k)) 32 := by
    rw [v2.gpr, v1.mem]
  have em : t3.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide),
      h.rest.gpr _ (by decide), h9]
  have hx : limb s.mem (State.addr b) FR k = limb s0.mem (State.addr b) FR k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  have hy : limb s.mem (State.addr b) FY k = limb s0.mem (State.addr b) FY k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  refine ⟨?_, (v1.rest (by decide)).trans ((v2.rest (by decide)).trans
    ((v3.rest (by decide)).trans ((v4.rest (by decide)).trans (v5.rest (by decide))))),
    by rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]⟩
  rw [v5.gpr]
  show (t4.gpr .r3 ^^^ t4.gpr .r2).toNat = _
  rw [v4.other .r3 (by decide), v4.gpr]
  show (t3.gpr .r3 ^^^ (t3.gpr .r2 &&& t3.gpr .r9)).toNat = _
  rw [v3.other .r3 (by decide), v3.gpr, em]
  show (t2.gpr .r3 ^^^ ((t2.gpr .r2 ^^^ t2.gpr .r3) &&& _)).toNat = _
  rw [ex, ey]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
  · rw [sel0r]; exact hx
  · rw [sel1r]; exact hy

end VG.Proof.Ed25519.Arm
end

/-! Canonical reduction preserves all working field elements. -/
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

theorem freezeRaw_ok {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) (a : Slot) :
    WP isa (.block (freeze a)) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = env s.mem b ∧ Lim t.mem (State.addr b) FR ∧
      V t.mem (State.addr b) FR = (env s.mem b a).val ∧
      ∀ (i : Slot) k, k < 16 → limb t.mem (State.addr b) (offset i) k = limb s.mem (State.addr b) (offset i) k := by
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
    funext fun i => congrArg VG.Proof.X25519.toFe (val16_congr (hs i)), hl', ?_, hs⟩
  · exact hframe.sub fun r hm => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hm]; exact Offset.sub _ (by decide) (by decide)⟩
  · rw [hv, V, val16_congr he]
    rfl

theorem freeze_ok {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) (a : Slot) :
    WP isa (.block (freeze a)) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = env s.mem b ∧ Lim t.mem (State.addr b) FR ∧
      V t.mem (State.addr b) FR = (env s.mem b a).val :=
  WP.mono (freezeRaw_ok hc hl a) fun _ ⟨hk, ht, he, hf, hv, _⟩ => ⟨hk, ht, he, hf, hv⟩

end VG.Proof.Ed25519.Arm
