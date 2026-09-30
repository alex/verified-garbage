import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Ntt

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_inv_ntt`

Untrusted: everything here is checked by Lean. As `vg_mldsa_ntt`
(`Ntt.lean`), with the negated zetas, from the last, and `bflyInv_spec`:
the eight layers are those of `NTT⁻¹` (`nttInvLayer`); then every
coefficient is multiplied by `8347681 = 256⁻¹ mod q` (`scale_ok`), which
`nttInv_eq_layers` says is `NTT⁻¹`.
-/

namespace VG.Proof.MlDsa.Arm.Arith.NttInv

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arm.Arith.Ntt
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr inRegions_of)
open VG.Proof.MlDsa.Arm.Arith.AddSub (reduced_zero)

/-! ## The layers -/

/-- The chain of zeta indices of the layers `ls` of `NTT⁻¹`, from `k`. -/
def ChainInv : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 256 / len - 1 ∧ ChainInv (128 / len - 1) ls

theorem lens_inv : ∀ len ∈ nttInvLens, len ∈ nttLens ∧ 128 / len ≤ 256 / len - 1 ∧ 256 / len ≤ 256 ∧
    256 / len = 2 * (128 / len) := by decide

theorem negZetaTab_of : TabOf negZetaTab (fun m => -zetas m) := fun k _ => negZetaNat_eq k

theorem negZetaTab_lt : ∀ k < 256, negZetaTab k < q := fun k _ => negZetaNat_lt k

theorem lays_ok {s₁ : State} (hp : PreB s₁) :
    ∀ (ls : List Nat) (G : Poly) (k : Nat) (s : State), (∀ len ∈ ls, len ∈ nttInvLens) → ChainInv k ls →
      LI negZetaTab s₁ G k s →
      WP isa (nttInvLays ls) s fun s' => ∃ k', LI negZetaTab s₁ (ls.foldl nttInvLayer G) k' s'
  | [], G, k, s, _, _, hI => WP.block_nil ⟨k, hI⟩
  | len :: ls, G, k, s, hls, ⟨hk, hc⟩, hI => by
    obtain ⟨hlen, h1, h2, h3⟩ := lens_inv len (hls len (List.mem_cons_self ..))
    have hl0 := (lens_facts len hlen).2.2.2.1
    refine WP.seq (WP.mono (lay_ok bflyInv_spec negZetaTab_of hp.fitF hp.fitS hlen .sub (.inr rfl)
      (fun c => 256 / len - 1 - c) (fun c hc => by omega)
      (fun c hc => by
        simp only [nextZ, reduceCtorEq, ite_false]
        rw [show 4 * (256 / len - 1 - c) = 4 * (256 / len - 1 - (c + 1)) + 4 by omega, BitVec.ofNat_add,
          ← BitVec.add_assoc]
        exact BitVec.add_sub_cancel _ _)
      G s hI.r0 (by rw [hI.r1, hk]; rfl) hI.r4 hI.poly (by rw [hI.keep.wr]; exact hp.wF)
      (by rw [hI.keep.wr]; exact List.mem_append_right _ hp.wS) hp.fs.symm hI.tab)
      fun s' ⟨hP, hf, h0, h1', hk'⟩ => ?_)
    refine lays_ok hp ls _ (128 / len - 1) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf h0 (by rw [h1']; congr 3; omega) hk' hp.fs.symm)

theorem chain_inv : ChainInv 255 nttInvLens := by simp only [nttInvLens, ChainInv]; decide

/-! ## The scaling -/

/-- The scaling after the load and `mulz`. -/
def scaleRest : List Instr :=
  csub .r9 .r12 .r4 ++ [.str .r9 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]

theorem scale_split : scaleBody = ([.ldr .r8 .r0 0] : List Instr) ++ (mulz .r9 .r8 .r12 ++ scaleRest) := by
  simp only [scaleBody, scaleRest, List.append_assoc, List.cons_append, List.nil_append]

section
variable {s : State} {x c v : BitVec 32} (h0 : s.gpr .r0 = x) (h3 : s.gpr .r3 = c) (h4 : s.gpr .r4 = Qw)
  (h9 : s.gpr .r9 = v) (oA : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h3 h4 h9 oA

theorem scaleRest_ok :
    WP isa (.block scaleRest) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0)) (bcsub v) ∧
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ Keep bflyKeep s s' := by
  run_block [scaleRest, csub, fixup, bcsub, bfix, h0, h3, h4, h9, oA]
  keep_simp

end

/-- The multiplier of the scaling. -/
abbrev cInv : Zq := 8347681

/-- After `t` coefficients of the polynomial `G` at `p` are scaled. -/
structure SInv (p : BitVec 32) (m₀ : Mem) (G : Poly) (s₀ : State) (t : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = p + BitVec.ofNat 32 (4 * t)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (256 - t))
  zeta : ZetaIn cInv s
  keep : Keep bflyKeep s₀ s
  frame : Frame [polyRegion (State.addr p)] m₀ s.mem
  coeff : ∀ j < 256, coeffAt s.mem (State.addr p) j =
    if j < t then BitVec.ofNat 32 (G[j]! * cInv).val else coeffAt m₀ (State.addr p) j

theorem scale_step {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {m₀ : Mem} {G : Poly}
    (hG : PolyIs m₀ (State.addr p) G) {s₀ : State} (hw : polyRegion (State.addr p) ∈ s₀.wr) {t : Nat}
    (ht : t < 256) {s : State} (h : SInv p m₀ G s₀ t s) :
    WP isa (.block scaleBody) s fun s' => SInv p m₀ G s₀ (t + 1) s' ∧ s'.z = decide (t + 1 = 256) := by
  obtain ⟨z4, z5, z6, z7⟩ := h.zeta
  have htn : t < n := by rw [n_eq]; exact ht
  have eA := addr_at0 hp ht
  have hw' : polyRegion (State.addr p) ∈ s.wr := by rw [h.keep.wr]; exact hw
  have hv : s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 0)) 32 = BitVec.ofNat 32 (G[t]!).val := by
    rw [h.r0, eA, ← coeffAt_eq, h.coeff t ht, ite_eq_right (Nat.lt_irrefl t), coeffAt_eq, word_val hG ht]
  rw [scale_split, WP.block_append_iff]
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, exec_ldr (by omega) (by rw [h.r0, eA]; exact rd_at hw' htn), runStep_some, runBlock_nil], ?_⟩
  rw [WP.block_append_iff, hv]
  refine WP.mono (mulz_ok (s := s.setReg .r8 _) (b := BitVec.ofNat 32 (G[t]!).val)
    (z₂ := BitVec.ofNat 32 cInv.val >>> 14) (z₁ := BitVec.ofNat 32 cInv.val <<< 18 >>> 25)
    (z₀ := BitVec.ofNat 32 cInv.val <<< 25 >>> 25) (by simp [State.setReg, z4]) (by simp [State.setReg, z5])
    (by simp [State.setReg, z6]) (by simp [State.setReg, z7]) (by simp [State.setReg]))
    fun s₁ ⟨e9, eo, m₁, rd₁, wr₁, sp₁⟩ => ?_
  have g : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r12 → s₁.gpr r = s.gpr r := fun r a8 a9 a12 => by
    rw [eo r a9 a12]; simp [State.setReg, a8]
  have nk : ∀ r ∈ bflyKeep, r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r12 := by decide
  have k₁ : Keep bflyKeep s s₁ := ⟨fun r hr => g r (nk r hr).1 (nk r hr).2.1 (nk r hr).2.2, rd₁, wr₁, sp₁⟩
  refine WP.mono (scaleRest_ok ((g _ (by decide) (by decide) (by decide)).trans h.r0)
    ((g _ (by decide) (by decide) (by decide)).trans h.r3) ((g _ (by decide) (by decide) (by decide)).trans z4) e9
    (by rw [eA, wr₁]; exact wr_at hw' htn)) fun s' ⟨hm, r0, r3, hzf, k₂⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_next p t
  · rw [r3]; exact count_sub (k := 1) ht
  · have k := k₁.trans k₂
    exact ⟨(k.gpr .r4 (by decide)).trans z4, (k.gpr .r5 (by decide)).trans z5, (k.gpr .r6 (by decide)).trans z6,
      (k.gpr .r7 (by decide)).trans z7⟩
  · exact (h.keep.trans k₁).trans k₂
  · rw [hm, m₁, eA]
    exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ htn)
  · intro j hj
    rw [hm, m₁, eA, mulz_val, coeffAt_writeW _ _ (show j < n by rw [n_eq]; exact hj) htn]
    simp only [State.setReg]
    rw [h.coeff j hj]
    by_cases e : t = j
    · subst e; rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self t), Fin.mul_comm]
    · rw [ite_eq_right e]
      by_cases hj' : j < t
      · rw [ite_eq_left hj', ite_eq_left (by omega)]
      · rw [ite_eq_right hj', ite_eq_right (by omega)]
  · rw [hzf]; exact count_z (k := 1) ht (by decide) (by decide)

theorem scale_ok {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {G : Poly} {s : State}
    (hG : PolyIs s.mem (State.addr p) G) (hw : polyRegion (State.addr p) ∈ s.wr) (h0 : s.gpr .r0 = p)
    (h4 : s.gpr .r4 = Qw) :
    WP isa (.seq (.block [.movw .r5 509, .movw .r6 64, .movw .r7 33, .mov .r3 (.imm 256)])
      (.loop (.block scaleBody) .ne)) s fun s' =>
      PolyIs s'.mem (State.addr p) (G.map (· * cInv)) ∧ Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        Keep [.r4, .r11, .lr] s s' := by
  refine WP.seq (WP.mono (Q := fun s₁ => SInv p s.mem G s₁ 0 s₁ ∧ Keep [.r4, .r11, .lr] s s₁) ?_
    fun s₁ ⟨h₁, k₁⟩ => ?_)
  · run_block [h0, h4]
    refine ⟨⟨by simp [h0], by simp, ⟨by simp [h4], by simp; decide, by simp; decide, by simp; decide⟩, Keep.refl _ _,
      Frame.refl _ _, fun j _ => by simp⟩, ?_⟩
    keep_simp
  · refine wp_loop_ne (SInv p s.mem G s₁) (N := 256) (by decide)
      (fun t ht s' h => scale_step hp hG (by rw [k₁.wr]; exact hw) ht h) (fun s' h => ?_) h₁
    refine ⟨polyIs_of_toNat fun j hj => ?_, h.frame, k₁.trans (h.keep.mono (by decide))⟩
    rw [h.coeff j (by rw [n_eq] at hj; exact hj), ite_eq_left (by rw [n_eq] at hj; exact hj), toNat_val,
      map_mul_get _ _ hj]

theorem pre_of {s : State} (h : (Spec.MlDsa.nttInvContract Arm.abi 28).pre s) : PreE s := by
  sig_pre [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Arith.nttInv s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (F s) (Spec.MlDsa.nttInv (polyAt s.mem (F s))) := by
  refine WP.mono (wp_saving nttSaved _ (W := [polyRegion (F s), polyRegion (S s)])
    (fun s₂ => s₂.gpr .r11 = s.gpr .r11 ∧ s₂.gpr .lr = s.gpr .lr ∧
      PolyIs s₂.mem (F s) (Spec.MlDsa.nttInv (polyAt s.mem (F s))))
    s hp.sp (stack_disj hp) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨h11, hlr, hq⟩, hm, _, hsp, _, hg⟩ => ⟨preserved_of hg h11 hlr, hsp, hm ▸ hq⟩
  obtain ⟨hpB, eP, eF, eS⟩ := pre_entry hp hE
  refine WP.seq (WP.mono (pro_ok hpB negZetaTab negZetaTab_lt 1020 255 rfl (by decide)) fun s₂ hI => ?_)
  refine WP.seq (WP.mono (lays_ok hpB nttInvLens _ 255 s₂ (fun _ h => h) chain_inv hI) fun s₃ ⟨k, hI'⟩ => ?_)
  refine WP.mono (scale_ok hpB.fitF hI'.poly (by rw [hI'.keep.wr]; exact hpB.wF) hI'.r0 hI'.r4)
    fun s₄ ⟨hP, hf, k₄⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [← eF, ← eS]; exact hI'.frame.trans (hf.mono (by simp))
  · rw [k₄.gpr .r11 (by decide), hI'.keep.gpr .r11 (by decide)]; exact congrFun hE.gpr _
  · rw [k₄.gpr .lr (by decide), hI'.keep.gpr .lr (by decide)]; exact congrFun hE.gpr _
  · rw [← eP, ← eF, VG.Proof.MlDsa.Arith.nttInv_eq_layers]; exact hP

theorem verified : Verified Arm.target Impl.MlDsa.Arm.Arith.nttInv (Spec.MlDsa.nttInvContract Arm.abi 28) := by
  refine ⟨fun s hs => ?_, ct_of_saving nttSaved _ [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi,
        Arm.argRegs, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Arith.NttInv
