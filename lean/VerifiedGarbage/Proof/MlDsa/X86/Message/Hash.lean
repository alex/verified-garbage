import VerifiedGarbage.Proof.MlDsa.X86.Message.Args
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.X86.SampleSetup

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: SHAKE256 through the sponge functions

Untrusted: everything here is checked by Lean. In `Ctx`: zeroing the Keccak
state at `X` (`zeroSt_ok`), and the calls of `vg_keccak_absorb` (keeping the
position it returns in `eax`), `vg_keccak_pad` and `vg_keccak_squeeze` on it,
with their working space at `X + 200` (`kabs_ok`, `kpad_ok`, `ksqz_ok`, from
ML-KEM's lemmas on their calls, `Proof/MlKem/X86/Keccak.lean`).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Only AbsArgs KBufs PadArgs absorb_pre absorb_post pad_pre pad_post squeeze_pre squeeze_post
  absorb_stack pad_stack squeeze_stack absorb_nosp pad_nosp squeeze_nosp toNat_ofNat32)
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

section
variable {L : Lay} {m₁ : Mem}

theorem x0 (L : Lay) : L.X + BitVec.ofNat 64 0 = L.X := BitVec.add_zero _
theorem x0' (L : Lay) : L.X32 + BitVec.ofNat 32 0 = L.X32 := BitVec.add_zero _

theorem st_ks : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.KS, 640⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 200) (k := 640) (by omega) (by omega) (by omega)
  simpa only [x0] using this

theorem st_mu : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.MU, 64⟩ := by
  have := Offset.disjoint L.X (d := 0) (n := 200) (e := 840) (k := 64) (by omega) (by omega) (by omega)
  simpa only [x0] using this

theorem mu_ks : Region.Disjoint ⟨L.MU, 64⟩ ⟨L.KS, 640⟩ :=
  Offset.disjoint L.X (d := 840) (n := 64) (e := 200) (k := 640) (by omega) (by omega) (by omega)

theorem w_st : Within ⟨L.ST, 200⟩ L.W := within_base _ (by omega)
theorem w_ks : Within ⟨L.KS, 640⟩ L.W := within_off _ (by omega)
theorem w_mu : Within ⟨L.MU, 64⟩ L.W := within_off _ (by omega)

theorem k_st (hL : L.Ok) : L.STK.Disjoint ⟨L.ST, 200⟩ := by
  have := hL.stk_x (e := 0) (k := 200) (by omega); simpa only [x0] using this
theorem k_ks (hL : L.Ok) : L.STK.Disjoint ⟨L.KS, 640⟩ := hL.stk_x (by omega)
theorem k_mu (hL : L.Ok) : L.STK.Disjoint ⟨L.MU, 64⟩ := hL.stk_x (by omega)

/-- The 40 bytes a call of a sponge function uses lie in `STK`. -/
theorem b40 (hL : L.Ok) : Region.Sub (below L.E1 40) L.STK := by
  have := hL.nSP; have := hL.hN
  exact below_sub (by omega) (by rw [Lay.E1, sub_toNat (by omega)]; omega)

theorem e40 (hL : L.Ok) : 40 ≤ L.E1.toNat := by
  have := hL.nSP; have := hL.hN
  rw [Lay.E1, sub_toNat (by omega)]; omega

theorem ks_eq (hL : L.Ok) : (L.X32 + BitVec.ofNat 32 200).setWidth 64 = L.KS := hL.xo (by decide)
theorem regKS (hL : L.Ok) : reg32 (L.X32 + BitVec.ofNat 32 200) 640 = ⟨L.KS, 640⟩ := by
  show (⟨_, 640⟩ : Region) = _; rw [ks_eq hL]
theorem mu_eq (hL : L.Ok) : (L.X32 + BitVec.ofNat 32 840).setWidth 64 = L.MU := hL.xo (by decide)

theorem cov_x (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    ∃ R ∈ L.rd ++ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R := by
  obtain ⟨R, hR, hw⟩ := hL.covX h₂; exact ⟨R, List.mem_append_right _ hR, hw⟩

/-- `Within` as ML-KEM's lemmas take it, in the body's writable regions. -/
theorem withinW {t : State} (hc : Ctx L m₁ t) {r : Region} (h : ∃ R ∈ L.wr, Within r R) :
    Proof.MlKem.X86.Within r t.wr := by
  obtain ⟨R, hR, o, hb, hl⟩ := h
  exact ⟨R, by rw [hc.wr]; exact List.mem_cons_of_mem _ hR, o, hb, hl⟩

theorem withinRW {t : State} (hc : Ctx L m₁ t) {r : Region} (h : ∃ R ∈ L.rd ++ L.wr, Within r R) :
    Proof.MlKem.X86.Within r (t.rd ++ t.wr) := by
  obtain ⟨R, hR, o, hb, hl⟩ := h
  refine ⟨R, ?_, o, hb, hl⟩
  rw [hc.rd, hc.wr]
  rcases List.mem_append.mp hR with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-- The Keccak state and the working space, for ML-KEM's lemmas. -/
theorem kbufs (hL : L.Ok) : KBufs L.E1 L.X32 (L.X32 + BitVec.ofNat 32 200) := by
  have := hL.x32_lt
  refine ⟨e40 hL, by omega, by rw [hL.x32_toNat (by omega)]; omega, ?_, ?_, ?_⟩
  · rw [regKS hL]; exact st_ks
  · exact (k_st hL).sub_left (b40 hL)
  · rw [regKS hL]; exact (k_ks hL).sub_left (b40 hL)

/-! ## Zeroing the state -/

theorem zeroSt_ok (hL : L.Ok) {t : State} (hc : Ctx L m₁ t) :
    WP isa (.block zeroSt) t fun t' => Ctx L m₁ t' ∧ Frame [⟨L.ST, 200⟩] t.mem t'.mem ∧
      stateAt t'.mem L.ST = Spec.Sha3.zero := by
  rw [zeroSt]
  refine wp_movi fun t1 u1 => ?_
  have e1 : t1.gpr .esi = L.X32 := by rw [u1.other _ (by decide), hc.esi]
  let Inv : Nat → State → Prop := fun k s => s.gpr = t1.gpr ∧ s.rd = t1.rd ∧ s.wr = t1.wr ∧
    Frame [⟨L.ST, 200⟩] t1.mem s.mem ∧ ∀ j < k, s.mem.readW (L.X + BitVec.ofNat 64 (4 * j)) 32 = 0
  refine WP.mono (wp_range_flatMap (M := isa) Inv (fun k s hk h => ?_) 50 (Nat.le_refl _) t1
    ⟨rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩) fun t' ⟨g, rd, wr, fr, z⟩ => ?_
  · have hb : s.gpr .esi = L.X32 := by rw [h.1, e1]
    have ea : addr L.X32 (4 * k) = L.X + BitVec.ofNat 64 (4 * k) := hL.xo (by omega)
    have hin : InRegions s.wr (addr L.X32 (4 * k)) 4 := by
      rw [ea, h.2.2.1, u1.wr, hc.wr]
      obtain ⟨R, hR, c⟩ := hL.inW (e := 4 * k) (k := 4) (by omega)
      exact ⟨R, List.mem_cons_of_mem _ hR, c⟩
    refine wp_stm (o := 4 * k) hb hin fun s' m => WP.block_nil ⟨by rw [m.gpr, h.1], by rw [m.rd, h.2.1], by rw [m.wr, h.2.2.1], ?_, fun j hj => ?_⟩
    · rw [m.mem, ea]
      exact h.2.2.2.1.writeW (List.mem_singleton_self _) _ (by
        have := Offset.contains_base L.X (d := 4 * k) (n := 4) (k := 200) (by omega) (by omega)
        simpa only [x0] using this)
    · rw [m.mem, ea, h.1, u1.gpr]
      by_cases e : j = k
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact h.2.2.2.2 j (by omega)
  · have hc1 : Ctx L m₁ t1 := hc.regs u1.rd u1.wr u1.mem (u1.other _ (by decide)) (u1.other _ (by decide))
    refine ⟨hc1.keep hL rd wr (by rw [g]) (by rw [g]) fr fun r hr => ?_, by rw [← u1.mem]; exact fr,
      Proof.MlKem.X86.Sample.stateAt_zero fun j hj => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact .inl w_st
    · have e := Mem.readW_byte t'.mem (L.X + BitVec.ofNat 64 (4 * (j / 4))) (i := j % 4) (by omega)
      rw [add_add, show 4 * (j / 4) + j % 4 = j by omega, z (j / 4) (by omega)] at e
      rw [e]
      apply BitVec.eq_of_toNat_eq
      simp

/-! ## Absorbing -/

/-- The arguments of a call of `vg_keccak_absorb`. -/
abbrev absArgs (src len pos : Arg) : List (Reg × Arg) :=
  [(.edx, pos), (.eax, .off oST), (.ecx, .imm 136), (.ebx, src), (.ebp, len), (.edi, .off oKS)]

/-- The position `vg_keccak_absorb` returns. -/
theorem absorb_eax {s s₂ : State} {E S D W : BitVec 32} {pos len : Nat} (hesp : s.gpr .esp = E)
    (ha : AbsArgs s S D W 136 pos len) (hE : 40 ≤ E.toNat) (hlen : len < 2 ^ 32) (hpos : pos < 2 ^ 32)
    {rd wr : List Region} (post : Proof.Sha3.absorbX86.post ((pushed Proof.MlKem.X86.rs6 s).callEntry.withRegions rd wr) s₂) :
    (s₂.gpr .eax).toNat = (pos + len) % 136 := by
  have fit : 4 * Proof.MlKem.X86.rs6.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have a1 : arg (pushed Proof.MlKem.X86.rs6 s).callEntry 1 = BitVec.ofNat 32 136 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed Proof.MlKem.X86.rs6 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a4 : arg (pushed Proof.MlKem.X86.rs6 s).callEntry 4 = BitVec.ofNat 32 len := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebp
  have := post.2
  simp only [arg_withRegions, a1, a2, a4, toNat_ofNat32 hlen, toNat_ofNat32 hpos,
    toNat_ofNat32 (show 136 < 2 ^ 32 by decide)] at this
  exact this

theorem kabs_ok (hL : L.Ok) {t : State} (hc : Ctx L m₁ t)
    {src len pos : Arg} (hok : argsOk L.nA (absArgs src len pos) = true)
    {dp : BitVec 32} {n q : Nat} (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 32 n)
    (hq : pos.val t = BitVec.ofNat 32 q) (hql : q < 136) (hnl : n < 2 ^ 32) (hfit : dp.toNat + n ≤ 2 ^ 32)
    (hin : ∃ R ∈ L.rd ++ L.wr, Within ⟨dp.setWidth 64, n⟩ R)
    (dS : Region.Disjoint ⟨dp.setWidth 64, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨dp.setWidth 64, n⟩ ⟨L.KS, 640⟩)
    (kD : L.STK.Disjoint ⟨dp.setWidth 64, n⟩) :
    WP isa (kabs src len pos) t fun t' => Ctx L m₁ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        Repr t'.mem L.ST 136 (msg ++ bytesAt t.mem (dp.setWidth 64) n)) ∧ (t'.gpr .eax).toNat = (q + n) % 136 := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t (hc.aOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx L m₁ t1 := hc.regs o.rd o.wr o.mem (o.gpr _ (by simp only [List.map_cons, List.map_nil]; decide))
    (o.gpr _ (by simp only [List.map_cons, List.map_nil]; decide))
  have e2 := hA (.edx, pos) (by simp)
  have e0 := hA (.eax, .off oST) (by simp)
  have e1 := hA (.ecx, .imm 136) (by simp)
  have e3 := hA (.ebx, src) (by simp)
  have e4 := hA (.ebp, len) (by simp)
  have e5 := hA (.edi, .off oKS) (by simp)
  simp only [Arg.val, hc.esi, oST, oKS, x0'] at e0 e1 e5
  rw [hq] at e2
  rw [hdp] at e3
  rw [hn] at e4
  have ha : AbsArgs t1 L.X32 dp (L.X32 + BitVec.ofNat 32 200) 136 q n := ⟨e0, e1, e2, e3, e4, e5⟩
  have hsp : t1.gpr .esp = L.E1 := hc1.esp
  have bD : (below L.E1 40).Disjoint (reg32 dp n) := kD.sub_left (b40 hL)
  have hE := e40 hL
  refine WP.callRet Proof.Sha3.X86.Stream.Absorb.absorb_verified.1 absorb_nosp (by decide) (by decide)
    (by rw [absorb_stack, hsp]; simp only [List.length_cons, List.length_nil]; omega)
    (absorb_pre hsp ha (kbufs hL) hfit dS (by rw [regKS hL]; exact dK) bD (by decide) hql hnl
      (withinRW hc1 hin) (withinW hc1 (by have := hL.covX (e := 0) (k := 200) (by omega); rwa [x0] at this))
      (withinW hc1 (by rw [regKS hL]; exact hL.covX (e := 200) (by omega))))
    fun s' hrd hwr hcs hf ⟨s₂, m₂, g₂, post⟩ => ?_
  have kb : ∀ r ∈ [reg32 L.X32 200, reg32 (L.X32 + BitVec.ofNat 32 200) 640, below L.E1 24] ++
      [below (t1.gpr .esp) (4 * Proof.MlKem.X86.rs6.length + stackUse Impl.Sha3.X86.Stream.absorb + 4)],
      Within r L.W ∨ Region.Sub r L.STK := fun r hr => by
    rw [absorb_stack, hsp] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
      List.length_nil] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl w_st
    · rw [regKS hL]; exact .inl w_ks
    · exact .inr fun x h => b40 hL x (below_sub (a := 24) (b := 40) (by omega) hE x h)
    · exact .inr (b40 hL)
  refine ⟨hc1.keep hL hrd hwr (hcs .esp (by decide)) (hcs .esi (by decide)) hf kb, ?_, fun msg hm hp => ?_, ?_⟩
  · rw [← o.mem]
    refine hf.sub fun r hr => ?_
    rw [absorb_stack, hsp] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
      List.length_nil] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · rw [regKS hL]; exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun x h => b40 hL x (below_sub (a := 24) (b := 40) (by omega) hE x h)⟩
    · exact ⟨_, by simp, b40 hL⟩
  · have := absorb_post hsp ha hE hnl (by decide) (by omega) (kbufs hL).bS bD ⟨s₂, m₂, post⟩ msg
      (by rw [o.mem]; exact hm) hp
    rwa [o.mem] at this
  · rw [← g₂]; exact absorb_eax hsp ha hE hnl (by omega) post

/-! ## Padding -/

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (pos : Arg) : List (Reg × Arg) :=
  [(.edx, pos), (.eax, .off oST), (.ecx, .imm 136), (.ebx, .imm 0x1f), (.edi, .off oKS)]

theorem kpad_ok (hL : L.Ok) {t : State} (hc : Ctx L m₁ t)
    {pos : Arg} (hok : argsOk L.nA (padArgs pos) = true) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 32 q) (hql : q < 136) :
    WP isa (kpad pos) t fun t' => Ctx L m₁ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        stateAt t'.mem L.ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t (hc.aOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx L m₁ t1 := hc.regs o.rd o.wr o.mem (o.gpr _ (by simp only [List.map_cons, List.map_nil]; decide))
    (o.gpr _ (by simp only [List.map_cons, List.map_nil]; decide))
  have e2 := hA (.edx, pos) (by simp)
  have e0 := hA (.eax, .off oST) (by simp)
  have e1 := hA (.ecx, .imm 136) (by simp)
  have e3 := hA (.ebx, .imm 0x1f) (by simp)
  have e4 := hA (.edi, .off oKS) (by simp)
  simp only [Arg.val, hc.esi, oST, oKS, x0'] at e0 e1 e3 e4
  rw [hq] at e2
  have ha : PadArgs t1 L.X32 (L.X32 + BitVec.ofNat 32 200) 136 q 0x1f := ⟨e0, e1, e2, e3, e4⟩
  have hsp : t1.gpr .esp = L.E1 := hc1.esp
  have hE := e40 hL
  refine WP.callWith Proof.Sha3.X86.Stream.Pad.pad_verified.1 pad_nosp (by decide) (by decide)
    (by rw [pad_stack, hsp]; simp only [List.length_cons, List.length_nil]; omega)
    (pad_pre hsp ha (kbufs hL) (by decide) hql
      (withinW hc1 (by have := hL.covX (e := 0) (k := 200) (by omega); rwa [x0] at this))
      (withinW hc1 (by rw [regKS hL]; exact hL.covX (e := 200) (by omega))))
    fun s' hrd hwr hcs hf ⟨s₂, m₂, post⟩ => ?_
  have kb : ∀ r ∈ [reg32 L.X32 200, reg32 (L.X32 + BitVec.ofNat 32 200) 640, below L.E1 20] ++
      [below (t1.gpr .esp) (4 * Proof.MlKem.X86.rs5.length + stackUse Impl.Sha3.X86.Stream.pad + 4)],
      Within r L.W ∨ Region.Sub r L.STK := fun r hr => by
    rw [pad_stack, hsp] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
      List.length_nil] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl w_st
    · rw [regKS hL]; exact .inl w_ks
    · exact .inr fun x h => b40 hL x (below_sub (a := 20) (b := 40) (by omega) hE x h)
    · exact .inr fun x h => b40 hL x (below_sub (a := 36) (b := 40) (by omega) hE x h)
  refine ⟨hc1.keep hL hrd hwr (hcs .esp (by decide)) (hcs .esi (by decide)) hf kb, ?_, fun msg hm hp => ?_⟩
  · rw [← o.mem]
    refine hf.sub fun r hr => ?_
    rw [pad_stack, hsp] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
      List.length_nil] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · rw [regKS hL]; exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun x h => b40 hL x (below_sub (a := 20) (b := 40) (by omega) hE x h)⟩
    · exact ⟨_, by simp, fun x h => b40 hL x (below_sub (a := 36) (b := 40) (by omega) hE x h)⟩
  · have := pad_post hsp ha hE (by decide) (by omega) (kbufs hL).bS ⟨s₂, m₂, post⟩ msg
      (by rw [o.mem]; exact hm) hp
    rw [this]; rfl

/-! ## Squeezing -/

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs : List (Reg × Arg) :=
  [(.eax, .off oST), (.ecx, .imm 136), (.edx, .imm 0), (.ebx, .off oMU), (.ebp, .imm 64), (.edi, .off oKS)]

theorem regMU (hL : L.Ok) : reg32 (L.X32 + BitVec.ofNat 32 840) 64 = ⟨L.MU, 64⟩ := by
  show (⟨_, 64⟩ : Region) = _; rw [mu_eq hL]

theorem ksqz_ok (hL : L.Ok) {t : State} (hc : Ctx L m₁ t) (hok : argsOk L.nA sqzArgs = true) :
    WP isa ksqz t fun t' => Ctx L m₁ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.MU, 64⟩, ⟨L.KS, 640⟩, L.STK] t.mem t'.mem ∧
      bytesAt t'.mem L.MU 64 = squeezeFrom 136 (stateAt t.mem L.ST) 0 64 := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t (hc.aOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx L m₁ t1 := hc.regs o.rd o.wr o.mem (o.gpr _ (by simp only [List.map_cons, List.map_nil]; decide))
    (o.gpr _ (by simp only [List.map_cons, List.map_nil]; decide))
  have e0 := hA (.eax, .off oST) (by simp)
  have e1 := hA (.ecx, .imm 136) (by simp)
  have e2 := hA (.edx, .imm 0) (by simp)
  have e3 := hA (.ebx, .off oMU) (by simp)
  have e4 := hA (.ebp, .imm 64) (by simp)
  have e5 := hA (.edi, .off oKS) (by simp)
  simp only [Arg.val, hc.esi, oST, oKS, oMU, x0'] at e0 e1 e2 e3 e4 e5
  have ha : AbsArgs t1 L.X32 (L.X32 + BitVec.ofNat 32 840) (L.X32 + BitVec.ofNat 32 200) 136 0 64 :=
    ⟨e0, e1, e2, e3, e4, e5⟩
  have hsp : t1.gpr .esp = L.E1 := hc1.esp
  have hE := e40 hL
  have hX := hL.x32_lt
  refine WP.callWith Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.1 squeeze_nosp (by decide) (by decide)
    (by rw [squeeze_stack, hsp]; simp only [List.length_cons, List.length_nil]; omega)
    (squeeze_pre hsp ha (kbufs hL) (by rw [hL.x32_toNat (by omega)]; omega) (by rw [regMU hL]; exact st_mu)
      (by rw [regMU hL, regKS hL]; exact mu_ks) (by rw [regMU hL]; exact (k_mu hL).sub_left (b40 hL))
      (by decide) (by decide) (by decide)
      (withinW hc1 (by have := hL.covX (e := 0) (k := 200) (by omega); rwa [x0] at this))
      (withinW hc1 (by rw [regMU hL]; exact hL.covX (e := 840) (by omega)))
      (withinW hc1 (by rw [regKS hL]; exact hL.covX (e := 200) (by omega))))
    fun s' hrd hwr hcs hf ⟨s₂, m₂, post⟩ => ?_
  have kb : ∀ r ∈ [reg32 L.X32 200, reg32 (L.X32 + BitVec.ofNat 32 840) 64, reg32 (L.X32 + BitVec.ofNat 32 200) 640,
      below L.E1 24] ++
      [below (t1.gpr .esp) (4 * Proof.MlKem.X86.rs6.length + stackUse Impl.Sha3.X86.Stream.squeeze + 4)],
      Within r L.W ∨ Region.Sub r L.STK := fun r hr => by
    rw [squeeze_stack, hsp] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
      List.length_nil] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact .inl w_st
    · rw [regMU hL]; exact .inl w_mu
    · rw [regKS hL]; exact .inl w_ks
    · exact .inr fun x h => b40 hL x (below_sub (a := 24) (b := 40) (by omega) hE x h)
    · exact .inr (b40 hL)
  refine ⟨hc1.keep hL hrd hwr (hcs .esp (by decide)) (hcs .esi (by decide)) hf kb, ?_, ?_⟩
  · rw [← o.mem]
    refine hf.sub fun r hr => ?_
    rw [squeeze_stack, hsp] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
      List.length_nil] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · rw [regMU hL]; exact ⟨_, by simp, fun _ h => h⟩
    · rw [regKS hL]; exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun x h => b40 hL x (below_sub (a := 24) (b := 40) (by omega) hE x h)⟩
    · exact ⟨_, by simp, b40 hL⟩
  · have := (squeeze_post hsp ha hE (by decide) (by decide) (by decide) (kbufs hL).bS ⟨s₂, m₂, post⟩).1
    rw [mu_eq hL, o.mem] at this
    exact this

end

end VG.Proof.MlDsa.X86.Message
