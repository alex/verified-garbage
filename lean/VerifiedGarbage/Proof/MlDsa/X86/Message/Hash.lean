import VerifiedGarbage.Proof.MlDsa.X86.Message.Call
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
open VG.Proof.MlKem.X86 (Piece Only AbsArgs KBufs PadArgs absorb_pre absorb_post pad_pre pad_post squeeze_pre squeeze_post
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

theorem regMU (hL : L.Ok) : reg32 (L.X32 + BitVec.ofNat 32 840) 64 = ⟨L.MU, 64⟩ := by
  show (⟨_, 64⟩ : Region) = _; rw [mu_eq hL]

theorem SetPost.ctx {n : Nat} {as : List (Reg × Arg)} (hok : argsOk n as = true) {s s₁ : State}
    (hs : SetPost as s s₁) (hc : Ctx L m₁ s) : Ctx L m₁ s₁ :=
  hc.regs hs.2.rd hs.2.wr hs.2.mem (hs.esp hok) (hs.esi hok)

end

/-! ## As pieces -/

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {lay : State → Lay} {A B : State → State → Prop}

theorem zeroSt_piece (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → CtxO lay s₀ s' → Frame [⟨(lay s₀).ST, 200⟩] s.mem s'.mem →
      stateAt s'.mem (lay s₀).ST = Spec.Sha3.zero → B s₀ s') :
    Piece Pre Pub A B (.block zeroSt) :=
  Piece.taint [.esi] (fun s₀ s h₀ ha => by
      have h := hA s₀ s h₀ ha
      exact (zeroSt_ok h.ok h.ctx).mono fun s' ⟨c, f, z⟩ => hQ s₀ s s' h₀ ha ⟨h.ok, c⟩ f z)
    (fun s₀ s₀' s s' h₀ h₀' hq ha ha' r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [(hA s₀ s h₀ ha).ctx.esi, (hA s₀' s' h₀' ha').ctx.esi, (hpub s₀ s₀' h₀ h₀' hq).x]) (by taint_decide)

/-- The stack the sponge functions' calls use. -/
theorem kb_stk {L : Lay} (hL : L.Ok) {a : Nat} (ha : a ≤ 40) : Region.Sub (below L.E1 a) L.STK :=
  fun x h => b40 hL x (below_sub (a := a) (b := 40) ha (e40 hL) x h)

/-- A call of `vg_keccak_absorb`, continuing the message at the position `q s₀`
with the `n s₀` bytes at `dp s₀`. -/
theorem kabs_piece (src len pos : Arg) (dp : State → BitVec 32) (n q : State → Nat)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs (absArgs src len pos))) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → argsOk (lay s₀).nA (absArgs src len pos) = true)
    (hv : ∀ s₀ s, Pre s₀ → A s₀ s → src.val s = dp s₀ ∧ len.val s = BitVec.ofNat 32 (n s₀) ∧
      pos.val s = BitVec.ofNat 32 (q s₀))
    (hdn : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → dp s₀ = dp s₀' ∧ n s₀ = n s₀' ∧ q s₀ = q s₀')
    (hb : ∀ s₀ s, Pre s₀ → A s₀ s → q s₀ < 136 ∧ n s₀ < 2 ^ 32 ∧ (dp s₀).toNat + n s₀ ≤ 2 ^ 32 ∧
      (∃ R ∈ (lay s₀).rd ++ (lay s₀).wr, Within ⟨(dp s₀).setWidth 64, n s₀⟩ R) ∧
      Region.Disjoint ⟨(dp s₀).setWidth 64, n s₀⟩ ⟨(lay s₀).ST, 200⟩ ∧
      Region.Disjoint ⟨(dp s₀).setWidth 64, n s₀⟩ ⟨(lay s₀).KS, 640⟩ ∧
      (lay s₀).STK.Disjoint ⟨(dp s₀).setWidth 64, n s₀⟩)
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → CtxO lay s₀ s' →
      Frame [⟨(lay s₀).ST, 200⟩, ⟨(lay s₀).KS, 640⟩, (lay s₀).STK] s.mem s'.mem →
      (∀ msg, Repr s.mem (lay s₀).ST 136 msg → q s₀ = msg.length % 136 →
        Repr s'.mem (lay s₀).ST 136 (msg ++ bytesAt s.mem ((dp s₀).setWidth 64) (n s₀))) →
      (s'.gpr .eax).toNat = (q s₀ + n s₀) % 136 → B s₀ s') :
    Piece Pre Pub A B (kabs src len pos) := by
  have hargs : ∀ s₀ s s₁, Pre s₀ → A s₀ s → SetPost (absArgs src len pos) s s₁ →
      AbsArgs s₁ (lay s₀).X32 (dp s₀) ((lay s₀).X32 + BitVec.ofNat 32 200) 136 (q s₀) (n s₀) := by
    intro s₀ s s₁ h₀ ha hs
    have hc := (hA s₀ s h₀ ha).ctx
    obtain ⟨v₁, v₂, v₃⟩ := hv s₀ s h₀ ha
    have e2 := hs.1 (.edx, pos) (by simp)
    have e0 := hs.1 (.eax, .off oST) (by simp)
    have e1 := hs.1 (.ecx, .imm 136) (by simp)
    have e3 := hs.1 (.ebx, src) (by simp)
    have e4 := hs.1 (.ebp, len) (by simp)
    have e5 := hs.1 (.edi, .off oKS) (by simp)
    simp only [Arg.val, hc.esi, oST, oKS, x0'] at e0 e1 e5
    rw [v₃] at e2
    rw [v₁] at e3
    rw [v₂] at e4
    exact ⟨e0, e1, e2, e3, e4, e5⟩
  refine argsRet_piece Proof.Sha3.X86.Stream.Absorb.absorb_verified.1
    Proof.Sha3.X86.Stream.Absorb.absorb_verified.2.1 absorb_nosp (by decide) (by decide) tt hpub hA hok
    (fun s₀ => [reg32 (dp s₀) (n s₀)])
    (fun s₀ => [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 24])
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => ?_)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · obtain ⟨d₁, d₂, -⟩ := hdn s₀ s₀' h₀ h₀' hq
    have hp := hpub s₀ s₀' h₀ h₀' hq
    refine ⟨by rw [d₁, d₂], ?_⟩
    simp only [Lay.E1, hp.x, hp.sp]
  · have := e40 (hA s₀ s h₀ ha).ok
    rw [absorb_stack]; simp only [List.length_cons, List.length_nil]; omega
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    have hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    obtain ⟨hql, hnl, hfit, hin, dS, dK, kD⟩ := hb s₀ s h₀ ha
    exact absorb_pre hc1.esp (hargs s₀ s s₁ h₀ ha hs) (kbufs hL) hfit dS (by rw [regKS hL]; exact dK)
      (kD.sub_left (b40 hL)) (by decide) hql hnl (withinRW hc1 hin)
      (withinW hc1 (by have := hL.covX (e := 0) (k := 200) (by omega); rwa [x0] at this))
      (withinW hc1 (by rw [regKS hL]; exact hL.covX (e := 200) (by omega)))
  · have a := hargs s₀ s s₁ h₀ ha hs
    have a' := hargs s₀' s' s₁' h₀' ha' hs'
    obtain ⟨d₁, d₂, d₃⟩ := hdn s₀ s₀' h₀ h₀' hq
    have hp := hpub s₀ s₀' h₀ h₀' hq
    rw [← d₁, ← d₂, ← d₃, ← hp.x] at a'
    have hsp : s₁.gpr .esp = s₁'.gpr .esp := by
      rw [hs.esp (hok s₀ h₀), hs'.esp (hok s₀' h₀'), (hA s₀ s h₀ ha).ctx.esp, (hA s₀' s' h₀' ha').ctx.esp,
        Lay.E1, Lay.E1, hp.sp]
    have hE : 40 ≤ (s₁.gpr .esp).toNat := by
      rw [hs.esp (hok s₀ h₀), (hA s₀ s h₀ ha).ctx.esp]; exact e40 (hA s₀ s h₀ ha).ok
    exact Proof.MlKem.X86.args6_eq hE hsp (Proof.MlKem.X86.absArgs_eq a a') _ _
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    have hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    have a := hargs s₀ s s₁ h₀ ha hs
    obtain ⟨hql, hnl, -, -, -, -, kD⟩ := hb s₀ s h₀ ha
    have hsp : s₁.gpr .esp = (lay s₀).E1 := hc1.esp
    have hE := e40 hL
    have kb : ∀ r ∈ [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 24] ++
        [below (s₁.gpr .esp) (4 * Proof.MlKem.X86.rs6.length + stackUse Impl.Sha3.X86.Stream.absorb + 4)],
        Within r (lay s₀).W ∨ Region.Sub r (lay s₀).STK := fun r hr => by
      rw [absorb_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inl w_st
      · rw [regKS hL]; exact .inl w_ks
      · exact .inr (kb_stk hL (by omega))
      · exact .inr (b40 hL)
    obtain ⟨s₂, m₂, g₂, post⟩ := post
    refine hQ s₀ s s' h₀ ha ⟨hL, hc1.keep hL e₁ e₂ (e₃ .esp (by decide)) (e₃ .esi (by decide)) fr kb⟩ ?_
      (fun msg hm hp => ?_) ?_
    · rw [← hs.2.mem]
      refine fr.sub fun r hr => ?_
      rw [absorb_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · rw [regKS hL]; exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, kb_stk hL (by omega)⟩
      · exact ⟨_, by simp, b40 hL⟩
    · have := absorb_post hsp a hE hnl (by decide) (by omega) (kbufs hL).bS (kD.sub_left (b40 hL))
        ⟨s₂, m₂, post⟩ msg (by rw [hs.2.mem]; exact hm) hp
      rwa [hs.2.mem] at this
    · rw [← g₂]; exact absorb_eax hsp a hE hnl (by omega) post

/-! ## Padding -/

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (pos : Arg) : List (Reg × Arg) :=
  [(.edx, pos), (.eax, .off oST), (.ecx, .imm 136), (.ebx, .imm 0x1f), (.edi, .off oKS)]

/-- A call of `vg_keccak_pad` at the position `q s₀`, with the suffix of SHAKE. -/
theorem kpad_piece (pos : Arg) (q : State → Nat) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs (padArgs pos))) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → argsOk (lay s₀).nA (padArgs pos) = true)
    (hv : ∀ s₀ s, Pre s₀ → A s₀ s → pos.val s = BitVec.ofNat 32 (q s₀))
    (hdn : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → q s₀ = q s₀')
    (hb : ∀ s₀ s, Pre s₀ → A s₀ s → q s₀ < 136)
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → CtxO lay s₀ s' →
      Frame [⟨(lay s₀).ST, 200⟩, ⟨(lay s₀).KS, 640⟩, (lay s₀).STK] s.mem s'.mem →
      (∀ msg, Repr s.mem (lay s₀).ST 136 msg → q s₀ = msg.length % 136 →
        stateAt s'.mem (lay s₀).ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) → B s₀ s') :
    Piece Pre Pub A B (kpad pos) := by
  have hargs : ∀ s₀ s s₁, Pre s₀ → A s₀ s → SetPost (padArgs pos) s s₁ →
      PadArgs s₁ (lay s₀).X32 ((lay s₀).X32 + BitVec.ofNat 32 200) 136 (q s₀) 0x1f := by
    intro s₀ s s₁ h₀ ha hs
    have hc := (hA s₀ s h₀ ha).ctx
    have e2 := hs.1 (.edx, pos) (by simp)
    have e0 := hs.1 (.eax, .off oST) (by simp)
    have e1 := hs.1 (.ecx, .imm 136) (by simp)
    have e3 := hs.1 (.ebx, .imm 0x1f) (by simp)
    have e4 := hs.1 (.edi, .off oKS) (by simp)
    simp only [Arg.val, hc.esi, oST, oKS, x0'] at e0 e1 e3 e4
    rw [hv s₀ s h₀ ha] at e2
    exact ⟨e0, e1, e2, e3, e4⟩
  refine argsWith_piece Proof.Sha3.X86.Stream.Pad.pad_verified.1
    Proof.Sha3.X86.Stream.Pad.pad_verified.2.1 pad_nosp (by decide) (by decide) tt hpub hA hok
    (fun _ => [])
    (fun s₀ => [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 20])
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => ?_)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · have hp := hpub s₀ s₀' h₀ h₀' hq
    refine ⟨rfl, ?_⟩
    simp only [Lay.E1, hp.x, hp.sp]
  · have := e40 (hA s₀ s h₀ ha).ok
    rw [pad_stack]; simp only [List.length_cons, List.length_nil]; omega
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    have hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    exact pad_pre hc1.esp (hargs s₀ s s₁ h₀ ha hs) (kbufs hL) (by decide) (hb s₀ s h₀ ha)
      (withinW hc1 (by have := hL.covX (e := 0) (k := 200) (by omega); rwa [x0] at this))
      (withinW hc1 (by rw [regKS hL]; exact hL.covX (e := 200) (by omega)))
  · have a := hargs s₀ s s₁ h₀ ha hs
    have a' := hargs s₀' s' s₁' h₀' ha' hs'
    have hp := hpub s₀ s₀' h₀ h₀' hq
    rw [← hdn s₀ s₀' h₀ h₀' hq, ← hp.x] at a'
    have hsp : s₁.gpr .esp = s₁'.gpr .esp := by
      rw [hs.esp (hok s₀ h₀), hs'.esp (hok s₀' h₀'), (hA s₀ s h₀ ha).ctx.esp, (hA s₀' s' h₀' ha').ctx.esp,
        Lay.E1, Lay.E1, hp.sp]
    have hE : 40 ≤ (s₁.gpr .esp).toNat := by
      rw [hs.esp (hok s₀ h₀), (hA s₀ s h₀ ha).ctx.esp]; exact e40 (hA s₀ s h₀ ha).ok
    exact Proof.MlKem.X86.args5_eq hE hsp (Proof.MlKem.X86.padArgs_eq a a') _ _
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    have hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    have a := hargs s₀ s s₁ h₀ ha hs
    have hsp : s₁.gpr .esp = (lay s₀).E1 := hc1.esp
    have hE := e40 hL
    have kb : ∀ r ∈ [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 20] ++
        [below (s₁.gpr .esp) (4 * Proof.MlKem.X86.rs5.length + stackUse Impl.Sha3.X86.Stream.pad + 4)],
        Within r (lay s₀).W ∨ Region.Sub r (lay s₀).STK := fun r hr => by
      rw [pad_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inl w_st
      · rw [regKS hL]; exact .inl w_ks
      · exact .inr (kb_stk hL (by omega))
      · exact .inr (kb_stk hL (by omega))
    obtain ⟨s₂, m₂, post⟩ := post
    refine hQ s₀ s s' h₀ ha ⟨hL, hc1.keep hL e₁ e₂ (e₃ .esp (by decide)) (e₃ .esi (by decide)) fr kb⟩ ?_
      (fun msg hm hp => ?_)
    · rw [← hs.2.mem]
      refine fr.sub fun r hr => ?_
      rw [pad_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · rw [regKS hL]; exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, kb_stk hL (by omega)⟩
      · exact ⟨_, by simp, kb_stk hL (by omega)⟩
    · have := pad_post hsp a hE (by decide) (by have := hb s₀ s h₀ ha; omega) (kbufs hL).bS ⟨s₂, m₂, post⟩ msg
        (by rw [hs.2.mem]; exact hm) hp
      rw [this]; rfl

/-! ## Squeezing -/

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs : List (Reg × Arg) :=
  [(.eax, .off oST), (.ecx, .imm 136), (.edx, .imm 0), (.ebx, .off oMU), (.ebp, .imm 64), (.edi, .off oKS)]

/-- A call of `vg_keccak_squeeze`, of 64 bytes to `μ`. -/
theorem ksqz_piece (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → argsOk (lay s₀).nA sqzArgs = true)
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → CtxO lay s₀ s' →
      Frame [⟨(lay s₀).ST, 200⟩, ⟨(lay s₀).MU, 64⟩, ⟨(lay s₀).KS, 640⟩, (lay s₀).STK] s.mem s'.mem →
      bytesAt s'.mem (lay s₀).MU 64 = squeezeFrom 136 (stateAt s.mem (lay s₀).ST) 0 64 → B s₀ s') :
    Piece Pre Pub A B ksqz := by
  have hargs : ∀ s₀ s s₁, Pre s₀ → A s₀ s → SetPost sqzArgs s s₁ →
      AbsArgs s₁ (lay s₀).X32 ((lay s₀).X32 + BitVec.ofNat 32 840) ((lay s₀).X32 + BitVec.ofNat 32 200) 136 0 64 := by
    intro s₀ s s₁ h₀ ha hs
    have hc := (hA s₀ s h₀ ha).ctx
    have e0 := hs.1 (.eax, .off oST) (by simp)
    have e1 := hs.1 (.ecx, .imm 136) (by simp)
    have e2 := hs.1 (.edx, .imm 0) (by simp)
    have e3 := hs.1 (.ebx, .off oMU) (by simp)
    have e4 := hs.1 (.ebp, .imm 64) (by simp)
    have e5 := hs.1 (.edi, .off oKS) (by simp)
    simp only [Arg.val, hc.esi, oST, oKS, oMU, x0'] at e0 e1 e2 e3 e4 e5
    exact ⟨e0, e1, e2, e3, e4, e5⟩
  refine argsWith_piece Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.1
    Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.2.1 squeeze_nosp (by decide) (by decide) (by taint_decide) hpub hA hok
    (fun _ => [])
    (fun s₀ => [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 840) 64,
      reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 24])
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => ?_)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · have hp := hpub s₀ s₀' h₀ h₀' hq
    refine ⟨rfl, ?_⟩
    simp only [Lay.E1, hp.x, hp.sp]
  · have := e40 (hA s₀ s h₀ ha).ok
    rw [squeeze_stack]; simp only [List.length_cons, List.length_nil]; omega
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    have hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    have hX := hL.x32_lt
    exact squeeze_pre hc1.esp (hargs s₀ s s₁ h₀ ha hs) (kbufs hL) (by rw [hL.x32_toNat (by omega)]; omega)
      (by rw [regMU hL]; exact st_mu) (by rw [regMU hL, regKS hL]; exact mu_ks)
      (by rw [regMU hL]; exact (k_mu hL).sub_left (b40 hL)) (by decide) (by decide) (by decide)
      (withinW hc1 (by have := hL.covX (e := 0) (k := 200) (by omega); rwa [x0] at this))
      (withinW hc1 (by rw [regMU hL]; exact hL.covX (e := 840) (by omega)))
      (withinW hc1 (by rw [regKS hL]; exact hL.covX (e := 200) (by omega)))
  · have a := hargs s₀ s s₁ h₀ ha hs
    have a' := hargs s₀' s' s₁' h₀' ha' hs'
    have hp := hpub s₀ s₀' h₀ h₀' hq
    rw [← hp.x] at a'
    have hsp : s₁.gpr .esp = s₁'.gpr .esp := by
      rw [hs.esp (hok s₀ h₀), hs'.esp (hok s₀' h₀'), (hA s₀ s h₀ ha).ctx.esp, (hA s₀' s' h₀' ha').ctx.esp,
        Lay.E1, Lay.E1, hp.sp]
    have hE : 40 ≤ (s₁.gpr .esp).toNat := by
      rw [hs.esp (hok s₀ h₀), (hA s₀ s h₀ ha).ctx.esp]; exact e40 (hA s₀ s h₀ ha).ok
    exact Proof.MlKem.X86.args6_eq hE hsp (Proof.MlKem.X86.absArgs_eq a a') _ _
  · obtain ⟨hL, hc⟩ := hA s₀ s h₀ ha
    have hc1 := SetPost.ctx (hok s₀ h₀) hs hc
    have a := hargs s₀ s s₁ h₀ ha hs
    have hsp : s₁.gpr .esp = (lay s₀).E1 := hc1.esp
    have hE := e40 hL
    have kb : ∀ r ∈ [reg32 (lay s₀).X32 200, reg32 ((lay s₀).X32 + BitVec.ofNat 32 840) 64,
        reg32 ((lay s₀).X32 + BitVec.ofNat 32 200) 640, below (lay s₀).E1 24] ++
        [below (s₁.gpr .esp) (4 * Proof.MlKem.X86.rs6.length + stackUse Impl.Sha3.X86.Stream.squeeze + 4)],
        Within r (lay s₀).W ∨ Region.Sub r (lay s₀).STK := fun r hr => by
      rw [squeeze_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact .inl w_st
      · rw [regMU hL]; exact .inl w_mu
      · rw [regKS hL]; exact .inl w_ks
      · exact .inr (kb_stk hL (by omega))
      · exact .inr (b40 hL)
    obtain ⟨s₂, m₂, post⟩ := post
    refine hQ s₀ s s' h₀ ha ⟨hL, hc1.keep hL e₁ e₂ (e₃ .esp (by decide)) (e₃ .esi (by decide)) fr kb⟩ ?_ ?_
    · rw [← hs.2.mem]
      refine fr.sub fun r hr => ?_
      rw [squeeze_stack, hsp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · rw [regMU hL]; exact ⟨_, by simp, fun _ h => h⟩
      · rw [regKS hL]; exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, kb_stk hL (by omega)⟩
      · exact ⟨_, by simp, b40 hL⟩
    · have := (squeeze_post hsp a hE (by decide) (by decide) (by decide) (kbufs hL).bS ⟨s₂, m₂, post⟩).1
      rw [mu_eq hL, hs.2.mem] at this
      exact this

end

end VG.Proof.MlDsa.X86.Message
