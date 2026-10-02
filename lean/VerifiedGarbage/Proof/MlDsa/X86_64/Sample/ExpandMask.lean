import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.ExpandMaskLoop
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly`

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`H(ρ′, 640)` (`J6`), the branch on `γ₁`, and the loop for `c = 1 + bitlen (γ₁ -
1)`, iteration `g` of which starts from `EAt σ c g` with the coefficients of
the first `g` groups stored. It is constant time: the taint analysis proves
each piece but the sponge, whose proof is `sponge_ct`, from the pointers and
`γ₁`.
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H PolyIs coeffAt toRq bitUnpack bitlen)
open VG.Spec.Sha3 (bytesAt)

/-- `γ₁`, the `u32` argument in `esi`. -/
abbrev gOf (s : State) : Nat := ((s.gpr .rsi).setWidth 32).toNat

/-- `vg_mldsa_expand_mask_poly(seed = rdi, gamma1 = esi, a = rdx, scratch = rcx)`,
with 16 bytes of stack below `rsp`. -/
def emK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 66⟩] ∧ s.wr = [pR (s.gpr .rdx), ⟨s.gpr .rcx, 2048⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 66⟩ (pR (s.gpr .rdx)) ∧ Region.Disjoint ⟨s.gpr .rdi, 66⟩ ⟨s.gpr .rcx, 2048⟩ ∧
    (pR (s.gpr .rdx)).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 66⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdx)) ∧
    (retR s).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdi, 66⟩ ∧ (below (s.gpr .rsp) 16).Disjoint (pR (s.gpr .rdx)) ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧ (s.gpr .rcx).toNat + 2048 ≤ 2 ^ 64 ∧
    (gOf s = 2 ^ 17 ∨ gOf s = 2 ^ 19)
  post s s' :=
    PolyIs s'.mem (s.gpr .rdx) (toRq (bitUnpack (H (bytesAt s.mem (s.gpr .rdi) 66) (32 * (1 + bitlen (gOf s - 1))))
      (gOf s - 1) (gOf s)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32 ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

namespace ExpandMask

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .rdi, 66, σ.gpr .rcx, σ.gpr .rdx, BitVec.setWidth 64 ((σ.gpr .rsi).setWidth 32)⟩

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 66

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H (B σ) 640

section
variable {σ : State} (hp : emK.pre σ)
include hp

theorem spOk : SpOk (spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.1,
    by show (66 : Nat) < 2 ^ 64; decide⟩

theorem gamma : gOf σ = 2 ^ 17 ∨ gOf σ = 2 ^ 19 := hp.2.2.2.2.2.2.2.2.2.2.2.2

theorem pro_ok : WP isa (.block (pro .rcx .rdx (.reg .rsi) (.imm 66))) σ (J0 (spOf σ) σ) := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .rcx, .r8] (Q := fun s =>
      s.mem = ((σ.mem.writeW ((spOf σ).at' 2024) (σ.gpr .rbx)).writeW ((spOf σ).at' 2032) (σ.gpr .rbp)).writeW
        ((spOf σ).at' 2040) (σ.gpr .r12) ∧ s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdx ∧
        s.gpr .r12 = BitVec.setWidth 64 ((σ.gpr .rsi).setWidth 32) ∧
        s.gpr .rcx = σ.gpr .rdi ∧ s.gpr .r8 = BitVec.ofNat 64 66)
    (by unfold pro; xrun [inScrσ (spOk hp) (a := 2024) (n := 8) (by omega),
      inScrσ (spOk hp) (a := 2032) (n := 8) (by omega), inScrσ (spOk hp) (a := 2040) (n := 8) (by omega),
      RejBounded.sx66])
    (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, hcx, h8⟩, k⟩ => pro_J0 hm hbx hbp h12 hcx h8 k

/-! ## The loop -/

/-- At the start of iteration `g` of the loop for `c`. -/
structure EAt (σ : State) (c g : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 640 = X σ
  rsi : s.gpr .rsi = (spOf σ).at' 840 + BitVec.ofNat 64 (c / 2 * g)
  rdi : s.gpr .rdi = σ.gpr .rdx + BitVec.ofNat 64 (16 * g)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (64 - g)
  st : ∀ i < 4 * g, coeffAt s.mem (σ.gpr .rdx) i = emV (X σ) c i

theorem gpre {c g : Nat} (hg : g < 64) {s : State} (h : EAt σ c g s) :
    GPre c (X σ) ((spOf σ).at' 840) (σ.gpr .rdx) g s := by
  have hp' := spOk hp
  refine ⟨h.rsi, h.rdi, hg, fun j hj => ?_, fun j hj => ?_, by rw [h.env.wr, hp.2.1]; simp, fun j hj hc => ?_⟩
  · have := congrArg (fun L => L.getD j 0) h.out
    rw [MlKem.bytesAt_getD _ _ hj] at this
    exact this
  · rw [at_add]; exact inScrRd hp' h.env (by omega)
  · rw [at_add] at hc
    exact a_scr' hp' (a := 840 + j) (n := 1) (by omega) _ hc (Region.contains_self _ _)

/-- An iteration, from `EAt`. -/
theorem eat_step {c g : Nat} (hc : emOk c) (hg : g < 64) {s : State} (h : EAt σ c g s) :
    WP isa (.block (emBody c)) s fun s' => EAt σ c (g + 1) s' ∧
      s'.zf = some (BitVec.ofNat 64 (64 - g) - 1 == 0) := by
  have hp' := spOk hp
  refine WP.mono (emBody_ok hc (gpre hp hg h)) fun s' ⟨hk, hf, hst, hsame, hsi, hdi, hcx, hz⟩ => ?_
  have hk' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := hk.mono (by simp)
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 →
      s'.mem.readW ((spOf σ).at' k) 64 = s.mem.readW ((spOf σ).at' k) 64 := fun k h1 h2 =>
    hf.readW (Region.contains_self _ _) (by simpa using (a_scr' hp' h2).symm) (by decide)
  refine ⟨⟨⟨hk'.2.1.trans h.env.rd, hk'.2.2.trans h.env.wr, by rw [hk'.gpr (by decide), h.env.rbx],
    by rw [hk'.gpr (by decide), h.env.rbp], by rw [hk'.gpr (by decide), h.env.r12],
    by rw [hk'.gpr (by decide), h.env.rsp],
    fun r hr => by rw [hk'.gpr (r13_not hr), h.env.cs r hr],
    (by rw [hsv 2024 (by omega) (by omega), hsv 2032 (by omega) (by omega), hsv 2040 (by omega) (by omega)];
        exact h.env.saved), h.env.frame.trans (hf.mono (by simp))⟩,
    by rw [MlKem.bytesAt_frame hf (by simpa using (a_scr' hp' (a := 840) (n := 640) (by omega)).symm)
      (by omega)]; exact h.out, hsi, hdi, by rw [hcx, h.rcx, ofNat64_pred (by omega) (by omega)]; rfl,
    fun i hi => ?_⟩, by rw [hz, h.rcx]⟩
  by_cases hlo : i < 4 * g
  · rw [hsame i (by omega) (.inl hlo)]; exact h.st i hlo
  · have := hst (i - 4 * g) (by omega)
    rwa [show 4 * g + (i - 4 * g) = i by omega] at this

/-- The loop for `c`, from the sponge's output. -/
theorem loop_ok {c : Nat} (hc : emOk c) {s : State} (h : J6 136 640 (spOf σ) σ s) :
    WP isa (emLoop c) s (EAt σ c 64) := by
  refine WP.seq (WP.mono (WP.keep [.rsi, .rdi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = (spOf σ).at' 840 ∧ s'.gpr .rdi = σ.gpr .rdx) (by xrun [h.env.rbx, h.env.rbp, sx840])
    (by decide)) fun s1 ⟨⟨hm1, hsi1, hdi1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s1.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 64)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_)
  have he1 := h.env.keep hm1 (k1.mono (by decide))
  refine wp_countdown (N := 64) (by decide) (by decide) (EAt σ c) (fun g hg s hI _ =>
    WP.mono (eat_step hp hc hg hI) fun s' ⟨hI', hz⟩ => ⟨hI', ?_, by rw [hz, hI.rcx]⟩) (fun _ h => h)
    ⟨he1.keep hm2 (k2.mono (by decide)), by rw [hm2, hm1, h.out]; exact (H_eq _ _).symm,
      by rw [k2.gpr (by decide), hsi1]; simp, by rw [k2.gpr (by decide), hdi1]; simp, hcx,
      fun i hi => absurd hi (by omega)⟩ hcx
  rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl

omit hp in
theorem sx17 : BitVec.signExtend 64 (0x20000 : BitVec 32) = BitVec.ofNat 64 0x20000 := by decide

/-- The branch on `γ₁`, and the loop for it. -/
theorem sel_ok {s : State} (h : J6 136 640 (spOf σ) σ s) :
    WP isa (.seq (.block [.alu32 .cmp .r12 (.imm 0x20000)]) (.ite .e (emLoop 18) (emLoop 20))) s
      (EAt σ (emC (gOf σ)) 64) := by
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r12 = s.gpr .r12 ∧
      s'.zf = some (BitVec.setWidth 32 (s.gpr .r12) - 0x20000 == 0)) (by xrun) (by rfl))
    fun s1 ⟨⟨hm1, h12, hz1⟩, k1⟩ => ?_)
  have k1' : Keep [] s s1 := ⟨fun r hr => by
    by_cases e : r = .r12
    · subst e; exact h12
    · exact k1.gpr (by simp [e]), k1.2⟩
  have hr12 : BitVec.setWidth 32 (s.gpr .r12) = BitVec.ofNat 32 (gOf σ) := by
    rw [h.env.r12]; rw [sw32_64, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hJ : J6 136 640 (spOf σ) σ s1 := ⟨h.env.keep hm1 (k1'.mono (by decide)), by rw [hm1]; exact h.out⟩
  rcases gamma hp with he | he
  · refine WP.ite true (by show s1.zf = _; rw [hz1, hr12, he]; rfl) (fun _ => ?_) (fun hb => absurd hb (by decide))
    rw [show emC (gOf σ) = 18 by rw [he]; rfl]; exact loop_ok hp (.inl rfl) hJ
  · refine WP.ite false (by show s1.zf = _; rw [hz1, hr12, he]; rfl) (fun hb => absurd hb (by decide)) (fun _ => ?_)
    rw [show emC (gOf σ) = 20 by rw [he]; rfl]; exact loop_ok hp (.inr rfl) hJ

/-- The end: the postcondition and the calling convention. -/
theorem end_ok {s : State} (h : EAt σ (emC (gOf σ)) 64 s) :
    WP isa (.block epi) s fun s' => emK.post σ s' ∧ gprPreserved σ s' := by
  refine WP.mono (epi_ok (spOk hp) h.env) fun s' ⟨⟨hbx, hbp, h12, hm⟩, k⟩ =>
    ⟨?_, gpr_end (spOk hp) h.env hbx hbp h12 (k.mono (by simp)) hm⟩
  obtain ⟨_, _, hγ⟩ := emC_eq (gamma hp)
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [expandMask_getElem _ (gamma hp) hi, hm, h.st i (by omega)]
  simp only [emV]
  congr 3
  rw [← hγ]

end

end ExpandMask

theorem expandMask_correct (σ : State) (hp : emK.pre σ) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Sample.expandMask σ t s' ∧ abiPreserved σ s' ∧ emK.post σ s' := by
  open ExpandMask in
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun s1 h1 =>
    WP.seq (WP.mono (sponge_ok (spOk hp) (rate := 136) (outlen := 640) (.inl rfl) (by decide) h1) fun s2 h2 =>
      WP.seq (WP.mono (sel_ok hp h2) fun s3 h3 => end_ok hp h3)))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

namespace ExpandMask

theorem hok : ∀ σ, emK.pre σ → SpOk (spOf σ) σ := fun _ hp => spOk hp

theorem hpub : ∀ σ₁ σ₂, emK.pre σ₁ → emK.pre σ₂ → emK.pub σ₁ σ₂ → SpPub (spOf σ₁) (spOf σ₂) σ₁ σ₂ :=
  fun _ _ _ _ hq => ⟨hq.1, rfl, hq.2.2.2.1, hq.2.2.1, by simp only [hq.2.1], hq.2.2.2.2⟩

end ExpandMask

open ExpandMask in
theorem expandMask_ct : ConstantTime isa emK.pre emK.pub Impl.MlDsa.X86_64.Sample.expandMask := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ => J0 (spOf σ) σ)
    (fun σ s hp h => by subst h; exact pro_ok hp)
    (taintRel [.rdi, .rdx, .rcx, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2]) (by taint_decide))) ?_)
  refine RelCT.seq (sponge_ct hok hpub (.inl rfl) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  exact taintSp hpub (J := J6 136 640) (fun _ _ h => h.env) [] nil_regs (by taint_decide)

/-- A state satisfying the precondition. -/
def emSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x20000 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem expandMask_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Sample.expandMask (Spec.MlDsa.expandMaskContract X86_64.abi 16) :=
  Verified.of_correct expandMask_correct expandMask_ct
    { pre := by sig_implies_pre [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, emK, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, emK, X86_64.abi, X86_64.argRegs]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, emK, X86_64.abi, X86_64.argRegs] at h
        obtain ⟨hsp, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp⟩
      sat := by sig_implies_sat [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, emK, X86_64.abi,
        X86_64.argRegs] [emSat] using emSat }

end VG.Proof.MlDsa.X86_64.Sample
