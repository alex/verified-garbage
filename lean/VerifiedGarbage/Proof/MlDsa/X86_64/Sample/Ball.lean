import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallLoop
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNtt

/-!
# ML-DSA on x86-64: `vg_mldsa_sample_in_ball`, correctness

Untrusted: everything here is checked by Lean. The function runs in pieces:
the prologue (`J0`), the sponge, whose output is `H(c̃, 272)` (`J6`), the
zeroing of `c`, and the loop over the 264 bytes after the sign bits,
iteration `t` of which starts from `BAt σ t`: with the polynomial and `i`
that `bFold` computes from the first `t` of them, and the sign bits not yet
used in `r9` (`W σ`, the first 8 bytes as a `u64`, shifted right once per
coefficient set).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H PolyIs IPoly n toRq ballParams)
open VG.Spec.Sha3 (bytesAt)

/-- `τ`, the `u32` argument in `edx`. -/
abbrev tauOf (s : State) : Nat := ((s.gpr .rdx).setWidth 32).toNat

/-- `vg_mldsa_sample_in_ball(ctilde = rdi, len = rsi, tau = edx, c = rcx, scratch = r8) -> eax`,
with 16 bytes of stack below `rsp`. -/
def sbK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩] ∧ s.wr = [pR (s.gpr .rcx), ⟨s.gpr .r8, 2048⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ (pR (s.gpr .rcx)) ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ⟨s.gpr .r8, 2048⟩ ∧
    (pR (s.gpr .rcx)).Disjoint ⟨s.gpr .r8, 2048⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint ⟨s.gpr .r8, 2048⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint (pR (s.gpr .rcx)) ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r8, 2048⟩ ∧ (s.gpr .r8).toNat + 2048 ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat, tauOf s) ∈ ballParams
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).2 = 256 then 1 else 0) ∧
      ((ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).2 = 256 →
        PolyIs s'.mem (s.gpr .rcx) (toRq (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).1))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat = bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat

theorem readW64_getLsbD (m : Mem) (a : Addr) {k : Nat} (hk : k < 64) :
    (m.readW a 64).getLsbD k = (m (a + BitVec.ofNat 64 (k / 8))).getLsbD (k % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 8) (j := k / 8) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, show k % 8 < 8 by omega, decide_true, Bool.true_and, hk]
  congr 1; omega

/-- The `u64` at `p`, from the bytes there. -/
theorem readW_leNat (m : Mem) (p : Addr) (L : List Byte) (h : ∀ k < 8, m (p + BitVec.ofNat 64 k) = L.getD k 0) :
    m.readW p 64 = BitVec.ofNat 64 (leNat (L.take 8)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [readW64_getLsbD m p hk, h _ (by omega), BitVec.getLsbD_ofNat, testBit_leNat, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
  simp [hk]

namespace Ball

theorem ballParams_le {len τ : Nat} (h : (len, τ) ∈ ballParams) : len ≤ 64 ∧ 39 ≤ τ ∧ τ ≤ 60 := by
  simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  omega

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .rdi, (σ.gpr .rsi).toNat, σ.gpr .r8, σ.gpr .rcx, BitVec.setWidth 64 ((σ.gpr .rdx).setWidth 32)⟩

/-- `c̃`. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) (σ.gpr .rsi).toNat

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H (B σ) 272

/-- The first `i`. -/
abbrev i0 (σ : State) : Nat := 256 - tauOf σ

/-- The sign bits, as a `u64`. -/
abbrev W (σ : State) : BitVec 64 := BitVec.ofNat 64 (leNat ((X σ).take 8))

/-- The polynomial and `i` after `t` iterations. -/
abbrev St (σ : State) (t : Nat) : IPoly × Nat :=
  bFold (tauOf σ) (signs (X σ)) (Vector.replicate n 0, i0 σ) (((X σ).drop 8).take t)

section
variable {σ : State} (hp : sbK.pre σ)
include hp

theorem params : (σ.gpr .rsi).toNat ≤ 64 ∧ 39 ≤ tauOf σ ∧ tauOf σ ≤ 60 :=
  ballParams_le hp.2.2.2.2.2.2.2.2.2.2.2.2

theorem spOk : SpOk (spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.1,
    by show (σ.gpr .rsi).toNat < 2 ^ 64; have := (params hp).1; omega⟩

theorem pro_ok : WP isa (.block (pro .r8 .rcx (.reg .rdx) (.reg .rsi))) σ (J0 (spOf σ) σ) := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .rcx, .r8] (Q := fun s =>
      s.mem = ((σ.mem.writeW ((spOf σ).at' 2024) (σ.gpr .rbx)).writeW ((spOf σ).at' 2032) (σ.gpr .rbp)).writeW
        ((spOf σ).at' 2040) (σ.gpr .r12) ∧ s.gpr .rbx = σ.gpr .r8 ∧ s.gpr .rbp = σ.gpr .rcx ∧
        s.gpr .r12 = BitVec.setWidth 64 ((σ.gpr .rdx).setWidth 32) ∧
        s.gpr .rcx = σ.gpr .rdi ∧ s.gpr .r8 = σ.gpr .rsi)
    (by unfold pro; xrun [inScrσ (spOk hp) (a := 2024) (n := 8) (by omega),
      inScrσ (spOk hp) (a := 2032) (n := 8) (by omega), inScrσ (spOk hp) (a := 2040) (n := 8) (by omega)])
    (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, hcx, h8⟩, k⟩ =>
      pro_J0 hm hbx hbp h12 hcx (by rw [h8]; simp) k

omit hp in
theorem X_length : (X σ).length = 272 := H_length _ _

/-! ## The zeroing, and the setup of the loop -/

/-- After the zeroing. -/
structure ZDone (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  st : CStored s.mem (σ.gpr .rcx) (Vector.replicate n 0)

theorem zero_ok {s : State} (h : J6 136 272 (spOf σ) σ s) : WP isa bZero s (ZDone σ) := by
  have hp' := spOk hp
  refine WP.mono (bZero_ok s h.env.rbp (by rw [h.env.wr, hp.2.1]; simp)) fun s' ⟨k, hf, hst⟩ => ?_
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 →
      s'.mem.readW ((spOf σ).at' k) 64 = s.mem.readW ((spOf σ).at' k) 64 := fun k h1 h2 =>
    hf.readW (Region.contains_self _ _) (by simpa using (a_scr' hp' h2).symm) (by decide)
  have k' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := k.mono (by simp)
  refine ⟨⟨k'.2.1.trans h.env.rd, k'.2.2.trans h.env.wr, by rw [k'.gpr (by decide), h.env.rbx],
    by rw [k'.gpr (by decide), h.env.rbp], by rw [k'.gpr (by decide), h.env.r12],
    by rw [k'.gpr (by decide), h.env.rsp], fun r hr => by rw [k'.gpr (r13_not hr), h.env.cs r hr],
    (by rw [hsv 2024 (by omega) (by omega), hsv 2032 (by omega) (by omega), hsv 2040 (by omega) (by omega)];
        exact h.env.saved), h.env.frame.trans (hf.mono (by simp))⟩, ?_, hst⟩
  rw [MlKem.bytesAt_frame hf (by simpa using (a_scr' hp' (a := 840) (n := 272) (by omega)).symm) (by omega), h.out]
  exact (H_eq _ _).symm

/-- At the start of iteration `t`. -/
structure BAt (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  rsi : s.gpr .rsi = (spOf σ).at' 848 + BitVec.ofNat 64 t
  rdi : s.gpr .rdi = BitVec.ofNat 64 (St σ t).2
  r9 : s.gpr .r9 = W σ >>> ((St σ t).2 - i0 σ)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (264 - t)
  st : CStored s.mem (σ.gpr .rcx) (St σ t).1

omit hp in
theorem out_getD {s : State} (hout : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ) {j : Nat} (hj : j < 272) :
    s.mem ((spOf σ).at' 840 + BitVec.ofNat 64 j) = (X σ).getD j 0 := by
  have := congrArg (fun L => L.getD j 0) hout
  rw [MlKem.bytesAt_getD _ _ hj] at this
  exact this

theorem setup_ok {s : State} (h : ZDone σ s) :
    WP isa (.block bSetup) s fun s1 => WP isa (.block [.mov32 .rcx (.imm 264)]) s1 (BAt σ 0) := by
  have hp' := spOk hp
  have ht := (params hp).2
  refine (WP.mono (WP.keep [.r9, .rdi, .rsi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .r9 = s.mem.readW ((spOf σ).at' 840) 64 ∧ s'.gpr .rdi = BitVec.ofNat 64 (i0 σ) ∧
      s'.gpr .rsi = (spOf σ).at' 848) (by
        unfold bSetup
        xrun [h.env.rbx, h.env.r12, inScrRd hp' h.env (a := 840) (n := 8) (by omega), sx840, sw32_64,
          show BitVec.signExtend 64 (848 : BitVec 32) = BitVec.ofNat 64 848 by decide]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, show (256 : BitVec 32).toNat = 256 from rfl]
        have := ((σ.gpr .rdx).setWidth 32).isLt
        simp only [i0, tauOf] at ht ⊢
        omega) (by decide)) fun s1 ⟨⟨hm1, h91, hdi1, hsi1⟩, k1⟩ => ?_)
  refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s1.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 264)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_
  have he1 := h.env.keep hm1 (k1.mono (by decide))
  have hSt : St σ 0 = (Vector.replicate n 0, i0 σ) := rfl
  refine ⟨he1.keep hm2 (k2.mono (by decide)), by rw [hm2, hm1]; exact h.out,
    by rw [k2.gpr (by decide), hsi1]; simp, by rw [k2.gpr (by decide), hdi1, hSt], ?_, hcx,
    by rw [hm2, hm1, hSt]; exact h.st⟩
  rw [k2.gpr (by decide), h91, hSt, Nat.sub_self, BitVec.ushiftRight_zero]
  exact readW_leNat _ _ _ fun k hk => out_getD h.out (by omega)

/-! ## The loop -/

omit hp in
theorem St_le (t : Nat) : (St σ t).2 ≤ 256 := bFold_le (by simp) _

omit hp in
theorem St_ge (t : Nat) : i0 σ ≤ (St σ t).2 :=
  bFold_ge (τ := tauOf σ) (h := signs (X σ)) (Vector.replicate n 0, i0 σ) _

omit hp in
theorem take_succ'' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The sign bit of `i`. -/
theorem sign_bit {i : Nat} (hi0 : i0 σ ≤ i) (hi : i < 256) :
    (W σ >>> (i - i0 σ)).getLsbD 0 = (signs (X σ)).getD (i + tauOf σ - 256) false := by
  have ht := (params hp).2
  simp only [i0] at hi0
  rw [BitVec.getLsbD_ushiftRight, Nat.add_zero, signs_getD, BitVec.getLsbD_ofNat,
    show i - (256 - tauOf σ) = i + tauOf σ - 256 by omega,
    decide_eq_true (show i + tauOf σ - 256 < 64 by omega), Bool.true_and]

/-- An iteration, from `BAt`. -/
theorem bat_step {t : Nat} {s : State} (ht : t < 264) (h : BAt σ t s) :
    WP isa bBody s fun s' => BAt σ (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (264 - t) - 1 == 0) := by
  have hp' := spOk hp
  have hw : pR (σ.gpr .rcx) ∈ s.wr := by rw [h.env.wr, hp.2.1]; simp
  have hle := St_le (σ := σ) t
  have hge := St_ge (σ := σ) t
  refine WP.mono (bBody_ok s (τ := tauOf σ) (h := signs (X σ)) (c := (St σ t).1) (aP := σ.gpr .rcx) h.env.rbp h.rdi
    hle hw (List.mem_append_right _ hw) h.st
    (by rw [h.rsi, at_add]; exact inScrRd hp' h.env (by omega))
    (fun hi => by rw [h.r9]; exact sign_bit hp hge hi)) fun s' ⟨hdi, hst, hf, h9, hsi, hcx, hz, hk⟩ => ?_
  have hb : s.mem (s.gpr .rsi) = ((X σ).drop 8).getD t 0 := by
    rw [h.rsi, at_add, show 848 + t = 840 + (8 + t) by omega, ← at_add, out_getD h.out (by omega),
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have ht1 : St σ (t + 1) = bStep (tauOf σ) (signs (X σ)) (St σ t) (((X σ).drop 8).getD t 0) := by
    simp only [St]
    rw [take_succ'' _ (by rw [List.length_drop, X_length]; omega), bFold_snoc]
  rw [hb, ← ht1] at hdi hst h9
  have hk' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := hk.mono (by simp)
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 →
      s'.mem.readW ((spOf σ).at' k) 64 = s.mem.readW ((spOf σ).at' k) 64 := fun k h1 h2 =>
    hf.readW (Region.contains_self _ _) (by simpa using (a_scr' hp' h2).symm) (by decide)
  refine ⟨⟨⟨hk'.2.1.trans h.env.rd, hk'.2.2.trans h.env.wr, by rw [hk'.gpr (by decide), h.env.rbx],
    by rw [hk'.gpr (by decide), h.env.rbp], by rw [hk'.gpr (by decide), h.env.r12],
    by rw [hk'.gpr (by decide), h.env.rsp], fun r hr => by rw [hk'.gpr (r13_not hr), h.env.cs r hr],
    (by rw [hsv 2024 (by omega) (by omega), hsv 2032 (by omega) (by omega), hsv 2040 (by omega) (by omega)];
        exact h.env.saved), h.env.frame.trans (hf.mono (by simp))⟩,
    by rw [MlKem.bytesAt_frame hf (by simpa using (a_scr' hp' (a := 840) (n := 272) (by omega)).symm)
      (by omega)]; exact h.out, by rw [hsi, h.rsi, offAdd], hdi, ?_,
    by rw [hcx, h.rcx, ofNat64_pred (by omega) (by omega)]; rfl, hst⟩, by rw [hz, h.rcx]⟩
  rw [h9, h.r9]
  have hs : (St σ (t + 1)).2 = (St σ t).2 ∨ (St σ (t + 1)).2 = (St σ t).2 + 1 := by
    rw [ht1]; unfold bStep; split
    · split
      · exact .inl rfl
      · exact .inr rfl
    · exact .inl rfl
  rcases hs with e | e
  · rw [ifT e, e]
  · rw [ifF (by omega), e, ← BitVec.shiftRight_add, show (St σ t).2 + 1 - i0 σ = (St σ t).2 - i0 σ + 1 by omega]

theorem loop_ok {s : State} (h : ZDone σ s) : WP isa bLoop s (BAt σ 264) :=
  WP.seq (WP.mono (setup_ok hp h) fun _ h1 => WP.seq (WP.mono h1 fun _ h2 =>
    wp_countdown (N := 264) (by decide) (by decide) (BAt σ) (fun t ht s hI _ => WP.mono (bat_step hp ht hI)
      fun s' ⟨hI', hz⟩ => ⟨hI', by rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl,
        by rw [hz, hI.rcx]⟩) (fun _ h => h) h2 h2.rcx))

/-- The end: the postcondition and the calling convention. -/
theorem end_ok {s : State} (h : BAt σ 264 s) :
    WP isa (.block (retJ ++ epi)) s fun s' => sbK.post σ s' ∧ gprPreserved σ s' := by
  have hL : St σ 264 = ballFold (tauOf σ) (X σ) := by
    simp only [St, ballFold, i0]; rw [List.take_of_length_le (by rw [List.length_drop, X_length])]
  refine WP.mono (retEpi_ok (spOk hp) h.env h.rdi (St_le 264)) fun s' ⟨hax, hm, hg⟩ => ⟨⟨?_, fun hf => ?_⟩, hg⟩
  · rw [hax, hL]
  · rw [hm]
    have hst := h.st
    rw [hL] at hst
    refine polyIs_of_coeffAt fun i hi => ?_
    rw [hst i hi, getElem!_pos _ i hi, getElem!_pos _ i hi]
    simp only [toRq, Vector.getElem_map]

end

end Ball

theorem sampleInBall_correct (σ : State) (hp : sbK.pre σ) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Sample.sampleInBall σ t s' ∧ abiPreserved σ s' ∧ sbK.post σ s' := by
  open Ball in
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun s1 h1 =>
    WP.seq (WP.mono (sponge_ok (spOk hp) (rate := 136) (outlen := 272) (.inl rfl) (by decide) h1) fun s2 h2 =>
      WP.seq (WP.mono (zero_ok hp h2) fun s3 h3 => WP.seq (WP.mono (loop_ok hp h3) fun s4 h4 => end_ok hp h4))))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Sample
