import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedLoop
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNtt

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_bounded_poly`, correctness

Untrusted: everything here is checked by Lean. The function runs in pieces:
the prologue (`J0`), the sponge, whose output is `H(ρ, 544)` (`J6`), the
branch on `η`, and the loop for `η`, iteration `t` of which starts from
`LAt σ t` with the coefficients `rbFold` samples from the first `t` bytes of
output stored.
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- `η`, the `u32` argument in `esi`. -/
abbrev etaOf (s : State) : Nat := ((s.gpr .rsi).setWidth 32).toNat

/-- `vg_mldsa_rej_bounded_poly(seed = rdi, eta = esi, a = rdx, scratch = rcx) -> eax`, with
16 bytes of stack below `rsp`. -/
def rbK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 66⟩] ∧ s.wr = [pR (s.gpr .rdx), ⟨s.gpr .rcx, 2048⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 66⟩ (pR (s.gpr .rdx)) ∧ Region.Disjoint ⟨s.gpr .rdi, 66⟩ ⟨s.gpr .rcx, 2048⟩ ∧
    (pR (s.gpr .rdx)).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 66⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdx)) ∧
    (retR s).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdi, 66⟩ ∧ (below (s.gpr .rsp) 16).Disjoint (pR (s.gpr .rdx)) ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧ (s.gpr .rcx).toNat + 2048 ≤ 2 ^ 64 ∧
    (etaOf s = 2 ∨ etaOf s = 4)
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (rbFold (etaOf s) [] (H (bytesAt s.mem (s.gpr .rdi) 66) 544)).length = 256 then 1 else 0) ∧
      ((rbFold (etaOf s) [] (H (bytesAt s.mem (s.gpr .rdi) 66) 544)).length = 256 →
        PolyIs s'.mem (s.gpr .rdx) (toPoly (rbFold (etaOf s) [] (H (bytesAt s.mem (s.gpr .rdi) 66) 544))))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32 ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    Spec.MlDsa.rejBoundedLeak (etaOf s₁) (bytesAt s₁.mem (s₁.gpr .rdi) 66) =
      Spec.MlDsa.rejBoundedLeak (etaOf s₂) (bytesAt s₂.mem (s₂.gpr .rdi) 66)

namespace RejBounded

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .rdi, 66, σ.gpr .rcx, σ.gpr .rdx, BitVec.setWidth 64 ((σ.gpr .rsi).setWidth 32)⟩

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 66

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H (B σ) 544

section
variable {σ : State} (hp : rbK.pre σ)
include hp

theorem spOk : SpOk (spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.1,
    by show (66 : Nat) < 2 ^ 64; decide⟩

theorem eta : etaOf σ = 2 ∨ etaOf σ = 4 := hp.2.2.2.2.2.2.2.2.2.2.2.2

omit hp in
theorem sx66 : BitVec.signExtend 64 (66 : BitVec 32) = BitVec.ofNat 64 66 := by decide

theorem pro_ok : WP isa (.block (pro .rcx .rdx (.reg .rsi) (.imm 66))) σ (J0 (spOf σ) σ) := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .rcx, .r8] (Q := fun s =>
      s.mem = ((σ.mem.writeW ((spOf σ).at' 2024) (σ.gpr .rbx)).writeW ((spOf σ).at' 2032) (σ.gpr .rbp)).writeW
        ((spOf σ).at' 2040) (σ.gpr .r12) ∧ s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdx ∧
        s.gpr .r12 = BitVec.setWidth 64 ((σ.gpr .rsi).setWidth 32) ∧
        s.gpr .rcx = σ.gpr .rdi ∧ s.gpr .r8 = BitVec.ofNat 64 66)
    (by unfold pro; xrun [inScrσ (spOk hp) (a := 2024) (n := 8) (by omega),
      inScrσ (spOk hp) (a := 2032) (n := 8) (by omega), inScrσ (spOk hp) (a := 2040) (n := 8) (by omega), sx66])
    (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, hcx, h8⟩, k⟩ => pro_J0 hm hbx hbp h12 hcx h8 k

/-! ## The loop -/

/-- The coefficients sampled after `t` iterations. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := rbFold (etaOf σ) [] ((X σ).take t)

/-- At the start of iteration `t`. -/
structure LAt (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 544 = X σ
  rsi : s.gpr .rsi = (spOf σ).at' 840 + BitVec.ofNat 64 t
  rdi : s.gpr .rdi = BitVec.ofNat 64 (Lt σ t).length
  rcx : s.gpr .rcx = BitVec.ofNat 64 (544 - t)
  stored : Stored s.mem (σ.gpr .rdx) (Lt σ t)

omit hp in
theorem X_length : (X σ).length = 544 := H_length _ _

omit hp in
theorem take_succ' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

omit hp in
theorem out_byte {t : Nat} {s : State} (h : LAt σ t s) (ht : t < 544) : s.mem (s.gpr .rsi) = (X σ).getD t 0 := by
  have := congrArg (fun L => L.getD t 0) h.out
  rw [MlKem.bytesAt_getD _ _ ht] at this
  rw [h.rsi]; exact this

omit hp in
theorem Lt_length_le (t : Nat) : (Lt σ t).length ≤ 256 := rbFold_length_le (by simp) _

/-- An iteration, from `LAt`. -/
theorem lat_step {t : Nat} {s : State} (ht : t < 544) (h : LAt σ t s) :
    WP isa (rbBody (etaOf σ)) s fun s' => LAt σ (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (544 - t) - 1 == 0) := by
  have hw : pR (σ.gpr .rdx) ∈ s.wr := by rw [h.env.wr, hp.2.1]; simp
  have hp' := spOk hp
  refine WP.mono (rbBody_ok (eta hp) s (aP := σ.gpr .rdx) h.env.rbp h.rdi (Lt_length_le t) hw h.stored
    (by rw [h.rsi, at_add]; exact inScrRd hp' h.env (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have ht1 : Lt σ (t + 1) = rbStep (etaOf σ) (Lt σ t) ((X σ).getD t 0) := by
    simp only [Lt]
    rw [take_succ' _ (by rw [X_length]; omega), rbFold_snoc]
  rw [out_byte h ht, ← ht1] at hdi hst
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
    by rw [MlKem.bytesAt_frame hf (by simpa using (a_scr' hp' (a := 840) (n := 544) (by omega)).symm)
      (by omega)]; exact h.out,
    by rw [hsi, h.rsi, offAdd],
    hdi, by rw [hcx, h.rcx, ofNat64_pred (by omega) (by omega)]; rfl, hst⟩, by rw [hz, h.rcx]⟩

omit hp in
theorem lat0 {s : State} (h : J6 136 544 (spOf σ) σ s) :
    WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov32 .rdi (.imm 0)]) s fun s' =>
      Env (spOf σ) σ s' ∧ bytesAt s'.mem ((spOf σ).at' 840) 544 = X σ ∧ s'.gpr .rsi = (spOf σ).at' 840 ∧
        s'.gpr .rdi = 0 := by
  refine WP.mono (WP.keep [.rsi, .rdi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = (spOf σ).at' 840 ∧ s'.gpr .rdi = 0) (by xrun [h.env.rbx, sx840]) (by decide))
    fun s1 ⟨⟨hm1, hsi1, hdi1⟩, k1⟩ => ⟨h.env.keep hm1 (k1.mono (by decide)), ?_, hsi1, hdi1⟩
  rw [hm1, h.out]; exact (H_eq _ _).symm

/-- The loop: `LAt σ 544` at the end. -/
theorem loop_ok {s : State} (h : J6 136 544 (spOf σ) σ s) : WP isa (rbLoop (etaOf σ)) s (LAt σ 544) := by
  refine WP.seq (WP.mono (lat0 h) fun s1 ⟨he, hout, hsi, hdi⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s1.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 544)
    (by xrun) (by decide)) fun s2 ⟨⟨hm, hcx⟩, hk⟩ => ?_)
  refine wp_countdown (N := 544) (by decide) (by decide) (LAt σ) (fun t ht s hI _ =>
    WP.mono (lat_step hp ht hI) fun s' ⟨hI', hz⟩ => ⟨hI', ?_, by rw [hz, hI.rcx]⟩) (fun _ h => h)
    ⟨he.keep hm (hk.mono (by decide)), by rw [hm]; exact hout, by rw [hk.gpr (by decide), hsi]; simp,
      by rw [hk.gpr (by decide), hdi]; rfl, hcx, by rw [hm]; exact stored_nil _ _⟩ hcx
  rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl

/-- The branch on `η`, and the loop for it. -/
theorem sel_ok {s : State} (h : J6 136 544 (spOf σ) σ s) :
    WP isa (.seq (.block [.alu32 .cmp .r12 (.imm 2)]) (.ite .e (rbLoop 2) (rbLoop 4))) s (LAt σ 544) := by
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r12 = s.gpr .r12 ∧
      s'.zf = some (BitVec.setWidth 32 (s.gpr .r12) - 2 == 0)) (by xrun) (by rfl))
    fun s1 ⟨⟨hm1, h12, hz1⟩, k1⟩ => ?_)
  have k1' : Keep [] s s1 := ⟨fun r hr => by
    by_cases e : r = .r12
    · subst e; exact h12
    · exact k1.gpr (by simp [e]), k1.2⟩
  have hr12 : BitVec.setWidth 32 (s.gpr .r12) = BitVec.ofNat 32 (etaOf σ) := by
    rw [h.env.r12]; rw [sw32_64, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hJ : J6 136 544 (spOf σ) σ s1 := ⟨h.env.keep hm1 (k1'.mono (by decide)), by rw [hm1]; exact h.out⟩
  rcases eta hp with he | he
  · refine WP.ite true (by show s1.zf = _; rw [hz1, hr12, he]; rfl) (fun _ => ?_) (fun hb => absurd hb (by decide))
    rw [← he]; exact loop_ok hp hJ
  · refine WP.ite false (by show s1.zf = _; rw [hz1, hr12, he]; rfl) (fun hb => absurd hb (by decide)) (fun _ => ?_)
    rw [← he]; exact loop_ok hp hJ

/-- The end: the postcondition and the calling convention. -/
theorem end_ok {s : State} (h : LAt σ 544 s) :
    WP isa (.block (retJ ++ epi)) s fun s' => rbK.post σ s' ∧ gprPreserved σ s' := by
  have hL : Lt σ 544 = rbFold (etaOf σ) [] (X σ) := by
    simp only [Lt]; rw [List.take_of_length_le (by rw [X_length])]
  refine WP.mono (retEpi_ok (spOk hp) h.env h.rdi (Lt_length_le 544)) fun s' ⟨hax, hm, hg⟩ => ⟨⟨?_, fun hf => ?_⟩, hg⟩
  · rw [hax, hL]
  · rw [hm, ← hL]
    rw [← hL] at hf
    exact stored_polyIs h.stored hf

end

end RejBounded

theorem rejBounded_correct (σ : State) (hp : rbK.pre σ) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Sample.rejBounded σ t s' ∧ abiPreserved σ s' ∧ rbK.post σ s' := by
  open RejBounded in
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun s1 h1 =>
    WP.seq (WP.mono (sponge_ok (spOk hp) (rate := 136) (outlen := 544) (.inl rfl) (by decide) h1) fun s2 h2 =>
      WP.seq (WP.mono (sel_ok hp h2) fun s3 h3 => end_ok hp h3)))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Sample
