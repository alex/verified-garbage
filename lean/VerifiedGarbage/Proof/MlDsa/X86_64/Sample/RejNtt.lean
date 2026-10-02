import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttLoop

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly`, correctness

Untrusted: everything here is checked by Lean. The function runs in pieces:
the prologue (`J0`), the sponge, whose output is `G(ρ, 1008)` (`J6`), and
the loop, iteration `t` of which starts from `LAt σ t` with the coefficients
`rnFold` samples from the first `3t` bytes of output stored.
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mldsa_rej_ntt_poly(seed = rdi, a = rsi, scratch = rdx) -> eax`, with
16 bytes of stack below `rsp`. -/
def rnK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 34⟩] ∧ s.wr = [pR (s.gpr .rsi), ⟨s.gpr .rdx, 2048⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 34⟩ (pR (s.gpr .rsi)) ∧ Region.Disjoint ⟨s.gpr .rdi, 34⟩ ⟨s.gpr .rdx, 2048⟩ ∧
    (pR (s.gpr .rsi)).Disjoint ⟨s.gpr .rdx, 2048⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 34⟩ ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 2048⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdi, 34⟩ ∧ (below (s.gpr .rsp) 16).Disjoint (pR (s.gpr .rsi)) ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdx, 2048⟩ ∧ (s.gpr .rdx).toNat + 2048 ≤ 2 ^ 64
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (rnFold [] (G (bytesAt s.mem (s.gpr .rdi) 34) 1008)).length = 256 then 1 else 0) ∧
      ((rnFold [] (G (bytesAt s.mem (s.gpr .rdi) 34) 1008)).length = 256 →
        PolyIs s'.mem (s.gpr .rsi) (toPoly (rnFold [] (G (bytesAt s.mem (s.gpr .rdi) 34) 1008))))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ bytesAt s₁.mem (s₁.gpr .rdi) 34 = bytesAt s₂.mem (s₂.gpr .rdi) 34

namespace RejNtt

/-- The call. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .rdi, 34, σ.gpr .rdx, σ.gpr .rsi, 0⟩

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 34

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := G (B σ) 1008

section
variable {σ : State} (hp : rnK.pre σ)
include hp

theorem spOk : SpOk (spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2, by show (34 : Nat) < 2 ^ 64; decide⟩

omit hp in
theorem sx34 : BitVec.signExtend 64 (34 : BitVec 32) = BitVec.ofNat 64 34 := by decide

theorem pro_ok : WP isa (.block (pro .rdx .rsi (.imm 0) (.imm 34))) σ (J0 (spOf σ) σ) := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .rcx, .r8] (Q := fun s =>
      s.mem = ((σ.mem.writeW ((spOf σ).at' 2024) (σ.gpr .rbx)).writeW ((spOf σ).at' 2032) (σ.gpr .rbp)).writeW
        ((spOf σ).at' 2040) (σ.gpr .r12) ∧ s.gpr .rbx = σ.gpr .rdx ∧ s.gpr .rbp = σ.gpr .rsi ∧ s.gpr .r12 = 0 ∧
        s.gpr .rcx = σ.gpr .rdi ∧ s.gpr .r8 = BitVec.ofNat 64 34)
    (by unfold pro; xrun [inScrσ (spOk hp) (a := 2024) (n := 8) (by omega),
      inScrσ (spOk hp) (a := 2032) (n := 8) (by omega), inScrσ (spOk hp) (a := 2040) (n := 8) (by omega), sx34])
    (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, hcx, h8⟩, k⟩ => pro_J0 hm hbx hbp h12 hcx h8 k

/-! ## The loop -/

/-- The coefficients sampled after `t` iterations. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := rnFold [] ((X σ).take (3 * t))

/-- At the start of iteration `t`. -/
structure LAt (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 1008 = X σ
  rsi : s.gpr .rsi = (spOf σ).at' 840 + BitVec.ofNat 64 (3 * t)
  rdi : s.gpr .rdi = BitVec.ofNat 64 (Lt σ t).length
  rcx : s.gpr .rcx = BitVec.ofNat 64 (336 - t)
  stored : Stored s.mem (σ.gpr .rsi) (Lt σ t)

omit hp in
theorem X_length : (X σ).length = 1008 := G_length _ _

omit hp in
theorem take_add_three (L : List Byte) {i : Nat} (h : i + 3 ≤ L.length) :
    L.take (i + 3) = L.take i ++ [L.getD i 0, L.getD (i + 1) 0, L.getD (i + 2) 0] := by
  rw [List.take_add, List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < L.length by omega), List.getElem?_eq_getElem (show i + 1 < L.length by omega),
    List.getElem?_eq_getElem (show i + 2 < L.length by omega), Option.getD_some]

omit hp in
theorem out_byte {t : Nat} {s : State} (h : LAt σ t s) {k : Nat} (hk : 3 * t + k < 1008) :
    s.mem (s.gpr .rsi + BitVec.ofNat 64 k) = (X σ).getD (3 * t + k) 0 := by
  have := congrArg (fun L => L.getD (3 * t + k) 0) h.out
  rw [MlKem.bytesAt_getD _ _ hk] at this
  rw [h.rsi, offAdd]; exact this

theorem lat_regions {t : Nat} {s : State} (h : LAt σ t s) {k : Nat} (hk : 3 * t + k < 1008) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 k) 1 := by
  rw [h.rsi, at_add, at_add]; exact inScrRd (spOk hp) h.env (by omega)

omit hp in
theorem Lt_length_le (t : Nat) : (Lt σ t).length ≤ 256 := rnFold_length_le (by simp) _

/-- An iteration, from `LAt`. -/
theorem lat_step {t : Nat} {s : State} (ht : t < 336) (h : LAt σ t s) :
    WP isa rnBody s fun s' => LAt σ (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (336 - t) - 1 == 0) := by
  have hw : pR (σ.gpr .rsi) ∈ s.wr := by rw [h.env.wr, hp.2.1]; simp
  refine WP.mono (rnBody_ok s (aP := σ.gpr .rsi) h.env.rbp h.rdi (Lt_length_le t) (.of_mem hw) h.stored
    (by simpa using lat_regions hp h (k := 0) (by omega)) (lat_regions hp h (by omega))
    (lat_regions hp h (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have e0 := out_byte h (k := 0) (by omega)
  rw [add_ofNat_zero, Nat.add_zero] at e0
  have ht3 : Lt σ (t + 1) = rnStep (Lt σ t) ((X σ).getD (3 * t) 0) ((X σ).getD (3 * t + 1) 0)
      ((X σ).getD (3 * t + 2) 0) := by
    simp only [Lt]
    rw [show 3 * (t + 1) = 3 * t + 3 by omega, take_add_three _ (by rw [X_length]; omega),
      rnFold_snoc _ (by rw [List.length_take, X_length]; omega)]
  rw [e0, out_byte h (k := 1) (by omega), out_byte h (k := 2) (by omega), ← ht3] at hdi hst
  have hp' := spOk hp
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
    by rw [MlKem.bytesAt_frame hf (by simpa using (a_scr' hp' (a := 840) (n := 1008) (by omega)).symm)
      (by omega)]; exact h.out,
    by rw [hsi, h.rsi, offAdd, show 3 * (t + 1) = 3 * t + 3 by omega],
    hdi, by rw [hcx, h.rcx, ofNat64_pred (by omega) (by omega)]; rfl, hst⟩, by rw [hz, h.rcx]⟩

omit hp in
theorem lat0 {s : State} (h : J6 168 1008 (spOf σ) σ s) :
    WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov32 .rdi (.imm 0)]) s fun s' =>
      Env (spOf σ) σ s' ∧ bytesAt s'.mem ((spOf σ).at' 840) 1008 = X σ ∧ s'.gpr .rsi = (spOf σ).at' 840 ∧
        s'.gpr .rdi = 0 := by
  refine WP.mono (WP.keep [.rsi, .rdi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = (spOf σ).at' 840 ∧ s'.gpr .rdi = 0) (by xrun [h.env.rbx, sx840]) (by decide))
    fun s1 ⟨⟨hm1, hsi1, hdi1⟩, k1⟩ => ⟨h.env.keep hm1 (k1.mono (by decide)), ?_, hsi1, hdi1⟩
  rw [hm1, h.out]; exact (G_eq _ _).symm

/-- The loop: `LAt σ 336` at the end. -/
theorem loop_ok {s : State} (h : J6 168 1008 (spOf σ) σ s) : WP isa rnLoop s (LAt σ 336) := by
  refine WP.seq (WP.mono (lat0 h) fun s1 ⟨he, hout, hsi, hdi⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s1.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 336)
    (by xrun) (by decide)) fun s2 ⟨⟨hm, hcx⟩, hk⟩ => ?_)
  refine wp_countdown (N := 336) (by decide) (by decide) (LAt σ) (fun t ht s hI _ =>
    WP.mono (lat_step hp ht hI) fun s' ⟨hI', hz⟩ => ⟨hI', ?_, by rw [hz, hI.rcx]⟩) (fun _ h => h)
    ⟨he.keep hm (hk.mono (by decide)), by rw [hm]; exact hout, by rw [hk.gpr (by decide), hsi]; simp,
      by rw [hk.gpr (by decide), hdi]; rfl, hcx, by rw [hm]; exact stored_nil _ _⟩ hcx
  rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl

/-- The end: the postcondition and the calling convention. -/
theorem end_ok {s : State} (h : LAt σ 336 s) :
    WP isa (.block (retJ ++ epi)) s fun s' => rnK.post σ s' ∧ gprPreserved σ s' := by
  have hL : Lt σ 336 = rnFold [] (X σ) := by
    simp only [Lt]; rw [List.take_of_length_le (by rw [X_length])]
  refine WP.mono (retEpi_ok (spOk hp) h.env h.rdi (Lt_length_le 336)) fun s' ⟨hax, hm, hg⟩ => ⟨⟨?_, fun hf => ?_⟩, hg⟩
  · rw [hax, hL]
  · rw [hm, ← hL]
    rw [← hL] at hf
    exact stored_polyIs h.stored hf

end

end RejNtt

theorem rejNTT_correct (σ : State) (hp : rnK.pre σ) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Sample.rejNTT σ t s' ∧ abiPreserved σ s' ∧ rnK.post σ s' := by
  open RejNtt in
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun s1 h1 =>
    WP.seq (WP.mono (sponge_ok (spOk hp) (rate := 168) (outlen := 1008) (.inr rfl) (by decide) h1) fun s2 h2 =>
      WP.seq (WP.mono (loop_ok hp h2) fun s3 h3 => end_ok hp h3)))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Sample
