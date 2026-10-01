import VerifiedGarbage.Proof.MlKem1024.X86_64.DcTop
import VerifiedGarbage.Impl.MlKem1024.X86_64.Expanded
import VerifiedGarbage.Proof.MlKem.X86_64.FragX
import VerifiedGarbage.Proof.MlKem.Expanded

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_decaps_expanded`

Untrusted: everything here is checked by Lean. `vg_mlkem1024_decaps`'s proof
(`DcBase.lean`, `DcDec.lean`, `DcTop.lean`), in the same layout of `dk`,
`c`, `scratch` and `key` (`dcR`, `dcW`, with the same checks), with the
expanded key `ekx` in `r13`. `Â` is copied from `ekx` to the working space
first (`matIn_ok`, in a layout of `ekx` and `scratch` alone, `mLay`: `r13`
is a register of written buffers in the layouts, and `ekx` may overlap `dk`
and `c`), and K-PKE.Decrypt and the hashes keep it (`dcxD`), so that
K-PKE.Encrypt runs with the matrix `dcxA`, whatever `ekx` holds. When
`SampleNTT` samples the matrix of the key's `ρ` for some bound, `dcxA` is
that matrix (`ExpandedEk`), so the key is `ML-KEM.Decaps_internal`'s
(`post_of`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (polyIs_copied sampleMatrix_entry)

/-- `vg_mlkem1024_decaps_expanded(dk = rdi, ekx = rsi, ct = rdx, key = rcx, scratch = r8)`, with 32 bytes of
stack. -/
def decapsX1024K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 3168⟩, ⟨s.gpr .rsi, 17984⟩, ⟨s.gpr .rdx, 1568⟩] ∧
    s.wr = [⟨s.gpr .rcx, 32⟩, ⟨s.gpr .r8, 49152⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 3168⟩ ⟨s.gpr .rcx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 3168⟩ ⟨s.gpr .r8, 49152⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 17984⟩ ⟨s.gpr .rcx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 17984⟩ ⟨s.gpr .r8, 49152⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 1568⟩ ⟨s.gpr .rcx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, 1568⟩ ⟨s.gpr .r8, 49152⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, 32⟩ ⟨s.gpr .r8, 49152⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 3168⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 17984⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 1568⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, 32⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, 49152⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, 3168⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, 17984⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, 1568⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, 32⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .r8, 49152⟩ ∧
    (s.gpr .rdi).toNat + 3168 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 17984 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 1568 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + 49152 ≤ 2 ^ 64 ∧
    DecapsExpandedPre mlKem1024 (s.gpr .rdi) (s.gpr .rsi) s.mem
  post s s' := DecapsExpandedPost mlKem1024 (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

theorem decapsX1024K_ekx {σ : State} (hp : decapsX1024K.pre σ) : DecapsExpandedPre mlKem1024 (σ.gpr .rdi) (σ.gpr .rsi) σ.mem := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hp
  exact h

namespace DecapsX4

open VG.Impl.MlKem1024.X86_64.Decaps1024
open Decaps4 (dcR dcW dcB dcB_bases dcChk dckChk dcEncChk)
open Decaps (slice_of)

/-- The pointers the function keeps. -/
abbrev dcxM : List (Reg × Reg) := [(.rbx, .r8), (.rbp, .rdi), (.r13, .rsi), (.r14, .rdx), (.r12, .rcx)]

theorem dcxM_bases : ∀ p ∈ dcxM, p.1 ∈ bases := by decide

section
variable {σ : State} (hp : decapsX1024K.pre σ)
include hp

theorem dcxLay {s : State} (h : Top dcxM σ s) : Lay dcR dcW s := by
  obtain ⟨hrd, hwr, d1, d2, _, _, d5, d6, d7, r1, _, r3, r4, r5, k1, _, k3, k4, k5, n1, _, n3, n4, n5, -⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .r8 := h.regs (.rbx, .r8) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r14 = σ.gpr .rdx := h.regs (.r14, .rdx) (by decide)
  have e4 : s.gpr .r12 = σ.gpr .rcx := h.regs (.r12, .rcx) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of (by decide) (pw4 ?_ ?_ ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_)
    (fa2 ?_ ?_) (fa4 ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, h.rsp, retR]
  · exact fun hw => absurd hw (by decide)
  · exact fun _ => d2
  · exact fun _ => d1
  · exact fun _ => d6
  · exact fun _ => d5
  · exact fun _ => d7.symm
  exacts [k1, k3, k5, k4, n1, n3, n5, n4,
    mem ⟨σ.gpr .rdi, 3168⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rdx, 1568⟩ (by rw [hrd]; simp),
    mem ⟨σ.gpr .r8, 49152⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rcx, 32⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    r1, r3, r5, r4]

/-- The layout of the copy of `Â`: `ekx` and `scratch`. -/
theorem mLay {s : State} (h : Top dcxM σ s) : Lay [(.r13, 17984)] [(.rbx, 49152)] s := by
  obtain ⟨hrd, hwr, _, _, _, d4, _, _, _, _, r2, _, _, r5, _, k2, _, _, k5, _, n2, _, _, n5, -⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .r8 := h.regs (.rbx, .r8) (by decide)
  have e2 : s.gpr .r13 = σ.gpr .rsi := h.regs (.r13, .rsi) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of (by decide) (List.pairwise_pair.mpr ?_) (fa2 ?_ ?_) (fa2 ?_ ?_) (fa2 ?_ ?_)
    (List.forall_mem_singleton.mpr ?_) (fa2 ?_ ?_)
    <;> simp only [e1, e2, h.rsp, retR]
  · exact fun _ => d4
  exacts [k2, k5, n2, n5, mem ⟨σ.gpr .rsi, 17984⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .r8, 49152⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, r2, r5]

end

/-- `dk`, `c` and `ekx`. -/
abbrev dcxDk (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 3168
abbrev dcxC (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdx) 1568

/-- The matrix the expanded key holds. -/
abbrev dcxA (σ : State) (i j : Nat) : Poly := polyAt σ.mem (σ.gpr .rsi + BitVec.ofNat 64 (mlKem1024.ekxA i j))

/-- What holds throughout. -/
structure DCX (σ s : State) : Prop where
  top : Top dcxM σ s
  dk : bytesAt s.mem (pa s (.rbp, 0)) 3168 = dcxDk σ
  c : bytesAt s.mem (pa s (.r14, 0)) 1568 = dcxC σ

theorem DCX.lay {σ : State} (hp : decapsX1024K.pre σ) {s : State} (h : DCX σ s) : Lay dcR dcW s := dcxLay hp h.top

theorem DCX.step {σ : State} (hp : decapsX1024K.pre σ) {s s' : State} (h : DCX σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hc : dcChk ws = true) : DCX σ s' := by
  simp only [dcChk, Bool.and_eq_true] at hc
  have L := h.lay hp
  exact ⟨h.top.step L hP dcxM_bases hc.1.1, by rw [L.keepBytes hP hc.1.2]; exact h.dk,
    by rw [L.keepBytes hP hc.2]; exact h.c⟩

/-- `Â` in the working space. -/
def MatAt (σ s : State) : Prop := ∀ i < 4, ∀ j < 4, PolyIs s.mem (pa s (aS4 i j)) (dcxA σ i j)

/-- A piece that writes `ws` keeps `Â`. -/
def matKeep (ws : List (Ptr × Nat)) : Bool := (List.range 16).all fun e => keepB dcB ws (aS4 (e / 4) (e % 4)) 1024

theorem MatAt.keep {σ s s' : State} (h : MatAt σ s) (L : Lay dcR dcW s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hc : matKeep ws = true) : MatAt σ s' := fun i hi j hj => by
  simp only [matKeep, List.all_eq_true, List.mem_range] at hc
  have := hc (4 * i + j) (by omega)
  rw [show (4 * i + j) / 4 = i by omega, show (4 * i + j) % 4 = j by omega] at this
  exact L.keepPoly hP this (h i hi j hj)

/-- What holds while the function decrypts: `DCX`, and `Â`. -/
def dcxChk (ws : List (Ptr × Nat)) : Bool := dcChk ws && matKeep ws

theorem dcx_lrel {σ₁ σ₂ x y : State} (p₁ : decapsX1024K.pre σ₁) (p₂ : decapsX1024K.pre σ₂) (pub : decapsX1024K.pub σ₁ σ₂)
    (h₁ : DCX σ₁ x) (h₂ : DCX σ₂ y) : LRel dcR dcW x y := by
  obtain ⟨e1, _, e3, e4, e5, e6⟩ := pub
  refine ⟨h₁.lay p₁, h₂.lay p₂, fa4 ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e6]⟩
  · rw [h₁.top.regs (.rbp, .rdi) (by decide), h₂.top.regs (.rbp, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.r14, .rdx) (by decide), h₂.top.regs (.r14, .rdx) (by decide), e3]
  · rw [h₁.top.regs (.rbx, .r8) (by decide), h₂.top.regs (.rbx, .r8) (by decide), e5]
  · rw [h₁.top.regs (.r12, .rcx) (by decide), h₂.top.regs (.r12, .rcx) (by decide), e4]

theorem dcxChks : Decaps4.decWs.all dcxChk = true := by decide

/-- What the function holds of its state while it decrypts. -/
def dcxD : Decaps4.DCtx where
  Pre := decapsX1024K.pre
  Pub := decapsX1024K.pub
  Out σ s := DCX σ s ∧ MatAt σ s
  chk := dcxChk
  dk := dcxDk
  c := dcxC
  lay hp h := h.1.lay hp
  step hp h hP hc := by
    simp only [dcxChk, Bool.and_eq_true] at hc
    exact ⟨h.1.step hp hP hc.1, h.2.keep (h.1.lay hp) hP hc.2⟩
  dkAt h := h.1.dk
  cAt h := h.1.c
  lrel p₁ p₂ pub h₁ h₂ := dcx_lrel p₁ p₂ pub h₁.1 h₂.1
  chks := dcxChks

theorem dcxD_dk (σ : State) : dcxD.dk σ = dcxDk σ := by simp only [dcxD]
theorem dcxD_c (σ : State) : dcxD.c σ = dcxC σ := by simp only [dcxD]

theorem pro_eq : DecapsX1024.pro = [.store (at_ .r8 840) .rbx, .store (at_ .r8 848) .rbp, .store (at_ .r8 856) .r12,
    .store (at_ .r8 864) .r13, .store (at_ .r8 872) .r14, .store (at_ .r8 880) .r15, .mov .rbx (.reg .r8),
    .mov .rbp (.reg .rdi), .mov .r13 (.reg .rsi), .mov .r14 (.reg .rdx), .mov .r12 (.reg .rcx),
    .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {σ : State} (hp : decapsX1024K.pre σ) : WP isa (.block DecapsX1024.pro) σ fun s => DCX σ s ∧
    s.gpr .r15 = 1 ∧ bytesAt s.mem (pa s (.r13, 0)) 17984 = bytesAt σ.mem (σ.gpr .rsi) 17984 := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5,
    -⟩ := hp'
  have hS : ⟨σ.gpr .r8, 49152⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ 49152 → (⟨σ.gpr .r8, 49152⟩ : Region).Contains (σ.gpr .r8 + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega)
  have w : ∀ o, o + 8 ≤ 49152 → InRegions σ.wr (σ.gpr .r8 + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .r8 + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .r8 + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .r8 + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .r8 ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r13 = σ.gpr .rsi ∧ s.gpr .r14 = σ.gpr .rdx ∧
    s.gpr .r12 = σ.gpr .rcx ∧ s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h13, h14, h12, h15⟩, k⟩ => ?_
  have hf : Frame [⟨σ.gpr .r8, 49152⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨⟨k.2.1, k.2.2, hsp, fa5 hbx hbp h13 h14 h12, fun j hj => ?_, ?_⟩, ?_, ?_⟩, h15, ?_⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .r8) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r5) (by decide)
  · rw [pa, hbp, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d2) (by decide)
  · rw [pa, h14, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d6) (by decide)
  · rw [pa, h13, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d4) (by decide)

/-! ## `Â` -/

/-- After `Â`. -/
abbrev DXM (σ s : State) : Prop := (DCX σ s ∧ MatAt σ s) ∧ s.gpr .r15 = 1

theorem matIn_ok {σ : State} (hp : decapsX1024K.pre σ) {s : State}
    (h : DCX σ s ∧ s.gpr .r15 = 1 ∧ bytesAt s.mem (pa s (.r13, 0)) 17984 = bytesAt σ.mem (σ.gpr .rsi) 17984) :
    WP isa (matIn4 .r13) s (DXM σ) := by
  have L := mLay hp h.1.top
  unfold matIn4
  refine WP.mono (copy16_okL L (dst := aS4 0 0) (src := (.r13, oXA4)) (n := 1024) (by decide) (by decide))
    fun s' ⟨hP, hb⟩ => ?_
  have hx := h.2.2
  have e13 : s.gpr .r13 = σ.gpr .rsi := h.1.top.regs (.r13, .rsi) (by decide)
  rw [pa, e13, add_ofNat_zero] at hx
  have hb' : bytesAt s'.mem (pa s (aS4 0 0)) (16 * 1024) =
      bytesAt σ.mem (σ.gpr .rsi + BitVec.ofNat 64 oXA4) (16 * 1024) := by
    rw [hb]
    show bytesAt s.mem (s.gpr .r13 + BitVec.ofNat 64 oXA4) (16 * 1024) = _
    rw [e13, ← bytesAt_slice _ _ (show oXA4 + 16 * 1024 ≤ 17984 by decide), hx,
      bytesAt_slice _ _ (show oXA4 + 16 * 1024 ≤ 17984 by decide)]
  refine ⟨⟨h.1.step hp hP.b (by decide), fun i hi j hj => ?_⟩, by rw [hP.cs .r15 (by decide)]; exact h.2.1⟩
  have hx := ((decapsX1024K_ekx hp).2.2.1) i hi j hj
  have e₁ : σ.gpr .rsi + BitVec.ofNat 64 (mlKem1024.ekxA i j) =
      σ.gpr .rsi + BitVec.ofNat 64 oXA4 + BitVec.ofNat 64 (1024 * (4 * i + j)) := by
    rw [off_add]; rfl
  have e₂ : pa s' (aS4 i j) = pa s (aS4 0 0) + BitVec.ofNat 64 (1024 * (4 * i + j)) := by
    rw [hP.pa rbx_cs, pa, pa, off_add]
    exact congrArg (fun k => s.gpr .rbx + BitVec.ofNat 64 k) (by simp only [oP]; omega)
  rw [e₂]
  exact polyIs_copied hb' (by omega) ⟨by rw [← e₁]; exact hx, by rw [← e₁]⟩

/-! ## K-PKE.Decrypt -/

theorem decrypt_ok {σ : State} (hp : decapsX1024K.pre σ) {s : State} (h : DXM σ s) :
    WP isa decrypt s (Decaps4.DM dcxD σ) := by
  unfold decrypt
  refine WP.seq (WP.mono (seqR_ok (I := fun k => Decaps4.DR dcxD k 0 σ) 4 0
    (fun k _ hk s hs => Decaps4.u_ok (D := dcxD) hp (by omega) hs) s (Decaps4.DR.zero h.1 h.2)) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => Decaps4.DR dcxD 4 k σ) 4 0
    (fun k _ hk s hs => Decaps4.s_ok (D := dcxD) hp (by omega) hs) s₁ h₁) fun s₂ h₂ => ?_)
  exact Decaps4.tail_ok (D := dcxD) hp h₂

/-! ## `G(m' ‖ h)` and `J(z ‖ c)` -/

/-- `m'`, `(K', r') = G(m' ‖ h)`, `K̄ = J(z ‖ c)` and the encryption key of `σ`. -/
abbrev dcxM' (σ : State) : List Byte := decM1024 (dcxDk σ) (dcxC σ)
abbrev dcxG (σ : State) : List Byte × List Byte := G (dcxM' σ ++ dkH1024 (dcxDk σ))
abbrev dcxKb (σ : State) : List Byte := J (dkZ1024 (dcxDk σ) ++ dcxC σ)
abbrev dcxEk (σ : State) : List Byte := dkEk1024 (dcxDk σ)

/-- What `K-PKE.Encrypt` keeps: `DCX`, `K'` at `G` and `K̄` at `KB`. -/
structure DCXK (σ s : State) : Prop where
  dc : DCX σ s
  k : bytesAt s.mem (pa s (sc oG)) 32 = (dcxG σ).1
  kb : bytesAt s.mem (pa s (sc oKB)) 32 = dcxKb σ

theorem DCXK.step {σ : State} (hp : decapsX1024K.pre σ) {s s' : State} (h : DCXK σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hc : dckChk ws = true) : DCXK σ s' := by
  simp only [dckChk, Bool.and_eq_true] at hc
  have L := h.dc.lay hp
  exact ⟨h.dc.step hp hP hc.1.1, by rw [L.keepBytes hP hc.1.2]; exact h.k, by rw [L.keepBytes hP hc.2]; exact h.kb⟩

/-- The context of `K-PKE.Encrypt` in a run from `σ`. -/
def dcxX (σ : State) : Ctx dcR dcW where
  Out s := decapsX1024K.pre σ ∧ DCXK σ s
  chk := dckChk
  bs := dcB_bases
  lay h := h.2.dc.lay h.1
  step h hP hc := ⟨h.1, h.2.step h.1 hP hc⟩

/-- The context of `K-PKE.Encrypt` in any run. -/
def dcxXA : Ctx dcR dcW where
  Out s := ∃ σ, decapsX1024K.pre σ ∧ DCXK σ s
  chk := dckChk
  bs := dcB_bases
  lay := fun ⟨_, hp, h⟩ => h.dc.lay hp
  step := fun ⟨σ, hp, h⟩ hP hc => ⟨σ, hp, h.step hp hP hc⟩

/-- Before `K-PKE.Encrypt`'s steps after its matrix. -/
abbrev ERX (σ s : State) : Prop := Enc4.ER (dcxX σ) (.rbp, 1536) (dcxA σ) (dcxEk σ) (dcxM' σ) (dcxG σ).2 0 0 0 s

theorem hashes_ok {σ : State} (hp : decapsX1024K.pre σ) {s : State} (h : Decaps4.DM dcxD σ s) : WP isa hashes s (ERX σ) := by
  have hm := h.m
  rw [dcxD_dk, dcxD_c] at hm
  have hd : DCX σ s := h.out.1
  have L := hd.lay hp
  unfold hashes
  -- `G(m' ‖ h)`.
  refine WP.seq (WP.mono (hash_ok dcB_bases (ps := [(sc oM, 32), ((.rbp, 3104), 32)]) (rate := 72) (out := sc oG)
    (len := 64) (by decide) (show 6 < 256 by decide) L) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := hd.step hp hP₁.b (by decide)
  have m₁ := h.out.2.keep L hP₁.b (by decide)
  have L₁ := k₁.lay hp
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hm,
    slice_of hd.dk (show 3104 + 32 ≤ 3168 by decide), KeyGen.sha3Suffix6] at hb₁
  rw [← sha3_512_eq, ← hP₁.pa rbx_cs] at hb₁
  -- `J(z ‖ c)`.
  refine WP.mono (hash_ok dcB_bases (ps := [((.rbp, 3136), 32), ((.r14, 0), 1568)]) (rate := 136) (out := sc oKB)
    (len := 32) (by decide) (show 0x1f < 256 by decide) L₁) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have k₂ := k₁.step hp hP₂.b (by decide)
  have m₂ := m₁.keep L₁ hP₂.b (by decide)
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, k₁.c,
    slice_of k₁.dk (show 3136 + 32 ≤ 3168 by decide), Decaps.shakeSuffix31] at hb₂
  rw [← J_eq, ← hP₂.pa rbx_cs] at hb₂
  have hG : bytesAt s₂.mem (pa s₂ (sc oG)) 64 = Spec.Sha3.sha3_512 (dcxM' σ ++ dkH1024 (dcxDk σ)) := by
    rw [L₁.keepBytes hP₂.b (by decide)]; exact hb₁
  have hK : bytesAt s₂.mem (pa s₂ (sc oG)) 32 = (dcxG σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hG]; rfl
  have hr : bytesAt s₂.mem (pa s₂ sigP) 32 = (dcxG σ).2 := by
    have e := bytesAt_drop s₂.mem (pa s₂ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₂.mem (pa s₂ (sc oG)) 64).drop 32 = bytesAt s₂.mem (pa s₂ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hG]; rfl
  refine ⟨⟨⟨hp, k₂, hK, hb₂⟩, slice_of k₂.dk (show 1536 + 1568 ≤ 3168 by decide), ?_, hr⟩, ?_, m₂,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · rw [L₁.keepBytes hP₂.b (by decide), L.keepBytes hP₁.b (by decide)]; exact hm
  · rw [hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15]

/-! ## The key -/

/-- The end of `K-PKE.Encrypt`. -/
abbrev EncO (σ s : State) : Prop := (dcxX σ).Out s ∧ s.gpr .r15 = 1 ∧
  bytesAt s.mem (pa s (sc oCT4)) 1568 = ct1024 (dcxA σ) (dcxEk σ) (dcxM' σ) (dcxG σ).2

/-- At the end: the key. -/
structure DXEnd (σ s : State) : Prop where
  dc : DCX σ s
  key : bytesAt s.mem (pa s (.r12, 0)) 32 =
    if dcxC σ = ct1024 (dcxA σ) (dcxEk σ) (dcxM' σ) (dcxG σ).2 then (dcxG σ).1 else dcxKb σ

theorem select_ok {σ : State} {s : State} (h : EncO σ s) : WP isa select s (DXEnd σ) := by
  have hp := h.1.1
  have k := h.1.2
  have L := k.dc.lay hp
  have cR : ∀ {p : Ptr} {l : Nat}, inB dcB p l = true → InRegions (s.rd ++ s.wr) (pa s p) l := fun hi =>
    L.cR hi _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (Decaps4.select4_ok (cR (p := (.r14, 0)) (l := 1568) (by decide))
    (cR (p := sc oCT4) (l := 1568) (by decide)) (cR (p := sc oG) (l := 32) (by decide))
    (cR (p := sc oKB) (l := 32) (by decide))
    (L.cW (show inB dcW (.r12, 0) 32 = true by decide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    (L.disj (show sepB dcB (sc oG) 32 (.r12, 0) 32 = true by decide))
    (L.disj (show sepB dcB (sc oKB) 32 (.r12, 0) 32 = true by decide))) fun s' ⟨hP, hb⟩ => ?_
  refine ⟨k.dc.step hp hP.b (by decide), ?_⟩
  rw [hP.pa KeyGen.r12_cs, hb]
  exact ite_congr (propext (by rw [k.dc.c, h.2.2])) (fun _ => k.k) (fun _ => k.kb)

theorem DXEnd.hin {σ s : State} (hp : decapsX1024K.pre σ) (h : DXEnd σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk => by
  have hk' : ∀ k < 6, inB dcB (sc (oSV + 8 * k)) 8 = true := by decide
  exact (h.dc.lay hp).cR (hk' k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem dkEk1024_eq {σ : State} : bytesAt σ.mem (σ.gpr .rdi + BitVec.ofNat 64 (384 * mlKem1024.k)) mlKem1024.ekLen =
    dcxEk σ := by
  show _ = ((bytesAt σ.mem (σ.gpr .rdi) 3168).drop 1536).take 1568
  rw [bytesAt_slice _ _ (show 1536 + 1568 ≤ 3168 by decide)]
  rfl

/-- The postcondition, from the key: for every bound for which
`Decaps_internal` returns, `ExpandedEk` gives that the matrix it samples is
`dcxA`. -/
theorem post_of {σ s : State} (hp : decapsX1024K.pre σ) (h : DXEnd σ s) {s' : State} (hm : s'.mem = s.mem) :
    decapsX1024K.post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rcx := by
    rw [pa, h.dc.top.regs (.r12, .rcx) (by decide), add_ofNat_zero]
  have hx := decapsX1024K_ekx hp
  unfold DecapsExpandedPre at hx
  rw [dkEk1024_eq] at hx
  intro iters r hr
  change decapsInternal mlKem1024 iters (dcxDk σ) (dcxC σ) = some r at hr
  rw [decapsInternal1024] at hr
  by_cases hall : ∀ i < 4, ∀ j < 4, (sampleNTT iters (matSeed (Enc4.rhoE (dcxEk σ)) i j)).isSome
  · have hs : ∀ i < 4, ∀ j < 4, sampleNTT iters (matSeed (Enc4.rhoE (dcxEk σ)) i j) =
        some ((sampleNTT iters (matSeed (Enc4.rhoE (dcxEk σ)) i j)).getD zero) := fun i hi j hj => by
      have := hall i hi j hj
      cases e : sampleNTT iters (matSeed (Enc4.rhoE (dcxEk σ)) i j) with
      | none => rw [e] at this; cases this
      | some f => rfl
    have hM := sampleMatrix_some hs
    have hA : ∀ i < 4, ∀ j < 4, sampleNTT iters (matSeed (ekRho mlKem1024 (dcxEk σ)) i j) = some (dcxA σ i j) :=
      fun i hi j hj => by
        show _ = some (polyAt σ.mem (σ.gpr .rsi + BitVec.ofNat 64 (mlKem1024.ekxA i j)))
        rw [hx.2.2.2 iters _ hM i hi j hj]
        exact sampleMatrix_entry hM hi hj
    rw [kpkeEncrypt1024_some hA, Option.map_some, Option.some.injEq] at hr
    rw [← hr, hm, ← e12, h.key]
  · obtain ⟨i, hi, j, hj, hn⟩ : ∃ i < 4, ∃ j < 4, sampleNTT iters (matSeed (Enc4.rhoE (dcxEk σ)) i j) = none := by
      refine Classical.byContradiction fun hc => hall fun i hi j hj => ?_
      cases e : sampleNTT iters (matSeed (Enc4.rhoE (dcxEk σ)) i j) with
      | none => exact absurd ⟨i, hi, j, hj, e⟩ hc
      | some _ => rfl
    rw [kpkeEncrypt1024_none hi hj hn] at hr
    cases hr

end DecapsX4

open DecapsX4 in
theorem decapsX1024_correct (σ : State) (hp : decapsX1024K.pre σ) :
    ∃ t s', Exec isa Impl.MlKem1024.X86_64.decapsX1024 σ t s' ∧ abiPreserved σ s' ∧ decapsX1024K.post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun s₁ h₁ =>
    WP.seq (WP.mono (matIn_ok hp h₁) fun s₂ h₂ =>
      WP.seq (WP.mono (decrypt_ok hp h₂) fun s₃ h₃ =>
        WP.seq (WP.mono (hashes_ok hp h₃) fun s₄ h₄ =>
          WP.seq (WP.mono (Enc4.rest_ok (C := dcxX σ) (Enc4.encChk_spec Decaps4.dcEncChk) h₄) fun s₅ h₅ =>
            WP.seq (WP.mono (select_ok h₅) fun s₆ h₆ =>
              WP.mono (topEpi_ok h₆.dc.top (h₆.hin hp)) fun s₇ ⟨_, hg, hm⟩ =>
                (⟨hg, post_of hp h₆ hm⟩ : gprPreserved σ s₇ ∧ decapsX1024K.post σ s₇)))))))
  exact ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he hF.1, hF.2⟩

/-! ## Constant time -/

namespace DecapsX4

open VG.Impl.MlKem1024.X86_64.Decaps1024
open Decaps4 (dcR dcW dcB dcB_bases dcEncChk)

abbrev R (I : State → State → Prop) : State → State → Prop := Rel2 decapsX1024K.pre decapsX1024K.pub I

theorem pro_tr : RelCT isa (R fun σ s => s = σ) (.block DecapsX1024.pro) fun _ _ => True :=
  taintRel [.r8, .rdi, .rsi, .rdx, .rcx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa5 pub.2.2.2.2.1 pub.1 pub.2.1 pub.2.2.1 pub.2.2.2.1) (by taint_decide)

theorem matIn_tr : RelCT isa (R fun σ s => DCX σ s ∧ s.gpr .r15 = 1 ∧
    bytesAt s.mem (pa s (.r13, 0)) 17984 = bytesAt σ.mem (σ.gpr .rsi) 17984) (matIn4 .r13) fun _ _ => True :=
  taintRel [.rbx, .r13] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => fa2
    (by rw [h₁.1.top.regs (.rbx, .r8) (by decide), h₂.1.top.regs (.rbx, .r8) (by decide), pub.2.2.2.2.1])
    (by rw [h₁.1.top.regs (.r13, .rsi) (by decide), h₂.1.top.regs (.r13, .rsi) (by decide), pub.2.1]))
    (by taint_decide)

theorem decrypt_tr : RelCT isa (R DXM) decrypt fun _ _ => True := by
  unfold decrypt
  refine RelCT.seq (RelCT.mono (seqR_tr (R := fun k => Decaps4.R dcxD (Decaps4.DR dcxD k 0)) 4 0
    fun k _ hk => relInv (fun σ s hp hs => Decaps4.u_ok (D := dcxD) hp (by omega) hs) (Decaps4.u_tr (by omega)))
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, Decaps4.DR.zero h₁.1 h₁.2,
      Decaps4.DR.zero h₂.1 h₂.2⟩)
    fun _ _ h => h) ?_
  refine RelCT.seq (seqR_tr (R := fun k => Decaps4.R dcxD (Decaps4.DR dcxD 4 k)) 4 0
    fun k _ hk => relInv (fun σ s hp hs => Decaps4.s_ok (D := dcxD) hp (by omega) hs) (Decaps4.s_tr (by omega))) ?_
  exact Decaps4.tail_tr (D := dcxD)

theorem hashes_tr : RelCT isa (R (Decaps4.DM dcxD)) hashes fun _ _ => True :=
  rel2_of Decaps4.hashes_trL fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dcx_lrel p₁ p₂ pub h₁.out.1 h₂.out.1

theorem ER.any {σ : State} {a : Nat → Nat → Poly} {ek m r : List Byte} {s : State}
    (h : Enc4.ER (dcxX σ) (.rbp, 1536) a ek m r 0 0 0 s) : Enc4.ER dcxXA (.rbp, 1536) a ek m r 0 0 0 s :=
  ⟨⟨⟨σ, h.i.out⟩, h.i.ek, h.i.m, h.i.r⟩, h.r15, h.mat, h.y, h.u, h.t⟩

theorem rest_tr : RelCT isa (R ERX) (Encrypt1024.rest (.rbp, 1536)) fun _ _ => True :=
  RelCT.mono (Enc4.rest_tr (C := dcxXA) (Enc4.encChk_spec dcEncChk) (P := fun _ _ => True))
    (fun _ _ ⟨_, _, p₁, p₂, pub, h₁, h₂⟩ => ⟨dcx_lrel p₁ p₂ pub h₁.i.out.2.dc h₂.i.out.2.dc,
      ⟨_, _, _, _, trivial, ER.any h₁⟩, ⟨_, _, _, _, trivial, ER.any h₂⟩⟩) fun _ _ _ => trivial

theorem select_tr : RelCT isa (R EncO) select fun _ _ => True :=
  rel2_of (Q := LRel dcR dcW) (taintRel [.rbx, .r12, .r14] (fun x y h =>
    fa3 (h.eq (p := sc 0) (l := 1) (by decide)) (h.eq (p := (.r12, 0)) (l := 1) (by decide))
      (h.eq (p := (.r14, 0)) (l := 1) (by decide))) (by taint_decide))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dcx_lrel p₁ p₂ pub h₁.1.2.dc h₂.1.2.dc

theorem epi_tr : RelCT isa (R DXEnd) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.dc.top.regs (.rbx, .r8) (by decide), h₂.dc.top.regs (.rbx, .r8) (by decide), pub.2.2.2.2.1])
    (by taint_decide)

end DecapsX4

open DecapsX4 in
theorem decapsX1024_ct : ConstantTime isa decapsX1024K.pre decapsX1024K.pub Impl.MlKem1024.X86_64.decapsX1024 := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold Impl.MlKem1024.X86_64.decapsX1024
  refine RelCT.seq (relInv (I' := fun σ s => DCX σ s ∧ s.gpr .r15 = 1 ∧
    bytesAt s.mem (pa s (.r13, 0)) 17984 = bytesAt σ.mem (σ.gpr .rsi) 17984)
    (fun σ s hp hs => by subst hs; exact pro_ok hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := DXM) (fun σ s hp hs => matIn_ok hp hs) matIn_tr) ?_
  refine RelCT.seq (relInv (I' := Decaps4.DM dcxD) (fun σ s hp hs => decrypt_ok hp hs) decrypt_tr) ?_
  refine RelCT.seq (relInv (I' := ERX) (fun σ s hp hs => hashes_ok hp hs) hashes_tr) ?_
  refine RelCT.seq (relInv (I' := EncO) (fun σ s _ hs =>
    Enc4.rest_ok (C := dcxX σ) (Enc4.encChk_spec Decaps4.dcEncChk) hs) rest_tr) ?_
  refine RelCT.seq (relInv (I' := DXEnd) (fun σ s _ hs => select_ok hs) select_tr) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem1024.X86_64
