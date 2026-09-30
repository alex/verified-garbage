import VerifiedGarbage.Proof.MlKem1024.X86_64.EcTop
import VerifiedGarbage.Impl.MlKem1024.X86_64.Expanded
import VerifiedGarbage.Proof.MlKem.X86_64.FragX
import VerifiedGarbage.Proof.MlKem.Expanded

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_encaps_expanded`

Untrusted: everything here is checked by Lean. `vg_mlkem1024_encaps`'s
proof (`EcBase.lean`, `EcTop.lean`), with the expanded key `ekx` (17984
bytes) where `ek` was: `H(ek)` is copied from `ekx` rather than computed
(`hashes_ok`), and `Â` is copied from `ekx` to the working space rather than
sampled (`matIn_ok`), so that `K-PKE.Encrypt` runs with the matrix
`ecA`, whatever `ekx` holds. When `SampleNTT` samples the matrix of the
key's `ρ` for some bound, `ecA` is that matrix (`ExpandedEk`), so the
outputs are those of `ML-KEM.Encaps_internal` (`post_of`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mlkem1024_encaps_expanded(ekx = rdi, m = rsi, key = rdx, ct = rcx, scratch = r8)`, with 32 bytes of
stack. -/
def encapsX1024K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 17984⟩, ⟨s.gpr .rsi, 32⟩] ∧
    s.wr = [⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, 1568⟩, ⟨s.gpr .r8, 49152⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 17984⟩ ⟨s.gpr .rdx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 17984⟩ ⟨s.gpr .rcx, 1568⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 17984⟩ ⟨s.gpr .r8, 49152⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rdx, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rcx, 1568⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .r8, 49152⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, 1568⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r8, 49152⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, 1568⟩ ⟨s.gpr .r8, 49152⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 17984⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 32⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, 1568⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, 49152⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, 17984⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, 32⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, 1568⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .r8, 49152⟩ ∧
    (s.gpr .rdi).toNat + 17984 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 1568 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + 49152 ≤ 2 ^ 64 ∧
    ExpandedEk mlKem1024 s.mem (s.gpr .rdi) (bytesAt s.mem (s.gpr .rdi) 1568)
  post s s' := EncapsExpandedPost mlKem1024 (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

theorem encapsX1024K_ekx {σ : State} (hp : encapsX1024K.pre σ) :
    ExpandedEk mlKem1024 σ.mem (σ.gpr .rdi) (bytesAt σ.mem (σ.gpr .rdi) 1568) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hp
  exact h

namespace EncapsX4

open VG.Impl.MlKem1024.X86_64.EncapsX1024
open Encaps4 (ecM ecW ecM_bases ecEk ecMs ecG)

/-- `ekx` and `m`. -/
abbrev ecxR : List (Reg × Nat) := [(.r14, 17984), (.rbp, 32)]
abbrev ecxB : List (Reg × Nat) := ecxR ++ ecW

theorem ecxB_bases : ∀ b ∈ ecxB, b.1 ∈ bases := by decide

section
variable {σ : State} (hp : encapsX1024K.pre σ)
include hp

theorem ecxLay {s : State} (h : Top ecM σ s) : Lay ecxR ecW s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5,
    -⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .r8 := h.regs (.rbx, .r8) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rsi := h.regs (.rbp, .rsi) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rdx := h.regs (.r12, .rdx) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .rcx := h.regs (.r13, .rcx) (by decide)
  have e5 : s.gpr .r14 = σ.gpr .rdi := h.regs (.r14, .rdi) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of (by decide) (pw5 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_)
    (fa5 ?_ ?_ ?_ ?_ ?_) (fa3 ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, e5, h.rsp, retR]
  · exact fun hw => absurd hw (by decide)
  · exact fun _ => d3
  · exact fun _ => d1
  · exact fun _ => d2
  · exact fun _ => d6
  · exact fun _ => d4
  · exact fun _ => d5
  · exact fun _ => d8.symm
  · exact fun _ => d9.symm
  · exact fun _ => d7
  exacts [k1, k2, k5, k3, k4, n1, n2, n5, n3, n4,
    mem ⟨σ.gpr .rdi, 17984⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rsi, 32⟩ (by rw [hrd]; simp),
    mem ⟨σ.gpr .r8, 49152⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, 32⟩ (by rw [hwr]; simp),
    mem ⟨σ.gpr .rcx, 1568⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, r1, r2, r5, r3, r4]

end

/-- What holds throughout: `Top`, and `ekx` and `m` at their pointers. -/
structure ECX (σ s : State) : Prop where
  top : Top ecM σ s
  x : bytesAt s.mem (pa s (.r14, 0)) 17984 = bytesAt σ.mem (σ.gpr .rdi) 17984
  m : bytesAt s.mem (pa s (.rbp, 0)) 32 = ecMs σ

/-- A piece that writes `ws` keeps `ECX`. -/
def ecxChk (ws : List (Ptr × Nat)) : Bool :=
  topChk ecxB ws && keepB ecxB ws (.r14, 0) 17984 && keepB ecxB ws (.rbp, 0) 32

theorem ECX.lay {σ : State} (hp : encapsX1024K.pre σ) {s : State} (h : ECX σ s) : Lay ecxR ecW s := ecxLay hp h.top

theorem ECX.step {σ : State} (hp : encapsX1024K.pre σ) {s s' : State} (h : ECX σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hc : ecxChk ws = true) : ECX σ s' := by
  simp only [ecxChk, Bool.and_eq_true] at hc
  have L := h.lay hp
  exact ⟨h.top.step L hP ecM_bases hc.1.1, by rw [L.keepBytes hP hc.1.2]; exact h.x,
    by rw [L.keepBytes hP hc.2]; exact h.m⟩

/-- `c` bytes of `ekx` from byte `o`. -/
theorem ECX.slice {σ s : State} (h : ECX σ s) {o c : Nat} (hoc : o + c ≤ 17984) :
    bytesAt s.mem (pa s (.r14, o)) c = bytesAt σ.mem (σ.gpr .rdi + BitVec.ofNat 64 o) c := by
  have hx := h.x
  rw [pa, h.top.regs (.r14, .rdi) (by decide), add_ofNat_zero] at hx
  show bytesAt s.mem (s.gpr .r14 + BitVec.ofNat 64 o) c = _
  rw [h.top.regs (.r14, .rdi) (by decide), ← bytesAt_slice _ _ hoc, ← bytesAt_slice _ _ hoc, hx]

theorem ECX.ek {σ s : State} (h : ECX σ s) : bytesAt s.mem (pa s (.r14, 0)) 1568 = ecEk σ := by
  rw [← bytesAt_take _ _ (show 1568 ≤ 17984 by decide), h.x, bytesAt_take _ _ (show 1568 ≤ 17984 by decide)]

/-- What `K-PKE.Encrypt` keeps: `ECX`, and `K` at `G`. -/
structure ECXK (σ s : State) : Prop where
  ec : ECX σ s
  k : bytesAt s.mem (pa s (sc oG)) 32 = (ecG σ).1

def eckxChk (ws : List (Ptr × Nat)) : Bool := ecxChk ws && keepB ecxB ws (sc oG) 32

theorem ECXK.step {σ : State} (hp : encapsX1024K.pre σ) {s s' : State} (h : ECXK σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hc : eckxChk ws = true) : ECXK σ s' := by
  simp only [eckxChk, Bool.and_eq_true] at hc
  exact ⟨h.ec.step hp hP hc.1, by rw [(h.ec.lay hp).keepBytes hP hc.2]; exact h.k⟩

/-- The context of `K-PKE.Encrypt` in a run from `σ`. -/
def ecxC (σ : State) : Ctx ecxR ecW where
  Out s := encapsX1024K.pre σ ∧ ECXK σ s
  chk := eckxChk
  bs := ecxB_bases
  lay h := h.2.ec.lay h.1
  step h hP hc := ⟨h.1, h.2.step h.1 hP hc⟩

/-- The context of `K-PKE.Encrypt` in any run. -/
def ecxCA : Ctx ecxR ecW where
  Out s := ∃ σ, encapsX1024K.pre σ ∧ ECXK σ s
  chk := eckxChk
  bs := ecxB_bases
  lay := fun ⟨_, hp, h⟩ => h.ec.lay hp
  step := fun ⟨σ, hp, h⟩ hP hc => ⟨σ, hp, h.step hp hP hc⟩

theorem ecxEncChk : Enc4.encChk (ecxR ++ ecW) ecW eckxChk (.r14, 0) = true := by decide

theorem pro_ok {σ : State} (hp : encapsX1024K.pre σ) :
    WP isa (.block Encaps1024.pro) σ fun s => ECX σ s ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, n1, n2, n3, n4,
    n5, -⟩ := hp'
  have hS : ⟨σ.gpr .r8, 49152⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ 49152 → (⟨σ.gpr .r8, 49152⟩ : Region).Contains (σ.gpr .r8 + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega)
  have w : ∀ o, o + 8 ≤ 49152 → InRegions σ.wr (σ.gpr .r8 + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [Encaps4.pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .r8 + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .r8 + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .r8 + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .r8 ∧ s.gpr .rbp = σ.gpr .rsi ∧ s.gpr .r12 = σ.gpr .rdx ∧ s.gpr .r13 = σ.gpr .rcx ∧
    s.gpr .r14 = σ.gpr .rdi ∧ s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h13, h14, h15⟩, k⟩ => ⟨?_, h15⟩
  have hf : Frame [⟨σ.gpr .r8, 49152⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨k.2.1, k.2.2, hsp, fa5 hbx hbp h12 h13 h14, fun j hj => ?_, ?_⟩, ?_, ?_⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .r8) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r5) (by decide)
  · rw [pa, h14, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d3) (by decide)
  · rw [pa, hbp, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d6) (by decide)

/-! ## `H(ek)` and `G(m ‖ H(ek))` -/

/-- The inputs of `K-PKE.Encrypt`, and `r15 = 1`. -/
abbrev EncI (σ s : State) : Prop := Enc4.EIn (ecxC σ) (.r14, 0) (ecEk σ) (ecMs σ) (ecG σ).2 s ∧ s.gpr .r15 = 1

theorem hashes_ok {σ : State} (hp : encapsX1024K.pre σ) {s : State} (h : ECX σ s) (h15 : s.gpr .r15 = 1) :
    WP isa hashes s (EncI σ) := by
  have L := h.lay hp
  unfold hashes
  -- `m` to `M`.
  refine WP.seq (WP.mono (copy_okL L (dst := sc oM) (src := (.rbp, 0)) (n := 32) (by decide) (by decide))
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.step hp hP₁.b (by decide)
  have L₁ := k₁.lay hp
  rw [h.m] at hb₁
  -- `H(ek)` from `ekx`.
  refine WP.seq (WP.mono (copy_okL L₁ (dst := sc oH) (src := (.r14, oXH4)) (n := 32) (by decide) (by decide))
    fun s₂ ⟨hP₂, hb₂⟩ => ?_)
  have k₂ := k₁.step hp hP₂.b (by decide)
  have L₂ := k₂.lay hp
  have hH : bytesAt σ.mem (σ.gpr .rdi + BitVec.ofNat 64 oXH4) 32 = H (ecEk σ) := (encapsX1024K_ekx hp).2.1
  rw [k₁.slice (show oXH4 + 32 ≤ 17984 by decide), hH, ← hP₂.pa rbx_cs] at hb₂
  have hM₂ : bytesAt s₂.mem (pa s₂ (sc oM)) 32 = ecMs σ := by
    rw [L₁.keepBytes hP₂.b (by decide), hP₁.pa rbx_cs, hb₁]
  -- `G(m ‖ H(ek))`.
  refine WP.mono (hash_ok ecxB_bases (ps := [(sc oM, 32), (sc oH, 32)]) (rate := 72) (out := sc oG) (len := 64)
    (by decide) (show 6 < 256 by decide) L₂) fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have k₃ := k₂.step hp hP₃.b (by decide)
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hM₂, hb₂, KeyGen.sha3Suffix6] at hb₃
  rw [← sha3_512_eq, ← hP₃.pa rbx_cs] at hb₃
  have hK : bytesAt s₃.mem (pa s₃ (sc oG)) 32 = (ecG σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hb₃]; rfl
  have hr : bytesAt s₃.mem (pa s₃ sigP) 32 = (ecG σ).2 := by
    have e := bytesAt_drop s₃.mem (pa s₃ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₃.mem (pa s₃ (sc oG)) 64).drop 32 = bytesAt s₃.mem (pa s₃ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hb₃]; rfl
  refine ⟨⟨⟨hp, k₃, hK⟩, k₃.ek, ?_, hr⟩, ?_⟩
  · rw [L₂.keepBytes hP₃.b (by decide)]; exact hM₂
  · rw [hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h15]

/-! ## `Â` -/

/-- The matrix the expanded key holds. -/
abbrev ecA (σ : State) (i j : Nat) : Poly := polyAt σ.mem (σ.gpr .rdi + BitVec.ofNat 64 (mlKem1024.ekxA i j))

/-- Before `K-PKE.Encrypt`'s steps after its matrix. -/
abbrev ERX (σ s : State) : Prop := Enc4.ER (ecxC σ) (.r14, 0) (ecA σ) (ecEk σ) (ecMs σ) (ecG σ).2 0 0 0 s

theorem matIn_ok {σ : State} (hp : encapsX1024K.pre σ) {s : State} (h : EncI σ s) : WP isa (matIn4 .r14) s (ERX σ) := by
  have L := h.1.out.2.ec.lay hp
  unfold matIn4
  refine WP.mono (copy16_okL L (dst := aS4 0 0) (src := (.r14, oXA4)) (n := 1024) (by decide) (by decide))
    fun s' ⟨hP, hb⟩ => ?_
  have i' := h.1.keep hP.b (show Enc4.inKeep (ecxR ++ ecW) eckxChk (.r14, 0) [(aS4 0 0, 16 * 1024)] = true by decide)
  rw [h.1.out.2.ec.slice (show oXA4 + 16 * 1024 ≤ 17984 by decide)] at hb
  refine ⟨i', by rw [hP.cs .r15 (by decide)]; exact h.2, fun i hi j hj => ?_, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hx := (encapsX1024K_ekx hp).2.2.1 i hi j hj
  have e₁ : σ.gpr .rdi + BitVec.ofNat 64 (mlKem1024.ekxA i j) =
      σ.gpr .rdi + BitVec.ofNat 64 oXA4 + BitVec.ofNat 64 (1024 * (4 * i + j)) := by
    rw [off_add]; rfl
  have e₂ : pa s' (aS4 i j) = pa s (aS4 0 0) + BitVec.ofNat 64 (1024 * (4 * i + j)) := by
    rw [hP.pa rbx_cs, pa, pa, off_add]
    exact congrArg (fun k => s.gpr .rbx + BitVec.ofNat 64 k) (by simp only [oP]; omega)
  rw [e₂]
  exact polyIs_copied hb (by omega) ⟨by rw [← e₁]; exact hx, by rw [← e₁]⟩

/-! ## The end -/

/-- The end of `K-PKE.Encrypt`. -/
abbrev EncO (σ s : State) : Prop := (ecxC σ).Out s ∧ s.gpr .r15 = 1 ∧
  bytesAt s.mem (pa s (sc oCT4)) 1568 = ct1024 (ecA σ) (ecEk σ) (ecMs σ) (ecG σ).2

/-- At the end: `K` in `key`, and the ciphertext in `ct`. -/
structure ECXEnd (σ s : State) : Prop where
  ec : ECX σ s
  key : bytesAt s.mem (pa s (.r12, 0)) 32 = (ecG σ).1
  ct : bytesAt s.mem (pa s (.r13, 0)) 1568 = ct1024 (ecA σ) (ecEk σ) (ecMs σ) (ecG σ).2

theorem out_ok {σ : State} {s : State} (h : EncO σ s) : WP isa Encaps1024.out s (ECXEnd σ) := by
  have hp := h.1.1
  have L := h.1.2.ec.lay hp
  unfold Encaps1024.out
  refine WP.seq (WP.mono (copy_okL L (dst := (.r12, 0)) (src := sc oG) (n := 32) (by decide) (by decide))
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.1.2.ec.step hp hP₁.b (by decide)
  have L₁ := k₁.lay hp
  refine WP.mono (copy_okL L₁ (dst := (.r13, 0)) (src := sc oCT4) (n := 1568) (by decide) (by decide))
    fun s₂ ⟨hP₂, hb₂⟩ => ?_
  refine ⟨k₁.step hp hP₂.b (by decide), ?_, ?_⟩
  · rw [L₁.keepBytes hP₂.b (by decide), hP₁.pa (by decide), hb₁]; exact h.1.2.k
  · rw [hP₂.pa (by decide), hb₂, L.keepBytes hP₁.b (by decide)]; exact h.2.2

theorem ECXEnd.hin {σ s : State} (hp : encapsX1024K.pre σ) (h : ECXEnd σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk => by
  have hk' : ∀ k < 6, inB ecxB (sc (oSV + 8 * k)) 8 = true := by decide
  exact (h.ec.lay hp).cR (hk' k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- The postcondition, from the outputs: for every bound for which
`Encaps_internal` returns, `ExpandedEk` gives that the matrix it samples is
`ecA`. -/
theorem post_of {σ s : State} (hp : encapsX1024K.pre σ) (h : ECXEnd σ s) {s' : State} (hm : s'.mem = s.mem) :
    encapsX1024K.post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rdx := by
    rw [pa, h.ec.top.regs (.r12, .rdx) (by decide), add_ofNat_zero]
  have e13 : pa s (.r13, 0) = σ.gpr .rcx := by
    rw [pa, h.ec.top.regs (.r13, .rcx) (by decide), add_ofNat_zero]
  intro iters r hr
  change encapsInternal mlKem1024 iters (ecEk σ) (ecMs σ) = some r at hr
  rw [encapsInternal1024] at hr
  by_cases hall : ∀ i < 4, ∀ j < 4, (sampleNTT iters (matSeed (Enc4.rhoE (ecEk σ)) i j)).isSome
  · have hs : ∀ i < 4, ∀ j < 4, sampleNTT iters (matSeed (Enc4.rhoE (ecEk σ)) i j) =
        some ((sampleNTT iters (matSeed (Enc4.rhoE (ecEk σ)) i j)).getD zero) := fun i hi j hj => by
      have := hall i hi j hj
      cases e : sampleNTT iters (matSeed (Enc4.rhoE (ecEk σ)) i j) with
      | none => rw [e] at this; cases this
      | some f => rfl
    have hM := sampleMatrix_some hs
    have hA : ∀ i < 4, ∀ j < 4, sampleNTT iters (matSeed (ekRho mlKem1024 (ecEk σ)) i j) = some (ecA σ i j) :=
      fun i hi j hj => by
        show _ = some (polyAt σ.mem (σ.gpr .rdi + BitVec.ofNat 64 (mlKem1024.ekxA i j)))
        rw [(encapsX1024K_ekx hp).2.2.2 iters _ hM i hi j hj]
        exact sampleMatrix_entry hM hi hj
    rw [kpkeEncrypt1024_some hA, Option.map_some, Option.some.injEq] at hr
    rw [← hr, hm, ← e12, ← e13, h.key]
    show _ = (_, bytesAt s.mem (pa s (.r13, 0)) 1568)
    rw [h.ct]
  · obtain ⟨i, hi, j, hj, hn⟩ : ∃ i < 4, ∃ j < 4, sampleNTT iters (matSeed (Enc4.rhoE (ecEk σ)) i j) = none := by
      refine Classical.byContradiction fun hc => hall fun i hi j hj => ?_
      cases e : sampleNTT iters (matSeed (Enc4.rhoE (ecEk σ)) i j) with
      | none => exact absurd ⟨i, hi, j, hj, e⟩ hc
      | some _ => rfl
    rw [kpkeEncrypt1024_none hi hj hn] at hr
    cases hr

end EncapsX4

open EncapsX4 in
theorem encapsX1024_correct (σ : State) (hp : encapsX1024K.pre σ) :
    ∃ t s', Exec isa Impl.MlKem1024.X86_64.encapsX1024 σ t s' ∧ abiPreserved σ s' ∧ encapsX1024K.post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (hashes_ok hp h₁ h15) fun s₂ h₂ =>
      WP.seq (WP.mono (matIn_ok hp h₂) fun s₃ h₃ =>
        WP.seq (WP.mono (Enc4.rest_ok (C := ecxC σ) (Enc4.encChk_spec ecxEncChk) h₃) fun s₄ h₄ =>
          WP.seq (WP.mono (out_ok h₄) fun s₅ h₅ =>
            WP.mono (topEpi_ok h₅.ec.top (h₅.hin hp)) fun s₆ ⟨_, hg, hm⟩ =>
              (⟨hg, post_of hp h₅ hm⟩ : gprPreserved σ s₆ ∧ encapsX1024K.post σ s₆))))))
  exact ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he hF.1, hF.2⟩

/-! ## Constant time -/

namespace EncapsX4

open VG.Impl.MlKem1024.X86_64.EncapsX1024
open Encaps4 (ecM ecW ecM_bases ecEk ecMs ecG)

abbrev R (I : State → State → Prop) : State → State → Prop := Rel2 encapsX1024K.pre encapsX1024K.pub I

theorem ec_lrel {σ₁ σ₂ x y : State} (p₁ : encapsX1024K.pre σ₁) (p₂ : encapsX1024K.pre σ₂) (pub : encapsX1024K.pub σ₁ σ₂)
    (h₁ : ECX σ₁ x) (h₂ : ECX σ₂ y) : LRel ecxR ecW x y := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := pub
  refine ⟨h₁.lay p₁, h₂.lay p₂, fa5 ?_ ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e6]⟩
  · rw [h₁.top.regs (.r14, .rdi) (by decide), h₂.top.regs (.r14, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.rbp, .rsi) (by decide), h₂.top.regs (.rbp, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.rbx, .r8) (by decide), h₂.top.regs (.rbx, .r8) (by decide), e5]
  · rw [h₁.top.regs (.r12, .rdx) (by decide), h₂.top.regs (.r12, .rdx) (by decide), e3]
  · rw [h₁.top.regs (.r13, .rcx) (by decide), h₂.top.regs (.r13, .rcx) (by decide), e4]

/-- Code the taint analysis proves constant time from the pointers. -/
theorem trL {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) c h).isSome = true) :
    RelCT isa (LRel ecxR ecW) c fun _ _ => True :=
  taintRel [.rbx, .rbp, .r12, .r13, .r14] (fun x y h =>
    fa5 (h.eq (p := sc 0) (l := 1) (by decide)) (h.eq (p := (.rbp, 0)) (l := 1) (by decide))
      (h.eq (p := (.r12, 0)) (l := 1) (by decide)) (h.eq (p := (.r13, 0)) (l := 1) (by decide))
      (h.eq (p := (.r14, 0)) (l := 1) (by decide))) ht

theorem hashes_trL : RelCT isa (LRel ecxR ecW) hashes fun _ _ => True := by
  unfold hashes
  refine RelCT.seq (LRel.step ecxB_bases (trL (by taint_decide)) fun x Lx =>
      WP.mono (copy_okL Lx (dst := sc oM) (src := (.rbp, 0)) (n := 32) (by decide) (by decide))
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step ecxB_bases (trL (by taint_decide)) fun x Lx =>
      WP.mono (copy_okL Lx (dst := sc oH) (src := (.r14, oXH4)) (n := 32) (by decide) (by decide))
        fun _ h => ⟨_, h.1⟩)
    (hash_tr ecxB_bases (ps := [(sc oM, 32), (sc oH, 32)]) (rate := 72) (out := sc oG) (len := 64) (by decide)
      (show 6 < 256 by decide)))

theorem hashes_tr : RelCT isa (R fun σ s => ECX σ s ∧ s.gpr .r15 = 1) hashes fun _ _ => True :=
  rel2_of hashes_trL fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ec_lrel p₁ p₂ pub h₁.1 h₂.1

theorem matIn_tr : RelCT isa (R EncI) (matIn4 .r14) fun _ _ => True :=
  rel2_of (trL (by taint_decide)) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ec_lrel p₁ p₂ pub h₁.1.out.2.ec h₂.1.out.2.ec

theorem ER.any {σ : State} {a : Nat → Nat → Poly} {ek m r : List Byte} {s : State}
    (h : Enc4.ER (ecxC σ) (.r14, 0) a ek m r 0 0 0 s) : Enc4.ER ecxCA (.r14, 0) a ek m r 0 0 0 s :=
  ⟨⟨⟨σ, h.i.out⟩, h.i.ek, h.i.m, h.i.r⟩, h.r15, h.mat, h.y, h.u, h.t⟩

theorem rest_tr : RelCT isa (R ERX) (Encrypt1024.rest (.r14, 0)) fun _ _ => True :=
  RelCT.mono (Enc4.rest_tr (C := ecxCA) (Enc4.encChk_spec ecxEncChk) (P := fun _ _ => True))
    (fun _ _ ⟨_, _, p₁, p₂, pub, h₁, h₂⟩ => ⟨ec_lrel p₁ p₂ pub h₁.i.out.2.ec h₂.i.out.2.ec,
      ⟨_, _, _, _, trivial, ER.any h₁⟩, ⟨_, _, _, _, trivial, ER.any h₂⟩⟩) fun _ _ _ => trivial

theorem out_tr : RelCT isa (R EncO) Encaps1024.out fun _ _ => True := by
  refine rel2_of (Q := LRel ecxR ecW) ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ec_lrel p₁ p₂ pub h₁.1.2.ec h₂.1.2.ec
  unfold Encaps1024.out
  exact RelCT.seq (LRel.step ecxB_bases (trL (by taint_decide)) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r12, 0)) (src := sc oG) (n := 32) (by decide) (by decide))
        fun _ h => ⟨_, h.1⟩) (trL (by taint_decide))

theorem pro_tr : RelCT isa (R fun σ s => s = σ) (.block Encaps1024.pro) fun _ _ => True :=
  taintRel [.r8, .rsi, .rdx, .rcx, .rdi] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa5 pub.2.2.2.2.1 pub.2.1 pub.2.2.1 pub.2.2.2.1 pub.1) (by taint_decide)

theorem epi_tr : RelCT isa (R ECXEnd) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.ec.top.regs (.rbx, .r8) (by decide), h₂.ec.top.regs (.rbx, .r8) (by decide), pub.2.2.2.2.1])
    (by taint_decide)

end EncapsX4

open EncapsX4 in
theorem encapsX1024_ct : ConstantTime isa encapsX1024K.pre encapsX1024K.pub Impl.MlKem1024.X86_64.encapsX1024 := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold Impl.MlKem1024.X86_64.encapsX1024
  refine RelCT.seq (relInv (I' := fun σ s => ECX σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := EncI) (fun σ s hp hs => hashes_ok hp hs.1 hs.2) hashes_tr) ?_
  refine RelCT.seq (relInv (I' := ERX) (fun σ s hp hs => matIn_ok hp hs) matIn_tr) ?_
  refine RelCT.seq (relInv (I' := EncO) (fun σ s _ hs =>
    Enc4.rest_ok (C := ecxC σ) (Enc4.encChk_spec ecxEncChk) hs) rest_tr) ?_
  refine RelCT.seq (relInv (I' := ECXEnd) (fun σ s _ hs => out_ok hs) out_tr) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem1024.X86_64
