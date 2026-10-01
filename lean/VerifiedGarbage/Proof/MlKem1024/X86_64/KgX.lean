import VerifiedGarbage.Proof.MlKem1024.X86_64.KgTop
import VerifiedGarbage.Impl.MlKem1024.X86_64.Expanded
import VerifiedGarbage.Proof.MlKem.X86_64.FragX
import VerifiedGarbage.Proof.MlKem.Expanded

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_keygen_expanded`

Untrusted: everything here is checked by Lean. `vg_mlkem1024_keygen`'s proof
(`KgBase.lean` … `KgTop.lean`, for any `KPre`), run with the expanded key
`ekx` (17984 bytes) where `ek` was, in the layout of `vg_mlkem1024_keygen`
(its first 1568 bytes, `kgxK`); then `H(ek)` (from `dk`) and `Â` (from the
working space) to `ekx` (`copies_ok`), in the layout of the whole of `ekx`
(`kgxLay`). The matrix is the one sampled within `minIterations`, which any
bound for which `SampleNTT` samples one gives too (`post_of`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (polyIs_copied sampleMatrix_entry)

/-- `vg_mlkem1024_keygen_expanded(seed = rdi, ekx = rsi, dk = rdx, scratch = rcx) -> eax`, with 32 bytes of
stack. -/
def keyGenX1024K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 64⟩] ∧ s.wr = [⟨s.gpr .rsi, 17984⟩, ⟨s.gpr .rdx, 3168⟩, ⟨s.gpr .rcx, 49152⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rsi, 17984⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rdx, 3168⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rcx, 49152⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 17984⟩ ⟨s.gpr .rdx, 3168⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 17984⟩ ⟨s.gpr .rcx, 49152⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, 3168⟩ ⟨s.gpr .rcx, 49152⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 64⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 17984⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 3168⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, 49152⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, 64⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, 17984⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, 3168⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, 49152⟩ ∧
    (s.gpr .rdi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 17984 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 3168 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 49152 ≤ 2 ^ 64
  post s s' := KeyGenExpandedPost mlKem1024 (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) s.mem s'.mem
    ((s'.gpr .rax).setWidth 32)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    keyGenRho mlKem1024 (bytesAt s₁.mem (s₁.gpr .rdi) 32) = keyGenRho mlKem1024 (bytesAt s₂.mem (s₂.gpr .rdi) 32)

namespace KeyGenX4

open VG.Impl.MlKem1024.X86_64.KeyGen1024
open KeyGen4 (kgM kgR kgW kgB KC KPre KB KFin KEnd KRest rhoK kgD)

/-- `scratch`, the whole of `ekx`, and `dk`. -/
abbrev kgxW : List (Reg × Nat) := [(.rbx, 49152), (.r12, 17984), (.r13, 3168)]
abbrev kgxB : List (Reg × Nat) := kgR ++ kgxW

theorem kgxB_bases : ∀ b ∈ kgxB, b.1 ∈ bases := by decide

section
variable {σ : State} (hp : keyGenX1024K.pre σ)
include hp

theorem kgxLay {s : State} (h : Top kgM σ s) : Lay kgR kgxW s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .rcx := h.regs (.rbx, .rcx) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rsi := h.regs (.r12, .rsi) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .rdx := h.regs (.r13, .rdx) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of (by decide) (pw4 ?_ ?_ ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_)
    (fa3 ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, h.rsp, retR]
  · exact fun _ => d3
  · exact fun _ => d1
  · exact fun _ => d2
  · exact fun _ => d5.symm
  · exact fun _ => d6.symm
  · exact fun _ => d4
  exacts [k1, k4, k2, k3, n1, n4, n2, n3,
    mem ⟨σ.gpr .rdi, 64⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rcx, 49152⟩ (by rw [hwr]; simp),
    mem ⟨σ.gpr .rsi, 17984⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, 3168⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, r1, r4, r2, r3]

/-- The layout of `vg_mlkem1024_keygen`: the first 1568 bytes of `ekx`. -/
theorem kgxLayK {s : State} (h : Top kgM σ s) : Lay kgR kgW s :=
  (kgxLay hp h).mono (by decide) (by decide)

end

/-- `vg_mlkem1024_keygen`'s proof, with `ekx`. -/
def kgxK : KPre where
  pre := keyGenX1024K.pre
  pub := keyGenX1024K.pub
  lay hp h := kgxLayK hp h
  eq h := h

theorem pro_ok {σ : State} (hp : keyGenX1024K.pre σ) :
    WP isa (.block pro) σ fun s => KC σ s ∧ s.gpr .r15 = 1 := by
  obtain ⟨_, hwr, _, _, d3, _, _, _, _, _, _, r4, _⟩ := hp
  exact KeyGen4.pro_okF (by rw [hwr]; simp) d3 r4

/-! ## `H(ek)` and `Â` to `ekx` -/

theorem ekRho_ekPKE (a : Nat → Nat → Poly) (d : List Byte) : ekRho mlKem1024 (ekPKE1024 a d) = kgRho1024 d := by
  show ((ekPKE1024 a d).drop 1536).take 32 = _
  have h : (encode12 (kgT1024 a d 0) ++ encode12 (kgT1024 a d 1) ++ encode12 (kgT1024 a d 2) ++
      encode12 (kgT1024 a d 3)).length = 1536 := by
    simp only [List.length_append, encode12_length]
  rw [ekPKE1024, List.drop_left' h, List.take_of_length_le (by rw [kgRho1024, G_fst_length])]

/-- `H(ek)` in `dk`. -/
theorem dk_h {a : Nat → Nat → Poly} {d z : List Byte} :
    ((dkPKE1024 d ++ ekPKE1024 a d ++ H (ekPKE1024 a d) ++ z).drop 3104).take 32 = H (ekPKE1024 a d) := by
  have h : (dkPKE1024 d ++ ekPKE1024 a d).length = 3104 := by
    rw [List.length_append, dkPKE1024_length, ekPKE1024_length]
  rw [List.append_assoc, List.drop_left' h, List.take_left' (H_length _)]

/-- The expanded key at `ekx`, when every `SampleNTT` succeeded. -/
structure XOut (σ s : State) : Prop where
  h : bytesAt s.mem (pa s (.r12, oXH4)) 32 = H (ekPKE1024 (aHat (rhoK σ)) (kgD σ))
  mat : ∀ i < 4, ∀ j < 4, PolyIs s.mem (pa s (.r12, mlKem1024.ekxA i j)) (aHat (rhoK σ) i j)

/-- A piece that writes `ws` keeps `KC`, in the layout of the whole of `ekx`. -/
def kcxChk (ws : List (Ptr × Nat)) : Bool :=
  topChk kgxB ws && keepB kgxB ws (.rbp, 0) 32 && keepB kgxB ws (.rbp, 32) 32 &&
    keepB kgxB ws (.r12, 0) 1568 && keepB kgxB ws (.r13, 0) 3168 &&
    (List.range 16).all fun e => keepB kgxB ws (aS4 (e / 4) (e % 4)) 1024

theorem stepX {σ : State} (hp : keyGenX1024K.pre σ) {s s' : State} (h : KFin σ s) {ws : List (Ptr × Nat)}
    (hP : PPost s s' ws) (hc : kcxChk ws = true) : KFin σ s' := by
  simp only [kcxChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨ht, kd⟩, kz⟩, ke⟩, kk⟩, kA⟩ := hc
  have L := kgxLay hp h.kc.top
  refine ⟨⟨h.kc.top.step L hP.b KeyGen4.kgM_bases ht, by rw [L.keepBytes hP.b kd]; exact h.kc.d,
    by rw [L.keepBytes hP.b kz]; exact h.kc.z⟩, by rw [hP.cs .r15 (by decide)]; exact h.r15,
    by rw [L.keepBytes hP.b ke]; exact h.ek, by rw [L.keepBytes hP.b kk]; exact h.dk, fun i hi j hj => ?_⟩
  have := kA (4 * i + j) (by omega)
  rw [show (4 * i + j) / 4 = i by omega, show (4 * i + j) % 4 = j by omega] at this
  exact L.keepPoly hP.b this (h.mat i hi j hj)

/-- `H(ek)` and `Â` to `ekx`. -/
abbrev copies : Prog isa := .seq (copy (.r12, oXH4) (.r13, 3104) 32) (matOut4 .r12)

theorem copies_ok {σ : State} (hp : keyGenX1024K.pre σ) {s : State} (h : KFin σ s) :
    WP isa copies s fun s' => KFin σ s' ∧ XOut σ s' := by
  have L := kgxLay hp h.kc.top
  refine WP.seq (WP.mono (copy_okL L (dst := (.r12, oXH4)) (src := (.r13, 3104)) (n := 32) (by decide) (by decide))
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have f₁ := stepX hp h hP₁ (by decide)
  have L₁ := kgxLay hp f₁.kc.top
  have hH : bytesAt s₁.mem (pa s₁ (.r12, oXH4)) 32 = H (ekPKE1024 (aHat (rhoK σ)) (kgD σ)) := by
    rw [hP₁.pa (by decide), hb₁, ← dk_h (z := KeyGen4.kgZ σ), ← h.dk, bytesAt_slice _ _ (by decide), pa, pa, off_add]
  unfold matOut4
  refine WP.mono (copy16_okL L₁ (dst := (.r12, oXA4)) (src := aS4 0 0) (n := 1024) (by decide) (by decide))
    fun s₂ ⟨hP₂, hb₂⟩ => ⟨stepX hp f₁ hP₂ (by decide), by rw [L₁.keepBytes hP₂.b (by decide)]; exact hH,
      fun i hi j hj => ?_⟩
  have e₁ : pa s₂ (.r12, mlKem1024.ekxA i j) = pa s₁ (.r12, oXA4) + BitVec.ofNat 64 (1024 * (4 * i + j)) := by
    rw [hP₂.pa KeyGen.r12_cs, pa, pa, off_add]; rfl
  have e₂ : pa s₁ (aS4 i j) = pa s₁ (aS4 0 0) + BitVec.ofNat 64 (1024 * (4 * i + j)) := by
    rw [pa, pa, off_add]
    exact congrArg (fun k => s₁.gpr .rbx + BitVec.ofNat 64 k) (by simp only [oP]; omega)
  rw [e₁]
  exact polyIs_copied hb₂ (by omega) (by rw [← e₂]; exact f₁.mat i hi j hj)

/-- At the end: `r15` as `allOk`, and the keys and the expanded key if it is 1. -/
structure KXEnd (σ s : State) : Prop where
  kc : KC σ s
  r15 : s.gpr .r15 = if allOk4 (rhoK σ) 16 then 1 else 0
  keys : allOk4 (rhoK σ) 16 → KFin σ s ∧ XOut σ s

theorem KXEnd.toKEnd {σ s : State} (h : KXEnd σ s) : KEnd σ s := ⟨h.kc, h.r15, fun ho => (h.keys ho).1⟩

theorem body_ok {σ : State} (hp : keyGenX1024K.pre σ) {s : State} (h : KB 16 σ s) :
    WP isa (ifOk (.seq rest copies)) s (KXEnd σ) := by
  refine ifOk_ok (fun s₁ hP hne => ?_) fun s₁ hP he => ?_
  · have ho := KeyGen4.r15_ne h.r15 hne
    exact WP.seq (WP.mono (KeyGen4.rest_ok (K := kgxK) hp (KRest.start (h.flag (K := kgxK) hp (by decide) hP) ho))
      fun s₂ hf => WP.mono (copies_ok hp hf) fun s₃ ⟨hf', hx⟩ => ⟨hf'.kc, by rw [hf'.r15, ifp ho], fun _ => ⟨hf', hx⟩⟩)
  · have ho := KeyGen4.r15_eq h.r15 he
    have h' := h.flag (K := kgxK) hp (by decide) hP
    exact ⟨h'.a.kc, h'.r15, fun h => absurd h ho⟩

theorem KXEnd.hin {σ s : State} (hp : keyGenX1024K.pre σ) (h : KXEnd σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := KeyGen4.KEnd.hin (K := kgxK) hp h.toKEnd

/-- The postcondition, from the keys: `vg_mlkem1024_keygen`'s, and the expanded key, whose matrix is the
one any bound gives for which `SampleNTT` samples one. -/
theorem post_of {σ s : State} (h : KXEnd σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : keyGenX1024K.post σ s' := by
  refine ⟨KeyGen4.post_of h.toKEnd hr hm, fun h1 => ?_⟩
  have ho : allOk4 (rhoK σ) 16 := KeyGen4.r15_ne h.r15 (by rw [← hr, h1]; decide)
  obtain ⟨hf, hx⟩ := h.keys ho
  have e12 : ∀ o, pa s (.r12, o) = σ.gpr .rsi + BitVec.ofNat 64 o := fun o => by
    rw [pa, h.kc.top.regs (.r12, .rsi) (by decide)]
  have hek : bytesAt s'.mem (σ.gpr .rsi) mlKem1024.ekLen = ekPKE1024 (aHat (rhoK σ)) (kgD σ) := by
    rw [hm, ← add_ofNat_zero (σ.gpr .rsi), ← e12]; exact hf.ek
  rw [hek]
  refine ⟨hek, ?_, fun i hi j hj => ?_, fun iters A hA i hi j hj => ?_⟩
  · rw [hm, ← e12]; exact hx.h
  · rw [hm, ← e12]; exact (hx.mat i hi j hj).1
  · rw [hm, ← e12, (hx.mat i hi j hj).2]
    rw [ekRho_ekPKE] at hA
    have h₁ := sampleMatrix_entry hA hi hj
    have h₂ := aHat4_eq ho hi hj
    have e₁ := sampleNTT_mono' _ h₁ (Nat.le_max_left iters minIterations)
    have e₂ := sampleNTT_mono' _ h₂ (Nat.le_max_right iters minIterations)
    rw [e₁] at e₂
    exact (Option.some.inj e₂).symm

end KeyGenX4

open KeyGenX4 in
theorem keyGenX1024_correct (v : Sample4Impl) (σ : State) (hp : keyGenX1024K.pre σ) :
    ∃ t s', Exec isa (Impl.MlKem1024.X86_64.keyGenX1024 v.callee) σ t s' ∧ abiPreserved σ s' ∧ keyGenX1024K.post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (KeyGen4.gRho_ok (K := kgxK) hp h₁ h15) fun s₂ ⟨h₂, h15'⟩ =>
      WP.seq (WP.mono (KeyGen4.samples_ok v (K := kgxK) hp (KeyGen4.KB.zero h₂ h15')) fun s₃ h₃ =>
        WP.seq (WP.mono (body_ok hp h₃) fun s₄ h₄ =>
          WP.mono (topEpi_ok h₄.kc.top (h₄.hin hp)) fun s₅ ⟨hr, hg, hm⟩ =>
            (⟨hg, post_of h₄ hr hm⟩ : gprPreserved σ s₅ ∧ keyGenX1024K.post σ s₅)))))
  exact ⟨t, s', he, abiPreserved_of_ctl (by s4_ctl v) he hF.1, hF.2⟩

end VG.Proof.MlKem1024.X86_64
