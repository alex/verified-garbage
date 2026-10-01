import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
import VerifiedGarbage.Proof.MlKem.X86_64.FragX
import VerifiedGarbage.Proof.MlKem.Expanded

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_expand_ek`

Untrusted: everything here is checked by Lean. `ek` and `H(ek)` to `ekx`
(`hash_ok`), `Â` sampled from the `ρ` of `ek` as `vg_mlkem768_encaps`
samples it (`Enc.mat_ok`, with `ek` at `rbp`, in the context `xeC`), and,
if every `SampleNTT` succeeded, copied to `ekx` (`body_ok`). It returns 1
exactly when every `SampleNTT` succeeded within `minIterations`, and then
`ekx` is the expanded key of `ek` (`post_of`); it leaks only the pointers
and `ρ` (`expandEk_ct`); so it meets the shared contract
(`expandEk_verified`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (polyIs_copied sampleMatrix_entry)

/-- `vg_mlkem768_expand_ek(ek = rdi, ekx = rsi, scratch = rdx) -> eax`, with 32 bytes of stack. -/
def expandEkK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 1184⟩] ∧ s.wr = [⟨s.gpr .rsi, 10432⟩, ⟨s.gpr .rdx, 32768⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 1184⟩ ⟨s.gpr .rsi, 10432⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 1184⟩ ⟨s.gpr .rdx, 32768⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 10432⟩ ⟨s.gpr .rdx, 32768⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 1184⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 10432⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32768⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, 1184⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, 10432⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, 32768⟩ ∧
    (s.gpr .rdi).toNat + 1184 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 10432 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 32768 ≤ 2 ^ 64
  post s s' := ExpandEkPost mlKem768 (s.gpr .rdi) (s.gpr .rsi) s.mem s'.mem ((s'.gpr .rax).setWidth 32)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧
    ekRho mlKem768 (bytesAt s₁.mem (s₁.gpr .rdi) 1184) = ekRho mlKem768 (bytesAt s₂.mem (s₂.gpr .rdi) 1184)

namespace ExpandEk

open VG.Impl.MlKem.X86_64.ExpandEk

/-- The pointers the function keeps. -/
abbrev xeM : List (Reg × Reg) := [(.rbx, .rdx), (.rbp, .rdi), (.r12, .rsi)]
/-- `ek`. -/
abbrev xeR : List (Reg × Nat) := [(.rbp, 1184)]
/-- `scratch` and `ekx`. -/
abbrev xeW : List (Reg × Nat) := [(.rbx, 32768), (.r12, 10432)]
abbrev xeB : List (Reg × Nat) := xeR ++ xeW

theorem xeB_bases : ∀ b ∈ xeB, b.1 ∈ bases := by decide
theorem xeM_bases : ∀ p ∈ xeM, p.1 ∈ bases := by decide

theorem pw3 {α : Type} {R : α → α → Prop} {a b c : α} (hab : R a b) (hac : R a c) (hbc : R b c) :
    [a, b, c].Pairwise R := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, false_implies, implies_true, and_true]
  exact ⟨⟨hab, hac⟩, hbc⟩

section
variable {σ : State} (hp : expandEkK.pre σ)
include hp

theorem xeLay {s : State} (h : Top xeM σ s) : Lay xeR xeW s := by
  obtain ⟨hrd, hwr, d1, d2, d3, r1, r2, r3, k1, k2, k3, n1, n2, n3⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .rdx := h.regs (.rbx, .rdx) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rsi := h.regs (.r12, .rsi) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of (by decide) (pw3 ?_ ?_ ?_) (fa3 ?_ ?_ ?_) (fa3 ?_ ?_ ?_) (fa3 ?_ ?_ ?_) (fa2 ?_ ?_) (fa3 ?_ ?_ ?_)
    <;> simp only [e1, e2, e3, h.rsp, retR]
  · exact fun _ => d2
  · exact fun _ => d1
  · exact fun _ => d3.symm
  exacts [k1, k3, k2, n1, n3, n2, mem ⟨σ.gpr .rdi, 1184⟩ (by rw [hrd]; simp),
    mem ⟨σ.gpr .rdx, 32768⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rsi, 10432⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    r1, r3, r2]

end

/-- `ek`. -/
abbrev xeEk (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 1184

/-- What holds throughout: `Top`, and `ek` at its pointer. -/
structure XC (σ s : State) : Prop where
  top : Top xeM σ s
  ek : bytesAt s.mem (pa s (.rbp, 0)) 1184 = xeEk σ

/-- What holds after `hash`: `ek` and `H(ek)` at `ekx`. -/
structure XH (σ s : State) : Prop where
  xc : XC σ s
  ek : bytesAt s.mem (pa s (.r12, 0)) 1184 = xeEk σ
  h : bytesAt s.mem (pa s (.r12, oXH)) 32 = H (xeEk σ)

def xhChk (ws : List (Ptr × Nat)) : Bool :=
  topChk xeB ws && keepB xeB ws (.rbp, 0) 1184 && keepB xeB ws (.r12, 0) 1184 && keepB xeB ws (.r12, oXH) 32

theorem XH.step {σ : State} (hp : expandEkK.pre σ) {s s' : State} (h : XH σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hc : xhChk ws = true) : XH σ s' := by
  simp only [xhChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨ht, k1⟩, k2⟩, k3⟩ := hc
  have L := xeLay hp h.xc.top
  exact ⟨⟨h.xc.top.step L hP xeM_bases ht, by rw [L.keepBytes hP k1]; exact h.xc.ek⟩,
    by rw [L.keepBytes hP k2]; exact h.ek, by rw [L.keepBytes hP k3]; exact h.h⟩

/-- The context of the sampling of `Â` in a run from `σ`. -/
def xeC (σ : State) : Ctx xeR xeW where
  Out s := expandEkK.pre σ ∧ XH σ s
  chk := xhChk
  bs := xeB_bases
  lay h := xeLay h.1 h.2.xc.top
  step h hP hc := ⟨h.1, h.2.step h.1 hP hc⟩

/-- The context of the sampling of `Â` in any run. -/
def xeCA : Ctx xeR xeW where
  Out s := ∃ σ, expandEkK.pre σ ∧ XH σ s
  chk := xhChk
  bs := xeB_bases
  lay := fun ⟨_, hp, h⟩ => xeLay hp h.xc.top
  step := fun ⟨σ, hp, h⟩ hP hc => ⟨σ, hp, h.step hp hP hc⟩

theorem xeMatChk : Enc.matChk (xeR ++ xeW) xeW xhChk (.rbp, 0) = true := by decide
theorem xeSampChks : Enc.SampChks (xeR ++ xeW) xeW xhChk (.rbp, 0) := ⟨by decide, by decide, by decide⟩

theorem pro_eq : pro = [.store (at_ .rdx 840) .rbx, .store (at_ .rdx 848) .rbp, .store (at_ .rdx 856) .r12,
    .store (at_ .rdx 864) .r13, .store (at_ .rdx 872) .r14, .store (at_ .rdx 880) .r15, .mov .rbx (.reg .rdx),
    .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {σ : State} (hp : expandEkK.pre σ) : WP isa (.block pro) σ fun s => XC σ s ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, r1, r2, r3, k1, k2, k3, n1, n2, n3⟩ := hp'
  have hS : ⟨σ.gpr .rdx, 32768⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ 32768 → (⟨σ.gpr .rdx, 32768⟩ : Region).Contains (σ.gpr .rdx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega)
  have w : ∀ o, o + 8 ≤ 32768 → InRegions σ.wr (σ.gpr .rdx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .rdx + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .rdx + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .rdx + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .rdx + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .rdx + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .rdx + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .rdx ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r12 = σ.gpr .rsi ∧ s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h15⟩, k⟩ => ⟨?_, h15⟩
  have hf : Frame [⟨σ.gpr .rdx, 32768⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨k.2.1, k.2.2, hsp, fa3 hbx hbp h12, fun j hj => ?_, ?_⟩, ?_⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .rdx) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r3) (by decide)
  · rw [pa, hbp, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d2) (by decide)

/-! ## `ek` and `H(ek)` to `ekx` -/

/-- Before the sampling: its inputs (whatever `M` and `sigP` hold), and `r15 = 1`. -/
abbrev XI (σ s : State) : Prop := (∃ m r, Enc.EIn (xeC σ) (.rbp, 0) (xeEk σ) m r s) ∧ s.gpr .r15 = 1

theorem hashes_ok {σ : State} (hp : expandEkK.pre σ) {s : State} (h : XC σ s) (h15 : s.gpr .r15 = 1) :
    WP isa hash s (XI σ) := by
  have L := xeLay hp h.top
  unfold VG.Impl.MlKem.X86_64.ExpandEk.hash
  refine WP.seq (WP.mono (copy16_okL L (dst := (.r12, 0)) (src := (.rbp, 0)) (n := 74) (by decide) (by decide))
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have L₁ := L.post hP₁.b xeB_bases
  have t₁ : Top xeM σ s₁ := h.top.step L hP₁.b xeM_bases (by decide)
  have k₁ : bytesAt s₁.mem (pa s₁ (.rbp, 0)) 1184 = xeEk σ := by rw [L.keepBytes hP₁.b (by decide)]; exact h.ek
  rw [h.ek, ← hP₁.pa KeyGen.r12_cs] at hb₁
  refine WP.mono (hash_ok xeB_bases (ps := [((.rbp, 0), 1184)]) (rate := 136) (out := (.r12, oXH)) (len := 32)
    (by decide) (show 6 < 256 by decide) L₁) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, k₁, KeyGen.sha3Suffix6] at hb₂
  rw [← H_eq, ← hP₂.pa KeyGen.r12_cs] at hb₂
  have hx : XH σ s₂ := ⟨⟨t₁.step L₁ hP₂.b xeM_bases (by decide), by rw [L₁.keepBytes hP₂.b (by decide)]; exact k₁⟩,
    by rw [L₁.keepBytes hP₂.b (by decide)]; exact hb₁, hb₂⟩
  exact ⟨⟨_, _, ⟨hp, hx⟩, hx.xc.ek, rfl, rfl⟩,
    by rw [hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h15]⟩

/-! ## `Â` to `ekx` -/

/-- After the sampling. -/
abbrev XB (σ s : State) : Prop := ∃ m r, Enc.EB (xeC σ) (.rbp, 0) (xeEk σ) m r 9 s

/-- `Â` at `ekx`. -/
def XMat (σ s : State) : Prop := ∀ i < 3, ∀ j < 3, PolyIs s.mem (pa s (.r12, mlKem768.ekxA i j)) (aHat (Enc.rhoE (xeEk σ)) i j)

/-- At the end: `r15` as `allOk`, and the expanded key if it is 1. -/
structure XEnd (σ s : State) : Prop where
  xh : XH σ s
  r15 : s.gpr .r15 = if allOk (Enc.rhoE (xeEk σ)) 9 then 1 else 0
  mat : allOk (Enc.rhoE (xeEk σ)) 9 → XMat σ s

theorem matOut_ok {σ : State} (hp : expandEkK.pre σ) {s : State} {m r : List Byte}
    (h : Enc.EB (xeC σ) (.rbp, 0) (xeEk σ) m r 9 s) (hne : (s.gpr .r15).setWidth 32 ≠ 0) :
    WP isa (matOut .r12) s (XEnd σ) := by
  have ho := KeyGen.r15_ne h.r15 hne
  have L := xeLay hp h.i.out.2.xc.top
  unfold matOut
  refine WP.mono (copy16_okL L (dst := (.r12, oXA)) (src := aS 0 0) (n := 576) (by decide) (by decide))
    fun s₂ ⟨hP₂, hb₂⟩ => ⟨h.i.out.2.step hp hP₂.b (by decide), by rw [hP₂.cs .r15 (by decide)]; rw [h.r15],
      fun _ i hi j hj => ?_⟩
  have e₁ : pa s₂ (.r12, mlKem768.ekxA i j) = pa s (.r12, oXA) + BitVec.ofNat 64 (1024 * (3 * i + j)) := by
    rw [hP₂.pa KeyGen.r12_cs, pa, pa, off_add]; rfl
  have e₂ : pa s (aS i j) = pa s (aS 0 0) + BitVec.ofNat 64 (1024 * (3 * i + j)) := by
    rw [pa, pa, off_add]
    exact congrArg (fun k => s.gpr .rbx + BitVec.ofNat 64 k) (by simp only [oP]; omega)
  have hm := h.mat (3 * i + j) (by omega)
  rw [show (3 * i + j) / 3 = i by omega, show (3 * i + j) % 3 = j by omega] at hm
  rw [e₁]
  exact polyIs_copied hb₂ (by omega) (by rw [← e₂]; exact hm _ (aHat_eq ho hi hj))

theorem skip_end {σ : State} {s : State} {m r : List Byte} (h : Enc.EB (xeC σ) (.rbp, 0) (xeEk σ) m r 9 s)
    (he : (s.gpr .r15).setWidth 32 = 0) : XEnd σ s :=
  ⟨h.i.out.2, h.r15, fun ho => absurd ho (KeyGen.r15_eq h.r15 he)⟩

theorem EB.flag' {σ : State} {s s' : State} {m r : List Byte} (h : Enc.EB (xeC σ) (.rbp, 0) (xeEk σ) m r 9 s)
    (hP : PPost s s' []) : Enc.EB (xeC σ) (.rbp, 0) (xeEk σ) m r 9 s' :=
  h.flag hP (show Enc.inKeep (xeR ++ xeW) xhChk (.rbp, 0) [] = true by decide) (by decide) (by decide)

theorem body_ok {σ : State} (hp : expandEkK.pre σ) {s : State} (h : XB σ s) :
    WP isa (ifOk (matOut .r12)) s (XEnd σ) := by
  obtain ⟨m, r, h⟩ := h
  refine ifOk_ok (fun s₁ hP hne => matOut_ok hp (EB.flag' h hP) (by rw [hP.cs .r15 (by decide)]; exact hne))
    fun s₁ hP he => skip_end (EB.flag' h hP) (by rw [hP.cs .r15 (by decide)]; exact he)

theorem XEnd.hin {σ s : State} (hp : expandEkK.pre σ) (h : XEnd σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk => by
  have hk' : ∀ k < 6, inB xeB (sc (oSV + 8 * k)) 8 = true := by decide
  exact (xeLay hp h.xh.xc.top).cR (hk' k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- The postcondition, from the expanded key. -/
theorem post_of {σ s : State} (h : XEnd σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : expandEkK.post σ s' := by
  have e12 : ∀ o, pa s (.r12, o) = σ.gpr .rsi + BitVec.ofNat 64 o := fun o => by
    rw [pa, h.xh.xc.top.regs (.r12, .rsi) (by decide)]
  by_cases ho : allOk (Enc.rhoE (xeEk σ)) 9
  · refine .inl ⟨by rw [hr, h.r15, ifp ho]; rfl, ?_, ?_⟩
    · show (sampleMatrix 3 minIterations (Enc.rhoE (xeEk σ))).isSome = true
      rw [sampleMatrix_some (fun i hi j hj => aHat_eq ho hi hj)]; rfl
    have hx := h.mat ho
    have hek : bytesAt s'.mem (σ.gpr .rsi) mlKem768.ekLen = xeEk σ := by
      rw [hm, ← add_ofNat_zero (σ.gpr .rsi), ← e12]; exact h.xh.ek
    refine ⟨hek, ?_, fun i hi j hj => ?_, fun iters A hA i hi j hj => ?_⟩
    · rw [hm, ← e12]; exact h.xh.h
    · rw [hm, ← e12]; exact (hx i hi j hj).1
    · rw [hm, ← e12, (hx i hi j hj).2]
      change sampleMatrix 3 iters (Enc.rhoE (xeEk σ)) = some A at hA
      have h₁ := sampleMatrix_entry hA hi hj
      have h₂ := aHat_eq ho hi hj
      have e₁ := sampleNTT_mono' _ h₁ (Nat.le_max_left iters minIterations)
      have e₂ := sampleNTT_mono' _ h₂ (Nat.le_max_right iters minIterations)
      rw [e₁] at e₂
      exact (Option.some.inj e₂).symm
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := not_allOk ho
    exact sampleMatrix_none hi hj hn

end ExpandEk

open ExpandEk in
theorem expandEk_correct (v : Sample4Impl) (σ : State) (hp : expandEkK.pre σ) :
    ∃ t s', Exec isa (Impl.MlKem.X86_64.expandEk v.callee) σ t s' ∧ abiPreserved σ s' ∧ expandEkK.post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (hashes_ok hp h₁ h15) fun s₂ ⟨⟨m, r, h₂⟩, h15'⟩ =>
      WP.seq (WP.mono (Enc.mat_ok v xeMatChk xeSampChks h₂ h15') fun s₃ h₃ =>
        WP.seq (WP.mono (body_ok hp ⟨m, r, h₃⟩) fun s₄ h₄ =>
          WP.mono (topEpi_ok h₄.xh.xc.top (h₄.hin hp)) fun s₅ ⟨hr, hg, hm⟩ =>
            (⟨hg, post_of h₄ hr hm⟩ : gprPreserved σ s₅ ∧ expandEkK.post σ s₅)))))
  exact ⟨t, s', he, abiPreserved_of_ctl (by s4_ctl v) he hF.1, hF.2⟩

end VG.Proof.MlKem.X86_64
