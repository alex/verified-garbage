import VerifiedGarbage.Proof.MlKem1024.X86_64.EncTop
import VerifiedGarbage.Proof.MlKem1024.X86_64.DcSel
import VerifiedGarbage.Proof.MlKem.X86_64.DcTop

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_decaps`, its contract, layout and entry

Untrusted: everything here is checked by Lean. The contract the proof is
written against (`decaps1024K`, which the shared contract implies), the layout
of the function's buffers (`dk` and `c` in `rbp` and `r14`, which may
overlap each other; `scratch` and `key` in `rbx` and `r12`), what holds
throughout (`DC`: `Top`, and `dk` and `c` at their pointers), and the
prologue.
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mlkem1024_decaps(dk = rdi, ct = rsi, key = rdx, scratch = rcx) -> eax`, with 32 bytes of stack. -/
def decaps1024K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 3168⟩, ⟨s.gpr .rsi, 1568⟩] ∧ s.wr = [⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, 49152⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 3168⟩ ⟨s.gpr .rdx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 3168⟩ ⟨s.gpr .rcx, 49152⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 1568⟩ ⟨s.gpr .rdx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 1568⟩ ⟨s.gpr .rcx, 49152⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, 49152⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 3168⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 1568⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, 49152⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, 3168⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, 1568⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, 49152⟩ ∧
    (s.gpr .rdi).toNat + 3168 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 1568 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 49152 ≤ 2 ^ 64
  post s s' :=
    Outcome (fun iters => decapsInternal mlKem1024 iters (bytesAt s.mem (s.gpr .rdi) 3168)
      (bytesAt s.mem (s.gpr .rsi) 1568)) ((s'.gpr .rax).setWidth 32) (bytesAt s'.mem (s.gpr .rdx) 32)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    dkRho mlKem1024 (bytesAt s₁.mem (s₁.gpr .rdi) 3168) = dkRho mlKem1024 (bytesAt s₂.mem (s₂.gpr .rdi) 3168)

namespace Decaps4

open VG.Impl.MlKem1024.X86_64.Decaps1024

/-- The pointers the function keeps. -/
abbrev dcM : List (Reg × Reg) := [(.rbx, .rcx), (.rbp, .rdi), (.r14, .rsi), (.r12, .rdx)]
/-- `dk` and `c`. -/
abbrev dcR : List (Reg × Nat) := [(.rbp, 3168), (.r14, 1568)]
/-- `scratch` and `key`. -/
abbrev dcW : List (Reg × Nat) := [(.rbx, 49152), (.r12, 32)]
abbrev dcB : List (Reg × Nat) := dcR ++ dcW

theorem dcB_bases : ∀ b ∈ dcB, b.1 ∈ bases := by decide
theorem dcM_bases : ∀ p ∈ dcM, p.1 ∈ bases := by decide

section
variable {σ : State} (hp : decaps1024K.pre σ)
include hp

theorem dcLay {s : State} (h : Top dcM σ s) : Lay dcR dcW s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .rcx := h.regs (.rbx, .rcx) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r14 = σ.gpr .rsi := h.regs (.r14, .rsi) (by decide)
  have e4 : s.gpr .r12 = σ.gpr .rdx := h.regs (.r12, .rdx) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of (by decide) (pw4 ?_ ?_ ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_)
    (fa2 ?_ ?_) (fa4 ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, h.rsp, retR]
  · exact fun hw => absurd hw (by decide)
  · exact fun _ => d2
  · exact fun _ => d1
  · exact fun _ => d4
  · exact fun _ => d3
  · exact fun _ => d5.symm
  exacts [k1, k2, k4, k3, n1, n2, n4, n3,
    mem ⟨σ.gpr .rdi, 3168⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rsi, 1568⟩ (by rw [hrd]; simp),
    mem ⟨σ.gpr .rcx, 49152⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, 32⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    r1, r2, r4, r3]

end

/-- `dk` and `c`. -/
abbrev dcDk (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 3168
abbrev dcC (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rsi) 1568

/-- What holds throughout. -/
structure DC (σ s : State) : Prop where
  top : Top dcM σ s
  dk : bytesAt s.mem (pa s (.rbp, 0)) 3168 = dcDk σ
  c : bytesAt s.mem (pa s (.r14, 0)) 1568 = dcC σ

/-- A piece that writes `ws` keeps `DC`. -/
def dcChk (ws : List (Ptr × Nat)) : Bool :=
  topChk dcB ws && keepB dcB ws (.rbp, 0) 3168 && keepB dcB ws (.r14, 0) 1568

theorem DC.lay {σ : State} (hp : decaps1024K.pre σ) {s : State} (h : DC σ s) : Lay dcR dcW s := dcLay hp h.top

theorem DC.step {σ : State} (hp : decaps1024K.pre σ) {s s' : State} (h : DC σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hc : dcChk ws = true) : DC σ s' := by
  simp only [dcChk, Bool.and_eq_true] at hc
  have L := h.lay hp
  exact ⟨h.top.step L hP dcM_bases hc.1.1, by rw [L.keepBytes hP hc.1.2]; exact h.dk,
    by rw [L.keepBytes hP hc.2]; exact h.c⟩

theorem pro_eq : pro = [.store (at_ .rcx 840) .rbx, .store (at_ .rcx 848) .rbp, .store (at_ .rcx 856) .r12,
    .store (at_ .rcx 864) .r13, .store (at_ .rcx 872) .r14, .store (at_ .rcx 880) .r15, .mov .rbx (.reg .rcx),
    .mov .rbp (.reg .rdi), .mov .r14 (.reg .rsi), .mov .r12 (.reg .rdx), .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {σ : State} (hp : decaps1024K.pre σ) : WP isa (.block pro) σ fun s => DC σ s ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp'
  have hS : ⟨σ.gpr .rcx, 49152⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ 49152 → (⟨σ.gpr .rcx, 49152⟩ : Region).Contains (σ.gpr .rcx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega)
  have w : ∀ o, o + 8 ≤ 49152 → InRegions σ.wr (σ.gpr .rcx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r14, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .rcx + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .rcx + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .rcx + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r14 = σ.gpr .rsi ∧ s.gpr .r12 = σ.gpr .rdx ∧
    s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h14, h12, h15⟩, k⟩ => ⟨?_, h15⟩
  have hf : Frame [⟨σ.gpr .rcx, 49152⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨k.2.1, k.2.2, hsp, fa4 hbx hbp h14 h12, fun j hj => ?_, ?_⟩, ?_, ?_⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .rcx) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r4) (by decide)
  · rw [pa, hbp, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d2) (by decide)
  · rw [pa, h14, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d4) (by decide)

end Decaps4

end VG.Proof.MlKem1024.X86_64
