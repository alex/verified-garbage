import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
import VerifiedGarbage.Impl.MlKem.X86_64.KeyGen

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_keygen`, its contract, layout and entry

Untrusted: everything here is checked by Lean. The contract the proof is
written against (`keyGenK`, which the shared contract implies), the layout
of the function's buffers (`seed` in `rbp`; `scratch`, `ek`, `dk` in `rbx`,
`r12`, `r13`), what holds throughout (`KC`: `Top`, and `d ‖ z` at `seed`),
and the prologue.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mlkem768_keygen(seed = rdi, ek = rsi, dk = rdx, scratch = rcx) -> eax`, with 32 bytes of stack. -/
def keyGenK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 64⟩] ∧ s.wr = [⟨s.gpr .rsi, 1184⟩, ⟨s.gpr .rdx, 2400⟩, ⟨s.gpr .rcx, 32768⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rsi, 1184⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rdx, 2400⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rcx, 32768⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 1184⟩ ⟨s.gpr .rdx, 2400⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 1184⟩ ⟨s.gpr .rcx, 32768⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, 2400⟩ ⟨s.gpr .rcx, 32768⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 64⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 1184⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 2400⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, 32768⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, 64⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, 1184⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, 2400⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, 32768⟩ ∧
    (s.gpr .rdi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 1184 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 2400 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 32768 ≤ 2 ^ 64
  post s s' :=
    Outcome (fun iters => keyGenInternal mlKem768 iters (bytesAt s.mem (s.gpr .rdi) 32)
      (bytesAt s.mem (s.gpr .rdi + 32) 32)) ((s'.gpr .rax).setWidth 32)
      (bytesAt s'.mem (s.gpr .rsi) 1184, bytesAt s'.mem (s.gpr .rdx) 2400)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    keyGenRho mlKem768 (bytesAt s₁.mem (s₁.gpr .rdi) 32) = keyGenRho mlKem768 (bytesAt s₂.mem (s₂.gpr .rdi) 32)

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

/-- The pointers the function keeps. -/
abbrev kgM : List (Reg × Reg) := [(.rbx, .rcx), (.rbp, .rdi), (.r12, .rsi), (.r13, .rdx)]
/-- `seed`. -/
abbrev kgR : List (Reg × Nat) := [(.rbp, 64)]
/-- `scratch`, `ek` and `dk`. -/
abbrev kgW : List (Reg × Nat) := [(.rbx, 32768), (.r12, 1184), (.r13, 2400)]
abbrev kgB : List (Reg × Nat) := kgR ++ kgW

theorem kgB_bases : ∀ b ∈ kgB, b.1 ∈ bases := by decide
theorem kgM_bases : ∀ p ∈ kgM, p.1 ∈ bases := by decide

section
variable {σ : State} (hp : keyGenK.pre σ)
include hp

theorem kgLay {s : State} (h : Top kgM σ s) : Lay kgR kgW s := by
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
    mem ⟨σ.gpr .rdi, 64⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rcx, 32768⟩ (by rw [hwr]; simp),
    mem ⟨σ.gpr .rsi, 1184⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, 2400⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, r1, r4, r2, r3]

/-- `d` and `z`. -/
abbrev kgD (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 32
abbrev kgZ (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi + 32) 32

/-- What holds throughout. -/
structure KC (σ s : State) : Prop where
  top : Top kgM σ s
  d : bytesAt s.mem (pa s (.rbp, 0)) 32 = kgD σ
  z : bytesAt s.mem (pa s (.rbp, 32)) 32 = kgZ σ

/-- A piece that writes `ws` keeps `KC`. -/
def kcChk (ws : List (Ptr × Nat)) : Bool :=
  topChk kgB ws && keepB kgB ws (.rbp, 0) 32 && keepB kgB ws (.rbp, 32) 32

end

/-- The precondition `pre` of a function that keeps the pointers of `vg_mlkem768_keygen` (`kgM`), under
which its buffers are laid out as `kgR`/`kgW` (`lay`), and its public data `pub`, on which two runs have the
same pointers and `ρ` (`eq`). The proof of `vg_mlkem768_keygen` holds for any: `vg_mlkem768_keygen_expanded`
runs it with a larger `ek`. -/
structure KPre where
  pre : State → Prop
  pub : State → State → Prop
  lay : ∀ {σ s : State}, pre σ → Top kgM σ s → Lay kgR kgW s
  eq : ∀ {σ₁ σ₂ : State}, pub σ₁ σ₂ → σ₁.gpr .rdi = σ₂.gpr .rdi ∧ σ₁.gpr .rsi = σ₂.gpr .rsi ∧
    σ₁.gpr .rdx = σ₂.gpr .rdx ∧ σ₁.gpr .rcx = σ₂.gpr .rcx ∧ σ₁.gpr .rsp = σ₂.gpr .rsp ∧
    keyGenRho mlKem768 (kgD σ₁) = keyGenRho mlKem768 (kgD σ₂)

/-- `vg_mlkem768_keygen`'s. -/
def kgK : KPre where
  pre := keyGenK.pre
  pub := keyGenK.pub
  lay hp h := kgLay hp h
  eq h := h

section
variable {K : KPre} {σ : State} (hp : K.pre σ)
include hp

theorem KC.lay {s : State} (h : KC σ s) : Lay kgR kgW s := K.lay hp h.top

theorem KC.step {s s' : State} (h : KC σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (hc : kcChk ws = true) : KC σ s' := by
  simp only [kcChk, Bool.and_eq_true] at hc
  have L := h.lay hp
  exact ⟨h.top.step L hP kgM_bases hc.1.1, by rw [L.keepBytes hP hc.1.2]; exact h.d,
    by rw [L.keepBytes hP hc.2]; exact h.z⟩

end

theorem pro_eq : pro = [.store (at_ .rcx 840) .rbx, .store (at_ .rcx 848) .rbp, .store (at_ .rcx 856) .r12,
    .store (at_ .rcx 864) .r13, .store (at_ .rcx 872) .r14, .store (at_ .rcx 880) .r15, .mov .rbx (.reg .rcx),
    .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov32 .r15 (.imm 1)] := rfl

/-- The prologue, from the facts it needs of the precondition: `scratch` is written, and apart from `seed`
and the return address. -/
theorem pro_okF {σ : State} (hS : ⟨σ.gpr .rcx, 32768⟩ ∈ σ.wr)
    (d3 : Region.Disjoint ⟨σ.gpr .rdi, 64⟩ ⟨σ.gpr .rcx, 32768⟩) (r4 : (retR σ).Disjoint ⟨σ.gpr .rcx, 32768⟩) :
    WP isa (.block pro) σ fun s => KC σ s ∧ s.gpr .r15 = 1 := by
  have c : ∀ o, o + 8 ≤ 32768 → (⟨σ.gpr .rcx, 32768⟩ : Region).Contains (σ.gpr .rcx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega)
  have w : ∀ o, o + 8 ≤ 32768 → InRegions σ.wr (σ.gpr .rcx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .rcx + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .rcx + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .rcx + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r12 = σ.gpr .rsi ∧ s.gpr .r13 = σ.gpr .rdx ∧
    s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h13, h15⟩, k⟩ => ⟨?_, h15⟩
  have hf : Frame [⟨σ.gpr .rcx, 32768⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsd : bytesAt s.mem (σ.gpr .rdi) 64 = bytesAt σ.mem (σ.gpr .rdi) 64 :=
    bytesAt_frame hf (by simpa using d3) (by decide)
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨k.2.1, k.2.2, hsp, fa4 hbx hbp h12 h13, fun j hj => ?_, ?_⟩, ?_, ?_⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .rcx) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r4) (by decide)
  · rw [pa, hbp, add_ofNat_zero, ← bytesAt_take s.mem _ (show 32 ≤ 64 by decide), hsd,
      bytesAt_take σ.mem _ (show 32 ≤ 64 by decide)]
  · rw [pa, hbp, ← bytesAt_slice s.mem _ (show 32 + 32 ≤ 64 by decide), hsd,
      bytesAt_slice σ.mem _ (show 32 + 32 ≤ 64 by decide)]
    rfl

theorem pro_ok {σ : State} (hp : keyGenK.pre σ) : WP isa (.block pro) σ fun s => KC σ s ∧ s.gpr .r15 = 1 := by
  obtain ⟨_, hwr, _, _, d3, _, _, _, _, _, _, r4, _⟩ := hp
  exact pro_okF (by rw [hwr]; simp) d3 r4

end KeyGen

end VG.Proof.MlKem.X86_64
