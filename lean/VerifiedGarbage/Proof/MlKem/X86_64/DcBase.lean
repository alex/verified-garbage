import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
import VerifiedGarbage.Proof.MlKem.X86_64.DcSel

/-!
# ML-KEM on x86-64: decapsulation, its contract, layout, checks and entry

For a parameter set `L`: the contract the proof is written against
(`decapsK L`, which the shared contract implies), the layout of the
function's buffers (`dk` and `c` in `rbp` and `r14`, which may overlap each
other; `scratch` and `key` in `rbx` and `r12`), what holds throughout (`DC`:
`Top`, and `dk` and `c` at their pointers), the checks of the layout every
piece needs (`DcWf L`), and the prologue.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `kemDecaps L (dk = rdi, ct = rsi, key = rdx, scratch = rcx) -> eax`, with 32 bytes of stack. -/
def decapsK (L : Kem) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, L.dkLen⟩, ⟨s.gpr .rsi, L.ctLen⟩] ∧ s.wr = [⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, L.scr⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, L.dkLen⟩ ⟨s.gpr .rdx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, L.dkLen⟩ ⟨s.gpr .rcx, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, L.ctLen⟩ ⟨s.gpr .rdx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, L.ctLen⟩ ⟨s.gpr .rcx, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, L.scr⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, L.dkLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, L.ctLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, L.scr⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, L.dkLen⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, L.ctLen⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, L.scr⟩ ∧
    (s.gpr .rdi).toNat + L.dkLen ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + L.ctLen ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + L.scr ≤ 2 ^ 64
  post s s' :=
    Outcome (fun iters => decapsInternal L.p iters (bytesAt s.mem (s.gpr .rdi) L.dkLen)
      (bytesAt s.mem (s.gpr .rsi) L.ctLen)) ((s'.gpr .rax).setWidth 32) (bytesAt s'.mem (s.gpr .rdx) 32)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    dkRho L.p (bytesAt s₁.mem (s₁.gpr .rdi) L.dkLen) = dkRho L.p (bytesAt s₂.mem (s₂.gpr .rdi) L.dkLen)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

variable (L : Kem)

/-- The pointers the function keeps. -/
abbrev dcM : List (Reg × Reg) := [(.rbx, .rcx), (.rbp, .rdi), (.r14, .rsi), (.r12, .rdx)]
/-- `dk` and `c`. -/
abbrev dcR : List (Reg × Nat) := [(.rbp, L.dkLen), (.r14, L.ctLen)]
/-- `scratch` and `key`. -/
abbrev dcW : List (Reg × Nat) := [(.rbx, L.scr), (.r12, 32)]
abbrev dcB : List (Reg × Nat) := dcR L ++ dcW L

theorem dcB_bases : ∀ b ∈ dcB L, b.1 ∈ bases := by
  intro b hb; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp [bases]

theorem dcM_bases : ∀ p ∈ dcM, p.1 ∈ bases := by decide

/-- A piece that writes `ws` keeps `DC`. -/
def dcChk (ws : List (Ptr × Nat)) : Bool :=
  topChk (dcB L) ws && keepB (dcB L) ws (.rbp, 0) L.dkLen && keepB (dcB L) ws (.r14, 0) L.ctLen

/-- A piece that writes `ws` keeps `DR nu ns`. -/
def drChk (nu ns : Nat) (ws : List (Ptr × Nat)) : Bool :=
  dcChk L ws && (List.range nu).all (fun i => keepB (dcB L) ws (pS i) 1024) &&
    (List.range ns).all (fun i => keepB (dcB L) ws (pS (L.k + i)) 1024)

abbrev uW (i : Nat) : List (Ptr × Nat) := [(pS i, 1024)] ++ [(pS i, 1024), (sc oSS, 1024)]

def uChk (i : Nat) : Bool :=
  twoChk (dcB L) (dcW L) (.r14, 32 * L.du * i) (32 * L.du) (pS i) 1024 && ipChk (dcB L) (dcW L) (pS i) &&
    drChk L i 0 (uW i)

def sChk (i : Nat) : Bool :=
  twoChk (dcB L) (dcW L) (.rbp, 384 * i) 384 (pS (L.k + i)) 1024 && drChk L L.k i [(pS (L.k + i), 1024)]

abbrev tailW : List (Ptr × Nat) := dotW L.k ++ [(pS 15, 1024), (sc oSS, 1024)] ++ [(pS 16, 1024)] ++
  [(pS 16, 1024)] ++ [(sc oM, 32 * 1)]

def tailChk : Bool :=
  dotChk (dcB L) (dcW L) (fun j => pS (L.k + j)) pS L.k && ipChk (dcB L) (dcW L) (pS 15) &&
    twoChk (dcB L) (dcW L) (.r14, 32 * L.du * L.k) (32 * L.dv) (pS 16) 1024 &&
    keepB (dcB L) [(pS 16, 1024)] (pS 15) 1024 && accChk (dcB L) (dcW L) (pS 16) (pS 15) &&
    twoChk (dcB L) (dcW L) (pS 16) 1024 (sc oM) (32 * 1) && dcChk L (tailW L) &&
    dcChk L (dotW L.k ++ [(pS 15, 1024), (sc oSS, 1024)])

def dckChk (ws : List (Ptr × Nat)) : Bool := dcChk L ws && keepB (dcB L) ws (sc oG) 32 && keepB (dcB L) ws (sc oKB) 32

/-- The writes of the hashes. -/
abbrev hW₁ : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), (sc oG, 64)]
abbrev hW₂ : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), (sc oKB, 32)]

/-- What every piece of decapsulation needs of the layout, evaluated for each parameter set. -/
structure DcWf : Prop extends KemWf L where
  scr : 888 ≤ L.scr ∧ L.scr < 2 ^ 32
  small : ∀ b ∈ dcB L, b.2 < 2 ^ 32
  -- K-PKE.Decrypt
  u : ∀ i < L.k, uChk L i = true
  s : ∀ i < L.k, sChk L i = true
  tail : tailChk L = true
  -- the hashes
  h₁ : hashChk (dcB L) (dcW L) [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)] 72 (sc oG) 64 = true
  h₁K : dcChk L hW₁ = true
  h₁M : keepB (dcB L) hW₁ (sc oM) 32 = true
  h₂ : hashChk (dcB L) (dcW L) [((.rbp, 768 * L.k + 64), 32), ((.r14, 0), L.ctLen)] 136 (sc oKB) 32 = true
  h₂K : dcChk L hW₂ = true
  h₂G : keepB (dcB L) hW₂ (sc oG) 64 = true
  h₂M : keepB (dcB L) hW₂ (sc oM) 32 = true
  enc : Enc.encChk L (dcB L) (dcW L) (dckChk L) (.rbp, 384 * L.k) = true
  -- the choice of the key
  selK : dcChk L [((.r12, 0), 32)] = true
  sel : inB (dcB L) (.r14, 0) L.ctLen = true ∧ inB (dcB L) (sc L.oCT) L.ctLen = true ∧
    inB (dcB L) (sc oG) 32 = true ∧ inB (dcB L) (sc oKB) 32 = true ∧ inB (dcW L) (.r12, 0) 32 = true ∧
    sepB (dcB L) (sc oG) 32 (.r12, 0) 32 = true ∧ sepB (dcB L) (sc oKB) 32 (.r12, 0) 32 = true
  ct : L.oCT < 2 ^ 31 ∧ L.ctLen < 2 ^ 32 ∧ 0 < L.ctLen
  sv : ∀ k < 6, inB (dcB L) (sc (oSV + 8 * k)) 8 = true
  -- constant time
  inBs : inB (dcB L) (sc 0) 1 = true ∧ inB (dcB L) (.r12, 0) 1 = true ∧ inB (dcB L) (.r14, 0) 1 = true
  selT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .r12, .r14]) (select L) h).isSome = true
  rhoT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp]) (copy (sc oSB) (.rbp, 384 * L.k + 384 * L.k) 32)
    h).isSome = true

section
variable {L : Kem} (W : DcWf L) {σ : State} (hp : (decapsK L).pre σ)
include W hp

theorem dcLay {s : State} (h : Top dcM σ s) : Lay (dcR L) (dcW L) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .rcx := h.regs (.rbx, .rcx) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r14 = σ.gpr .rsi := h.regs (.r14, .rsi) (by decide)
  have e4 : s.gpr .r12 = σ.gpr .rdx := h.regs (.r12, .rdx) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of W.small (pw4 ?_ ?_ ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_)
    (fa2 ?_ ?_) (fa4 ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, h.rsp, retR]
  · exact fun hw => absurd hw (by decide)
  · exact fun _ => d2
  · exact fun _ => d1
  · exact fun _ => d4
  · exact fun _ => d3
  · exact fun _ => d5.symm
  exacts [k1, k2, k4, k3, n1, n2, n4, n3,
    mem ⟨σ.gpr .rdi, L.dkLen⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rsi, L.ctLen⟩ (by rw [hrd]; simp),
    mem ⟨σ.gpr .rcx, L.scr⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, 32⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    r1, r2, r4, r3]

end

/-- `dk` and `c`. -/
abbrev dcDk (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) L.dkLen
abbrev dcC (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rsi) L.ctLen

/-- What holds throughout. -/
structure DC (L : Kem) (σ s : State) : Prop where
  top : Top dcM σ s
  dk : bytesAt s.mem (pa s (.rbp, 0)) L.dkLen = dcDk L σ
  c : bytesAt s.mem (pa s (.r14, 0)) L.ctLen = dcC L σ

section
variable {L : Kem} (W : DcWf L) {σ : State} (hp : (decapsK L).pre σ)
include W hp

theorem DC.lay {s : State} (h : DC L σ s) : Lay (dcR L) (dcW L) s := dcLay W hp h.top

theorem DC.step {s s' : State} (h : DC L σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (hc : dcChk L ws = true) : DC L σ s' := by
  simp only [dcChk, Bool.and_eq_true] at hc
  have L₀ := h.lay W hp
  exact ⟨h.top.step L₀ hP dcM_bases hc.1.1, by rw [L₀.keepBytes hP hc.1.2]; exact h.dk,
    by rw [L₀.keepBytes hP hc.2]; exact h.c⟩

end

/-- Bytes of a buffer. -/
theorem slice_of {s : State} {r : Reg} {n : Nat} {B : List Byte} (h : bytesAt s.mem (pa s (r, 0)) n = B) {o l : Nat}
    (hol : o + l ≤ n) : bytesAt s.mem (pa s (r, o)) l = (B.drop o).take l := by
  rw [← h, bytesAt_slice _ _ hol, pa, pa, off_add, Nat.zero_add]

theorem pro_eq : pro = [.store (at_ .rcx 840) .rbx, .store (at_ .rcx 848) .rbp, .store (at_ .rcx 856) .r12,
    .store (at_ .rcx 864) .r13, .store (at_ .rcx 872) .r14, .store (at_ .rcx 880) .r15, .mov .rbx (.reg .rcx),
    .mov .rbp (.reg .rdi), .mov .r14 (.reg .rsi), .mov .r12 (.reg .rdx), .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {L : Kem} (W : DcWf L) {σ : State} (hp : (decapsK L).pre σ) :
    WP isa (.block pro) σ fun s => DC L σ s ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp'
  have hsc := W.scr
  have hS : ⟨σ.gpr .rcx, L.scr⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ L.scr → (⟨σ.gpr .rcx, L.scr⟩ : Region).Contains (σ.gpr .rcx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega)
  have w : ∀ o, o + 8 ≤ L.scr → InRegions σ.wr (σ.gpr .rcx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
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
  have hf : Frame [⟨σ.gpr .rcx, L.scr⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  have hdk := W.small (.rbp, L.dkLen) (by simp)
  have hct := W.small (.r14, L.ctLen) (by simp)
  refine ⟨⟨k.2.1, k.2.2, hsp, fa4 hbx hbp h14 h12, fun j hj => ?_, ?_⟩, ?_, ?_⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .rcx) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r4) (by decide)
  · rw [pa, hbp, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d2) (by simp only at hdk; omega)
  · rw [pa, h14, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d4) (by simp only at hct; omega)

end Decaps

end VG.Proof.MlKem.X86_64
