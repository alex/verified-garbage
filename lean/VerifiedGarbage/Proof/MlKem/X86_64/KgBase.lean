import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
import VerifiedGarbage.Proof.MlKem.X86_64.Dot
import VerifiedGarbage.Proof.MlKem.X86_64.FragS4
import VerifiedGarbage.Proof.MlKem.X86_64.Prfs
import VerifiedGarbage.Impl.MlKem.X86_64.KeyGen

/-!
# ML-KEM on x86-64: key generation, its contract, layout, checks and entry

For a parameter set `L` (`Impl/MlKem/X86_64/Kem.lean`): the contract the
proof is written against (`keyGenK L`, which the shared contract of
ML-KEM-768 or ML-KEM-1024 implies), the layout of the function's buffers
(`seed` in `rbp`; `scratch`, `ek`, `dk` in `rbx`, `r12`, `r13`), what holds
throughout (`KC`: `Top`, and `d ‖ z` at `seed`), the prologue, and the
checks of the layout every piece needs (`KgWf L`), which each parameter set
evaluates.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `kemKeyGen L (seed = rdi, ek = rsi, dk = rdx, scratch = rcx) -> eax`, with 32 bytes of stack. -/
def keyGenK (L : Kem) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 64⟩] ∧ s.wr = [⟨s.gpr .rsi, L.ekLen⟩, ⟨s.gpr .rdx, L.dkLen⟩, ⟨s.gpr .rcx, L.scr⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rsi, L.ekLen⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rdx, L.dkLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rcx, L.scr⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, L.ekLen⟩ ⟨s.gpr .rdx, L.dkLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, L.ekLen⟩ ⟨s.gpr .rcx, L.scr⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, L.dkLen⟩ ⟨s.gpr .rcx, L.scr⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 64⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, L.ekLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, L.dkLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, L.scr⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, 64⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, L.ekLen⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, L.dkLen⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, L.scr⟩ ∧
    (s.gpr .rdi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + L.ekLen ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + L.dkLen ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + L.scr ≤ 2 ^ 64
  post s s' :=
    Outcome (fun iters => keyGenInternal L.p iters (bytesAt s.mem (s.gpr .rdi) 32)
      (bytesAt s.mem (s.gpr .rdi + 32) 32)) ((s'.gpr .rax).setWidth 32)
      (bytesAt s'.mem (s.gpr .rsi) L.ekLen, bytesAt s'.mem (s.gpr .rdx) L.dkLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    keyGenRho L.p (bytesAt s₁.mem (s₁.gpr .rdi) 32) = keyGenRho L.p (bytesAt s₂.mem (s₂.gpr .rdi) 32)

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

variable (L : Kem)

/-- The pointers the function keeps. -/
abbrev kgM : List (Reg × Reg) := [(.rbx, .rcx), (.rbp, .rdi), (.r12, .rsi), (.r13, .rdx)]
/-- `seed`. -/
abbrev kgR : List (Reg × Nat) := [(.rbp, 64)]
/-- `scratch`, `ek` and `dk`. -/
abbrev kgW : List (Reg × Nat) := [(.rbx, L.scr), (.r12, L.ekLen), (.r13, L.dkLen)]
abbrev kgB : List (Reg × Nat) := kgR ++ kgW L

theorem kgB_bases : ∀ b ∈ kgB L, b.1 ∈ bases := by
  intro b hb; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp [bases]

theorem kgM_bases : ∀ p ∈ kgM, p.1 ∈ bases := by decide

/-- A piece that writes `ws` keeps `KC`. -/
def kcChk (ws : List (Ptr × Nat)) : Bool :=
  topChk (kgB L) ws && keepB (kgB L) ws (.rbp, 0) 32 && keepB (kgB L) ws (.rbp, 32) 32

/-! ## The checks of the pieces -/

/-- `ρ` of `Â`'s entry `e`. -/
abbrev aE (e : Nat) : Ptr := L.aS (e / L.k) (e % L.k)

/-- What entry `e` of `Â` writes. -/
abbrev ijW (e : Nat) : List (Ptr × Nat) :=
  [(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)] ++ [(pS (L.pA + e), 1024), (sc oSS, 2048)]

/-- Entry `e` of `Â`, on its own. -/
def kbChk (e : Nat) : Bool :=
  ijChk (kgB L) (kgW L) (pS (L.pA + e)) && kcChk L (ijW L e) && keepB (kgB L) (ijW L e) (sc oG) 32 &&
    keepB (kgB L) (ijW L e) sigP 32 && keepB (kgB L) (ijW L e) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB (kgB L) (ijW L e) (pS (L.pA + e')) 1024

/-- What entries `e, …, e + 3` of `Â` write. -/
abbrev qW (e : Nat) : List (Ptr × Nat) := quadW (oP (L.pA + e)) (oP L.pW)

/-- Entries `e, …, e + 3` of `Â`, at once. -/
def kqChk (e : Nat) : Bool :=
  quadChk (kgB L) (kgW L) (oP (L.pA + e)) (oP L.pW) && kcChk L (qW L e) && keepB (kgB L) (qW L e) (sc oG) 32 &&
    keepB (kgB L) (qW L e) sigP 32 && keepB (kgB L) (qW L e) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB (kgB L) (qW L e) (pS (L.pA + e')) 1024

/-- `PRF₂(σ, N)`, in the outputs of `prfs`. -/
abbrev prfO (N : Nat) : Ptr := sc (L.oPR + 128 * N)

/-- A piece that writes `ws` keeps `KRest n r e`. -/
def restChk (n r e : Nat) (ws : List (Ptr × Nat)) : Bool :=
  kcChk L ws && keepB (kgB L) ws (sc oG) 32 && keepB (kgB L) ws sigP 32 &&
    (List.range (L.k * L.k)).all (fun e => keepB (kgB L) ws (pS (L.pA + e)) 1024) &&
    (List.range (2 * L.k)).all (fun N => keepB (kgB L) ws (prfO L N) 128) &&
    (List.range n).all (fun k => keepB (kgB L) ws (pS k) 1024) &&
    (List.range r).all (fun i => keepB (kgB L) ws (.r12, 384 * i) 384) &&
    (List.range e).all (fun j => keepB (kgB L) ws (.r13, 384 * j) 384)

def prfsKChk : Bool :=
  prfsChk (kgB L) (kgW L) (2 * L.k) L.oPR L.lPW && kcChk L (prfsW (2 * L.k) L.oPR L.lPW) &&
    keepB (kgB L) (prfsW (2 * L.k) L.oPR L.lPW) (sc oG) 32 && keepB (kgB L) (prfsW (2 * L.k) L.oPR L.lPW) sigP 32 &&
    (List.range (L.k * L.k)).all (fun e => keepB (kgB L) (prfsW (2 * L.k) L.oPR L.lPW) (pS (L.pA + e)) 1024)

/-- What `se N` writes. -/
abbrev seW (N : Nat) : List (Ptr × Nat) := [(pS N, 1024)] ++ [(pS N, 1024), (sc oSS, 1024)]

def seChk (N : Nat) : Bool :=
  twoChk (kgB L) (kgW L) (prfO L N) 128 (pS N) 1024 && ipChk (kgB L) (kgW L) (pS N) && restChk L N 0 0 (seW N)

/-- What `row i` writes. -/
abbrev rowW (i : Nat) : List (Ptr × Nat) := dotW L.k ++ [(pS 15, 1024)] ++ [((.r12, 384 * i), 384)]

def rowChk (i : Nat) : Bool :=
  dotChk (kgB L) (kgW L) (fun j => L.aS i j) pS L.k && accChk (kgB L) (kgW L) (pS 15) (pS (L.k + i)) &&
    keepB (kgB L) (dotW L.k) (pS (L.k + i)) 1024 && twoChk (kgB L) (kgW L) (pS 15) 1024 (.r12, 384 * i) 384 &&
    restChk L (2 * L.k) i 0 (rowW L i)

def encSChk (j : Nat) : Bool :=
  twoChk (kgB L) (kgW L) (pS j) 1024 (.r13, 384 * j) 384 && restChk L (2 * L.k) L.k j [((.r13, 384 * j), 384)]

/-- The writes of `fin`. -/
abbrev finW₁ : List (Ptr × Nat) := [((.r12, 384 * L.k), 32)]
abbrev finW₂ : List (Ptr × Nat) := [((.r13, 384 * L.k), L.ekLen)]
abbrev finW₃ : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), ((.r13, 384 * L.k + L.ekLen), 32)]
abbrev finW₄ : List (Ptr × Nat) := [((.r13, 384 * L.k + L.ekLen + 32), 32)]

end KeyGen

/-- What all the top-level functions need of the parameter set: its rank,
`η₁ = η₂ = 2`, and the constant time of the indices of the seeds of `Â`. -/
structure KemWf (L : Kem) : Prop where
  k : 0 < L.k ∧ L.k ≤ 4
  eta : L.p.η₁ = 2 ∧ L.p.η₂ = 2
  ijT : ∀ e < L.k * L.k, (taint.check (X86_64.Taint.ofRegs [.rbx])
    (.block (setB (sc (oSB + 32)) (e % L.k) ++ setB (sc (oSB + 33)) (e / L.k))) (.block [])).isSome = true

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

variable (L : Kem)

/-- What every piece of key generation needs of the layout, evaluated for each parameter set. -/
structure KgWf : Prop extends KemWf L where
  scr : 888 ≤ L.scr ∧ L.scr < 2 ^ 32
  small : ∀ b ∈ kgB L, b.2 < 2 ^ 32
  -- `G(d ‖ k)`
  nb : inB (kgW L) (sc oNB) 1 = true
  nbK : kcChk L [(sc oNB, 1)] = true
  gH : hashChk (kgB L) (kgW L) [((.rbp, 0), 32), (sc oNB, 1)] 72 (sc oG) 64 = true
  gK : kcChk L [(sc 0, 200), (sc 200, 640), (sc oG, 64)] = true
  gC : copyChk (kgB L) (kgW L) (sc oSB) (sc oG) 32 = true
  gCK : kcChk L [(sc oSB, 32)] = true
  gG : keepB (kgB L) [(sc oSB, 32)] (sc oG) 32 = true
  gS : keepB (kgB L) [(sc oSB, 32)] sigP 32 = true
  -- the matrix
  kq : ∀ q < L.k * L.k / 4, kqChk L (4 * q) = true
  kb : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → kbChk L e = true
  flag : kcChk L [] = true
  flagG : keepB (kgB L) [] (sc oG) 32 = true
  flagS : keepB (kgB L) [] sigP 32 = true
  flagB : keepB (kgB L) [] (sc oSB) 32 = true
  flagA : ∀ e < L.k * L.k, keepB (kgB L) [] (pS (L.pA + e)) 1024 = true
  -- the keys
  prfs : prfsKChk L = true
  se : ∀ N < 2 * L.k, seChk L N = true
  row : ∀ i < L.k, rowChk L i = true
  encS : ∀ j < L.k, encSChk L j = true
  f₁ : copyChk (kgB L) (kgW L) (.r12, 384 * L.k) (sc oG) 32 = true
  f₁K : kcChk L (finW₁ L) = true
  f₁E : ∀ i < L.k, keepB (kgB L) (finW₁ L) (.r12, 384 * i) 384 = true
  f₂ : copyChk (kgB L) (kgW L) (.r13, 384 * L.k) (.r12, 0) L.ekLen = true
  f₂K : kcChk L (finW₂ L) = true
  f₂E : keepB (kgB L) (finW₂ L) (.r12, 0) L.ekLen = true
  f₃ : hashChk (kgB L) (kgW L) [((.r12, 0), L.ekLen)] 136 (.r13, 384 * L.k + L.ekLen) 32 = true
  f₃K : kcChk L (finW₃ L) = true
  f₃E : keepB (kgB L) (finW₃ L) (.r12, 0) L.ekLen = true
  f₄ : copyChk (kgB L) (kgW L) (.r13, 384 * L.k + L.ekLen + 32) (.rbp, 32) 32 = true
  f₄K : kcChk L (finW₄ L) = true
  f₄E : keepB (kgB L) (finW₄ L) (.r12, 0) L.ekLen = true
  dkS : ∀ j < L.k, keepB (kgB L) (finW₁ L ++ finW₂ L ++ finW₃ L ++ finW₄ L) (.r13, 384 * j) 384 = true
  dkE : keepB (kgB L) (finW₃ L ++ finW₄ L) (.r13, 384 * L.k) L.ekLen = true
  dkH : keepB (kgB L) (finW₄ L) (.r13, 384 * L.k + L.ekLen) 32 = true
  -- the end
  sv : ∀ k < 6, inB (kgB L) (sc (oSV + 8 * k)) 8 = true
  -- constant time
  inBs : inB (kgB L) (sc 0) 1 = true ∧ inB (kgB L) (.r12, 0) 1 = true ∧ inB (kgB L) (.r13, 0) 1 = true
  nbT : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc oNB) L.k)) (.block [])).isSome = true
  finT₁ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13]) (copy (.r12, 384 * L.k) (sc oG) 32)
    h).isSome = true
  finT₂ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13]) (copy (.r13, 384 * L.k) (.r12, 0) L.ekLen)
    h).isSome = true
  finT₄ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13])
    (copy (.r13, 384 * L.k + L.ekLen + 32) (.rbp, 32) 32) h).isSome = true

section
variable {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ)
include W hp

theorem kgLay {s : State} (h : Top kgM σ s) : Lay kgR (kgW L) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .rcx := h.regs (.rbx, .rcx) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rsi := h.regs (.r12, .rsi) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .rdx := h.regs (.r13, .rdx) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of W.small (pw4 ?_ ?_ ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_)
    (fa3 ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, h.rsp, retR]
  · exact fun _ => d3
  · exact fun _ => d1
  · exact fun _ => d2
  · exact fun _ => d5.symm
  · exact fun _ => d6.symm
  · exact fun _ => d4
  exacts [k1, k4, k2, k3, n1, n4, n2, n3,
    mem ⟨σ.gpr .rdi, 64⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rcx, L.scr⟩ (by rw [hwr]; simp),
    mem ⟨σ.gpr .rsi, L.ekLen⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, L.dkLen⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, r1, r4, r2, r3]

end

/-- `d` and `z`. -/
abbrev kgD (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 32
abbrev kgZ (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi + 32) 32

/-- What holds throughout. -/
structure KC (σ s : State) : Prop where
  top : Top kgM σ s
  d : bytesAt s.mem (pa s (.rbp, 0)) 32 = kgD σ
  z : bytesAt s.mem (pa s (.rbp, 32)) 32 = kgZ σ

section
variable {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ)
include W hp

theorem KC.lay {s : State} (h : KC σ s) : Lay kgR (kgW L) s := kgLay W hp h.top

theorem KC.step {s s' : State} (h : KC σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (hc : kcChk L ws = true) : KC σ s' := by
  simp only [kcChk, Bool.and_eq_true] at hc
  have L' := h.lay W hp
  exact ⟨h.top.step L' hP kgM_bases hc.1.1, by rw [L'.keepBytes hP hc.1.2]; exact h.d,
    by rw [L'.keepBytes hP hc.2]; exact h.z⟩

end

theorem pro_eq : pro = [.store (at_ .rcx 840) .rbx, .store (at_ .rcx 848) .rbp, .store (at_ .rcx 856) .r12,
    .store (at_ .rcx 864) .r13, .store (at_ .rcx 872) .r14, .store (at_ .rcx 880) .r15, .mov .rbx (.reg .rcx),
    .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) :
    WP isa (.block pro) σ fun s => KC σ s ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp'
  have hsc := W.scr
  have hS : ⟨σ.gpr .rcx, L.scr⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ L.scr → (⟨σ.gpr .rcx, L.scr⟩ : Region).Contains (σ.gpr .rcx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega)
  have w : ∀ o, o + 8 ≤ L.scr → InRegions σ.wr (σ.gpr .rcx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
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
  have hf : Frame [⟨σ.gpr .rcx, L.scr⟩] σ.mem s.mem := by
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

end KeyGen

/-- Proves the checks of a parameter set's layout (`KemWf`, `KeyGen.KgWf`, …),
each field evaluated by the kernel: the taint checks with `taint_decide`, the
others with `decide +kernel`; `kem_wf w` takes the checks of `KemWf` from `w`. -/
syntax "kem_wf" (ppSpace term)? : tactic
macro_rules
  | `(tactic| kem_wf) =>
    `(tactic| constructor <;> first | exact ⟨_, by taint_decide⟩ | taint_decide | decide +kernel)
  | `(tactic| kem_wf $w) =>
    `(tactic| constructor <;> first | exact $w | exact ⟨_, by taint_decide⟩ | taint_decide | decide +kernel)

end VG.Proof.MlKem.X86_64
