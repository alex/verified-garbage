import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
import VerifiedGarbage.Impl.MlKem.X86_64.Encaps

/-!
# ML-KEM on x86-64: encapsulation, its contract, layout, entry and hashes

For a parameter set `L`: the contract the proof is written against
(`encapsK L`, which the shared contract implies), the layout of the
function's buffers (`ek` and `m` in `r14` and `rbp`, which may overlap each
other; `scratch`, `key`, `ct` in `rbx`, `r12`, `r13`), what holds throughout
(`EC`: `Top`, and `ek` and `m` at their pointers), the checks of the layout
every piece needs (`EcWf L`), the prologue, `H(ek)` and `G(m ‖ H(ek))`
(`hashes_ok`), and the context `K-PKE.Encrypt` runs in (`ecC`, which also
keeps `K`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `kemEncaps L (ek = rdi, m = rsi, key = rdx, ct = rcx, scratch = r8) -> eax`, with 32 bytes of stack. -/
def encapsK (L : Kem) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, L.ekLen⟩, ⟨s.gpr .rsi, 32⟩] ∧
    s.wr = [⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, L.ctLen⟩, ⟨s.gpr .r8, L.scr⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ⟨s.gpr .rdx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ⟨s.gpr .rcx, L.ctLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ⟨s.gpr .r8, L.scr⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rdx, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rcx, L.ctLen⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .r8, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, L.ctLen⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r8, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, L.ctLen⟩ ⟨s.gpr .r8, L.scr⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 32⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, L.ctLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, L.scr⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, 32⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, L.ctLen⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .r8, L.scr⟩ ∧
    (s.gpr .rdi).toNat + L.ekLen ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + L.ctLen ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + L.scr ≤ 2 ^ 64
  post s s' :=
    Outcome (fun iters => encapsInternal L.p iters (bytesAt s.mem (s.gpr .rdi) L.ekLen)
      (bytesAt s.mem (s.gpr .rsi) 32)) ((s'.gpr .rax).setWidth 32)
      (bytesAt s'.mem (s.gpr .rdx) 32, bytesAt s'.mem (s.gpr .rcx) L.ctLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    ekRho L.p (bytesAt s₁.mem (s₁.gpr .rdi) L.ekLen) = ekRho L.p (bytesAt s₂.mem (s₂.gpr .rdi) L.ekLen)

namespace Encaps

open VG.Impl.MlKem.X86_64.Encaps

variable (L : Kem)

/-- The pointers the function keeps. -/
abbrev ecM : List (Reg × Reg) := [(.rbx, .r8), (.rbp, .rsi), (.r12, .rdx), (.r13, .rcx), (.r14, .rdi)]
/-- `ek` and `m`. -/
abbrev ecR : List (Reg × Nat) := [(.r14, L.ekLen), (.rbp, 32)]
/-- `scratch`, `key` and `ct`. -/
abbrev ecW : List (Reg × Nat) := [(.rbx, L.scr), (.r12, 32), (.r13, L.ctLen)]
abbrev ecB : List (Reg × Nat) := ecR L ++ ecW L

theorem ecB_bases : ∀ b ∈ ecB L, b.1 ∈ bases := by
  intro b hb; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [bases]

theorem ecM_bases : ∀ p ∈ ecM, p.1 ∈ bases := by decide

/-- A piece that writes `ws` keeps `EC`. -/
def ecChk (ws : List (Ptr × Nat)) : Bool :=
  topChk (ecB L) ws && keepB (ecB L) ws (.r14, 0) L.ekLen && keepB (ecB L) ws (.rbp, 0) 32

def eckChk (ws : List (Ptr × Nat)) : Bool := ecChk L ws && keepB (ecB L) ws (sc oG) 32

/-- The writes of the hashes and of the outputs. -/
abbrev hW₂ : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), (sc oH, 32)]
abbrev hW₃ : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), (sc oG, 64)]

/-- What every piece of encapsulation needs of the layout, evaluated for each parameter set. -/
structure EcWf : Prop extends KemWf L where
  scr : 888 ≤ L.scr ∧ L.scr < 2 ^ 32
  small : ∀ b ∈ ecB L, b.2 < 2 ^ 32
  -- the hashes
  h₁ : copyChk (ecB L) (ecW L) (sc oM) (.rbp, 0) 32 = true
  h₁K : ecChk L [(sc oM, 32)] = true
  h₂ : hashChk (ecB L) (ecW L) [((.r14, 0), L.ekLen)] 136 (sc oH) 32 = true
  h₂K : ecChk L (hW₂) = true
  h₂M : keepB (ecB L) (hW₂) (sc oM) 32 = true
  h₃ : hashChk (ecB L) (ecW L) [(sc oM, 32), (sc oH, 32)] 72 (sc oG) 64 = true
  h₃K : ecChk L (hW₃) = true
  h₃M : keepB (ecB L) (hW₃) (sc oM) 32 = true
  enc : Enc.encChk L (ecB L) (ecW L) (eckChk L) (.r14, 0) = true
  -- the outputs
  o₁ : copyChk (ecB L) (ecW L) (.r12, 0) (sc oG) 32 = true
  o₁K : ecChk L [((.r12, 0), 32)] = true
  o₁C : keepB (ecB L) [((.r12, 0), 32)] (sc L.oCT) L.ctLen = true
  o₂ : copyChk (ecB L) (ecW L) (.r13, 0) (sc L.oCT) L.ctLen = true
  o₂K : ecChk L [((.r13, 0), L.ctLen)] = true
  o₂G : keepB (ecB L) [((.r13, 0), L.ctLen)] (.r12, 0) 32 = true
  sv : ∀ k < 6, inB (ecB L) (sc (oSV + 8 * k)) 8 = true
  -- constant time
  inBs : inB (ecB L) (sc 0) 1 = true ∧ inB (ecB L) (.r12, 0) 1 = true ∧ inB (ecB L) (.r13, 0) 1 = true ∧
    inB (ecB L) (.r14, 0) 1 = true
  hT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (copy (sc oM) (.rbp, 0) 32)
    h).isSome = true
  oT₁ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (copy (.r12, 0) (sc oG) 32)
    h).isSome = true
  oT₂ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (copy (.r13, 0) (sc L.oCT) L.ctLen)
    h).isSome = true
  rhoT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .r14]) (copy (sc oSB) (.r14, 0 + 384 * L.k) 32)
    h).isSome = true

section
variable {L : Kem} (W : EcWf L) {σ : State} (hp : (encapsK L).pre σ)
include W hp

theorem ecLay {s : State} (h : Top ecM σ s) : Lay (ecR L) (ecW L) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5⟩ :=
    hp
  have e1 : s.gpr .rbx = σ.gpr .r8 := h.regs (.rbx, .r8) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rsi := h.regs (.rbp, .rsi) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rdx := h.regs (.r12, .rdx) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .rcx := h.regs (.r13, .rcx) (by decide)
  have e5 : s.gpr .r14 = σ.gpr .rdi := h.regs (.r14, .rdi) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of W.small (pw5 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_)
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
    mem ⟨σ.gpr .rdi, L.ekLen⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rsi, 32⟩ (by rw [hrd]; simp),
    mem ⟨σ.gpr .r8, L.scr⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, 32⟩ (by rw [hwr]; simp),
    mem ⟨σ.gpr .rcx, L.ctLen⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, r1, r2, r5, r3, r4]

end

/-- `ek`, `m`, and `G(m ‖ H(ek))`. -/
abbrev ecEk (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) L.ekLen
abbrev ecMs (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rsi) 32
abbrev ecG (L : Kem) (σ : State) : List Byte × List Byte := G (ecMs σ ++ H (ecEk L σ))

/-- What holds throughout. -/
structure EC (L : Kem) (σ s : State) : Prop where
  top : Top ecM σ s
  ek : bytesAt s.mem (pa s (.r14, 0)) L.ekLen = ecEk L σ
  m : bytesAt s.mem (pa s (.rbp, 0)) 32 = ecMs σ

section
variable {L : Kem} (W : EcWf L) {σ : State} (hp : (encapsK L).pre σ)
include W hp

theorem EC.lay {s : State} (h : EC L σ s) : Lay (ecR L) (ecW L) s := ecLay W hp h.top

theorem EC.step {s s' : State} (h : EC L σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hc : ecChk L ws = true) : EC L σ s' := by
  simp only [ecChk, Bool.and_eq_true] at hc
  have L₀ := h.lay W hp
  exact ⟨h.top.step L₀ hP ecM_bases hc.1.1, by rw [L₀.keepBytes hP hc.1.2]; exact h.ek,
    by rw [L₀.keepBytes hP hc.2]; exact h.m⟩

end

/-- What `K-PKE.Encrypt` keeps: `EC`, and `K` at `G`. -/
structure ECK (L : Kem) (σ s : State) : Prop where
  ec : EC L σ s
  k : bytesAt s.mem (pa s (sc oG)) 32 = (ecG L σ).1

theorem ECK.step {L : Kem} (W : EcWf L) {σ : State} (hp : (encapsK L).pre σ) {s s' : State} (h : ECK L σ s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : eckChk L ws = true) : ECK L σ s' := by
  simp only [eckChk, Bool.and_eq_true] at hc
  exact ⟨h.ec.step W hp hP hc.1, by rw [(h.ec.lay W hp).keepBytes hP hc.2]; exact h.k⟩

/-- The context of `K-PKE.Encrypt` in a run from `σ`. -/
def ecC {L : Kem} (W : EcWf L) (σ : State) : Ctx (ecR L) (ecW L) where
  Out s := (encapsK L).pre σ ∧ ECK L σ s
  chk := eckChk L
  bs := ecB_bases L
  lay h := h.2.ec.lay W h.1
  step h hP hc := ⟨h.1, h.2.step W h.1 hP hc⟩

/-- The context of `K-PKE.Encrypt` in any run. -/
def ecCA {L : Kem} (W : EcWf L) : Ctx (ecR L) (ecW L) where
  Out s := ∃ σ, (encapsK L).pre σ ∧ ECK L σ s
  chk := eckChk L
  bs := ecB_bases L
  lay := fun ⟨_, hp, h⟩ => h.ec.lay W hp
  step := fun ⟨σ, hp, h⟩ hP hc => ⟨σ, hp, h.step W hp hP hc⟩

theorem pro_eq : pro = [.store (at_ .r8 840) .rbx, .store (at_ .r8 848) .rbp, .store (at_ .r8 856) .r12,
    .store (at_ .r8 864) .r13, .store (at_ .r8 872) .r14, .store (at_ .r8 880) .r15, .mov .rbx (.reg .r8),
    .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .rcx), .mov .r14 (.reg .rdi),
    .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {L : Kem} (W : EcWf L) {σ : State} (hp : (encapsK L).pre σ) :
    WP isa (.block pro) σ fun s => EC L σ s ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, n1, n2, n3, n4,
    n5⟩ := hp'
  have hsc := W.scr
  have hS : ⟨σ.gpr .r8, L.scr⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ L.scr → (⟨σ.gpr .r8, L.scr⟩ : Region).Contains (σ.gpr .r8 + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega)
  have w : ∀ o, o + 8 ≤ L.scr → InRegions σ.wr (σ.gpr .r8 + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .r8 + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .r8 + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .r8 + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .r8 ∧ s.gpr .rbp = σ.gpr .rsi ∧ s.gpr .r12 = σ.gpr .rdx ∧ s.gpr .r13 = σ.gpr .rcx ∧
    s.gpr .r14 = σ.gpr .rdi ∧ s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h13, h14, h15⟩, k⟩ => ⟨?_, h15⟩
  have hf : Frame [⟨σ.gpr .r8, L.scr⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  have hek := W.small (.r14, L.ekLen) (by simp)
  refine ⟨⟨k.2.1, k.2.2, hsp, fa5 hbx hbp h12 h13 h14, fun j hj => ?_, ?_⟩, ?_, ?_⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .r8) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r5) (by decide)
  · rw [pa, h14, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d3) (by simp only at hek; omega)
  · rw [pa, hbp, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d6) (by decide)

/-! ## `H(ek)` and `G(m ‖ H(ek))` -/

/-- The inputs of `K-PKE.Encrypt`, and `r15 = 1`. -/
abbrev EncI {L : Kem} (W : EcWf L) (σ s : State) : Prop :=
  Enc.EIn L (ecC W σ) (.r14, 0) (ecEk L σ) (ecMs σ) (ecG L σ).2 s ∧ s.gpr .r15 = 1

theorem hashes_ok {L : Kem} (W : EcWf L) {σ : State} (hp : (encapsK L).pre σ) {s : State} (h : EC L σ s)
    (h15 : s.gpr .r15 = 1) : WP isa (hashes L) s (EncI W σ) := by
  have L₀ := h.lay W hp
  unfold hashes
  -- `m` to `M`.
  refine WP.seq (WP.mono (copy_okL L₀ (dst := sc oM) (src := (.rbp, 0)) (n := 32) (by decide) W.h₁)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.step W hp hP₁.b W.h₁K
  have L₁ := k₁.lay W hp
  rw [h.m] at hb₁
  -- `H(ek)`.
  refine WP.seq (WP.mono (hash_ok (ecB_bases L) (ps := [((.r14, 0), L.ekLen)]) (rate := 136) (out := sc oH) (len := 32)
    W.h₂ (show 6 < 256 by decide) L₁) fun s₂ ⟨hP₂, hb₂⟩ => ?_)
  have k₂ := k₁.step W hp hP₂.b W.h₂K
  have L₂ := k₂.lay W hp
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, k₁.ek, KeyGen.sha3Suffix6] at hb₂
  rw [← H_eq, ← hP₂.pa rbx_cs] at hb₂
  have hM₂ : bytesAt s₂.mem (pa s₂ (sc oM)) 32 = ecMs σ := by
    rw [L₁.keepBytes hP₂.b W.h₂M, hP₁.pa rbx_cs, hb₁]
  -- `G(m ‖ H(ek))`.
  refine WP.mono (hash_ok (ecB_bases L) (ps := [(sc oM, 32), (sc oH, 32)]) (rate := 72) (out := sc oG) (len := 64)
    W.h₃ (show 6 < 256 by decide) L₂) fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have k₃ := k₂.step W hp hP₃.b W.h₃K
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hM₂, hb₂, KeyGen.sha3Suffix6] at hb₃
  rw [← sha3_512_eq, ← hP₃.pa rbx_cs] at hb₃
  have hK : bytesAt s₃.mem (pa s₃ (sc oG)) 32 = (ecG L σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hb₃]; rfl
  have hr : bytesAt s₃.mem (pa s₃ sigP) 32 = (ecG L σ).2 := by
    have e := bytesAt_drop s₃.mem (pa s₃ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₃.mem (pa s₃ (sc oG)) 64).drop 32 = bytesAt s₃.mem (pa s₃ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hb₃]; rfl
  refine ⟨⟨⟨hp, k₃, hK⟩, k₃.ek, ?_, hr⟩, ?_⟩
  · rw [L₂.keepBytes hP₃.b W.h₃M]; exact hM₂
  · rw [hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h15]

end Encaps

end VG.Proof.MlKem.X86_64
