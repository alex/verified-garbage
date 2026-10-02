import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Hash
import VerifiedGarbage.Proof.MlDsa.Sign.Setup

/-!
# ML-DSA signing on x86-64: the function's contract, layout, entry and exit

The contract the proof is written against (`signK`, which the shared contract
implies), the layout of the function's buffers (`sk`, `mu`, `rnd` read, in
`rbp`, `r12`, `r13`; `scratch` and `sig` written, in `rbx` and `r14`), what
holds of the state throughout (`Top`: the permissions and the stack pointer of
entry, the pointers in their registers, the caller's callee-saved registers
saved in `scratch`, and the return address), the saves (`pro_ok`), the return
(`topEpi_ok`), branches on `r15` (`ifOkElse_ok`, `ifOkElse_tr`) and sequences
of pieces indexed by a number (`seqR_ok`, `seqR_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The contract -/

/-- The size of `scratch` in bytes. -/
abbrev scrLen (p : Params) : Nat := 8 * scratchWords p

/-- `vg_mldsa*_sign(sk = rdi, mu = rsi, rnd = rdx, sig = rcx, scratch = r8) -> eax`, with `D` bytes
of stack, and the leakage `signLeakT`. -/
def signK (p : Params) (D : Nat) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, p.skLen⟩, ⟨s.gpr .rsi, 64⟩, ⟨s.gpr .rdx, 32⟩] ∧
    s.wr = [⟨s.gpr .rcx, p.sigLen⟩, ⟨s.gpr .r8, scrLen p⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, p.skLen⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, p.skLen⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 64⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 64⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, p.skLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 64⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, scrLen p⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rdi, p.skLen⟩ ∧ (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rsi, 64⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .r8, scrLen p⟩ ∧
    (s.gpr .rdi).toNat + p.skLen ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + p.sigLen ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + scrLen p ≤ 2 ^ 64 ∧
    D ≤ (s.gpr .rsp).toNat
  post s s' :=
    Outcome (fun b => signMu p b (bytesAt s.mem (s.gpr .rdi) p.skLen) (bytesAt s.mem (s.gpr .rsi) 64)
      (bytesAt s.mem (s.gpr .rdx) 32)) ((s'.gpr .rax).setWidth 32) (bytesAt s'.mem (s.gpr .rcx) p.sigLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    signLeakT p (bytesAt s₁.mem (s₁.gpr .rdi) p.skLen) (bytesAt s₁.mem (s₁.gpr .rsi) 64)
        (bytesAt s₁.mem (s₁.gpr .rdx) 32) =
      signLeakT p (bytesAt s₂.mem (s₂.gpr .rdi) p.skLen) (bytesAt s₂.mem (s₂.gpr .rsi) 64)
        (bytesAt s₂.mem (s₂.gpr .rdx) 32)

/-! ## The layout -/

/-- `sk`, `mu` and `rnd`. -/
abbrev sgR (p : Params) : List (Reg × Nat) := [(.rbp, p.skLen), (.r12, 64), (.r13, 32)]
/-- `scratch` and `sig`. -/
abbrev sgW (p : Params) : List (Reg × Nat) := [(.rbx, scrLen p), (.r14, p.sigLen)]
abbrev sgB (p : Params) : List (Reg × Nat) := sgR p ++ sgW p

/-- The pointers the function keeps, and the registers they arrive in. -/
abbrev sgM : List (Reg × Reg) := [(.rbx, .r8), (.rbp, .rdi), (.r12, .rsi), (.r13, .rdx), (.r14, .rcx)]

theorem sgB_bases (p : Params) : ∀ b ∈ sgB p, b.1 ∈ bases := by
  intro b hb; simp only [sgB, sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
theorem sgM_bases : ∀ m ∈ sgM, m.1 ∈ bases := by decide

/-- The register saved at `scratch + 840 + 8k`. -/
abbrev savedReg (k : Nat) : Reg := savedRegs.getD k .rbx

/-- What holds throughout the function entered in `σ`. -/
structure Top (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rsp : s.gpr .rsp = σ.gpr .rsp
  regs : ∀ m ∈ sgM, s.gpr m.1 = σ.gpr m.2
  saved : ∀ k < 6, s.mem.readW (pa s (sc (oSV + 8 * k))) 64 = σ.gpr (savedReg k)
  ret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64

theorem pairwise_sym {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with e | ha'
    · rcases List.mem_cons.mp hb with e' | hb'
      · exact absurd (e.trans e'.symm) hne
      · rw [e]; exact h.1 _ hb'
    · rcases List.mem_cons.mp hb with e' | hb'
      · rw [e']; exact hs _ _ (h.1 _ ha')
      · exact pairwise_sym hs h.2 ha' hb' hne

section
variable {p : Params} {D : Nat} {σ : State} (hp : (signK p D).pre σ)
include hp

theorem sgLay (hD : D < 2 ^ 32) (hsz : scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32) {s : State}
    (h : Top σ s) : Lay D (sgR p) (sgW p) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .r8 := h.regs (.rbx, .r8) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rsi := h.regs (.r12, .rsi) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .rdx := h.regs (.r13, .rdx) (by decide)
  have e5 : s.gpr .r14 = σ.gpr .rcx := h.regs (.r14, .rcx) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  have memw : ∀ r ∈ σ.wr, InRegions s.wr r.base r.len := fun r hr =>
    ⟨r, by rw [h.wr]; exact hr, Region.contains_self _ _⟩
  refine ⟨?_, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_, by rw [h.rsp]; exact hsp, hD⟩
  · intro b hb
    simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb hb'
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl <;>
      simp only [wRegs, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, or_self, ne_eq,
        not_true_eq_false] at hne hw ⊢ <;> simp only [e1, e2, e3, e4, e5]
    all_goals first
      | exact d1 | exact d2 | exact d3 | exact d4 | exact d5 | exact d6 | exact d7
      | exact d1.symm | exact d2.symm | exact d3.symm | exact d4.symm | exact d5.symm | exact d6.symm | exact d7.symm
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5, h.rsp]
    exacts [k1, k2, k3, k5, k4]
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5]
    exacts [n1, n2, n3, n5, n4]
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5]
    exacts [mem ⟨σ.gpr .rdi, p.skLen⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rsi, 64⟩ (by rw [hrd]; simp),
      mem ⟨σ.gpr .rdx, 32⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .r8, scrLen p⟩ (by rw [hwr]; simp),
      mem ⟨σ.gpr .rcx, p.sigLen⟩ (by rw [hwr]; simp)]
  · simp only [sgW, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp only [e1, e5]
    exacts [memw ⟨σ.gpr .r8, scrLen p⟩ (by rw [hwr]; simp), memw ⟨σ.gpr .rcx, p.sigLen⟩ (by rw [hwr]; simp)]
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [retR, e1, e2, e3, e4, e5, h.rsp]
    exacts [r1, r2, r3, r5, r4]

end

/-- The saved registers and the return address are apart from the regions `ws`. -/
def topChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) : Bool :=
  (List.range 6).all (fun k => keepB bs ws (sc (oSV + 8 * k)) 8) && ws.all fun w => inB bs w.1 w.2

theorem Top.step {D : Nat} {σ s s' : State} {rbs wbs : List (Reg × Nat)} (h : Top σ s)
    (L : Lay D rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws)
    (hc : topChk (rbs ++ wbs) ws = true) : Top σ s' := by
  simp only [topChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.rsp.trans h.rsp,
    fun m hm => (hP.bs _ (sgM_bases m hm)).trans (h.regs m hm), fun k hk => ?_, ?_⟩
  · rw [L.keepW hP (hc.1 k hk)]; exact h.saved k hk
  · have := L.keepRet hP hc.2
    rw [h.rsp] at this
    rw [this, h.ret]

/-! ## Saving the registers -/

theorem readW_writeW_slot (m : Mem) (a : Addr) {x y : Nat} (v : BitVec 64) (hxy : x + 8 ≤ y ∨ y + 8 ≤ x)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (m.writeW (a + BitVec.ofNat 64 y) v).readW (a + BitVec.ofNat 64 x) 64 = m.readW (a + BitVec.ofNat 64 x) 64 := by
  refine Mem.readW_writeW_sep ?_ (by decide)
  rcases hxy with h | h
  · exact (off_disj (base := a) h (by omega)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  · exact (off_disj (base := a) h (by omega)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- The six stores of `topPro`: each slot holds its register. -/
theorem stores_read (m : Mem) (a : Addr) (v : Nat → BitVec 64) : ∀ k < 6,
    ((((((m.writeW (a + BitVec.ofNat 64 840) (v 0)).writeW (a + BitVec.ofNat 64 848) (v 1)).writeW
      (a + BitVec.ofNat 64 856) (v 2)).writeW (a + BitVec.ofNat 64 864) (v 3)).writeW (a + BitVec.ofNat 64 872)
      (v 4)).writeW (a + BitVec.ofNat 64 880) (v 5)).readW (a + BitVec.ofNat 64 (oSV + 8 * k)) 64 = v k := by
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := omega) only [oSV, Nat.reduceMul, Nat.reduceAdd, readW_writeW_slot, Mem.readW_writeW_self64]

theorem pro_eq : pro = [.store (VG.Impl.MlKem.X86_64.at_ .r8 840) .rbx, .store (VG.Impl.MlKem.X86_64.at_ .r8 848) .rbp,
    .store (VG.Impl.MlKem.X86_64.at_ .r8 856) .r12, .store (VG.Impl.MlKem.X86_64.at_ .r8 864) .r13,
    .store (VG.Impl.MlKem.X86_64.at_ .r8 872) .r14, .store (VG.Impl.MlKem.X86_64.at_ .r8 880) .r15, .mov .rbx (.reg .r8),
    .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov .r14 (.reg .rcx),
    .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {p : Params} {D : Nat} {σ : State} (hp : (signK p D).pre σ) (hsz : scrLen p < 2 ^ 32) :
    WP isa (.block pro) σ fun s => Top σ s ∧ s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64 ∧
      Frame [⟨σ.gpr .r8, scrLen p⟩] σ.mem s.mem ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨_, hwr, _, _, _, _, _, _, _, _, _, _, _, r5, _, _, _, _, _, _, _, _, _, _, _⟩ := hp'
  have hS : ⟨σ.gpr .r8, scrLen p⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ 888 → (⟨σ.gpr .r8, scrLen p⟩ : Region).Contains (σ.gpr .r8 + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' (by have : 888 ≤ scrLen p := by unfold scrLen scratchWords; omega
                                     omega) (by omega)
  have w : ∀ o, o + 8 ≤ 888 → InRegions σ.wr (σ.gpr .r8 + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .r8 + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .r8 + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .r8 + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .r8 ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r12 = σ.gpr .rsi ∧ s.gpr .r13 = σ.gpr .rdx ∧
    s.gpr .r14 = σ.gpr .rcx ∧ s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h13, h14, h15⟩, k⟩ => ?_
  have hf : Frame [⟨σ.gpr .r8, scrLen p⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64 :=
    hf.readW (Region.contains_self _ _) (by simpa using r5) (by decide)
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨k.2.1, k.2.2, hsp, fun m hm => ?_, fun j hj => ?_, hret⟩, hret, hf, h15⟩
  · simp only [sgM, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, h12, h13, h14]
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .r8) (fun j => σ.gpr (savedReg j)) j hj

/-! ## The return -/

theorem topEpi_eq : topEpi = [.mov32 .rax (.reg .r15), .mov .r15 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 880)),
    .mov .r14 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 872)), .mov .r13 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 864)),
    .mov .r12 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 856)), .mov .rbp (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 848)),
    .mov .rbx (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 840))] := rfl

theorem topEpi_ok {σ s : State} (h : Top σ s)
    (hin : ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8) :
    WP isa (.block topEpi) s fun s' => (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32 ∧
      gprPreserved σ s' ∧ s'.mem = s.mem := by
  have e : ∀ k < 6, s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (840 + 8 * k)) 64 = σ.gpr (savedReg k) :=
    fun k hk => h.saved k hk
  have i : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (840 + 8 * k)) 8 := hin
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide); have e4 := e 4 (by decide); have e5 := e 5 (by decide)
  have i0 := i 0 (by decide); have i1 := i 1 (by decide); have i2 := i 2 (by decide)
  have i3 := i 3 (by decide); have i4 := i 4 (by decide); have i5 := i 5 (by decide)
  rw [show savedReg 0 = .rbx from rfl] at e0; rw [show savedReg 1 = .rbp from rfl] at e1
  rw [show savedReg 2 = .r12 from rfl] at e2; rw [show savedReg 3 = .r13 from rfl] at e3
  rw [show savedReg 4 = .r14 from rfl] at e4; rw [show savedReg 5 = .r15 from rfl] at e5
  simp only [Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 i0 i1 i2 i3 i4 i5
  rw [topEpi_eq]
  refine WP.mono (WP.keep [.rax, .r15, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' =>
    s'.gpr .rax = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32) ∧ s'.gpr .r15 = σ.gpr .r15 ∧
    s'.gpr .r14 = σ.gpr .r14 ∧ s'.gpr .r13 = σ.gpr .r13 ∧ s'.gpr .r12 = σ.gpr .r12 ∧ s'.gpr .rbp = σ.gpr .rbp ∧
    s'.gpr .rbx = σ.gpr .rbx ∧ s'.mem = s.mem) (by xrun [i0, i1, i2, i3, i4, i5, e0, e1, e2, e3, e4, e5]) (by decide))
    fun s' ⟨⟨hax, h15, h14, h13, h12, hbp, hbx, hm⟩, k⟩ => ⟨?_, ⟨fun r hr => ?_, ?_⟩, hm⟩
  · rw [hax]; apply BitVec.eq_of_toNat_eq; simp
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, by rw [k.gpr (by decide), h.rsp], h12, h13, h14, h15]
  · rw [hm]; exact h.ret

/-! ## Branches on `r15` -/

/-- A block that writes only `r15`'s flags keeps `PostB`. -/
theorem test15_ok (s : State) (D : Nat) :
    WP isa (.block [.alu32 .test .r15 (.reg .r15)]) s fun s₁ => PPostB D s s₁ [] ∧
      (∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.zf = some ((s.gpr .r15).setWidth 32 == 0) := by
  refine WP.mono (WP.keep [.r15] (Q := fun s₁ => s₁.mem = s.mem ∧ s₁.gpr .r15 = s.gpr .r15 ∧
      s₁.zf = some (((s.gpr .r15).setWidth 32 &&& (s.gpr .r15).setWidth 32) == 0)) (by xrun) (by decide))
    fun s₁ ⟨⟨hm, h15, hz⟩, k⟩ => ⟨⟨k.2.1, k.2.2, fun r hr => k.gpr (by
        simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), k.gpr (by decide),
        by rw [hm]; exact Frame.refl _ _⟩,
      fun r hr => by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | exact h15 | exact k.gpr (by decide), hm, by rw [hz, BitVec.and_self]⟩

theorem ifOkElse_ok {D : Nat} {t e : Prog isa} {s : State} {Q : State → Prop}
    (ht : ∀ s₁, PPostB D s s₁ [] → (∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) → s₁.mem = s.mem →
      (s.gpr .r15).setWidth 32 ≠ 0 → WP isa t s₁ Q)
    (he : ∀ s₁, PPostB D s s₁ [] → (∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) → s₁.mem = s.mem →
      (s.gpr .r15).setWidth 32 = 0 → WP isa e s₁ Q) : WP isa (ifOkElse t e) s Q := by
  unfold ifOkElse
  refine WP.seq (WP.mono (test15_ok s D) fun s₁ ⟨hP, hcs, hm, hz⟩ => ?_)
  refine WP.ite (M := isa) (!((s.gpr .r15).setWidth 32 == 0))
    (show s₁.zf.map (!·) = _ by rw [hz]; rfl) (fun hb => ?_) fun hb => ?_
  · exact ht s₁ hP hcs hm (by simpa using hb)
  · exact he s₁ hP hcs hm (by simpa using hb)

theorem ifOkElse_tr {D : Nat} {t e : Prog isa} {P Q : State → State → Prop}
    (hq : ∀ x y, P x y → (x.gpr .r15).setWidth 32 = (y.gpr .r15).setWidth 32)
    (ht : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ (PPostB D x₀ x [] ∧ (∀ r ∈ calleeSaved, x.gpr r = x₀.gpr r) ∧
      x.mem = x₀.mem) ∧ (PPostB D y₀ y [] ∧ (∀ r ∈ calleeSaved, y.gpr r = y₀.gpr r) ∧ y.mem = y₀.mem) ∧
      (x₀.gpr .r15).setWidth 32 ≠ 0) t Q)
    (he : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ (PPostB D x₀ x [] ∧ (∀ r ∈ calleeSaved, x.gpr r = x₀.gpr r) ∧
      x.mem = x₀.mem) ∧ (PPostB D y₀ y [] ∧ (∀ r ∈ calleeSaved, y.gpr r = y₀.gpr r) ∧ y.mem = y₀.mem) ∧
      (x₀.gpr .r15).setWidth 32 = 0) e Q) :
    RelCT isa P (ifOkElse t e) Q := by
  unfold ifOkElse
  refine RelCT.seq (VG.Proof.MlKem.X86_64.RelCT.postDep (block_nomem_tr fun i hi s => by
      simp only [List.mem_singleton] at hi; subst hi; rfl)
    (F := fun x x₁ => (PPostB D x x₁ [] ∧ (∀ r ∈ calleeSaved, x₁.gpr r = x.gpr r) ∧ x₁.mem = x.mem) ∧
      x₁.zf = some ((x.gpr .r15).setWidth 32 == 0))
    (fun x y _ => ⟨WP.mono (test15_ok x D) fun _ h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩,
      WP.mono (test15_ok y D) fun _ h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩)
    (Q := fun x₁ y₁ => ∃ x₀ y₀, P x₀ y₀ ∧
      ((PPostB D x₀ x₁ [] ∧ (∀ r ∈ calleeSaved, x₁.gpr r = x₀.gpr r) ∧ x₁.mem = x₀.mem) ∧
        x₁.zf = some ((x₀.gpr .r15).setWidth 32 == 0)) ∧
      ((PPostB D y₀ y₁ [] ∧ (∀ r ∈ calleeSaved, y₁.gpr r = y₀.gpr r) ∧ y₁.mem = y₀.mem) ∧
        y₁.zf = some ((y₀.gpr .r15).setWidth 32 == 0)))
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.ite ?_ ?_ ?_)
  · rintro x₁ y₁ ⟨x₀, y₀, hp, ⟨_, hx⟩, ⟨_, hy⟩⟩
    show x₁.zf.map (!·) = y₁.zf.map (!·)
    rw [hx, hy, hq x₀ y₀ hp]
  · refine RelCT.mono ht (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun _ _ h => h
    have hc' : x₁.zf.map (!·) = some true := hc
    rw [hx] at hc'
    simpa using hc'
  · refine RelCT.mono he (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun _ _ h => h
    have hc' : x₁.zf.map (!·) = some false := hc
    rw [hx] at hc'
    simpa using hc'

/-! ## Sequences -/

theorem seqR_ok {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [seqR]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega) s hs) fun s₁ h₁ => ?_)
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact seqR_ok n (a + 1) (fun k hk hk' => h k (by omega) (by omega)) s₁ h₁

theorem seqR_tr {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (seqR f a n) (R (a + n))
  | 0, _, _ => nil_tr
  | n + 1, a, h => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega)) (seqR_tr n (a + 1) fun k hk hk' => h k (by omega) (by omega))

end VG.Proof.MlDsa.X86_64.Sign
