import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Flag
import VerifiedGarbage.Proof.MlDsa.Verify.Norm
import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA verification on x86-64: the contract, the layout and the invariant

Untrusted: everything here is checked by Lean. The precondition of the
shared contract `verifyContract p X86_64.abi 32`, spelled out (`VPre`); the
layout of the function's buffers (`pk`, `mu`, `sig` read in `rbp`, `r12`,
`r13`; `scratch` written, in `rbx`: `vR p`, `vW p`); what holds throughout
(`T`: the permissions and stack pointer of entry, the pointers, the caller's
callee-saved registers saved in `scratch`, the return address and the
inputs); the prologue and the epilogue.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlKem.X86_64 (at_)
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The parameter sets. -/
def params : List Params := [mlDsa44, mlDsa65, mlDsa87]

/-- The size of `scratch` in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

/-- The precondition of `verifyContract p X86_64.abi 32`. -/
structure VPre (p : Params) (σ : State) : Prop where
  sp : 32 ≤ (σ.gpr .rsp).toNat
  rd : σ.rd = [⟨σ.gpr .rdi, p.pkLen⟩, ⟨σ.gpr .rsi, 64⟩, ⟨σ.gpr .rdx, p.sigLen⟩]
  wr : σ.wr = [⟨σ.gpr .rcx, scrLen p⟩]
  d1 : Region.Disjoint ⟨σ.gpr .rdi, p.pkLen⟩ ⟨σ.gpr .rcx, scrLen p⟩
  d2 : Region.Disjoint ⟨σ.gpr .rsi, 64⟩ ⟨σ.gpr .rcx, scrLen p⟩
  d3 : Region.Disjoint ⟨σ.gpr .rdx, p.sigLen⟩ ⟨σ.gpr .rcx, scrLen p⟩
  r1 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rdi, p.pkLen⟩
  r2 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rsi, 64⟩
  r3 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rdx, p.sigLen⟩
  r4 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rcx, scrLen p⟩
  k1 : (below (σ.gpr .rsp) 32).Disjoint ⟨σ.gpr .rdi, p.pkLen⟩
  k2 : (below (σ.gpr .rsp) 32).Disjoint ⟨σ.gpr .rsi, 64⟩
  k3 : (below (σ.gpr .rsp) 32).Disjoint ⟨σ.gpr .rdx, p.sigLen⟩
  k4 : (below (σ.gpr .rsp) 32).Disjoint ⟨σ.gpr .rcx, scrLen p⟩
  n1 : (σ.gpr .rdi).toNat + p.pkLen ≤ 2 ^ 64
  n2 : (σ.gpr .rsi).toNat + 64 ≤ 2 ^ 64
  n3 : (σ.gpr .rdx).toNat + p.sigLen ≤ 2 ^ 64
  n4 : (σ.gpr .rcx).toNat + scrLen p ≤ 2 ^ 64

/-- The inputs of a run from `σ`. -/
abbrev vPk (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) p.pkLen
abbrev vMu (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rsi) 64
abbrev vSig (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdx) p.sigLen

/-- The contract the proof is written against. -/
def verifyK (p : Params) : Contract isa where
  pre := VPre p
  post σ s := let v := fun b => verifyMu p b (vPk p σ) (vMu σ) (vSig p σ)
    (res s = 1 ∧ ∃ b, v b = some true) ∨ (res s = 0 ∧ v minBounds ≠ some true)
  pub σ₁ σ₂ := σ₁.gpr .rdi = σ₂.gpr .rdi ∧ σ₁.gpr .rsi = σ₂.gpr .rsi ∧ σ₁.gpr .rdx = σ₂.gpr .rdx ∧
    σ₁.gpr .rcx = σ₂.gpr .rcx ∧ σ₁.gpr .rsp = σ₂.gpr .rsp ∧ vPk p σ₁ = vPk p σ₂ ∧ vMu σ₁ = vMu σ₂ ∧
    vSig p σ₁ = vSig p σ₂

/-! ## The layout -/

/-- `pk`, `mu` and `sig`. -/
abbrev vR (p : Params) : List (Reg × Nat) := [(.rbp, p.pkLen), (.r12, 64), (.r13, p.sigLen)]
/-- `scratch`. -/
abbrev vW (p : Params) : List (Reg × Nat) := [(.rbx, scrLen p)]
abbrev vB (p : Params) : List (Reg × Nat) := vR p ++ vW p

/-- The register saved at `scratch + 840 + 8k`. -/
abbrev savedReg (k : Nat) : Reg := savedRegs.getD k .rbx

/-- What holds throughout a run from `σ`. -/
structure T (p : Params) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rsp : s.gpr .rsp = σ.gpr .rsp
  rbx : s.gpr .rbx = σ.gpr .rcx
  rbp : s.gpr .rbp = σ.gpr .rdi
  r12 : s.gpr .r12 = σ.gpr .rsi
  r13 : s.gpr .r13 = σ.gpr .rdx
  saved : ∀ k < 6, s.mem.readW (pa s (sc (oSV + 8 * k))) 64 = σ.gpr (savedReg k)
  ret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64
  pk : bytesAt s.mem (pa s (.rbp, 0)) p.pkLen = vPk p σ
  mu : bytesAt s.mem (pa s (.r12, 0)) 64 = vMu σ
  sig : bytesAt s.mem (pa s (.r13, 0)) p.sigLen = vSig p σ

theorem vB_small {p : Params} (hp : p ∈ params) : ∀ b ∈ vB p, b.2 < 2 ^ 31 := by
  revert p; decide

theorem T.lay {p : Params} (hp : p ∈ params) {σ s : State} (hv : VPre p σ) (h : T p σ s) : Lay (vR p) (vW p) s := by
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine ⟨vB_small hp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [h.rsp]; exact hv.sp⟩
  · intro b hb b' hb' hne hw
    simp only [vR, vW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb hb'
    rcases hb with rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl <;>
      simp only [wRegs, List.mem_singleton, ne_eq, not_true_eq_false, reduceCtorEq, or_self] at hne hw <;> simp only [h.rbx, h.rbp, h.r12, h.r13]
    all_goals first | exact hv.d1 | exact hv.d2 | exact hv.d3 | exact hv.d1.symm | exact hv.d2.symm |
      exact hv.d3.symm
  · intro b hb
    simp only [vR, vW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp only [h.rbx, h.rbp, h.r12, h.r13, h.rsp]
    exacts [hv.k1, hv.k2, hv.k3, hv.k4]
  · intro b hb
    simp only [vR, vW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp only [h.rbx, h.rbp, h.r12, h.r13]
    exacts [hv.n1, hv.n2, hv.n3, hv.n4]
  · intro b hb
    simp only [vR, vW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp only [h.rbx, h.rbp, h.r12, h.r13]
    · exact mem ⟨σ.gpr .rdi, p.pkLen⟩ (by rw [hv.rd]; simp)
    · exact mem ⟨σ.gpr .rsi, 64⟩ (by rw [hv.rd]; simp)
    · exact mem ⟨σ.gpr .rdx, p.sigLen⟩ (by rw [hv.rd]; simp)
    · exact mem ⟨σ.gpr .rcx, scrLen p⟩ (by rw [hv.wr]; simp)
  · intro b hb
    simp only [vW, List.mem_singleton] at hb
    subst hb
    exact ⟨_, by rw [h.wr, hv.wr, h.rbx]; simp, Region.contains_self _ _⟩
  · intro b hb
    simp only [vR, vW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp only [h.rbx, h.rbp, h.r12, h.r13, h.rsp]
    exacts [hv.r1, hv.r2, hv.r3, hv.r4]
  · intro b hb
    simp only [vR, vW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp only [bases, List.mem_cons, true_or, or_true]

/-- A piece that writes `ws` keeps `T`: the saved registers, the inputs, and
the regions written within the layout. -/
def tChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  (List.range 6).all (fun k => keepB (vB p) ws (sc (oSV + 8 * k)) 8) && ws.all (fun w => inB (vB p) w.1 w.2) &&
    keepB (vB p) ws (.rbp, 0) p.pkLen && keepB (vB p) ws (.r12, 0) 64 && keepB (vB p) ws (.r13, 0) p.sigLen

theorem tChk_nil : ∀ p ∈ params, tChk p [] = true := by decide

theorem T.step {p : Params} (hp : p ∈ params) {σ s s' : State} (hv : VPre p σ) (h : T p σ s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : tChk p ws = true) : T p σ s' := by
  have L := h.lay hp hv
  simp only [tChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hsv, hin⟩, hpk⟩, hmu⟩, hsig⟩ := hc
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.rsp.trans h.rsp, (hP.bs .rbx (by decide)).trans h.rbx,
    (hP.bs .rbp (by decide)).trans h.rbp, (hP.bs .r12 (by decide)).trans h.r12, (hP.bs .r13 (by decide)).trans h.r13,
    fun k hk => ?_, ?_, by rw [L.keepBytes hP hpk]; exact h.pk, by rw [L.keepBytes hP hmu]; exact h.mu,
    by rw [L.keepBytes hP hsig]; exact h.sig⟩
  · rw [L.keepW hP (hsv k hk)]; exact h.saved k hk
  · have := L.keepRet hP hin
    rw [h.rsp] at this
    rw [this, h.ret]


/-! ## Entry and exit -/

theorem readW_writeW_slot (m : Mem) (a : Addr) {x y : Nat} (v : BitVec 64) (hxy : x + 8 ≤ y ∨ y + 8 ≤ x)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (m.writeW (a + BitVec.ofNat 64 y) v).readW (a + BitVec.ofNat 64 x) 64 = m.readW (a + BitVec.ofNat 64 x) 64 := by
  refine Mem.readW_writeW_sep ?_ (by decide)
  rcases hxy with h | h
  · exact (off_disj (p := a) h (by omega)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  · exact (off_disj (p := a) h (by omega)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- The six stores of `pro`: each slot holds its register. -/
theorem stores_read (m : Mem) (a : Addr) (v : Nat → BitVec 64) : ∀ k < 6,
    ((((((m.writeW (a + BitVec.ofNat 64 840) (v 0)).writeW (a + BitVec.ofNat 64 848) (v 1)).writeW
      (a + BitVec.ofNat 64 856) (v 2)).writeW (a + BitVec.ofNat 64 864) (v 3)).writeW (a + BitVec.ofNat 64 872)
      (v 4)).writeW (a + BitVec.ofNat 64 880) (v 5)).readW (a + BitVec.ofNat 64 (oSV + 8 * k)) 64 = v k := by
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := omega) only [oSV, Nat.reduceMul, Nat.reduceAdd, readW_writeW_slot, Mem.readW_writeW_self64]

theorem pro_eq : pro = [.store (at_ .rcx 840) .rbx, .store (at_ .rcx 848) .rbp, .store (at_ .rcx 856) .r12,
    .store (at_ .rcx 864) .r13, .store (at_ .rcx 872) .r14, .store (at_ .rcx 880) .r15, .mov .rbx (.reg .rcx),
    .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov32 .r15 (.imm 1)] := rfl

theorem scr_big {p : Params} (hp : p ∈ params) : 888 ≤ scrLen p := by revert p; decide

theorem pro_ok {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ) :
    WP isa (.block pro) σ fun s => T p σ s ∧ s.gpr .r15 = flag True := by
  have hb := scr_big hp
  have hS : ⟨σ.gpr .rcx, scrLen p⟩ ∈ σ.wr := by rw [hv.wr]; simp
  have hsl : scrLen p < 2 ^ 64 := by have := vB_small hp (.rbx, scrLen p) (by simp); simp only at this; omega
  have c : ∀ o, o + 8 ≤ scrLen p → (⟨σ.gpr .rcx, scrLen p⟩ : Region).Contains (σ.gpr .rcx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho hsl
  have w : ∀ o, o + 8 ≤ scrLen p → InRegions σ.wr (σ.gpr .rcx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
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
  have hf : Frame [⟨σ.gpr .rcx, scrLen p⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  have z : ∀ x : Addr, x + BitVec.ofNat 64 0 = x := fun x => BitVec.add_zero x
  refine ⟨k.2.1, k.2.2, hsp, hbx, hbp, h12, h13, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .rcx) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using hv.r4) (by decide)
  · rw [pa, hbp, z]
    exact Proof.MlKem.bytesAt_frame hf (by simpa using hv.d1) (by have := hv.n1; omega)
  · rw [pa, h12, z]
    exact Proof.MlKem.bytesAt_frame hf (by simpa using hv.d2) (by decide)
  · rw [pa, h13, z]
    exact Proof.MlKem.bytesAt_frame hf (by simpa using hv.d3) (by have := hv.n3; omega)

theorem epi_eq : epi = [.mov32 .rax (.reg .r15), .mov .r15 (.mem (at_ .rbx 880)), .mov .r14 (.mem (at_ .rbx 872)),
    .mov .r13 (.mem (at_ .rbx 864)), .mov .r12 (.mem (at_ .rbx 856)), .mov .rbp (.mem (at_ .rbx 848)),
    .mov .rbx (.mem (at_ .rbx 840))] := rfl

theorem saved_in {p : Params} (hp : p ∈ params) : ∀ k < 6, inB (vB p) (sc (oSV + 8 * k)) 8 = true := by
  revert p; decide

theorem epi_ok {p : Params} (hp : p ∈ params) {σ s : State} (hv : VPre p σ) (h : T p σ s) :
    WP isa (.block epi) s fun s' => res s' = (s.gpr .r15).setWidth 32 ∧ gprPreserved σ s' := by
  have L := h.lay hp hv
  have hin : ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := by
    have hk : ∀ k < 6, inB (vB p) (sc (oSV + 8 * k)) 8 = true := saved_in hp
    exact fun k hkk => L.inR (hk k hkk)
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
  rw [epi_eq]
  refine WP.mono (WP.keep [.rax, .r15, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' =>
    s'.gpr .rax = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32) ∧ s'.gpr .r15 = σ.gpr .r15 ∧
    s'.gpr .r14 = σ.gpr .r14 ∧ s'.gpr .r13 = σ.gpr .r13 ∧ s'.gpr .r12 = σ.gpr .r12 ∧ s'.gpr .rbp = σ.gpr .rbp ∧
    s'.gpr .rbx = σ.gpr .rbx ∧ s'.mem = s.mem) (by xrun [i0, i1, i2, i3, i4, i5, e0, e1, e2, e3, e4, e5]) (by decide))
    fun s' ⟨⟨hax, h15, h14, h13, h12, hbp, hbx, hm⟩, k⟩ => ⟨?_, ⟨fun r hr => ?_, ?_⟩⟩
  · simp only [res, hax]; apply BitVec.eq_of_toNat_eq; simp
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, by rw [k.gpr (by decide), h.rsp], h12, h13, h14, h15]
  · rw [hm]; exact h.ret

end VG.Proof.MlDsa.X86_64.Verify
