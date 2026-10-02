import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Apply
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# Streaming ChaCha20 on x86-64: `apply`, constant time

Untrusted: everything here is checked by Lean. Two runs from states that
agree on the pointers, the length and the number of bytes of keystream left
(which the contract lets `apply` leak) are related piece by piece (`RelCT`):
the taint analysis proves each piece without calls constant time from the
registers that hold public values (`taintRegs`), which correctness determines
in each run (`Apply.lean`) from those public values; the calls of the block
function and of the implementation `v` of `vg_chacha20_xor` are constant time
by their own proofs (`RelCT.callEx`), their arguments agreeing; and the
branches are on public values (`RelCT.ite`).
-/

namespace VG.Proof.ChaCha20.X86_64.Stream

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Stream
open VG.Spec.ChaCha20 (stateAt)

/-- Code the taint analysis proves constant time from the registers `rs`. -/
theorem taintRegs {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun x y hp => Taint.agree_ofRegs (hr x y hp)) h

/-- What each run satisfies by correctness holds of the final states. -/
theorem RelCT.post {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x F₁ ∧ WP isa c y F₂) :
    RelCT isa P c fun x y => F₁ x ∧ F₂ y :=
  RelCT.mono (RelCT.wp h hw) (fun _ _ h => h) fun _ _ h => h.2

/-- Two entry states that agree on what is public. -/
structure Two (a b : State) : Prop where
  pa : APre a
  pb : APre b
  hst : st a = st b
  hdp : dp a = dp b
  hrdx : a.gpr .rdx = b.gpr .rdx
  hrsp : a.gpr .rsp = b.gpr .rsp
  hleft : N a = N b

theorem Two.eqL {a b : State} (h : Two a b) : L a = L b := by
  show (a.gpr .rdx).toNat = (b.gpr .rdx).toNat; rw [h.hrdx]
theorem Two.eqH {a b : State} (h : Two a b) : H a = H b := by
  show min (N a % 64) (L a) = min (N b % 64) (L b); rw [h.hleft, h.eqL]
theorem Two.eqNB {a b : State} (h : Two a b) : NB a = NB b := by
  show (L a - H a) / 64 = (L b - H b) / 64; rw [h.eqH, h.eqL]
theorem Two.eqT {a b : State} (h : Two a b) : T a = T b := by
  show (L a - H a) % 64 = (L b - H b) % 64; rw [h.eqH, h.eqL]


/-- The arguments of the call of `vg_chacha20_xor`. -/
structure Args (s₀ s : State) : Prop where
  rdi : s.gpr .rdi = st s₀ + BitVec.ofNat 64 192
  rsi : s.gpr .rsi = dp s₀ + BitVec.ofNat 64 (H s₀)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (64 * NB s₀)
  rcx : s.gpr .rcx = st s₀ + BitVec.ofNat 64 256
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = []
  wr : s.wr = [stR s₀, dR s₀]

theorem args_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) :
    WP isa (.block blocksArgs) s (Args s₀) :=
  WP.mono (args_exec h.rbx (h.w hp) (by rw [h.rd, hp.rd])) fun _ ⟨_, rdi₁, rsi₁, rcx₁, rdx₁, _, _, k₁, rd₁, wr₁⟩ =>
    ⟨rdi₁, by rw [rsi₁, h.rbp], by rw [rdx₁, h.rdx], rcx₁, by rw [k₁ .rsp (by simp), h.keep .rsp (by simp)],
      by rw [rd₁, h.rd, hp.rd], by rw [wr₁, h.wr, hp.wr]⟩

theorem Args.covers {s₀ s : State} (h : Args s₀ s) :
    Covers [cpR s₀, blR s₀, wkR s₀] s.wr ∧ Covers ([] ++ [cpR s₀, blR s₀, wkR s₀]) (s.rd ++ s.wr) := by
  have hcov : ∀ r ∈ [cpR s₀, blR s₀, wkR s₀], ∃ r' ∈ [stR s₀, dR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 192, rfl, by simp⟩
    · exact ⟨dR s₀, by simp, H s₀, rfl, HNB_le s₀⟩
    · exact ⟨stR s₀, by simp, 256, rfl, by simp⟩
  exact ⟨by rw [h.wr]; exact Covers.of_sub hcov,
    by rw [h.rd, h.wr, List.nil_append, List.nil_append]; exact Covers.of_sub hcov⟩

theorem Args.pre (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ s : State} (hp : APre s₀) (h : Args s₀ s) :
    (Proof.ChaCha20.xorStack v.stack).pre (s.callEntry.withRegions [] [cpR s₀, blR s₀, wkR s₀]) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHNB := HNB_le s₀
  have hstk : below (s.gpr .rsp) 24 = stkR s₀ := by rw [h.rsp]; rfl
  have hwrap : (dp s₀ + BitVec.ofNat 64 (H s₀)).toNat + 64 * NB s₀ ≤ 2 ^ 64 := by
    have := hp.wrap_d
    rw [BitVec.toNat_add, Proof.ChaCha20.X86_64.toNat_ofNat_lt (by omega)]
    omega
  exact xor_pre v h.rdi h.rsi h.rdx h.rcx (by omega)
    ((hp.st_d.sub_left (cpR_sub s₀)).sub_right (blR_sub s₀))
    (Offset.disjoint _ (by omega) (by omega) (by omega))
    ((hp.st_d.sub_left (wkR_sub s₀)).symm.sub_left (blR_sub s₀)) hwrap
    (by rw [hstk]; exact hp.stk_st.sub_right (cpR_sub s₀)) (by rw [hstk]; exact hp.stk_d.sub_right (blR_sub s₀))
    (by rw [hstk]; exact hp.stk_st.sub_right (wkR_sub s₀))

set_option simprocs false in
theorem test_ok {s₀ : State} {s : State} (h : Q2 s₀ s) :
    WP isa (.block [.alu .test .r12 (.reg .r12)]) s fun s₁ => Q2 s₀ s₁ ∧ s₁.zf = some (decide (T s₀ = 0)) := by
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨h.rbx, h.rbp, h.r12, h.keep, h.rd, h.wr, h.state, h.buf, h.saved, h.done, h.frame⟩, ?_⟩
  rw [BitVec.and_self, h.r12, ← Offset.ofNat_sub_ofNat_beq (x := T s₀) (y := 0) (by omega) (by omega)]
  simp

/-- The arguments of the call of the block function, and the registers the
rest uses. -/
structure TArgs (s₀ s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rsi : s.gpr .rsi = st s₀ + BitVec.ofNat 64 64
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (T s₀)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = []
  wr : s.wr = [stR s₀, dR s₀]

set_option simprocs false in
theorem tailArgs_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) :
    WP isa (.block tailArgs) s (TArgs s₀) := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [tailArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, h.rbx]
  exact ⟨rfl, rfl, by simp (config := {decide := true}) [h.rbx], by simp (config := {decide := true}) [h.rbp],
    by simp (config := {decide := true}) [h.r12], by simp (config := {decide := true}) [h.keep .rsp (by simp)],
    by simp [h.rd, hp.rd], by simp [h.wr, hp.wr]⟩

/-- After the block function: the registers the rest uses. -/
structure TAfter (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (T s₀)
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem TArgs.pre {s₀ s : State} (hp : APre s₀) (h : TArgs s₀ s) :
    Proof.ChaCha20.blockX86_64.pre (s.callEntry.withRegions [⟨st s₀, 64⟩] [⟨st s₀ + BitVec.ofNat 64 64, 256⟩]) := by
  simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
    h.rdi, h.rsi, h.rsp]
  exact ⟨trivial, trivial, Offset.disjoint_base _ (by omega) (by omega),
    (hp.stk_st.sub_left (below8_stk s₀)).sub_right (bufR_sub s₀)⟩

theorem TArgs.covers {s₀ s : State} (h : TArgs s₀ s) :
    Covers ([⟨st s₀, 64⟩] ++ [⟨st s₀ + BitVec.ofNat 64 64, 256⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨st s₀ + BitVec.ofNat 64 64, 256⟩] s.wr := by
  refine ⟨?_, ?_⟩
  · rw [h.rd, h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 768 by decide⟩
    · exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩
  · rw [h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩

theorem TArgs.call {s₀ s : State} (hp : APre s₀) (h : TArgs s₀ s) :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block) s (TAfter s₀) := by
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  have hb8 : below (s.gpr .rsp) 8 = below (s₀.gpr .rsp) 8 := by rw [h.rsp]
  refine block_call h.rdi h.rsi (Offset.disjoint_base _ (by omega) (by omega))
    (by rw [hb8]; exact (hp.stk_st.sub_left (below8_stk s₀)).sub_right (bufR_sub s₀))
    (by rw [hb8]; exact (hp.stk_st.sub_left (below8_stk s₀)).sub_right stS) h.covers.1 h.covers.2
    fun s' _ _ cs _ _ _ => ⟨by rw [cs .rbx (by simp [calleeSaved]), h.rbx],
      by rw [cs .rbp (by simp [calleeSaved]), h.rbp], by rw [cs .r12 (by simp [calleeSaved]), h.r12],
      by rw [cs .rsp (by simp [calleeSaved]), h.rsp]⟩

section
variable {a b : State} (h : Two a b)
include h

theorem check_rel : RelCT isa (fun x y => x = a ∧ y = b) (.block check) fun x y => Q0 a x ∧ Q0 b y :=
  RelCT.post (taintRegs [.rdi, .rsp] (fun x y ⟨hx, hy⟩ r hr => by
      subst hx hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.hst
      · exact h.hrsp) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨by subst hx; exact check_ok h.pa, by subst hy; exact check_ok h.pb⟩

theorem part1_rel (hle : L a ≤ N a) :
    RelCT isa (fun x y => Q0 a x ∧ Q0 b y) part1 fun x y => Q1 a x ∧ Q1 b y :=
  RelCT.post (taintRegs [.rdi, .rsi, .rdx, .rax, .rsp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hx.keep _ (by decide), hy.keep _ (by decide)]; exact h.hst
      · rw [hx.keep _ (by decide), hy.keep _ (by decide)]; exact h.hdp
      · rw [hx.keep _ (by decide), hy.keep _ (by decide)]; exact h.hrdx
      · rw [hx.rax, hy.rax, h.hleft]
      · rw [hx.keep _ (by decide), hy.keep _ (by decide)]; exact h.hrsp) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨part1_ok h.pa hle hx, part1_ok h.pb (by rw [← h.eqL, ← h.hleft]; exact hle) hy⟩

theorem xor_rel (v : Proof.ChaCha20.X86_64.XorImpl) :
    RelCT isa (fun x y => Args a x ∧ Args b y) (.call v.callee.name v.callee.code) fun _ _ => True :=
  RelCT.callEx v.ok v.ct fun x y ⟨hx, hy⟩ =>
    ⟨[], _, [], _, hx.pre v h.pa, hy.pre v h.pb, by
      simp only [Proof.ChaCha20.xorStack, Proof.ChaCha20.xorX86_64, State.withRegions_gpr,
        State.callEntry_rsp, callEntry_gpr' x (by decide : Reg.rdi ≠ .rsp),
        callEntry_gpr' x (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' x (by decide : Reg.rdx ≠ .rsp),
        callEntry_gpr' x (by decide : Reg.rcx ≠ .rsp), callEntry_gpr' y (by decide : Reg.rdi ≠ .rsp),
        callEntry_gpr' y (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' y (by decide : Reg.rdx ≠ .rsp),
        callEntry_gpr' y (by decide : Reg.rcx ≠ .rsp), hx.rdi, hx.rsi, hx.rdx, hx.rcx, hx.rsp, hy.rdi,
        hy.rsi, hy.rdx, hy.rcx, hy.rsp, h.hst, h.hdp, h.eqH, h.eqNB, h.hrsp]
      exact ⟨trivial, trivial, trivial, trivial, trivial⟩,
      hx.covers.2, hx.covers.1, hy.covers.2, hy.covers.1, by rw [hx.rsp, hy.rsp, h.hrsp]⟩

theorem part2_rel (v : Proof.ChaCha20.X86_64.XorImpl) :
    RelCT isa (fun x y => Q1 a x ∧ Q1 b y) (part2 v.callee) fun x y => Q2 a x ∧ Q2 b y := by
  refine RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨part2_ok v h.pa hx, part2_ok v h.pb hy⟩
  rw [part2_eq]
  refine RelCT.ite (fun x y ⟨hx, hy⟩ => by simp only [eval, hx.zf, hy.zf, h.eqNB])
    (taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => Args a x ∧ Args b y) ?_ (xor_rel h v)
  refine RelCT.post (taintRegs [.rbx, .rbp, .r12, .rdx, .rsp] (fun x y ⟨⟨hx, hy⟩, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hx.rbx, hy.rbx, h.hst]
      · rw [hx.rbp, hy.rbp, h.hdp, h.eqH]
      · rw [hx.r12, hy.r12, h.eqL, h.eqH]
      · rw [hx.rdx, hy.rdx, h.eqNB]
      · rw [hx.keep .rsp (by simp), hy.keep .rsp (by simp), h.hrsp]) (by taint_decide))
    fun x y ⟨⟨hx, hy⟩, _⟩ => ⟨args_ok h.pa hx, args_ok h.pb hy⟩

theorem part3_rel : RelCT isa (fun x y => Q2 a x ∧ Q2 b y) part3 fun x y => Q3 a x ∧ Q3 b y := by
  refine RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨part3_ok h.pa hx, part3_ok h.pb hy⟩
  rw [part3_eq]
  refine RelCT.seq (R := fun (x y : State) => (Q2 a x ∧ x.zf = some (decide (T a = 0))) ∧
      (Q2 b y ∧ y.zf = some (decide (T b = 0))))
    (RelCT.post (taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨test_ok hx, test_ok hy⟩) ?_
  refine RelCT.ite (fun x y ⟨hx, hy⟩ => by simp only [eval, hx.2, hy.2, h.eqT])
    (taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => TArgs a x ∧ TArgs b y)
    (RelCT.post (taintRegs [.rbx] (fun x y ⟨⟨hx, hy⟩, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hx.1.rbx, hy.1.rbx, h.hst]) (by taint_decide))
      fun x y ⟨⟨hx, hy⟩, _⟩ => ⟨tailArgs_ok h.pa hx.1, tailArgs_ok h.pb hy.1⟩) ?_
  refine RelCT.seq (R := fun x y => TAfter a x ∧ TAfter b y) ?_
    (taintRegs [.rbx, .rbp, .r12, .rsp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hx.rbx, hy.rbx, h.hst]
      · rw [hx.rbp, hy.rbp, h.hdp, h.eqH, h.eqNB]
      · rw [hx.r12, hy.r12, h.eqT]
      · rw [hx.rsp, hy.rsp, h.hrsp]) (by taint_decide))
  have hP : ∀ x y : State, TArgs a x ∧ TArgs b y → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      Proof.ChaCha20.blockX86_64.pre (x.callEntry.withRegions rd₁ wr₁) ∧
      Proof.ChaCha20.blockX86_64.pre (y.callEntry.withRegions rd₂ wr₂) ∧
      Proof.ChaCha20.blockX86_64.pub (x.callEntry.withRegions rd₁ wr₁) (y.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x.rd ++ x.wr) ∧ Covers wr₁ x.wr ∧
      Covers (rd₂ ++ wr₂) (y.rd ++ y.wr) ∧ Covers wr₂ y.wr ∧ x.gpr .rsp = y.gpr .rsp := by
    intro x y ⟨hx, hy⟩
    refine ⟨_, _, _, _, hx.pre h.pa, hy.pre h.pb, ?_, hx.covers.1, hx.covers.2, hy.covers.1,
      hy.covers.2, by rw [hx.rsp, hy.rsp, h.hrsp]⟩
    simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, callEntry_gpr' x (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' x (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' y (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' y (by decide : Reg.rsi ≠ .rsp), hx.rdi, hx.rsi, hy.rdi, hy.rsi, h.hst]
    exact ⟨trivial, trivial⟩
  exact RelCT.post (RelCT.callEx Proof.ChaCha20.X86_64.block_correct Proof.ChaCha20.X86_64.block_ct hP)
    fun x y ⟨hx, hy⟩ => ⟨hx.call h.pa, hy.call h.pb⟩

theorem apply_rel (v : Proof.ChaCha20.X86_64.XorImpl) :
    RelCT isa (fun x y => x = a ∧ y = b) (apply v.callee) fun _ _ => True := by
  rw [apply_eq]
  refine RelCT.seq (check_rel h) (RelCT.ite (fun x y ⟨hx, hy⟩ => by simp only [eval, hx.cf, hy.cf, h.hleft, h.eqL])
    (taintRegs [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_)
  by_cases hlt : N a < L a
  · exact RelCT.of_false fun x y ⟨⟨hx, _⟩, he⟩ => by simp [eval, hx.cf, hlt] at he
  have hle : L a ≤ N a := by omega
  refine RelCT.seq (RelCT.mono (part1_rel h hle) (fun _ _ hp => hp.1) fun _ _ hq => hq)
    (RelCT.seq (part2_rel h v) (RelCT.seq (part3_rel h) ?_))
  exact taintRegs [.rbx, .rsp] (fun x y ⟨hx, hy⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.rbx, hy.rbx, h.hst]
    · rw [hx.keep .rsp (by simp), hy.keep .rsp (by simp), h.hrsp]) (by taint_decide)

end

theorem Two.of {a b : State} (ha : Proof.ChaCha20.applyX86_64.pre a) (hb : Proof.ChaCha20.applyX86_64.pre b)
    (hq : Proof.ChaCha20.applyX86_64.pub a b) : Two a b := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hq
  exact ⟨APre.of a ha, APre.of b hb, p1, p2, p3, p4, (List.cons.inj p5).1⟩

theorem apply_ct (v : Proof.ChaCha20.X86_64.XorImpl) :
    ConstantTime isa Proof.ChaCha20.applyX86_64.pre Proof.ChaCha20.applyX86_64.pub (apply v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (apply_rel (Two.of h₁ h₂ hq) v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem apply_mxcsr (v : Proof.ChaCha20.X86_64.XorImpl) :
    (apply v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [apply, part2, Code.allInstrs, v.mxcsr, Bool.and_true, Bool.true_and]
  lit_decide

theorem apply_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    (apply v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [apply, part2, Code.all, v.spSafe, Bool.and_true]
  lit_decide

theorem apply_ok (v : Proof.ChaCha20.X86_64.XorImpl) (s : State) (hs : Proof.ChaCha20.applyX86_64.pre s) :
    ∃ t s', Exec isa (apply v.callee) s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.applyX86_64.post s s' := by
  obtain ⟨t, s', he, hf⟩ := apply_correct v (APre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (apply_mxcsr v) he hf.1, hf.2⟩

/-- A state satisfying the precondition of `apply` (with no data). -/
def applySat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 768⟩, ⟨0x2000, 0⟩]

theorem apply_verified (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target (apply v.callee) (Spec.ChaCha20.applyContract X86_64.abi 24) :=
  Verified.of_correct (apply_ok v) (apply_ct v) (by
    sig_implies [Spec.ChaCha20.applyContract, Spec.ChaCha20.applySig, Proof.ChaCha20.applyX86_64,
      X86_64.abi, X86_64.argRegs] [applySat] using applySat)

end VG.Proof.ChaCha20.X86_64.Stream
