import VerifiedGarbage.Proof.X25519.X86_64.Setup
import VerifiedGarbage.Proof.X25519.X86_64.Bits

/-!
# X25519 on x86-64: the last swap and the result
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem mask_of : ∀ a < 2, BitVec.setWidth 64 (0 : BitVec 32) - BitVec.ofNat 64 a =
    mask (decide (a = 1)) := by decide

theorem swapMask_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Nat} (hsw : sw < 2)
    (hw : word s.mem base SWAP = BitVec.ofNat 64 sw) :
    WP isa (.block ([.mov .rdx (.mem (sc SWAP)), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] :
      List Instr)) s fun s' => s'.gpr .rcx = mask (decide (sw = 1)) ∧ Keeps [.rdx, .rcx] s s' := by
  have hr : InRegions (s.rd ++ s.wr) (off base SWAP) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    State.load64, ea_sc, hs.rdi, hr, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, hw, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨mask_of sw hsw, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

theorem lastSwap_eq : lastSwap = ([.mov .rdx (.mem (sc SWAP)), .mov32 .rcx (.imm 0),
    .alu .sub .rcx (.reg .rdx)] : List Instr) ++ (cswap X2 X3 ++ cswap Z2 Z3) := by
  simp only [lastSwap, List.append_assoc]

/-- The swap after the loop, by the ladder's `swap`. -/
theorem lastSwap_ok {s : State} {base : Addr} (hs : Scr s base) {st : Spec.X25519.Ladder}
    (hsw : st.swap < 2) (hw : word s.mem base SWAP = BitVec.ofNat 64 st.swap)
    (h3 : E s.mem base 3 = st.x2) (h4 : E s.mem base 4 = st.z2) (h5 : E s.mem base 5 = st.x3)
    (h6 : E s.mem base 6 = st.z3) :
    WP isa (.block lastSwap) s fun s' =>
      Keep base s s' ∧ E s'.mem base 3 = (Spec.X25519.cswap st.swap st.x2 st.x3).1 ∧
        E s'.mem base 4 = (Spec.X25519.cswap st.swap st.z2 st.z3).1 := by
  rw [lastSwap_eq, WP.block_append_iff]
  refine WP.mono (swapMask_ok hs hsw hw) fun s₁ ⟨m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have g₁ : ∀ r, r ∉ clob → s₁.gpr r = s.gpr r := fun r hr => k₁.1 r fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
  have K₁ : Keep base s s₁ := ⟨g₁, k₁.2.2.1, k₁.2.2.2, by rw [k₁.2.1]; exact Outside.refl _ _ _ _⟩
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs₁ 3 5 (by decide) (by decide) (by decide) m₁)
    fun s₂ ⟨K₂, c₂, e₂⟩ => ?_
  refine WP.mono (cswapE (K₂.scr hs₁) 4 6 (by decide) (by decide) (by decide) (c₂.trans m₁))
    fun s₃ ⟨K₃, _, e₃⟩ => ?_
  refine ⟨(K₁.trans K₂).trans K₃, ?_, ?_⟩
  · rw [e₃, e₂, cswap_fst, ← h3, ← h5, ← k₁.2.1]
    simp (config := {decide := true}) only [opSwap, Function.update_apply, ite_true, ite_false]
  · rw [e₃, e₂, cswap_fst, ← h4, ← h6, ← k₁.2.1]
    simp (config := {decide := true}) only [opSwap, Function.update_apply, ite_true, ite_false]

/-! ## The result -/

theorem restore_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 64}
    (hsv : Saved base g s.mem) :
    WP isa (.block restore) s fun s' =>
      (∀ rd ∈ saved, s'.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.mono (Spill.restore_ok .rdi saved g s (by decide) (fun p hp => ?_) (by rw [hs.rdi]; exact hsv))
    fun s' ⟨h₁, h₂, hm, hrd, hwr⟩ => ⟨fun rd hrd => h₁ _ (List.mem_map_of_mem hrd), h₂, hm, hrd, hwr⟩
  have := saved_lt p hp
  rw [hs.rdi]; exact ⟨_, List.mem_append_right _ hs.wr, contains_sc (by omega)⟩

theorem outStores_ok {s : State} {q : Addr} (hq : s.gpr .rsi = q) (hw : (⟨q, 32⟩ : Region) ∈ s.wr) :
    WP isa (.block ([.store (at_ .rsi 0) .r8, .store (at_ .rsi 8) .r9, .store (at_ .rsi 16) .r10,
      .store (at_ .rsi 24) .r11] : List Instr)) s fun s' =>
      s'.mem = st4 s.mem q 0 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 32 → InRegions s.wr (off q d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base q hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hq, State.store64,
    w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega), ite_true, Option.some.injEq,
    exists_eq_left']
  exact ⟨rfl, trivial, trivial, trivial⟩

theorem bytesAt_st4 (m : Mem) (q : Addr) (w0 w1 w2 w3 : BitVec 64) :
    Spec.X25519.bytesAt (st4 m q 0 w0 w1 w2 w3) q 32 = leBytes 32 (val4 w0 w1 w2 w3) := by
  have e : ((st4 m q 0 w0 w1 w2 w3).readW (off q 0) 64).toNat +
      2 ^ 64 * ((st4 m q 0 w0 w1 w2 w3).readW (q + 8) 64).toNat +
      2 ^ 128 * ((st4 m q 0 w0 w1 w2 w3).readW (q + 16) 64).toNat +
      2 ^ 192 * ((st4 m q 0 w0 w1 w2 w3).readW (q + 24) 64).toNat = val4 w0 w1 w2 w3 :=
    fe_st4 m q (by decide) w0 w1 w2 w3
  rw [show off q 0 = q from BitVec.add_zero q] at e
  have := ((st4 m q 0 w0 w1 w2 w3).readW q 64).isLt
  have := ((st4 m q 0 w0 w1 w2 w3).readW (q + 8) 64).isLt
  have := ((st4 m q 0 w0 w1 w2 w3).readW (q + 16) 64).isLt
  have := ((st4 m q 0 w0 w1 w2 w3).readW (q + 24) 64).isLt
  exact bytesAt_leBytes_words64 _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem movRsi_ok (s : State) :
    WP isa (.block ([.mov .rsi (.reg .r12)] : List Instr)) s fun s' =>
      s'.gpr .rsi = s.gpr .r12 ∧ Keeps [.rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

end VG.Proof.X25519.X86_64
