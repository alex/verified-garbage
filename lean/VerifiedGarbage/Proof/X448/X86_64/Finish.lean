import VerifiedGarbage.Proof.X448.X86_64.Setup
import VerifiedGarbage.Proof.X448.X86_64.Iter

/-!
# X448 on x86-64: the last swap and the result
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

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
theorem lastSwap_ok {s : State} {base : Addr} (hs : Scr s base) {st : Spec.X448.Ladder}
    (hsw : st.swap < 2) (hw : word s.mem base SWAP = BitVec.ofNat 64 st.swap)
    (h1 : E s.mem base 1 = st.x2) (h2 : E s.mem base 2 = st.z2) (h3 : E s.mem base 3 = st.x3)
    (h4 : E s.mem base 4 = st.z3) :
    WP isa (.block lastSwap) s fun s' =>
      Keep base s s' ∧ E s'.mem base 1 = (Spec.X448.cswap st.swap st.x2 st.x3).1 ∧
        E s'.mem base 2 = (Spec.X448.cswap st.swap st.z2 st.z3).1 := by
  rw [lastSwap_eq, WP.block_append_iff]
  refine WP.mono (swapMask_ok hs hsw hw) fun s₁ ⟨m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have g₁ : ∀ r, r ∉ clob → s₁.gpr r = s.gpr r := fun r hr => k₁.1 r fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
  have K₁ : Keep base s s₁ := ⟨g₁, k₁.2.2.1, k₁.2.2.2, by rw [k₁.2.1]; exact Outside.refl _ _ _ _⟩
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs₁ 1 3 (by decide) m₁) fun s₂ ⟨K₂, c₂, e₂⟩ => ?_
  refine WP.mono (cswapE (K₂.scr hs₁) 2 4 (by decide) (c₂.trans m₁)) fun s₃ ⟨K₃, _, e₃⟩ => ?_
  refine ⟨(K₁.trans K₂).trans K₃, ?_, ?_⟩
  · rw [e₃, e₂, cswap_fst, ← h1, ← h3, ← k₁.2.1]
    simp (config := {decide := true}) only [opSwap, Function.update_apply, ite_true, ite_false]
  · rw [e₃, e₂, cswap_fst, ← h2, ← h4, ← k₁.2.1]
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

/-- Stores relative to a register `b`, as a list. -/
def storesR (b : Reg) : Nat → List Reg → List Instr
  | _, [] => []
  | o, r :: rs => .store (at_ b o) r :: storesR b (o + 8) rs

theorem outStores_eq : (List.range 7).map (fun i => Instr.store (at_ .rsi (8 * i)) (w i)) =
    storesR .rsi 0 W := rfl

/-- Words stored at `q + o`, … into the writable region `R`. -/
theorem storesR_ok {q : Addr} {R : Region} :
    ∀ (s : State) (o : Nat) (rs : List Reg), s.gpr .rsi = q → R ∈ s.wr →
      (∀ d, o ≤ d → d + 8 ≤ o + 8 * rs.length → R.Contains (off q d) 8) →
      o + 8 * rs.length < 2 ^ 64 →
      WP isa (.block (storesR .rsi o rs)) s fun s' =>
        mv s'.mem q o rs.length = rv s rs ∧ Outside q o (8 * rs.length) s.mem s'.mem ∧
        Frame [R] s.mem s'.mem ∧ (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | s, _, [], _, _, _, _ =>
    WP.block_nil ⟨rfl, Outside.refl _ _ _ _, Frame.refl _ _, fun _ => rfl, rfl, rfl⟩
  | s, o, r :: rs, hq, hR, hc, hn => by
    rw [storesR, WP.block_cons_iff]
    have hl : (r :: rs).length = rs.length + 1 := rfl
    let s1 : State := { s with mem := s.mem.writeW (off q o) (s.gpr r) }
    have hw : InRegions s.wr (off q o) 8 := ⟨R, hR, hc o (Nat.le_refl _) (by omega)⟩
    refine ⟨s1, by simp only [exec, ea_at, hq, State.store64, hw, ite_true]; rfl, ?_⟩
    refine WP.mono (storesR_ok s1 (o + 8) rs hq hR (fun d h₁ h₂ => hc d (by omega) (by omega))
      (by omega)) fun s' ⟨hv, ho', hf, hg, hrd, hwr⟩ => ?_
    have o1 : Outside q o 8 s.mem s1.mem := writeW_outside _ _ _ (by omega)
    refine ⟨?_, (o1.mono (by omega) (by omega)).trans (ho'.mono (by omega) (by omega)), ?_,
      fun r' => hg r', hrd, hwr⟩
    · rw [List.length_cons, mv, hv, rv, ho'.word (by omega) (by omega)]
      simp only [s1, word_writeW_self]
      rw [rv_congr (s := s) (s' := s1) fun _ _ => rfl]
    · exact (Frame.refl _ _ |>.writeW (List.mem_singleton_self R) _ (hc o (Nat.le_refl _) (by omega))).trans hf

/-- The bytes of seven words. -/
theorem bytesAt_mv (m : Mem) (q : Addr) :
    Spec.X448.bytesAt m q 56 = X25519.leBytes 56 (mv m q 0 7) := by
  have h := leNum_bytesAt_mv m q 0 7
  rw [show off q 0 = q from BitVec.add_zero q] at h
  have e : Spec.X448.bytesAt m q 56 = X25519.leBytes 56 (m.read q 56).toNat :=
    X25519.bytesAt_leBytes m q 56
  rw [e, ← leNum_bytesAt_read]
  exact congrArg _ h

theorem movRsi_ok (s : State) :
    WP isa (.block ([.mov .rsi (.reg .r15)] : List Instr)) s fun s' =>
      s'.gpr .rsi = s.gpr .r15 ∧ Keeps [.rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

end VG.Proof.X448.X86_64
