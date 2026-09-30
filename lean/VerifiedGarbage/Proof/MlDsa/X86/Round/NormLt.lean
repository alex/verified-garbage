import VerifiedGarbage.Proof.MlDsa.X86.Round.Bits

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_norm_lt`

Untrusted: everything here is checked by Lean. `ebp` is all ones while
every coefficient `a` so far has `a < bound` or `q - a < bound`, and zero
otherwise (`NInv`): each comparison borrows into a mask (`nl_step`). Its low
bit is the result (`normZq_lt`, `normRq_lt`).
-/

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_ leaf)
open VG.Spec.MlDsa (q coeffAt Reduced polyAt normRq normZq normLtContract normLtSig)
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains n_eq q_eq polyAt_val normZq_lt normRq_lt)
open VG.Proof.MlKem.X86 (Only E0 P0 P0_esp P0_wr frameR retR LeafPost LeafEnd Piece satState
  toNat_ofNat32 eq_ofNat_of_toNat ptr_next cnt_next cnt_ne setWidth_append32)

structure NPre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 8 ≤ 2 ^ 32
  rd : s₀.rd = [pR (pA s₀ 0), aR s₀ 2]
  wr : s₀.wr = []
  ret_f : (retR s₀).Disjoint (pR (pA s₀ 0))
  ret_a : (retR s₀).Disjoint (aR s₀ 2)
  stk_f : (stkR s₀).Disjoint (pR (pA s₀ 0))
  stk_a : (stkR s₀).Disjoint (aR s₀ 2)
  f_fit : (arg s₀ 0).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (pA s₀ 0)

theorem NPre.of {s₀ : State} (h : (normLtContract X86.abi 16).pre s₀) : NPre s₀ := by
  sig_pre [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The public data: the stack pointer, the pointer and the bound. -/
def NPub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

/-- Coefficient `i` is within the bound. -/
def okC (s₀ : State) (i : Nat) : Prop :=
  (coeffAt s₀.mem (pA s₀ 0) i).toNat < (arg s₀ 1).toNat ∨ q - (coeffAt s₀.mem (pA s₀ 0) i).toNat < (arg s₀ 1).toNat

instance (s₀ : State) (i : Nat) : Decidable (okC s₀ i) := by unfold okC; infer_instance

/-- The mask for the first `k` coefficients. -/
def maskN (s₀ : State) (k : Nat) : BitVec 32 := if ∀ i < k, okC s₀ i then BitVec.allOnes 32 else 0

/-- After `k` coefficients. -/
structure NInv (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = arg s₀ 0 + BitVec.ofNat 32 (4 * k)
  ebx : s.gpr .ebx = arg s₀ 1
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  ebp : s.gpr .ebp = maskN s₀ k

theorem maskN_succ (s₀ : State) (k : Nat) :
    maskN s₀ k &&& ((if okC s₀ k then BitVec.allOnes 32 else 0)) = maskN s₀ (k + 1) := by
  unfold maskN
  have e : (∀ i < k + 1, okC s₀ i) ↔ ((∀ i < k, okC s₀ i) ∧ okC s₀ k) :=
    ⟨fun h' => ⟨fun i hi => h' i (by omega), h' k (by omega)⟩, fun ⟨h₁, h₂⟩ i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      exacts [h₁ i hi, h₂]⟩
  by_cases h : ∀ i < k, okC s₀ i <;> by_cases hk : okC s₀ k
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true hk),
      ite_eq_left_of_eq_true _ _ (eq_true (e.mpr ⟨h, hk⟩))]; simp
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_right_of_eq_false _ _ (eq_false hk),
      ite_eq_right_of_eq_false _ _ (eq_false fun h' => hk (e.mp h').2)]; simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (e.mp h').1)]; simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (e.mp h').1)]; simp

theorem nlBody_eq : nlBody =
    [.mov .eax (.mem (at_ .esi 0)), .mov .edx (.imm qImm), .alu .sub .edx (.reg .eax), .alu .cmp .eax (.reg .ebx),
      .alu .sbb .eax (.reg .eax), .alu .cmp .edx (.reg .ebx), .alu .sbb .edx (.reg .edx), .alu .or .eax (.reg .edx),
      .alu .and .ebp (.reg .eax), .alu .add .esi (.imm 4), .alu .sub .ecx (.imm 1)] := rfl

theorem mask_or (b c : Bool) :
    ((if b then BitVec.allOnes 32 else 0) ||| (if c then BitVec.allOnes 32 else 0)) =
      if (b || c) then BitVec.allOnes 32 else 0 := by
  cases b <;> cases c <;> simp

theorem nl_step {s₀ : State} (hp : NPre s₀) {k : Nat} (hk : k < 256) {s : State} (h : NInv s₀ k s) :
    WP isa (.block nlBody) s fun s' => NInv s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < VG.Spec.MlDsa.n := by rw [n_eq]; exact hk
  have hin : InRegions (s.rd ++ s.wr) (addr (arg s₀ 0 + BitVec.ofNat 32 (4 * k)) 0) 4 := by
    rw [addr_cf hp.f_fit hk, h.rd, h.wr, pushed_rd, P0_wr, hp.rd]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  have hv : (s.mem.readW (addr (arg s₀ 0 + BitVec.ofNat 32 (4 * k)) 0) 32) = coeffAt s₀.mem (pA s₀ 0) k := by
    rw [addr_cf hp.f_fit hk, h.mem, ← VG.Proof.MlDsa.Round.coeffAt_eq]
    exact in_keep (W := []) hp.sp (Frame.refl _ _) hp.stk_f (by simp) hk
  have ha := hp.f_red k hk'
  rw [nlBody_eq]
  refine wp_ldm h.esi hin fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_subr fun s₃ u₃ _ => wp_cmp fun s₄ f₄ c₄ _ =>
    wp_sbb_self c₄ fun s₅ u₅ => wp_cmp fun s₆ f₆ c₆ _ => wp_sbb_self c₆ fun s₇ u₇ => wp_or fun s₈ u₈ =>
    wp_and fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ => wp_subi fun s₁₁ u₁₁ _ z₁₁ =>
    WP.block_nil_iff.mpr ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [u₁₁.other _ (by decide : Reg.esp ≠ .ecx), u₁₀.other _ (by decide : Reg.esp ≠ .esi),
      u₉.other _ (by decide : Reg.esp ≠ .ebp), u₈.other _ (by decide : Reg.esp ≠ .eax), u₇.other _ (by decide : Reg.esp ≠ .edx),
      f₆.gpr, u₅.other _ (by decide : Reg.esp ≠ .eax), f₄.gpr, u₃.other _ (by decide : Reg.esp ≠ .edx),
      u₂.other _ (by decide : Reg.esp ≠ .edx), u₁.other _ (by decide : Reg.esp ≠ .eax), h.esp]
  · rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, f₆.rd, u₅.rd, f₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, f₆.wr, u₅.wr, f₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, f₆.mem, u₅.mem, f₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem]
  · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), f₆.gpr, u₅.other _ (by decide), f₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
    exact ptr_next _ _ 4
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), f₆.gpr, u₅.other _ (by decide), f₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ebx]
  · rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), f₆.gpr, u₅.other _ (by decide), f₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
    exact cnt_next hk
  · have ea₃ : s₃.gpr .eax = coeffAt s₀.mem (pA s₀ 0) k := by
      rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hv]
    have eb₃ : s₃.gpr .ebx = arg s₀ 1 := by
      rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.ebx]
    have ed₅ : (s₅.gpr .edx).toNat = q - (coeffAt s₀.mem (pA s₀ 0) k).toNat := by
      rw [u₅.other _ (by decide), f₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, hv,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact Nat.le_of_lt ha)]
      rfl
    have eb₅ : s₅.gpr .ebx = arg s₀ 1 := by rw [u₅.other _ (by decide), f₄.gpr, eb₃]
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      f₆.gpr, u₅.other _ (by decide), f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.ebp, u₈.gpr, u₇.other _ (by decide), f₆.gpr, u₅.gpr, u₇.gpr, mask_or, ← maskN_succ]
    congr 1
    rw [ea₃, eb₃, ed₅, eb₅]
    unfold okC
    by_cases h1 : (coeffAt s₀.mem (pA s₀ 0) k).toNat < (arg s₀ 1).toNat
    · simp [h1]
    · by_cases h2 : q - (coeffAt s₀.mem (pA s₀ 0) k).toNat < (arg s₀ 1).toNat
      · simp [h1, h2]
      · simp [h1, h2]
  · simp only [eval, z₁₁, Option.map_some]
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), f₆.gpr, u₅.other _ (by decide), f₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
    exact cnt_ne hk (by decide)

/-- After `nlInit`. -/
structure NS1 (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = arg s₀ 0
  ebx : s.gpr .ebx = arg s₀ 1
  ebp : s.gpr .ebp = BitVec.allOnes 32

theorem maskN_zero (s₀ : State) : maskN s₀ 0 = BitVec.allOnes 32 :=
  ite_eq_left_of_eq_true _ _ (eq_true fun _ h => absurd h (Nat.not_lt_zero _))

theorem nl_piece : Piece NPre NPub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => NInv s₀ 256 s ∧ s.gpr .eax = maskN s₀ 256 &&& 1) s₀ s') normLt := by
  refine Piece.leaf (fun _ => []) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩) (fun _ _ r hr => absurd hr (by simp)) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (B := NS1) ?_ (Piece.seq (B := fun s₀ s => NInv s₀ 256 s)
      (Piece.seq (B := fun s₀ s => NInv s₀ 0 s) ?_ ?_) ?_)).mono
      (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨by rw [h.1.mem]; exact Frame.refl _ _, h.1.esp, h.1.rd, h.1.wr⟩, h⟩)
  · refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) (by taint_decide)
    · subst e
      have hin : aR s₀ 2 ∈ s₀.rd ++ s₀.wr := by simp [hp.rd]
      obtain ⟨a₀, i₀, v₀⟩ := arg_P0 (i := 0) (by omega) hp.sp hp.sp' hin hp.stk_a
      obtain ⟨a₁, i₁, v₁⟩ := arg_P0 (i := 1) (by omega) hp.sp hp.sp' hin hp.stk_a
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at a₀ a₁
      apply WP.of_runBlock
      simp (config := {decide := true}) only [nlInit, at_, runBlock_cons, runStep_some, runBlock_nil,
        exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, a₁, i₀, i₁, v₀, v₁,
        ite_true, ite_false, Option.some.injEq, exists_eq_left']
      exact ⟨by simp, rfl, rfl, rfl, by simp, by simp, by simp⟩
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [e, e', P0_esp, P0_esp, hq.1]
  · refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)
    refine wp_movi fun s₁ u₁ => WP.block_nil_iff.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₁.other _ (by decide), h.esp]
    · rw [u₁.rd, h.rd]
    · rw [u₁.wr, h.wr]
    · rw [u₁.mem, h.mem]
    · rw [u₁.other _ (by decide), h.esi]; simp
    · rw [u₁.other _ (by decide), h.ebx]
    · rw [u₁.gpr]; rfl
    · rw [u₁.other _ (by decide), h.ebp, maskN_zero]
  · exact Piece.countLoop (by decide) (fun k s₀ s => NInv s₀ k s) [.esp, .esi, .ecx]
      (fun k hk s₀ s hp h => nl_step hp hk h)
      (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, hq.2.1]
        · rw [h.ecx, h'.ecx]) (by taint_decide)
  · refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)
    refine wp_mov fun s₁ u₁ => wp_andi fun s₂ u₂ => WP.block_nil_iff.mpr ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
    · rw [u₂.rd, u₁.rd, h.rd]
    · rw [u₂.wr, u₁.wr, h.wr]
    · rw [u₂.mem, u₁.mem, h.mem]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ebx]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ebp]
    · rw [u₂.gpr, u₁.gpr, h.ebp]

theorem maskN_and_one (s₀ : State) :
    (maskN s₀ 256 &&& 1).toNat = if ∀ i : Nat, i < 256 → okC s₀ i then 1 else 0 := by
  unfold maskN
  by_cases h : ∀ i < 256, okC s₀ i
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h)]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl

/-- Memory with the arguments `0` and `1` at `0x5004`. -/
def nlSatMem : Mem := fun a => if a = 0x5008 then 1 else 0

theorem normLt_verified : Verified X86.target normLt (normLtContract X86.abi 16) := by
  refine Piece.verified ((nl_piece.pre_mono (fun _ h => NPre.of h) fun s s' _ _ h => by
      sig_pub [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, ⟨_, hinv⟩, -, hax⟩ := hq
    refine ⟨habi, ?_⟩
    have hp := NPre.of h₀
    sig_post [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hinv]
    apply BitVec.eq_of_toNat_eq
    rw [maskN_and_one]
    have e : (∀ i < 256, okC s₀ i) ↔ normRq [polyAt s₀.mem (pA s₀ 0)] < (arg s₀ 1).toNat := by
      rw [normRq_lt]
      refine forall_congr' fun i => imp_congr_right fun hi => ?_
      rw [normZq_lt, polyAt_val hp.f_red hi]
      rfl
    by_cases h : ∀ i : Nat, i < 256 → okC s₀ i
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (e.mp h))]; rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (e.mpr h'))]
      rfl
  · let st := satState nlSatMem [⟨0, 1024⟩, ⟨0x5004, 8⟩] []
    refine ⟨st, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg st 0) = BitVec.ofNat 64 0 by decide]
           refine reduced_zero (fun a ha => ?_) 0 (by decide)
           simp only [nlSatMem]
           rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)])
        | decide +kernel

end VG.Proof.MlDsa.X86.Round
