import VerifiedGarbage.Proof.MlDsa.X86.Round.Bits

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_power2round`

Untrusted: everything here is checked by Lean. One loop over the
coefficients (`p2r_step`): `x = a + 4095`, `t1 = x >> 13` and
`t0 = (x mod 2¹³) - 4095`, plus `q` if negative (`power2Round_eq`,
`power2Round_t0`).
-/

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_ leaf)
open VG.Spec.MlDsa (q coeffAt Reduced polyAt PolyIs NatPolyIs power2Round ofInt power2RoundContract
  power2RoundSig)
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_frame coeffAt_writeW coeffAt_writeW_disjoint
  n_eq q_eq polyAt_val natPolyIs_of_toNat polyIs_of_toNat map_get power2Round_eq power2Round_t0)
open VG.Proof.MlKem.X86 (Only E0 P0 P0_esp P0_wr frameR retR LeafPost LeafEnd Piece satState
  toNat_ofNat32 eq_ofNat_of_toNat ptr_next cnt_next cnt_ne)

structure P2Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 12 ≤ 2 ^ 32
  rd : s₀.rd = [pR (pA s₀ 0)]
  wr : s₀.wr = [pR (pA s₀ 1), pR (pA s₀ 2), aR s₀ 3]
  t_1 : (pR (pA s₀ 0)).Disjoint (pR (pA s₀ 1))
  t_0 : (pR (pA s₀ 0)).Disjoint (pR (pA s₀ 2))
  t_a : (pR (pA s₀ 0)).Disjoint (aR s₀ 3)
  t1_t0 : (pR (pA s₀ 1)).Disjoint (pR (pA s₀ 2))
  t1_a : (pR (pA s₀ 1)).Disjoint (aR s₀ 3)
  t0_a : (pR (pA s₀ 2)).Disjoint (aR s₀ 3)
  ret_t : (retR s₀).Disjoint (pR (pA s₀ 0))
  ret_1 : (retR s₀).Disjoint (pR (pA s₀ 1))
  ret_0 : (retR s₀).Disjoint (pR (pA s₀ 2))
  ret_a : (retR s₀).Disjoint (aR s₀ 3)
  stk_t : (stkR s₀).Disjoint (pR (pA s₀ 0))
  stk_1 : (stkR s₀).Disjoint (pR (pA s₀ 1))
  stk_0 : (stkR s₀).Disjoint (pR (pA s₀ 2))
  stk_a : (stkR s₀).Disjoint (aR s₀ 3)
  t_fit : (arg s₀ 0).toNat + 1024 ≤ 2 ^ 32
  t1_fit : (arg s₀ 1).toNat + 1024 ≤ 2 ^ 32
  t0_fit : (arg s₀ 2).toNat + 1024 ≤ 2 ^ 32
  t_red : Reduced s₀.mem (pA s₀ 0)

theorem P2Pre.of {s₀ : State} (h : (power2RoundContract X86.abi 16).pre s₀) : P2Pre s₀ := by
  sig_pre [power2RoundContract, power2RoundSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22⟩

/-- The public data: the stack pointer and the pointers. -/
def P2Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2

/-- The `r₁` of `Power2Round(a)`. -/
def p2r1 (a : Nat) : Nat := (a + 4095) / 8192

/-- The `r₀` of `Power2Round(a)`, modulo `q`. -/
def p2r0 (a : Nat) : Nat := condAddN ((a + 4095) % 8192) 4095 q

/-- After `k` coefficients. -/
structure P2Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = arg s₀ 0 + BitVec.ofNat 32 (4 * k)
  edi : s.gpr .edi = arg s₀ 1 + BitVec.ofNat 32 (4 * k)
  ebp : s.gpr .ebp = arg s₀ 2 + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  frame : Frame [pR (pA s₀ 1), pR (pA s₀ 2)] (P0 s₀).mem s.mem
  out1 : ∀ i < k, coeffAt s.mem (pA s₀ 1) i = BitVec.ofNat 32 (p2r1 (coeffAt s₀.mem (pA s₀ 0) i).toNat)
  out0 : ∀ i < k, coeffAt s.mem (pA s₀ 2) i = BitVec.ofNat 32 (p2r0 (coeffAt s₀.mem (pA s₀ 0) i).toNat)

theorem p2rBody_eq : p2rBody =
    .mov .eax (.mem (at_ .esi 0)) :: .alu .add .eax (.imm 4095) :: .mov .edx (.reg .eax) :: .shift .shr .edx 13 ::
      .store (at_ .edi 0) .edx :: .alu .and .eax (.imm 8191) :: (condAdd .eax (.imm 4095) .edx qImm ++
      [.store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4), .alu .add .ebp (.imm 4),
        .alu .sub .ecx (.imm 1)]) := by
  simp only [p2rBody, List.cons_append, List.nil_append]

theorem p2r_step {s₀ : State} (hp : P2Pre s₀) {k : Nat} (hk : k < 256) {s : State} (h : P2Inv s₀ k s) :
    WP isa (.block p2rBody) s fun s' => P2Inv s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < VG.Spec.MlDsa.n := by rw [n_eq]; exact hk
  have hin : InRegions (s.rd ++ s.wr) (addr (arg s₀ 0 + BitVec.ofNat 32 (4 * k)) 0) 4 := by
    rw [addr_cf hp.t_fit hk, h.rd, h.wr, pushed_rd, P0_wr, hp.rd]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  have hkeep : coeffAt s.mem (pA s₀ 0) k = coeffAt s₀.mem (pA s₀ 0) k :=
    in_keep hp.sp h.frame hp.stk_t (by simp [hp.t_1, hp.t_0]) hk
  have ha := hp.t_red k hk'
  generalize ea : (coeffAt s₀.mem (pA s₀ 0) k).toNat = a at ha
  rw [q_eq] at ha
  rw [p2rBody_eq]
  refine wp_ldm h.esi hin fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_mov fun s₃ u₃ =>
    wp_shr (by decide) fun s₄ u₄ _ => ?_
  have v₁ : (s₁.gpr .eax).toNat = a := by
    rw [u₁.gpr, addr_cf hp.t_fit hk, ← VG.Proof.MlDsa.Round.coeffAt_eq, hkeep, ea]
  have v₂ : (s₂.gpr .eax).toNat = a + 4095 := by
    rw [u₂.gpr, BitVec.toNat_add, v₁]; simp; omega
  have v₄ : (s₄.gpr .edx).toNat = p2r1 a := by
    rw [u₄.gpr, u₃.gpr, BitVec.toNat_ushiftRight, v₂, Nat.shiftRight_eq_div_pow]; rfl
  have edi₄ : s₄.gpr .edi = arg s₀ 1 + BitVec.ofNat 32 (4 * k) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.edi]
  have out₁ : InRegions s₄.wr (addr (arg s₀ 1 + BitVec.ofNat 32 (4 * k)) 0) 4 := by
    rw [addr_cf hp.t1_fit hk, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, P0_wr, hp.wr]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  refine wp_stm edi₄ out₁ fun s₅ m₅ => wp_andi fun s₆ u₆ => ?_
  have v₆ : (s₆.gpr .eax).toNat = (a + 4095) % 8192 := by
    rw [u₆.gpr, m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      show (8191 : BitVec 32) = BitVec.ofNat 32 (2 ^ 13 - 1) from rfl,
      VG.Proof.MlKem.X86.toNat_and_mask _ 13 (by decide), v₂]
  refine condAdd_spec (by decide) (X := 4095) rfl
    (by rw [v₆, show qImm.toNat = 8380417 from rfl, show (4095 : BitVec 32).toNat = 4095 from rfl]; omega)
    fun s₇ o₇ v₇ => ?_
  have ebp₇ : s₇.gpr .ebp = arg s₀ 2 + BitVec.ofNat 32 (4 * k) := by
    rw [o₇.gpr _ (by decide), u₆.other _ (by decide), m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ebp]
  have out₀ : InRegions s₇.wr (addr (arg s₀ 2 + BitVec.ofNat 32 (4 * k)) 0) 4 := by
    rw [addr_cf hp.t0_fit hk, o₇.wr, u₆.wr, m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, P0_wr, hp.wr]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  have g₇ : ∀ r, r ≠ .eax → r ≠ .edx → s₇.gpr r = s.gpr r := fun r h1 h2 => by
    rw [o₇.gpr r (by simp [h1, h2]), u₆.other r h1, m₅.gpr, u₄.other r h2, u₃.other r h2, u₂.other r h1,
      u₁.other r h1]
  have m₇ : s₇.mem = (s.mem.writeW (coeffAddr (pA s₀ 1) k) (s₄.gpr .edx)) := by
    rw [o₇.mem, u₆.mem, m₅.mem, addr_cf hp.t1_fit hk, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_stm ebp₇ out₀ fun s₈ m₈ => wp_addi fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ => wp_addi fun s₁₁ u₁₁ =>
    wp_subi fun s₁₂ u₁₂ _ z₁₂ => WP.block_nil_iff.mpr ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_,
      fun i hi => ?_⟩, ?_⟩
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      m₈.gpr, g₇ _ (by decide) (by decide), h.esp]
  · rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, m₈.rd, o₇.rd, u₆.rd, m₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, m₈.wr, o₇.wr, u₆.wr, m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, m₈.gpr,
      g₇ _ (by decide) (by decide), h.esi]
    exact ptr_next _ _ 4
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), m₈.gpr,
      g₇ _ (by decide) (by decide), h.edi]
    exact ptr_next _ _ 4
  · rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), m₈.gpr, ebp₇]
    exact ptr_next _ _ 4
  · rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), m₈.gpr,
      g₇ _ (by decide) (by decide), h.ecx]
    exact cnt_next hk
  · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, m₈.mem, addr_cf hp.t0_fit hk, m₇]
    exact (h.frame.writeW (by simp) _ (coeff_contains _ hk')).writeW (by simp) _ (coeff_contains _ hk')
  · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, m₈.mem, addr_cf hp.t0_fit hk, m₇, coeffAt_writeW_disjoint _ hp.t1_t0 (coeff_contains _ hk') (by rw [n_eq]; omega),
      coeffAt_writeW _ _ (by rw [n_eq]; omega) hk']
    by_cases e : k = i
    · subst e; rw [ite_eq_left rfl, ea]; exact eq_ofNat_of_toNat v₄
    · rw [ite_eq_right e]; exact h.out1 i (by omega)
  · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, m₈.mem, addr_cf hp.t0_fit hk, m₇, coeffAt_writeW _ _ (by rw [n_eq]; omega) hk',
      coeffAt_writeW_disjoint _ hp.t1_t0.symm (coeff_contains _ hk') (by rw [n_eq]; omega)]
    by_cases e : k = i
    · subst e; rw [ite_eq_left rfl, ea]
      refine eq_ofNat_of_toNat (v₇.trans ?_)
      rw [v₆]; rfl
    · rw [ite_eq_right e]; exact h.out0 i (by omega)
  · simp only [eval, z₁₂, Option.map_some]
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), m₈.gpr,
      g₇ _ (by decide) (by decide), h.ecx]
    exact cnt_ne hk (by decide)

/-- After `p2rInit`. -/
structure P2S (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = arg s₀ 0
  edi : s.gpr .edi = arg s₀ 1
  ebp : s.gpr .ebp = arg s₀ 2

theorem p2rInit_piece : Piece P2Pre P2Pub (fun s₀ s => s = P0 s₀) P2S (.block p2rInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) (by taint_decide)
  · subst e
    have hin : aR s₀ 3 ∈ s₀.rd ++ s₀.wr := by simp [hp.wr]
    obtain ⟨a₀, i₀, v₀⟩ := arg_P0 (i := 0) (by omega) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₁, i₁, v₁⟩ := arg_P0 (i := 1) (by omega) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₂, i₂, v₂⟩ := arg_P0 (i := 2) (by omega) hp.sp hp.sp' hin hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at a₀ a₁ a₂
    apply WP.of_runBlock
    simp (config := {decide := true}) only [p2rInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, a₁, a₂, i₀, i₁, i₂, v₀, v₁, v₂,
      ite_true, ite_false, Option.some.injEq, exists_eq_left']
    exact ⟨by simp, rfl, rfl, rfl, by simp, by simp, by simp⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

theorem p2r_piece : Piece P2Pre P2Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (P2Inv s₀ 256) s₀ s')
    power2Round := by
  refine Piece.leaf (fun s₀ => [pR (pA s₀ 1), pR (pA s₀ 2)]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩) (fun _ hp r hr => ?_) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq p2rInit_piece (Piece.seq (B := (P2Inv · 0)) ?_ ?_)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨by rw [← stk_eq hp.sp]; exact hp.stk_1, hp.ret_1⟩
    · exact ⟨by rw [← stk_eq hp.sp]; exact hp.stk_0, hp.ret_0⟩
  · refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)
    refine wp_movi fun s₁ u₁ => WP.block_nil_iff.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega),
      fun i hi => absurd hi (by omega)⟩
    · rw [u₁.other _ (by decide), h.esp]
    · rw [u₁.rd, h.rd]
    · rw [u₁.wr, h.wr]
    · rw [u₁.other _ (by decide), h.esi]; simp
    · rw [u₁.other _ (by decide), h.edi]; simp
    · rw [u₁.other _ (by decide), h.ebp]; simp
    · rw [u₁.gpr]; rfl
    · rw [u₁.mem, h.mem]; exact Frame.refl _ _
  · exact Piece.countLoop (by decide) (fun k s₀ s => P2Inv s₀ k s) [.esp, .esi, .edi, .ebp, .ecx]
      (fun k hk s₀ s hp h => p2r_step hp hk h)
      (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, hq.2.1]
        · rw [h.edi, h'.edi, hq.2.2.1]
        · rw [h.ebp, h'.ebp, hq.2.2.2]
        · rw [h.ecx, h'.ecx]) (by taint_decide)

theorem p2r0_lt {a : Nat} : p2r0 a < 2 ^ 32 := by
  have hq : q = 8380417 := rfl
  have := Nat.mod_lt (a + 4095) (show 8192 > 0 by decide)
  unfold p2r0 condAddN; split <;> omega

theorem p2r_post {s₀ s : State} (hp : P2Pre s₀) (hinv : P2Inv s₀ 256 s) :
    NatPolyIs s.mem (pA s₀ 1) ((polyAt s₀.mem (pA s₀ 0)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs s.mem (pA s₀ 2) ((polyAt s₀.mem (pA s₀ 0)).map fun c => ofInt (power2Round c).2) := by
  refine ⟨natPolyIs_of_toNat fun i hi => ?_, polyIs_of_toNat fun i hi => ?_⟩
  · rw [hinv.out1 i hi, map_get _ _ hi, power2Round_eq, polyAt_val hp.t_red hi,
      toNat_ofNat32 (by have := hp.t_red i hi; unfold p2r1; rw [q_eq] at this; omega)]
    rfl
  · rw [hinv.out0 i hi, map_get _ _ hi, power2Round_t0, polyAt_val hp.t_red hi, toNat_ofNat32 p2r0_lt]
    rfl

/-- Memory with the arguments `0x400`, `0` and `0x800` at `0x5004`. -/
def p2rSatMem : Mem := fun a => if a = 0x5005 then 4 else if a = 0x500d then 8 else 0

theorem p2rSat_zero (a : Addr) (ha : a.toNat < 0x5000) : p2rSatMem a = 0 := by
  simp only [p2rSatMem]
  rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)]

theorem power2Round_verified : Verified X86.target power2Round (power2RoundContract X86.abi 16) := by
  refine Piece.verified ((p2r_piece.pre_mono (fun _ h => P2Pre.of h) fun s s' _ _ h => by
      sig_pub [power2RoundContract, power2RoundSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [power2RoundContract, power2RoundSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact p2r_post (P2Pre.of h₀) hinv
  · let st := satState p2rSatMem [⟨0x400, 1024⟩] [⟨0, 1024⟩, ⟨0x800, 1024⟩, ⟨0x5004, 12⟩]
    have a0 : arg st 0 = 0x400 := by decide
    have a1 : arg st 1 = 0 := by decide
    have a2 : arg st 2 = 0x800 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [power2RoundContract, power2RoundSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, reduced_zero p2rSat_zero 0x400 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)

end VG.Proof.MlDsa.X86.Round
