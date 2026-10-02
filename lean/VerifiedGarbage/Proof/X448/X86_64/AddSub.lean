import VerifiedGarbage.Proof.X448.X86_64.Field
import VerifiedGarbage.Proof.Framework.Range

/-!
# X448 on x86-64: addition, subtraction, `a24` and the swap

`add`, `sub` and `mulSmall` as carry chains, multiply-accumulate steps and
folds, and `cswap` word by word (`wp_range_flatMap`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448
open VG.Spec.X448 (P)

theorem words_eq (o : Nat) : words o =
    Src.mem (sc o) :: ([o + 8, o + 16, o + 24, o + 32, o + 40, o + 48].map fun d => Src.mem (sc d)) :=
  rfl

theorem wv_words (m : Mem) (base : Addr) (o : Nat) :
    wv (word m base o :: [o + 8, o + 16, o + 24, o + 32, o + 40, o + 48].map fun d => word m base d) =
      fe m base o := by
  simp only [wv, List.map_cons, List.map_nil, mv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero,
    Nat.add_zero]

theorem wv_words' (m : Mem) (base : Addr) (o : Nat) :
    wv ([o, o + 8, o + 16, o + 24, o + 32, o + 40, o + 48].map fun d => word m base d) =
      fe m base o := wv_words m base o

theorem W_len : W.length = 7 := rfl

/-- `[o] = [a] + [b]`. -/
theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (add o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a + F s.mem base b := by
  have ha' : a + 56 ≤ 1536 := ha
  have hb' : b + 56 ≤ 1536 := hb
  have ho' : o + 56 ≤ 1536 := ho
  rw [add, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok hs a W W_nodup (by decide) (by rw [W_len]; omega))
    fun s1 ⟨_, v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff, words_eq]
  refine WP.mono (add_chain_ok W s1 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] _ _
    (word s1.mem base b) _ (fun _ h => h) W_nodup rfl (stable_sc hs1 (by decide) (by omega))
    (stable_scs hs1 (by decide) _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)))
    fun s2 ⟨c2, hc2, e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (carryOut_ok s2 hc2) fun s3 ⟨e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fold2_ok s3 (by rw [e3]; cases c2 <;> decide)) fun s4 ⟨e4, k4⟩ => ?_
  have hs4 := ((hs1.of_keeps k2 (by decide)).of_keeps k3 (by decide)).of_keeps k4 (by decide)
  refine WP.mono (stores_ok hs4 o W (by rw [W_len]; omega)) fun s5 ⟨e5, o5, g5, rd5, wr5⟩ => ?_
  rw [W_len] at e5 o5
  have K : Keeps clob s s4 := (k1.mono W_clob).trans <| (k2.mono (by decide)).trans <|
    (k3.mono (by decide)).trans (k4.mono (by decide))
  refine ⟨⟨fun r hr => (g5 r).trans (K.1 r hr), rd5.trans K.2.2.1, wr5.trans K.2.2.2,
    by rw [← K.2.1]; exact o5.left ACC 112⟩, toFe_add ?_⟩
  have w32 : rv s3 W = rv s2 W := k3.rv_eq (by decide)
  rw [len64_7, W_lit, wv_words, v1, W_len] at e2
  rw [k1.2.1] at e2
  change mv s5.mem base o 7 % P = (mv s.mem base a 7 + fe s.mem base b) % P
  rw [e5, e4, w32, e3, e2]

/-- `[o] = [a] - [b]`. -/
theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (sub o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a - F s.mem base b := by
  have ha' : a + 56 ≤ 1536 := ha
  have hb' : b + 56 ≤ 1536 := hb
  have ho' : o + 56 ≤ 1536 := ho
  simp only [sub, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs a W W_nodup (by decide) (by rw [W_len]; omega))
    fun s1 ⟨_, v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff, words_eq]
  refine WP.mono (sub_chain_ok W s1 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] _ _
    (word s1.mem base b) _ (fun _ h => h) W_nodup rfl (stable_sc hs1 (by decide) (by omega))
    (stable_scs hs1 (by decide) _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)))
    fun s2 ⟨c0, hc0, e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (carryOut_ok s2 hc0) fun s3 ⟨e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (unfold_ok s3 (by rw [e3]; cases c0 <;> decide)) fun s4 ⟨c1, hc1, e4, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (carryOut_ok s4 hc1) fun s5 ⟨e5, k5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (unfold_ok s5 (by rw [e5]; cases c1 <;> decide)) fun s6 ⟨c2, _, e6, k6⟩ => ?_
  have hs6 := ((((hs1.of_keeps k2 (by decide)).of_keeps k3 (by decide)).of_keeps k4
    (by decide)).of_keeps k5 (by decide)).of_keeps k6 (by decide)
  refine WP.mono (stores_ok hs6 o W (by rw [W_len]; omega)) fun s7 ⟨e7, o7, g7, rd7, wr7⟩ => ?_
  rw [W_len] at e7 o7
  have K : Keeps clob s s6 := (k1.mono W_clob).trans <| (k2.mono (by decide)).trans <|
    (k3.mono (by decide)).trans <| (k4.mono (by decide)).trans <| (k5.mono (by decide)).trans
      (k6.mono (by decide))
  refine ⟨⟨fun r hr => (g7 r).trans (K.1 r hr), rd7.trans K.2.2.1, wr7.trans K.2.2.2,
    by rw [← K.2.1]; exact o7.left ACC 112⟩, toFe_sub ?_⟩
  have w32 : rv s3 W = rv s2 W := k3.rv_eq (by decide)
  have w54 : rv s5 W = rv s4 W := k5.rv_eq (by decide)
  rw [len64_7, W_lit, wv_words, v1, W_len, k1.2.1] at e2
  rw [e3, w32] at e4
  rw [e5, w54] at e6
  have l2 := rv_lt s2 W; have l4 := rv_lt s4 W; have l6 := rv_lt s6 W
  rw [len_W] at l2 l4 l6
  have b0 := Bool.toNat_le c0; have b1 := Bool.toNat_le c1; have b2 := Bool.toNat_le c2
  have hc2 : c2.toNat = 0 := by
    rcases Nat.lt_or_ge c1.toNat 1 with h | h
    · omega
    · rcases Nat.lt_or_ge c2.toNat 1 with h' | h'
      · omega
      · exfalso; omega
  have hP := P_eq
  have p0 : 2 ^ 448 * c0.toNat = P * c0.toNat + (2 ^ 224 + 1) * c0.toNat := by
    rw [hP, Nat.add_mul]
  have p1 : 2 ^ 448 * c1.toNat = P * c1.toNat + (2 ^ 224 + 1) * c1.toNat := by
    rw [hP, Nat.add_mul]
  have key : rv s6 W + fe s.mem base b = fe s.mem base a + P * (c0.toNat + c1.toNat) := by
    rw [Nat.mul_add P]
    generalize P * c0.toNat = q0 at p0 ⊢
    generalize P * c1.toNat = q1 at p1 ⊢
    clear hP
    simp only [fe] at e2 ⊢
    omega
  change (mv s7.mem base o 7 + fe s.mem base b) % P = _
  rw [e7, key, Nat.add_mul_mod_self_left]

theorem init_ok (s : State) (k : BitVec 32) :
    WP isa (.block (([.mov32 .rcx (.imm k), .mov32 .rbp (.imm 0)] : List Instr) ++
      W.map fun r => .mov32 r (.imm 0))) s fun s' =>
      rv s' W = 0 ∧ s'.gpr .rbp = 0 ∧ s'.gpr .rcx = k.setWidth 64 ∧ Keeps (.rcx :: .rbp :: W) s s' := by
  apply WP.of_runBlock
  simp only [W, List.map_cons, List.map_nil, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, readSrc32, Option.map_some, State.setReg32,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [rv, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem ldStable_scs {X : List Reg} {s : State} {base : Addr} (hs : Scr s base) (hX : .rdi ∉ X) :
    ∀ ds : List Nat, (∀ d ∈ ds, d + 8 ≤ 8192) →
      List.Forall₂ (LdStable X s) (ds.map fun d => .mov .rax (.mem (sc d)))
        (ds.map fun d => word s.mem base d)
  | [], _ => .nil
  | d :: ds, h => .cons (ldStable_sc hs hX (h d List.mem_cons_self))
      (ldStable_scs hs hX ds fun d' hd => h d' (List.mem_cons_of_mem _ hd))

/-- `[o] = k · [a]`, for `k < 2¹⁶`. -/
theorem mulSmall_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) {k : BitVec 32} (hk : k.toNat < 2 ^ 16) :
    WP isa (.block (mulSmall o a k)) s fun s' =>
      Op base o s s' ∧ fe s'.mem base o % P = k.toNat * fe s.mem base a % P := by
  have ha' : a + 56 ≤ 1536 := ha
  have ho' : o + 56 ≤ 1536 := ho
  simp only [mulSmall, List.append_assoc]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (init_ok s k) fun s1 ⟨z1, b1, c1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff, show (List.range 7).map (fun i => Instr.mov .rax (.mem (sc (a + 8 * i)))) =
    [a, a + 8, a + 16, a + 24, a + 32, a + 40, a + 48].map fun d => .mov .rax (.mem (sc d)) from rfl]
  refine WP.mono (mulSteps_ok [.rax, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s1 W _
    _ s1 (Keeps.refl _ _) (by decide) (by decide) (by decide) rfl
    (ldStable_scs hs1 (by decide) _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)))
    fun s2 ⟨e2, k2⟩ => ?_
  rw [len_W, z1, b1, c1, wv_words', k1.2.1] at e2
  have hk' : (k.setWidth 64).toNat = k.toNat := toNat_setWidth_32_64 k
  rw [hk', toNat_zero64] at e2
  rw [WP.block_append_iff]
  have hs2 := hs1.of_keeps k2 (by decide)
  refine WP.mono (show WP isa (.block [.mov .r15 (.reg .rbp)]) s2 fun s' =>
      s'.gpr .r15 = s2.gpr .rbp ∧ Keeps [.r15] s2 s' by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr]) fun s3 ⟨e3, k3⟩ => ?_
  have hlt := fe_lt s.mem base a
  have hb : (s2.gpr .rbp).toNat < 2 ^ 16 := by
    have h2 : k.toNat * fe s.mem base a < 2 ^ 448 * 2 ^ 16 := by
      rw [Nat.mul_comm (2 ^ 448)]; exact Nat.mul_lt_mul'' hk hlt
    have h1 : 2 ^ 448 * (s2.gpr .rbp).toNat ≤ k.toNat * fe s.mem base a := by
      generalize k.toNat * fe s.mem base a = X at e2; omega
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h1 h2)
  rw [WP.block_append_iff]
  refine WP.mono (fold2_ok s3 (by rw [e3]; omega)) fun s4 ⟨e4, k4⟩ => ?_
  have hs4 := (hs2.of_keeps k3 (by decide)).of_keeps k4 (by decide)
  refine WP.mono (stores_ok hs4 o W (by rw [W_len]; omega)) fun s5 ⟨e5, o5, g5, rd5, wr5⟩ => ?_
  rw [W_len] at e5 o5
  have K : Keeps clob s s4 := (k1.mono (by decide)).trans <| (k2.mono (by decide)).trans <|
    (k3.mono (by decide)).trans (k4.mono (by decide))
  refine ⟨⟨fun r hr => (g5 r).trans (K.1 r hr), rd5.trans K.2.2.1, wr5.trans K.2.2.2,
    by rw [← K.2.1]; exact o5.left ACC 112⟩, ?_⟩
  have w32 : rv s3 W = rv s2 W := k3.rv_eq (by decide)
  change mv s5.mem base o 7 % P = _
  rw [e5, e4, w32, e3, e2, Nat.zero_add]

end VG.Proof.X448.X86_64
