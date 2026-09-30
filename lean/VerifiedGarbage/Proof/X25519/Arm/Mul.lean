import VerifiedGarbage.Proof.X25519.Arm.AddSub

/-!
# X25519 on 32-bit ARM: multiplication

Untrusted: everything here is checked by Lean. `mul o x y` computes the 32
limbs of `[x] · [y]` in `ACC`, row by row (`row_ok`, the loop invariant
`RowInv`: after `i` rows, `ACC[0, i + 16)` holds the limbs of
`x_{<i} · y`), then stores at `o` a number congruent to it, with limbs below
`2¹⁶` (`mul_ok`).
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P)

/-- Limb `k` of the product in `ACC`. -/
def accw (m : Mem) (B : Addr) (k : Nat) : Nat := wd m B (ACC + 4 * k)

theorem wd_shift (m : Mem) (B : Addr) (a d : Nat) : wd m (B + BitVec.ofNat 64 a) d = wd m B (a + d) := by
  unfold wd; rw [Offset.add_add]

theorem ACC_eq : ACC = 1152 := rfl

section
variable {b : BitVec 32}

theorem addr7 (hfit : b.toNat + 4096 ≤ 2 ^ 32) {i : Nat} (hi : 4 * i < 4096) :
    State.addr (b + BitVec.ofNat 32 (4 * i)) = State.addr b + BitVec.ofNat 64 (4 * i) :=
  addr_add (by omega)

theorem toNat7 (hfit : b.toNat + 4096 ≤ 2 ^ 32) {i : Nat} (hi : 4 * i < 4096) :
    (b + BitVec.ofNat 32 (4 * i)).toNat = b.toNat + 4 * i := by
  rw [toNat_add_lt (by rw [toNat_imm (by omega)]; omega), toNat_imm (by omega)]

theorem ea7 (hfit : b.toNat + 4096 ≤ 2 ^ 32) {i d : Nat} (h : 4 * i + d < 4096) :
    State.addr (b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 d) =
      State.addr b + BitVec.ofNat 64 (4 * i + d) := by
  rw [Offset.add_add]; exact addr_add (by omega)

theorem zeroAcc_ok {s : State} (hc : Ctx b s) :
    WP isa (.block zeroAcc) s fun s' => (∀ j < 16, accw s'.mem (State.addr b) j = 0) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 64⟩] s.mem s'.mem ∧ Rest [.r3] s s' := by
  have hA := ACC_eq
  unfold zeroAcc storeN
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r3]) (by decide)) (by decide)
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ j < n, accw s'.mem (State.addr b) j = 0) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 64⟩] s1.mem s'.mem ∧ Rest [] s1 s' ∧ s'.gpr .r3 = 0)
    (fun n s' hn ⟨h1, h2, h3, h4⟩ => ?_) 16 (Nat.le_refl _) s1
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Rest.refl _ _, u1.gpr⟩)
    fun s' ⟨h1, h2, h3, _⟩ => ⟨h1, by rw [← u1.mem]; exact h2,
      (u1.rest (by decide)).trans (h3.mono (by decide))⟩
  refine str0_ok (hc1.of_rest h3 (by decide)) (d := ACC + 4 * n) (by omega) fun s2 u2 =>
    WP.block_nil ⟨fun j hj => ?_, ?_, h3.trans (u2.rest _), by rw [u2.gpr, h4]⟩
  · rw [accw, u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h1 j hj
    · rw [wd_write_self, h4]; rfl
  · rw [u2.mem]
    exact h2.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

/-- The loop invariant of the rows of `mul o x y` from `s0`, after `i` rows. -/
structure RowInv (b : BitVec 32) (x y : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob s0 s
  r6 : s.gpr .r6 = mask16
  r8 : s.gpr .r8 = 38
  r7 : s.gpr .r7 = b + BitVec.ofNat 32 (4 * i)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (16 - i)
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s0.mem s.mem
  lt : ∀ k < i + 16, accw s.mem (State.addr b) k < 65536
  val : val16 (accw s.mem (State.addr b)) (i + 16) =
    val16 (limb s0.mem (State.addr b) x) i * V s0.mem (State.addr b) y

theorem mulPre_ok {x y : Nat} {s : State} (hc : Ctx b s) :
    WP isa (.block (prologue ++ zeroAcc ++ ([.mov .r7 (.reg .r0), .mov .r9 (.imm 16)] : List Instr))) s
      (RowInv b x y s 0) := by
  rw [List.append_assoc]
  refine WP.append prologue_ok fun s1 ⟨h6, h8, h5, hr1, hm1⟩ => ?_
  have hc1 : Ctx b s1 := hc.of_rest hr1 (by decide)
  refine WP.append (zeroAcc_ok hc1) fun s2 ⟨hz, hf2, hr2⟩ => ?_
  have hc2 : Ctx b s2 := hc1.of_rest hr2 (by decide)
  refine wp_mov (op2_reg _ _) fun s3 u3 => wp_mov (op2_imm (by decide)) fun s4 u4 => WP.block_nil ?_
  have hr : Rest clob s s4 :=
    (hr1.mono (by decide)).trans ((hr2.mono (by decide)).trans ((u3.rest (by decide)).trans
      (u4.rest (by decide))))
  have hr' : Rest [.r3, .r7, .r9] s1 s4 :=
    (hr2.mono (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
  have hm4 : s4.mem = s2.mem := by rw [u4.mem, u3.mem]
  refine ⟨hc.of_rest hr (by decide), hr, by rw [hr'.gpr _ (by decide), h6],
    by rw [hr'.gpr _ (by decide), h8], ?_, u4.gpr, ?_, fun k hk => ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.gpr, hc2.r0]; exact (BitVec.add_zero b).symm
  · rw [hm4, ← hm1]; exact hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
  · rw [accw, hm4]; unfold accw at hz; rw [hz k (by omega)]; decide
  · rw [hm4, val16_congr (g := fun _ => 0) (fun k hk => hz k hk), val16_zero_fn]
    exact (Nat.zero_mul _).symm

theorem row_ok {x y : Nat} (hx : x + 64 ≤ ACC) (hy : y + 64 ≤ ACC) {s0 : State}
    (hlx : Lim s0.mem (State.addr b) x) (hly : Lim s0.mem (State.addr b) y) {i : Nat} (hi : i < 16)
    {s : State} (h : RowInv b x y s0 i s) :
    WP isa (.block (row x y)) s fun s' =>
      RowInv b x y s0 (i + 1) s' ∧ s'.z = decide (16 - (i + 1) = 0) := by
  have hA := ACC_eq
  have hfit := h.ctx.fit
  have hframe0 : ∀ z : Nat, z + 64 ≤ ACC → ∀ k < 16,
      limb s.mem (State.addr b) z k = limb s0.mem (State.addr b) z k := fun z hz k hk =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  simp only [row, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (x + 4 * i)) (by omega)
    (by rw [h.r7, ea7 hfit (by omega), Nat.add_comm]) (h.ctx.inR (by omega)) fun s1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have hr2 : Rest [.r1, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := h.ctx.of_rest hr2 (by decide)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have e1 : (s2.gpr .r1).toNat = limb s0.mem (State.addr b) x i := by
    rw [u2.other _ (by decide), u1.gpr, ← hframe0 x hx i hi]; rfl
  have e7 : s2.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hr2.gpr _ (by decide), h.r7]
  have P7 : State.addr (s2.gpr .r7) = State.addr b + BitVec.ofNat 64 (4 * i) := by
    rw [e7]; exact addr7 hfit (by omega)
  have hlt : ∀ j < 16, rowC (accw s.mem (State.addr b)) (limb s0.mem (State.addr b) x)
      (limb s0.mem (State.addr b) y) i j + 65536 ≤ 2 ^ 32 := fun j hj =>
    rowC_le (hlx i hi) (hly j hj) (h.lt (i + j) (by omega))
  refine WP.append (pass_ok (rb := .r7) (o := ACC) (s0 := s2)
    (c := rowC (accw s.mem (State.addr b)) (limb s0.mem (State.addr b) x) (limb s0.mem (State.addr b) y) i)
    (cin := 0) (by decide) (by omega) (by rw [e7, toNat7 hfit (by omega)]; omega)
    (fun k hk => by rw [P7, Offset.add_add]; exact hc2.inW (by omega))
    (by rw [hr2.gpr _ (by decide), h.r6]) (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    have hc' : Ctx b s' := hc2.of_rest hp'.rest (by decide)
    have hf' : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [P7, Offset.add_add] at this
    simp only [rowSrc]
    refine ldr0_ok hc' (d := y + 4 * k) (by omega) fun t1 v1 => ?_
    refine wp_mul fun t2 v2 => ?_
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 4 * k))) (by omega)
      (by rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), e7,
        ea7 hfit (by omega)]) (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc'.inR (by omega))
      fun t3 v3 => ?_
    refine wp_dp (op2_reg _ _) fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have ey : (t1.gpr .r2).toNat = limb s0.mem (State.addr b) y k := by
        rw [v1.gpr, ← hframe0 y hy k hk, ← hm2]
        show wd s'.mem _ _ = wd s2.mem _ _
        exact wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      have ea : (t1.gpr .r1).toNat = limb s0.mem (State.addr b) x i := by
        rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
      have hab := Nat.mul_le_mul (Nat.le_of_lt_succ (hlx i hi)) (Nat.le_of_lt_succ (hly k hk))
      have e2 : (t2.gpr .r2).toNat = limb s0.mem (State.addr b) x i * limb s0.mem (State.addr b) y k := by
        rw [v2.gpr, toNat_mul_lt (by rw [ea, ey]; omega), ea, ey]
      have e3 : (t3.gpr .r3).toNat = accw s.mem (State.addr b) (i + k) := by
        rw [v3.gpr, v2.mem, v1.mem, accw, ← hm2]
        show wd s'.mem _ _ = _
        rw [wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)]
        congr 1; omega
      have := hlt k hk
      rw [v4.gpr]
      show (t3.gpr .r3 + t3.gpr .r2).toNat = _
      rw [v3.other .r2 (by decide), toNat_add_lt (by rw [e3, e2]; simp only [rowC] at this; omega), e3, e2,
        rowC, Nat.add_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · -- The carry, and the next row.
    have hc3 : Ctx b s3 := hc2.of_rest hp.rest (by decide)
    have e7' : s3.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hp.rest.gpr _ (by decide), e7]
    refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 64))) (by omega)
      (by rw [e7', ea7 hfit (by omega)]) (hc3.inW (by omega)) fun s4 u4 => ?_
    refine wp_dp (op2_imm (by decide)) fun s5 u5 => wp_subs (op2_imm (by decide)) fun s6 u6 hz => ?_
    refine WP.block_nil ?_
    have hr6 : Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9] s s6 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans (u6.rest (by decide)))))
    have hm6 : s6.mem = s3.mem.writeW (State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 64))) (s3.gpr .r5) := by
      rw [u6.mem, u5.mem, u4.mem]
    have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 64⟩] s.mem s3.mem := by
      have := hp.frame; rw [P7, Offset.add_add] at this; rw [← hm2]; exact this
    have hr9 : s6.gpr .r9 = BitVec.ofNat 32 (16 - (i + 1)) := by
      rw [u6.gpr, u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide), hr2.gpr _ (by decide), h.r9]
      have t1 : (1 : BitVec 32).toNat = 1 := rfl
      apply BitVec.eq_of_toNat_eq
      rw [toNat_sub_le (by rw [toNat_imm (by omega), t1]; omega), toNat_imm (by omega), toNat_imm (by omega),
        t1]
      omega
    -- The limbs of `ACC` after the row.
    have hacc : ∀ k < i + 17, accw s6.mem (State.addr b) k =
        rowAcc (accw s.mem (State.addr b)) (limb s0.mem (State.addr b) x) (limb s0.mem (State.addr b) y) i k := by
      intro k hk
      rw [accw, hm6]
      rcases Nat.lt_or_ge k (i + 16) with hk' | hk'
      · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
        rcases Nat.lt_or_ge k i with hki | hki
        · rw [wd_frame hpf fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)]
          simp only [rowAcc, hki, ite_true]; rfl
        · have := hp.outs (k - i) (by omega)
          rw [P7, wd_shift, show 4 * i + (ACC + 4 * (k - i)) = ACC + 4 * k by omega] at this
          rw [this]
          simp only [rowAcc, show ¬ k < i by omega, hk', ite_false, ite_true]
      · rw [show ACC + 4 * k = 4 * i + (ACC + 64) by omega, wd_write_self, hp.r5]
        simp only [rowAcc, show ¬ k < i by omega, show ¬ k < i + 16 by omega, ite_false]
    refine ⟨⟨hc3.of_rest ((u4.rest [.r7, .r9]).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))
        (by decide), h.rest.trans (hr6.mono (by decide)), by rw [hr6.gpr _ (by decide), h.r6],
      by rw [hr6.gpr _ (by decide), h.r8], ?_, hr9, ?_, fun k hk => ?_, ?_⟩, ?_⟩
    · rw [u6.other _ (by decide), u5.gpr, u4.gpr, e7']
      show b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _
      rw [Offset.add_add, Nat.mul_succ]
    · rw [hm6]
      refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
    · rw [hacc k hk]
      exact rowAcc_lt (fun k hk => h.lt k (by omega)) hlt k hk
    · rw [val16_congr hacc]; exact row_val h.val
    · rw [hz, ← u6.gpr, hr9, ofNat_beq_zero (by omega)]

theorem mul_ok {o x y : Nat} (ho : o + 64 ≤ ACC) (hx : x + 64 ≤ ACC) (hy : y + 64 ≤ ACC) {s : State}
    (hc : Ctx b s) (hlx : Lim s.mem (State.addr b) x) (hly : Lim s.mem (State.addr b) y) :
    WP isa (mul o x y) s fun s' =>
      Rest clob s s' ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem s'.mem ∧
      Lim s'.mem (State.addr b) o ∧
      V s'.mem (State.addr b) o % P = (V s.mem (State.addr b) x * V s.mem (State.addr b) y) % P := by
  have hA := ACC_eq
  unfold mul
  refine WP.seq (WP.mono (mulPre_ok (x := x) (y := y) hc) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (Q := RowInv b x y s 16) (WP.loop (M := isa)
    (fun n s' => ∃ i, n = 16 - i ∧ i < 16 ∧ RowInv b x y s i s') ?_ 16 s1 ⟨0, rfl, by decide, h1⟩)
    fun s2 h2 => ?_)
  · rintro n s' ⟨i, rfl, hi, hr⟩
    refine WP.mono (row_ok hx hy hlx hly hi hr) fun s'' ⟨hr', hz⟩ => ?_
    by_cases h16 : i + 1 = 16
    · refine .inl ⟨by rw [eval_ne, hz]; simp [h16], ?_⟩
      rw [h16] at hr'; exact hr'
    · exact .inr ⟨by rw [eval_ne, hz]; simp; omega, 16 - (i + 1), by omega, i + 1, rfl, by omega, hr'⟩
  · refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
    have hc3 : Ctx b s3 := h2.ctx.of_rest (u3.rest (ws := [.r5]) (by decide)) (by decide)
    have hl32 : ∀ k < 32, accw s2.mem (State.addr b) k < 65536 := h2.lt
    have hv : val16 (accw s2.mem (State.addr b)) 32 = V s.mem (State.addr b) x * V s.mem (State.addr b) y :=
      h2.val
    have hlo := val16_lt (f := accw s2.mem (State.addr b)) (n := 16) fun k hk => hl32 k (by omega)
    have hhi := val16_lt (f := fun k => accw s2.mem (State.addr b) (16 + k)) (n := 16) fun k hk =>
      hl32 (16 + k) (by omega)
    have hlox : ∀ z : Nat, z + 64 ≤ ACC → ∀ k < 16,
        limb s2.mem (State.addr b) z k = limb s.mem (State.addr b) z k := fun z hz k hk =>
      wd_frame h2.frame fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    refine WP.mono (passTail'_ok (c := foldC (accw s2.mem (State.addr b))) (by omega)
      (foldC_le hl32) (by rw [val16_foldC]; rw [show 16 * 16 = 256 from rfl] at hlo hhi; omega) hc3
      (by rw [u3.other _ (by decide), h2.r6]) (by rw [u3.other _ (by decide), h2.r8]) u3.gpr ?_)
      fun s4 ⟨hr4, hf4, hl4, hv4⟩ => ⟨h2.rest.trans ((u3.rest (by decide)).trans (hr4.mono (by decide))),
        ?_, hl4, ?_⟩
    · intro k hk s' hp
      have hc' : Ctx b s' := hc3.of_rest hp.rest (by decide)
      refine ldr0_ok hc' (d := ACC + 4 * k) (by omega) fun t1 v1 => ?_
      refine ldr0_ok (hc'.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide)) (d := ACC + 64 + 4 * k)
        (by omega) fun t2 v2 => ?_
      refine wp_mul fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 => WP.block_nil ⟨?_, ?_, by
        rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
      · have el : (t1.gpr .r3).toNat = accw s2.mem (State.addr b) k := by
          rw [v1.gpr]; show wd s'.mem _ _ = _
          rw [wd_pass hc3 hp.frame (by omega) (by omega) (by omega), u3.mem]; rfl
        have eh : (t2.gpr .r2).toNat = accw s2.mem (State.addr b) (16 + k) := by
          rw [v2.gpr, v1.mem]; show wd s'.mem _ _ = _
          rw [wd_pass hc3 hp.frame (by omega) (by omega) (by omega), u3.mem, accw]
          congr 1; omega
        have h8 : t2.gpr .r8 = 38 := by
          rw [v2.other _ (by decide), v1.other _ (by decide), hp.rest.gpr _ (by decide),
            u3.other _ (by decide), h2.r8]
        have hh := hl32 (16 + k) (by omega)
        have hl := hl32 k (by omega)
        have e3 : (t3.gpr .r2).toNat = accw s2.mem (State.addr b) (16 + k) * 38 := by
          rw [v3.gpr, h8, toNat_mul_lt (by rw [eh]; show _ * 38 < _; omega), eh]; rfl
        rw [v4.gpr]
        show (t3.gpr .r3 + t3.gpr .r2).toNat = _
        rw [v3.other .r3 (by decide), v2.other .r3 (by decide), toNat_add_lt (by rw [el, e3]; omega), el,
          e3, foldC, Nat.mul_comm]
      · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
          (v4.rest (by decide))))
    · have hf2 : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩]
          s.mem s2.mem := h2.frame.mono fun r hr => by simp [List.mem_singleton.mp hr]
      rw [u3.mem] at hf4
      exact hf2.trans (hf4.mono fun r hr => by simp [List.mem_singleton.mp hr])
    · rw [hv4, val16_foldC, ← hv, show (32 : Nat) = 16 + 16 from rfl, val16_append, fold256]

end

end VG.Proof.X25519.Arm
