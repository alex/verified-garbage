import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTBody
import VerifiedGarbage.Proof.Ed25519.Arm.PointMulLoop
import VerifiedGarbage.Proof.Ed25519.Arm.PointMul

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseCTInit`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarBaseCTLoop`. -/
section
/-! Both runs descend through the same public checkpoint count. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem pointMulLoop_ct (s₁ s₂ : State) (b ptr : BitVec 32) (count scalar₁ scalar₂ : Nat)
    (p₁ p₂ : Spec.Ed25519.Point) (n : Nat) :
    CT (fun x y => PointMulInv s₁ b ptr count scalar₁ p₁ n x ∧
      PointMulInv s₂ b ptr count scalar₂ p₂ n y) (.loop pointMulBody .ne) (fun _ _ => True) := by
  apply RelCT.loop (M := isa) (fun n x y => PointMulInv s₁ b ptr count scalar₁ p₁ n x ∧
    PointMulInv s₂ b ptr count scalar₂ p₂ n y) _ n
  intro k
  cases k with
  | zero =>
    apply RelCT.of_false
    intro x y h
    exact Nat.not_lt_zero _ h.1.positive
  | succ j =>
    by_cases hj : j < count ∧ count ≤ 32
    · have hc := (pointMulBody_ct b ptr j (by omega)).mono
        (fun x y (h : PointMulInv s₁ b ptr count scalar₁ p₁ (j + 1) x ∧
            PointMulInv s₂ b ptr count scalar₂ p₂ (j + 1) y) =>
          ⟨⟨h.1.ctx, h.1.lim, h.1.input.pointer, h.1.counter, h.1.d⟩,
           ⟨h.2.ctx, h.2.lim, h.2.input.pointer, h.2.counter, h.2.d⟩⟩)
        (fun _ _ h => h)
      intro x y tx ty u v h ex ey
      have he := (hc _ _ _ _ _ _ h ex ey).1
      obtain ⟨_, u', eu, hu⟩ := pointMulBody_ok h.1.ctx h.1.lim count scalar₁ j p₁ h.1.input
        hj.1 h.1.d h.1.value h.1.counter (h.1.table j hj.1)
      obtain ⟨_, v', ev, hv⟩ := pointMulBody_ok h.2.ctx h.2.lim count scalar₂ j p₂ h.2.input
        hj.1 h.2.d h.2.value h.2.counter (h.2.table j hj.1)
      obtain ⟨_, rfl⟩ := Exec.det ex eu
      obtain ⟨_, rfl⟩ := Exec.det ey ev
      have ez : VG.Arm.eval .ne u = VG.Arm.eval .ne v := by
        simp only [VG.Arm.eval, hu.2.2.2.2.2, hv.2.2.2.2.2]
      refine ⟨he, ez, fun _ => trivial, ?_⟩
      intro hj0
      have hnz : j ≠ 0 := by
        intro hz
        subst j
        simp only [VG.Arm.eval, hu.2.2.2.2.2, decide_true, Bool.not_true] at hj0
        cases hj0
      refine ⟨j, by omega, ?_, ?_⟩
      · refine ⟨by omega, by omega, hu.1.ctx h.1.ctx, hu.2.1,
          h.1.input.keep hu.1 (by decide) (by decide), hu.2.2.2.2.1,
          hu.2.2.1, hu.2.2.2.1, ?_, h.1.keep.trans hu.1⟩
        intro i hi
        exact (hu.1.table (by omega) (by omega) (by decide) (.inl (by omega))).trans (h.1.table i hi)
      · refine ⟨by omega, by omega, hv.1.ctx h.2.ctx, hv.2.1,
          h.2.input.keep hv.1 (by decide) (by decide), hv.2.2.2.2.1,
          hv.2.2.1, hv.2.2.2.1, ?_, h.2.keep.trans hv.1⟩
        intro i hi
        exact (hv.1.table (by omega) (by omega) (by decide) (.inl (by omega))).trans (h.2.table i hi)
    · apply RelCT.of_false
      intro x y h
      have := h.1.bound
      have := h.1.input.bound
      omega

end VG.Proof.Ed25519.Arm
end

/-! Checked initialization of the public descending loop. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def pointMultiplyInitCT (count : Nat) : Prog isa :=
  .seq (pointPowers 1600 count true) (.seq (constPoint Spec.Ed25519.identity)
    (.block [.movw .r11 (BitVec.ofNat 16 count), .str .r11 .r0 56]))

theorem pointMultiplyInitCT_ok {b ptr : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (count scalar : Nat) (hi : MulInput b ptr count scalar s) (hn : 0 < count)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa (pointMultiplyInitCT count) s fun t =>
      PointMulInv t b ptr count scalar (point (env s.mem b) 0 1 2 3) count t := by
  let p := point (env s.mem b) 0 1 2 3
  have hs : scalar < 2 ^ (16 * count) := by
    rw [← hi.value]
    exact val16_lt (fun k _ => packedLimb_lt _ _ k)
  refine WP.seq (WP.mono (pointPowers_ok true hc hl 1600 count (by decide)
    (by have := hi.bound; omega) hn hi.bound hd) fun a ⟨al, ats, _, ah, ak⟩ => ?_)
  have kam : MulKeep b 1600 6144 s a := (MulKeep.of_powers ak).mono (by decide) (by have := hi.bound; omega)
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) (kam.ctx hc) al)
    fun u ⟨uk, ul, ue⟩ => ?_)
  have kum : MulKeep b 1600 6144 s u := kam.trans (MulKeep.of_powers (PowersKeep.of_keep uk))
  have ud : env u.mem b 16 = Spec.Ed25519.d := by rw [ue, constPoint_d, ah 16 (by decide), hd]
  have up : point (env u.mem b) 0 1 2 3 = after scalar p (16 * count) :=
    ((congrArg (fun e => point e 0 1 2 3) ue).trans (constPoint_eval _ _)).trans
      (after_top scalar (16 * count) p hs).symm
  have ut : ∀ j < count, tablePoint u.mem b (1600 + 128 * j) = powerPoint p (16 * j) := by
    intro j hj
    have := hi.bound
    exact (workspace_tablePoint uk.frame (by omega) (by omega)).trans (ats j hj)
  refine wp_movw fun v hv => ?_
  have vc : v.gpr .r11 = BitVec.ofNat 32 count := by
    apply BitVec.eq_of_toNat_eq
    rw [hv.gpr, movw_nat (by have := hi.bound; omega), toNat_imm (by have := hi.bound; omega)]
  have kvm : MulKeep b 1600 6144 s v := kum.trans
    (MulKeep.of_rest (hv.rest (ws := [.r11]) (by decide)) (by decide) hv.mem)
  refine WP.mono (counterStore_ok (kvm.ctx hc) count vc) fun w ⟨wr, wf, wc⟩ => ?_
  have kwm : MulKeep b 1600 6144 s w := kvm.trans (MulKeep.of_counter wr (by decide) wf)
  have we : env w.mem b = env u.mem b := (smallFrame_env wf (by decide)).trans
    (congrArg (fun m => env m b) hv.mem)
  have wl : AllLim w.mem b := smallFrame_lim wf (by decide) (by rw [hv.mem]; exact ul)
  refine ⟨hn, Nat.le_refl _, kwm.ctx hc, wl,
    hi.keep kwm (by decide) (by decide), wc, (congrFun we 16).trans ud,
    (congrArg (fun e => point e 0 1 2 3) we).trans up, ?_, MulKeep.refl _ _ _ _⟩
  intro j hj
  have := hi.bound
  exact (smallFrame_table wf (by decide) (by omega) (by omega)).trans
    ((congrArg (fun m => tablePoint m b (1600 + 128 * j)) hv.mem).trans (ut j hj))

end VG.Proof.Ed25519.Arm
end

/-! Public initialization and synchronized batches prove scalar multiplication constant time. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

materialize_code mulInit16CT := pointMultiplyInitCT 16
materialize_code mulInit32CT := pointMultiplyInitCT 32

def MulCTPre (b ptr : BitVec 32) (count scalar : Nat) (s : State) : Prop :=
  Ctx b s ∧ AllLim s.mem b ∧ MulInput b ptr count scalar s ∧ env s.mem b 16 = Spec.Ed25519.d

theorem pointMultiply_ct (b ptr : BitVec 32) (count scalar₁ scalar₂ : Nat)
    (hn : count = 16 ∨ count = 32) :
    CT (fun x y => MulCTPre b ptr count scalar₁ x ∧ MulCTPre b ptr count scalar₂ y)
      (pointMultiply count) (fun _ _ => True) := by
  have hn0 : 0 < count := by rcases hn with rfl | rfl <;> decide
  have hi : CT (fun x y => MulCTPre b ptr count scalar₁ x ∧ MulCTPre b ptr count scalar₂ y)
      (pointMultiplyInitCT count) (fun _ _ => True) := by
    have hr : ∀ x y, (MulCTPre b ptr count scalar₁ x ∧ MulCTPre b ptr count scalar₂ y) →
        ∀ r ∈ ([.r0] : List Reg), x.gpr r = y.gpr r := by
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    rcases hn with rfl | rfl
    · exact ctRegs [.r0] hr (by taint_decide)
    · exact ctRegs [.r0] hr (by taint_decide)
  intro x y tx ty u v h ex ey
  cases ex with
  | seq ep ex =>
    cases ex with
    | seq ec ex =>
      cases ex with
      | seq ei el =>
        cases ey with
        | seq fp ey =>
          cases ey with
          | seq fc ey =>
            cases ey with
            | seq fi fl =>
              have exi := Exec.seq ep (Exec.seq ec ei)
              have eyi := Exec.seq fp (Exec.seq fc fi)
              have ht := (hi _ _ _ _ _ _ h exi eyi).1
              obtain ⟨_, a, ea, ha⟩ := pointMultiplyInitCT_ok h.1.1 h.1.2.1 count scalar₁ h.1.2.2.1 hn0 h.1.2.2.2
              obtain ⟨_, b', eb, hb⟩ := pointMultiplyInitCT_ok h.2.1 h.2.2.1 count scalar₂ h.2.2.2.1 hn0 h.2.2.2.2
              obtain ⟨_, rfl⟩ := Exec.det exi ea
              obtain ⟨_, rfl⟩ := Exec.det eyi eb
              have hl := (pointMulLoop_ct _ _ b ptr count scalar₁ scalar₂ _ _ count _ _ _ _ _ _
                ⟨ha, hb⟩ el fl).1
              exact ⟨by simpa only [List.append_assoc] using congrArg₂ (fun (a b : List Leak) => a ++ b) ht hl, trivial⟩

end VG.Proof.Ed25519.Arm
