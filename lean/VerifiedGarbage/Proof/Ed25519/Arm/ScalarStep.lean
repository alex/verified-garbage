import VerifiedGarbage.Proof.Ed25519.Arm.ScalarPass
import VerifiedGarbage.Proof.Ed25519.Arm.Field
import VerifiedGarbage.Proof.X25519.Arm.Cswap

/-! One fixed binary-reduction step modulo L. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed25519 (L)

abbrev scalarClob : List Reg := [.r2, .r3, .r4, .r5, .r6, .r9]
def scalarRegions (b : BitVec 32) : List Region :=
  [⟨State.addr b + BitVec.ofNat 64 SR, 64⟩, ⟨State.addr b + BitVec.ofNat 64 SD, 64⟩]

structure ScalarKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest scalarClob s t
  frame : Frame (scalarRegions b) s.mem t.mem

theorem ScalarKeep.ctx {b : BitVec 32} {s t : State} (h : ScalarKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)

theorem ScalarKeep.trans {b : BitVec 32} {s t u : State} (h : ScalarKeep b s t)
    (h' : ScalarKeep b t u) : ScalarKeep b s u := ⟨h.rest.trans h'.rest, h.frame.trans h'.frame⟩

theorem scalarBitSource_eval {s : State} {j : Nat} (hj : j < 8) :
    (scalarBitSource j).eval s = some (s.gpr .r11 >>> j) := by
  unfold scalarBitSource
  by_cases hz : j = 0
  · subst hz; simp only [ite_true, BitVec.ushiftRight_zero]; rfl
  · rw [ite_eq_right_iff.mpr (fun h => False.elim (hz h))]
    exact op2_lsr (by omega)

theorem scalarBitHead_ok {s : State} {j : Nat} (hj : j < 8) :
    WP isa (.block [.mov .r5 (scalarBitSource j), .dp .and .r5 .r5 (.imm 1), .movw .r6 65535]) s
      fun t => (t.gpr .r5).toNat = (s.gpr .r11).toNat / 2 ^ j % 2 ∧
        t.gpr .r6 = mask16 ∧ Rest [.r5, .r6] s t ∧ t.mem = s.mem := by
  refine wp_mov (scalarBitSource_eval hj) fun u hu => wp_dp (op2_imm (by decide)) fun v hv =>
    wp_movw fun w hw => WP.block_nil ⟨?_, hw.gpr, ?_, by rw [hw.mem, hv.mem, hu.mem]⟩
  · rw [hw.other _ (by decide), hv.gpr]
    show (u.gpr .r5 &&& (1 : BitVec 32)).toNat = _
    rw [hu.gpr, BitVec.toNat_and, toNat_shr]
    exact Nat.and_two_pow_sub_one_eq_mod _ 1
  · exact (hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest (by decide)))

theorem scalarBit_ok {b : BitVec 32} {s : State} (hc : Ctx b s) {j : Nat} (hj : j < 8)
    (hl : Lim s.mem (State.addr b) SR) (hr : V s.mem (State.addr b) SR < L) :
    WP isa (.block (scalarBit j)) s fun t => ScalarKeep b s t ∧
      Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR =
        (2 * V s.mem (State.addr b) SR + (s.gpr .r11).toNat / 2 ^ j % 2) % L := by
  let bit := (s.gpr .r11).toNat / 2 ^ j % 2
  have hb : bit < 2 := Nat.mod_lt _ (by decide)
  have hR : SR = 256 := rfl
  have hD : SD = 320 := rfl
  rw [scalarBit, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WP.append (scalarBitHead_ok hj) fun s1 ⟨h5, h6, k1, m1⟩ => ?_
  have hc1 := hc.of_rest k1 (by decide)
  refine WP.append (scalarDoublePass_ok hc1 (m1 ▸ hl) hb h5 h6) fun s2 h2 => ?_
  have hc2 := hc1.of_rest h2.rest (by decide)
  have f2 : Frame [⟨State.addr b + BitVec.ofNat 64 SR, 64⟩] s.mem s2.mem := by
    have hf := h2.frame; rw [hc1.r0, m1] at hf; exact hf
  have l2 : Lim s2.mem (State.addr b) SR := by
    intro k hk; have he := h2.outs k hk; rw [hc1.r0] at he
    rw [limb, he]; exact out_lt _ _ _
  have v2 : V s2.mem (State.addr b) SR = 2 * V s.mem (State.addr b) SR + bit := by
    have he : ∀ k < 16, limb s2.mem (State.addr b) SR k =
        out (fun k => 2 * limb s.mem (State.addr b) SR k) bit k := by
      intro k hk
      have he := h2.outs k hk
      rwa [hc1.r0, m1] at he
    exact (val16_congr he).trans (scalarDouble_val hr hb)
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have k3 : Rest [.r2, .r3, .r4, .r5, .r6] s s3 :=
    (k1.mono (by decide)).trans ((h2.rest.mono (by decide)).trans (u3.rest (by decide)))
  have hc3 := hc.of_rest k3 (by decide)
  refine WP.append (scalarSubtractPass_ok hc3 (u3.mem ▸ l2) (by rw [u3.gpr]; rfl)
    (by rw [u3.other _ (by decide), h2.rest.gpr _ (by decide), h6])) fun s4 h4 => ?_
  have subf := scalarSubtract_facts (f := limb s3.mem (State.addr b) SR)
    (by change V s3.mem (State.addr b) SR < _; rw [u3.mem, v2]; omega)
  have hc4 := hc3.of_rest h4.rest (by decide)
  have f4 : Frame [⟨State.addr b + BitVec.ofNat 64 SD, 64⟩] s3.mem s4.mem := by
    have hf := h4.frame; rwa [hc3.r0] at hf
  have lr4 : ∀ k < 16, limb s4.mem (State.addr b) SR k = limb s3.mem (State.addr b) SR k :=
    limb_frame f4 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have ld4 : ∀ k < 16, limb s4.mem (State.addr b) SD k =
      out (fun k => limb s3.mem (State.addr b) SR k + scalarComplement k) 1 k := by
    intro k hk; have he := h4.outs k hk; rwa [hc3.r0] at he
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => wp_dp (op2_reg _ _) fun s6 u6 => ?_
  have k6 : Rest scalarClob s s6 := (k3.mono (by decide)).trans
    ((h4.rest.mono (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))
  have m6 : s6.mem = s4.mem := by rw [u6.mem, u5.mem]
  have mask6 : s6.gpr .r9 = 0 - BitVec.ofNat 32
      (chain (fun k => limb s3.mem (State.addr b) SR k + scalarComplement k) 1 16) := by
    rw [u6.gpr]
    show s5.gpr .r9 - s5.gpr .r5 = _
    rw [u5.gpr, u5.other _ (by decide)]
    apply congrArg (fun x : BitVec 32 => 0 - x)
    apply BitVec.eq_of_toNat_eq
    rw [toNat_imm (by have := subf.1; omega), h4.r5]
  refine WP.mono (cswap_ok (by decide) (by decide) (Or.inl (by decide))
    (hc.of_rest k6 (by decide)) subf.1 mask6) fun t ht => ?_
  have ltout : ∀ k < 16, limb t.mem (State.addr b) SR k =
      sel (chain (fun j => limb s3.mem (State.addr b) SR j + scalarComplement j) 1 16)
        (limb s3.mem (State.addr b) SR k)
        (out (fun j => limb s3.mem (State.addr b) SR j + scalarComplement j) 1 k) := by
    intro k hk
    rw [ht.lx k hk, m6, lr4 k hk, ld4 k hk]
  refine ⟨⟨k6.trans (ht.rest.mono (by decide)), ?_⟩, ?_, ?_⟩
  · have fa : Frame (scalarRegions b) s.mem s2.mem := f2.mono fun r hr => by
      simp only [scalarRegions, List.mem_cons, List.mem_singleton.mp hr, true_or]
    have fb : Frame (scalarRegions b) s2.mem s4.mem := by
      rw [← u3.mem]; exact f4.mono fun r hr => by
        exact List.mem_cons_of_mem _ hr
    have fc : Frame (scalarRegions b) s4.mem t.mem := by rw [← m6]; exact ht.frame
    exact (fa.trans fb).trans fc
  · intro k hk
    rw [ltout k hk]; unfold sel
    split
    · exact out_lt _ _ _
    · rw [u3.mem]; exact l2 k hk
  · unfold V
    rw [val16_congr ltout, subf.2]
    change V s3.mem (State.addr b) SR % L = _
    rw [u3.mem, v2]
    rfl

end VG.Proof.Ed25519.Arm
