import VerifiedGarbage.Proof.Ed25519.Arm.ScalarPass
import VerifiedGarbage.Proof.Ed25519.Arm.Field
import VerifiedGarbage.Proof.X25519.Arm.Cswap
import VerifiedGarbage.Proof.Ed25519.Arm.InitFields
import VerifiedGarbage.Spec.Ed25519.Contract

/-! Merged from `Proof.Ed25519.Arm.ScalarByte`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarStep`. -/
section
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
end

/-! Eight reduction steps consume a byte from high bit to low bit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed25519 (L)

theorem scalarBits_ok {b : BitVec 32} (js : List Nat) (hj : ∀ j ∈ js, j < 8)
    {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) SR)
    (hr : V s.mem (State.addr b) SR < L) :
    WP isa (.block (js.flatMap scalarBit)) s fun t => ScalarKeep b s t ∧
      Lim t.mem (State.addr b) SR ∧ V t.mem (State.addr b) SR =
        js.foldl (fun v j => (2 * v + (s.gpr .r11).toNat / 2 ^ j % 2) % L)
          (V s.mem (State.addr b) SR) := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨⟨Rest.refl _ _, Frame.refl _ _⟩, hl, rfl⟩
  | cons j js ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (scalarBit_ok hc (hj j (by simp)) hl hr) fun t ⟨kt, lt, vt⟩ => ?_
    refine WP.mono (ih (fun i hi => hj i (List.mem_cons_of_mem _ hi)) (kt.ctx hc) lt
      (by rw [vt]; exact Nat.mod_lt _ order_pos)) fun u ⟨ku, lu, vu⟩ => ?_
    refine ⟨kt.trans ku, lu, ?_⟩
    rw [vu, kt.rest.gpr .r11 (by decide), vt]
    rfl

theorem scalarEight_ok {b : BitVec 32} {s : State} (hc : Ctx b s)
    (hl : Lim s.mem (State.addr b) SR) (hr : V s.mem (State.addr b) SR < L)
    (hb : (s.gpr .r11).toNat < 256) :
    WP isa (.block ((List.range 8).reverse.flatMap scalarBit)) s fun t =>
      ScalarKeep b s t ∧ Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR = (256 * V s.mem (State.addr b) SR + (s.gpr .r11).toNat) % L := by
  refine WP.mono (scalarBits_ok _ (by intro j hj; simpa only [List.mem_reverse, List.mem_range] using hj)
    hc hl hr) fun t ⟨kt, lt, vt⟩ => ?_
  change V t.mem (State.addr b) SR = scalarConsumeBits _ 8 _ at vt
  rw [scalarConsumeBits_eq _ _ _ hr, show 2 ^ 8 = 256 from rfl, Nat.mod_eq_of_lt hb] at vt
  exact ⟨kt, lt, vt⟩

theorem scalarRead_ok {s : State} {p : BitVec 32} {n : Nat} (hn : n < 64)
    (hp : s.gpr .r12 = p) (hfit : p.toNat + 64 ≤ 2 ^ 32)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 (n + 1))
    (hr : InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 n) 1) :
    WP isa (.block scalarRead) s fun t =>
      Rest [.r2, .r10, .r11] s t ∧ t.mem = s.mem ∧
      t.gpr .r10 = BitVec.ofNat 32 n ∧
      (t.gpr .r11).toNat = (s.mem (State.addr p + BitVec.ofNat 64 n)).toNat := by
  unfold scalarRead
  refine wp_dp (op2_imm (by decide)) fun u hu => wp_dp (op2_reg _ _) fun v hv => ?_
  have he : u.gpr .r10 = BitVec.ofNat 32 n := by
    rw [hu.gpr]
    change s.gpr .r10 - BitVec.ofNat 32 1 = _
    rw [h10, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hpv : v.gpr .r2 = p + BitVec.ofNat 32 n := by
    rw [hv.gpr]; change u.gpr .r12 + u.gpr .r10 = _
    rw [hu.other _ (by decide), hp, he]
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 n) (by decide)
    (by rw [hpv, BitVec.add_zero]; exact addr_add (by omega))
    (by rw [hv.rd, hv.wr, hu.rd, hu.wr]; exact hr) fun w hw => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest (by decide))),
    by rw [hw.mem, hv.mem, hu.mem], by rw [hw.other _ (by decide), hv.other _ (by decide), he], ?_⟩
  rw [hw.gpr, BitVec.toNat_setWidth_of_le (by decide), hv.mem, hu.mem]

abbrev scalarBodyClob : List Reg := [.r2, .r3, .r4, .r5, .r6, .r9, .r10, .r11]

structure ScalarBodyKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest scalarBodyClob s t
  frame : Frame (scalarRegions b) s.mem t.mem

theorem ScalarBodyKeep.ctx {b : BitVec 32} {s t : State} (h : ScalarBodyKeep b s t)
    (hc : Ctx b s) : Ctx b t := hc.of_rest h.rest (by decide)

theorem ScalarBodyKeep.trans {b : BitVec 32} {s t u : State} (h : ScalarBodyKeep b s t)
    (h' : ScalarBodyKeep b t u) : ScalarBodyKeep b s u :=
  ⟨h.rest.trans h'.rest, h.frame.trans h'.frame⟩

theorem scalarByte_ok {b p : BitVec 32} {s : State} (hc : Ctx b s)
    {n : Nat} (hn : n < 64) (hp : s.gpr .r12 = p) (hfit : p.toNat + 64 ≤ 2 ^ 32)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 (n + 1))
    (hread : InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 n) 1)
    (hl : Lim s.mem (State.addr b) SR) (hr : V s.mem (State.addr b) SR < L) :
    WP isa (.block scalarByte) s fun t =>
      ScalarBodyKeep b s t ∧ Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR =
        (256 * V s.mem (State.addr b) SR + (s.mem (State.addr p + BitVec.ofNat 64 n)).toNat) % L ∧
      t.gpr .r10 = BitVec.ofNat 32 n ∧ t.z = decide (n = 0) := by
  rw [scalarByte, List.append_assoc]
  refine WP.append (scalarRead_ok hn hp hfit h10 hread) fun u ⟨ku, mu, eu, bu⟩ => ?_
  have hcu := hc.of_rest ku (by decide)
  refine WP.append (scalarEight_ok hcu (mu ▸ hl) (mu ▸ hr) (by rw [bu]; exact BitVec.isLt _))
    fun v ⟨kv, lv, vv⟩ => ?_
  refine wp_cmp (op2_imm (by decide)) fun w hw hz => WP.block_nil ?_
  have ev : v.gpr .r10 = BitVec.ofNat 32 n := (kv.rest.gpr _ (by decide)).trans eu
  refine ⟨⟨(ku.mono (by decide)).trans ((kv.rest.mono (by decide)).trans (hw.rest _)), ?_⟩,
    hw.mem ▸ lv, ?_, by rw [hw.gpr, ev], ?_⟩
  · rw [hw.mem, ← mu]; exact kv.frame
  · rw [hw.mem, vv, mu, bu]
  · rw [hz, ev]
    have he : BitVec.ofNat 32 n - (0 : BitVec 32) = BitVec.ofNat 32 n := BitVec.sub_zero _
    rw [he, ofNat_beq_zero (by omega)]

end VG.Proof.Ed25519.Arm
end

/-! The fixed 64-byte reduction loop, with an exact suffix invariant. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed25519 (L bytesAt decodeLE)

theorem scalar_bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

theorem scalar_suffix_step (m : Mem) (p : Addr) (n : Nat) (hn : n < 64) :
    decodeLE ((bytesAt m p 64).drop n) % L =
      (256 * (decodeLE ((bytesAt m p 64).drop (n + 1)) % L) +
        (m (p + BitVec.ofNat 64 n)).toNat) % L := by
  rw [List.drop_eq_getElem_cons (by rw [scalar_bytesAt_length]; exact hn), reduce_cons]
  simp only [bytesAt, List.getElem_map, List.getElem_range]

structure ScalarInv (b : BitVec 32) (p : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 64
  counter : s.gpr .r10 = BitVec.ofNat 32 n
  limbs : Lim s.mem (State.addr b) SR
  value : V s.mem (State.addr b) SR = decodeLE ((bytesAt s0.mem p 64).drop n) % L
  keeps : ScalarBodyKeep b s0 s

theorem scalarLoop_ok {b p : BitVec 32} {s0 : State} (hc : Ctx b s0)
    (hp : s0.gpr .r12 = p) (hfit : p.toNat + 64 ≤ 2 ^ 32)
    (hread : ∀ n < 64, InRegions (s0.rd ++ s0.wr) (State.addr p + BitVec.ofNat 64 n) 1)
    (hsep : ∀ r ∈ scalarRegions b, (⟨State.addr p, 64⟩ : Region).Disjoint r)
    (h10 : s0.gpr .r10 = 64) (hl : Lim s0.mem (State.addr b) SR)
    (hz : V s0.mem (State.addr b) SR = 0) :
    WP isa (.loop (.block scalarByte) .ne) s0 fun t => ScalarBodyKeep b s0 t ∧
      Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR = decodeLE (bytesAt s0.mem (State.addr p) 64) % L := by
  apply WP.loop (ScalarInv b (State.addr p) s0) (n := 64)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 64 := by have := hi.bound; omega
    have hps : s.gpr .r12 = p := (hi.keeps.rest.gpr _ (by decide)).trans hp
    have hrs : InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 k) 1 := by
      rw [hi.keeps.rest.rd, hi.keeps.rest.wr]; exact hread k hk
    refine WP.mono (scalarByte_ok (hi.keeps.ctx hc) hk hps hfit hi.counter hrs hi.limbs
      (by rw [hi.value]; exact Nat.mod_lt _ order_pos)) fun t ⟨kt, lt, vt, et, zt⟩ => ?_
    have km := hi.keeps.trans kt
    have mb : s.mem (State.addr p + BitVec.ofNat 64 k) = s0.mem (State.addr p + BitVec.ofNat 64 k) :=
      hi.keeps.frame.bytes hsep (by decide : 64 ≤ 2 ^ 64) hk
    have val : V t.mem (State.addr b) SR = decodeLE ((bytesAt s0.mem (State.addr p) 64).drop k) % L := by
      rw [vt, hi.value, mb, scalar_suffix_step _ _ _ hk]
    by_cases hk0 : k = 0
    · subst hk0
      refine .inl ⟨by rw [eval_ne, zt]; rfl, km, lt, ?_⟩
      simpa only [List.drop_zero] using val
    · refine .inr ⟨by rw [eval_ne, zt]; simp only [hk0, decide_false, Bool.not_false],
        k, by omega, ?_⟩
      exact ⟨by omega, by omega, et, lt, val, km⟩
  · refine ⟨by decide, by decide, h10, hl, ?_, ⟨Rest.refl _ _, Frame.refl _ _⟩⟩
    rw [hz, List.drop_eq_nil_of_le (by rw [scalar_bytesAt_length])]
    rfl

theorem scalarInit_ok {b : BitVec 32} {s : State} (hc : Ctx b s) :
    WP isa (.block scalarInit) s fun t => ScalarBodyKeep b s t ∧
      t.gpr .r10 = 64 ∧ Lim t.mem (State.addr b) SR ∧ V t.mem (State.addr b) SR = 0 := by
  rw [scalarInit, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun u hu => ?_
  refine WP.append (stores_ok (by decide) (hc.of_rest (hu.rest (ws := [.r3]) (by decide)) (by decide)))
    fun v ⟨out, frame, _, kv⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun t ht => WP.block_nil ?_
  have he : ∀ k < 16, limb t.mem (State.addr b) SR k = 0 := by
    intro k hk; rw [ht.mem]; have h := out k hk; rw [hu.gpr] at h; exact h
  refine ⟨⟨(hu.rest (by decide)).trans ((kv.mono (by decide)).trans (ht.rest (by decide))), ?_⟩,
    ht.gpr, fun k hk => by rw [he k hk]; decide, ?_⟩
  · rw [ht.mem, ← hu.mem]
    exact frame.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self
  · exact (val16_congr he).trans (val16_zero_fn _)

theorem scalarReduceEngine_ok {b p : BitVec 32} {s : State} (hc : Ctx b s)
    (hp : s.gpr .r12 = p) (hfit : p.toNat + 64 ≤ 2 ^ 32)
    (hread : ∀ n < 64, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 n) 1)
    (hsep : ∀ r ∈ scalarRegions b, (⟨State.addr p, 64⟩ : Region).Disjoint r) :
    WP isa scalarReduceEngine s fun t => ScalarBodyKeep b s t ∧
      Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR = decodeLE (bytesAt s.mem (State.addr p) 64) % L := by
  unfold scalarReduceEngine
  refine WP.seq (WP.mono (scalarInit_ok hc) fun u ⟨ku, eu, lu, vu⟩ => ?_)
  refine WP.mono (scalarLoop_ok (ku.ctx hc) ((ku.rest.gpr _ (by decide)).trans hp) hfit
    (fun n hn => by rw [ku.rest.rd, ku.rest.wr]; exact hread n hn) hsep eu lu vu)
    fun t ⟨kt, lt, vt⟩ => ⟨ku.trans kt, lt, ?_⟩
  have bytes : bytesAt u.mem (State.addr p) 64 = bytesAt s.mem (State.addr p) 64 := by
    unfold bytesAt; apply List.map_congr_left
    intro n hn
    exact ku.frame.bytes hsep (by decide : 64 ≤ 2 ^ 64) (List.mem_range.mp hn)
  rw [vt, bytes]

end VG.Proof.Ed25519.Arm
