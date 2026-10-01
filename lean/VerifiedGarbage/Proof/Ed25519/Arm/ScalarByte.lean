import VerifiedGarbage.Proof.Ed25519.Arm.ScalarStep

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
