import VerifiedGarbage.Proof.X448.Arm.RowPass

/-!
# X448 on ARMv7: the multiplication-row working space

A row uses a second pointer, `r7`, at a public word offset from the
working-space pointer in `r0`.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm
open VG.Proof.X25519.Arm

structure RowCtx (b : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = b
  fit : b.toNat + 4096 ≤ 2 ^ 32
  wr : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr

theorem RowCtx.of_rest {b : BitVec 32} {s t : State} {ws : List Reg} (h : RowCtx b s)
    (hr : Rest ws s t) (h0 : Reg.r0 ∉ ws) : RowCtx b t :=
  ⟨(hr.gpr _ h0).trans h.r0, h.fit, hr.wr ▸ h.wr⟩

theorem RowCtx.ea {b : BitVec 32} {s : State} (h : RowCtx b s) {d : Nat} (hd : d < 4096) :
    State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = State.addr b + BitVec.ofNat 64 d := by
  rw [h.r0]; exact addr_add (by have := h.fit; omega)

theorem RowCtx.inW {b : BitVec 32} {s : State} (h : RowCtx b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions s.wr (State.addr b + BitVec.ofNat 64 d) n := in_base h.wr (by omega) (by omega)

theorem RowCtx.inR {b : BitVec 32} {s : State} (h : RowCtx b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions (s.rd ++ s.wr) (State.addr b + BitVec.ofNat 64 d) n :=
  in_base (List.mem_append_right _ h.wr) (by omega) (by omega)

theorem rowLoad_ok {b : BitVec 32} {s : State} (hc : RowCtx b s) {t : Reg} {d : Nat}
    (hd : d + 4 ≤ 4096) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32) →
      WP isa (.block is) s' Q) : WP isa (.block (ld t d :: is)) s Q :=
  wp_ldr (by omega) (hc.ea (by omega)) (hc.inR hd) k

abbrev accw (m : Mem) (B : Addr) (k : Nat) : Nat := wd m B (ACC + 4 * k)

theorem wd_shift (m : Mem) (B : Addr) (a d : Nat) : wd m (B + BitVec.ofNat 64 a) d = wd m B (a + d) := by
  unfold wd; rw [Offset.add_add]

theorem ACC_eq : ACC = 3584 := rfl

theorem chain_zero (c : Nat → Nat) (n : Nat) : chain c 0 n = Radix16.carry c n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [chain, Radix16.carry, ih]; rfl

theorem out_zero (c : Nat → Nat) (k : Nat) : out c 0 k = Radix16.digit c k := by
  rw [out, Radix16.digit, chain_zero]; rfl

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

end

/-- After `i` rows the initialized product limbs represent `a[0..i] * b`. -/
structure RowInv (b : BitVec 32) (x y : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : RowCtx b s
  rest : Rest clob s0 s
  r6 : s.gpr .r6 = mask16
  r7 : s.gpr .r7 = b + BitVec.ofNat 32 (4 * i)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (28 - i)
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 224⟩] s0.mem s.mem
  lt : ∀ k < i + 28, accw s.mem (State.addr b) k < 65536
  val : Radix16.valN (accw s.mem (State.addr b)) (i + 28) =
    Radix16.valN (limbs s0.mem (State.addr b) x) i * fe s0.mem (State.addr b) y

end VG.Proof.X448.Arm
