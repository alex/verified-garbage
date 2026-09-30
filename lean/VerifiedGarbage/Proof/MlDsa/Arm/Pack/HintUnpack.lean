import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintBase

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_unpack`, the steps

Untrusted: everything here is checked by Lean. As on x86-64, the code
follows the fold form of `HintBitUnpack` (`hintBitUnpack_eq`,
`Proof/MlDsa/Pack/Hint.lean`) step by step: while no check has failed, the
words of `h` are the hint of the spec (`HArr`) and `r1` its index; once one
has, `r1` is 256, which skips the rest (`SRel`). Here: the arguments,
zeroing `h`, and one coefficient (`first_ok`, `next_ok`); the loops are in
`HintUnpackLoops.lean`. They run from any state that permits reading `y` and
writing `h` (`MainPre`), so that constant time can narrow the state to those
two regions.
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr)
open VG.Proof.MlKem (bytesAt_length bytesAt_getD bytesAt_eq)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.Arm.Pack.Hint

/-! ## The arguments -/

section
variable (s₀ : State)

/-- `y`, `len`, `ω`, `h` and `hlen`. -/
abbrev uY : BitVec 32 := s₀.gpr .r0
abbrev uL : BitVec 32 := s₀.gpr .r1
abbrev uW : BitVec 32 := s₀.gpr .r2
abbrev uH : BitVec 32 := s₀.gpr .r3
abbrev uHL : BitVec 32 := stackArg s₀ 0
abbrev uω : Nat := (uW s₀).toNat
abbrev uLen : Nat := (uL s₀).toNat
abbrev uk : Nat := uLen s₀ - uω s₀
abbrev uyR : Region := ⟨State.addr (uY s₀), uLen s₀⟩
abbrev uhR : Region := ⟨State.addr (uH s₀), (uHL s₀).toNat * 4⟩
abbrev uargR : Region := ⟨stackArgAddr s₀ 0, 4⟩
/-- The bytes of `y`, as the spec reads them. -/
abbrev uYs : Array Byte := (bytesAt s₀.mem (State.addr (uY s₀)) (uLen s₀)).toArray

end

/-- The precondition, as `sig_pre` states it. -/
structure UPre (s : State) : Prop where
  sp : 16 ≤ s.sp.toNat
  spA : s.sp.toNat + 4 ≤ 2 ^ 32
  rd : s.rd = [uyR s, uargR s]
  wr : s.wr = [uhR s]
  d_yh : (uyR s).Disjoint (uhR s)
  d_ha : (uhR s).Disjoint (uargR s)
  b_y : (⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint (uyR s)
  b_h : (⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint (uhR s)
  b_a : (⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint (uargR s)
  fitY : (uY s).toNat + uLen s ≤ 2 ^ 32
  fitH : (uH s).toNat + (uHL s).toNat * 4 ≤ 2 ^ 32
  par : (uω s, uk s) ∈ hintParams
  ωle : uω s ≤ uLen s
  hlen : (uHL s).toNat = 256 * uk s

theorem ufacts {s₀ : State} (hp : UPre s₀) : 4 ≤ uk s₀ ∧ uk s₀ ≤ 8 ∧ 55 ≤ uω s₀ ∧ uω s₀ ≤ 80 ∧
    uω s₀ + uk s₀ = uLen s₀ ∧ uLen s₀ ≤ 88 := by
  have := mem_hintParams hp.par
  have := hp.ωle
  have e : uk s₀ = uLen s₀ - uω s₀ := rfl
  omega

/-! ## Zeroing `h` -/

theorem zeroPro_ok {s : State} :
    WP isa (.block [.dp .sub .r6 .r1 (.reg .r2), .mov .r4 (.reg .r12), .mov .r12 (.imm 0), .mov .r5 (.reg .r3)])
      s fun s' => s'.gpr .r6 = s.gpr .r1 - s.gpr .r2 ∧ s'.gpr .r4 = s.gpr .r12 ∧ s'.gpr .r12 = 0 ∧
        s'.gpr .r5 = s.gpr .r3 ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r3 = s.gpr .r3 ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block []

theorem zeroStep_ok {s : State} {p c : BitVec 32} (h5 : s.gpr .r5 = p) (h4 : s.gpr .r4 = c)
    (o : InRegions s.wr (State.addr (p + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.str .r12 .r5 0, .dp .add .r5 .r5 (.imm 4), .subs .r4 .r4 (.imm 1)]) s fun s' =>
      s'.gpr .r5 = p + 4 ∧ s'.gpr .r4 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (p + BitVec.ofNat 32 0)) (s.gpr .r12) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r6 = s.gpr .r6 ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h5, h4, o]

theorem zeroEnd_ok {s : State} :
    WP isa (.block [.mov .r1 (.imm 0)]) s fun s' => s'.gpr .r1 = 0 ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r1 → s'.gpr r = s.gpr r := by
  run_block []
  simp only [true_and]; intro r hr; rw [ite_neg' hr]

/-- Zeroing the `hlen` words of `h`, from the entry values of the registers. -/
theorem zero_ok {s₀ : State} (hp : UPre s₀) {s : State} (h0 : s.gpr .r0 = uY s₀) (h1 : s.gpr .r1 = uL s₀)
    (h2 : s.gpr .r2 = uW s₀) (h3 : s.gpr .r3 = uH s₀) (h12 : s.gpr .r12 = uHL s₀) (hwr : uhR s₀ ∈ s.wr) :
    WP isa hbuZero s fun s' => s'.gpr .r0 = uY s₀ ∧ s'.gpr .r1 = 0 ∧ s'.gpr .r2 = uW s₀ ∧
      s'.gpr .r3 = uH s₀ ∧ s'.gpr .r6 = BitVec.ofNat 32 (uk s₀) ∧
      (∀ t < 256 * uk s₀, coeffAt s'.mem (State.addr (uH s₀)) t = 0) ∧
      Frame [uhR s₀] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨hk4, hk8, -, -, hsum, hL88⟩ := ufacts hp
  have fH := hp.fitH
  have hl := hp.hlen
  have hHL := (uHL s₀).isLt
  unfold hbuZero
  refine WP.seq (WP.mono zeroPro_ok fun s₁ ⟨r6₁, r4₁, r12₁, r5₁, r0₁, r2₁, r3₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  refine WP.seq (wp_loop_ne (N := 256 * uk s₀) (fun t s' => s'.gpr .r5 = uH s₀ + BitVec.ofNat 32 (4 * t) ∧
      s'.gpr .r4 = BitVec.ofNat 32 (1 * (256 * uk s₀ - t)) ∧ s'.gpr .r12 = 0 ∧ s'.gpr .r0 = uY s₀ ∧
      s'.gpr .r2 = uW s₀ ∧ s'.gpr .r3 = uH s₀ ∧ s'.gpr .r6 = BitVec.ofNat 32 (uk s₀) ∧
      Frame [uhR s₀] s.mem s'.mem ∧ (∀ u < t, coeffAt s'.mem (State.addr (uH s₀)) u = 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp) (by omega)
    (fun t ht s' ⟨i5, i4, i12, i0, i2, i3, i6, hf, hz, hrd, hwr', hsp⟩ => ?_)
    (fun s₂ ⟨_, _, _, i0, i2, i3, i6, hf, hz, hrd, hwr', hsp⟩ => ?_)
    ⟨by rw [r5₁, h3]; simp, by rw [r4₁, h12, Nat.one_mul, Nat.sub_zero, ← hl, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      r12₁, by rw [r0₁, h0], by rw [r2₁, h2], by rw [r3₁, h3], ?_, by rw [m₁]; exact Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _), rd₁, wr₁, sp₁⟩)
  · have ea : State.addr (uH s₀ + BitVec.ofNat 32 (4 * t) + BitVec.ofNat 32 0) = coeffAddr (State.addr (uH s₀)) t :=
      by rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
    have hin : (uhR s₀).Contains (coeffAddr (State.addr (uH s₀)) t) 4 := Offset.contains_base _ (by omega) (by omega)
    refine WP.mono (zeroStep_ok i5 i4 (by rw [ea, hwr']; exact ⟨_, hwr, hin⟩))
      fun s'' ⟨r5', r4', z', m', r0', r2', r3', r6', r12', rd', wr', sp'⟩ =>
        ⟨⟨by rw [r5', show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ptr_add, Nat.mul_succ],
          by rw [r4']; exact count_sub (k := 1) ht, by rw [r12', i12],
          by rw [r0', i0], by rw [r2', i2], by rw [r3', i3], by rw [r6', i6], ?_, fun u hu => ?_,
          by rw [rd', hrd], by rw [wr', hwr'], by rw [sp', hsp]⟩,
          by rw [z']; exact count_z (k := 1) ht (by decide) (by omega)⟩
    · rw [m', ea]
      exact hf.writeW (List.mem_singleton_self _) _ hin
    · rw [m', ea, i12]
      by_cases e : u = t
      · subst e; rw [coeffAt_eq, Mem.readW_writeW_self32]
      · rw [coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
          ← coeffAt_eq, hz u (by omega)]
  · rw [r6₁, h1, h2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le hp.ωle, toNat_ofNat32 (by omega)]

  · refine WP.mono zeroEnd_ok
      fun s₃ ⟨r1₃, m₃, rd₃, wr₃, sp₃, g₃⟩ => ⟨by rw [g₃ _ (by decide), i0], r1₃, by rw [g₃ _ (by decide), i2],
        by rw [g₃ _ (by decide), i3], by rw [g₃ _ (by decide), i6], by rw [m₃]; exact hz,
        by rw [m₃]; exact hf, by rw [rd₃, hrd], by rw [wr₃, hwr'], by rw [sp₃, hsp]⟩

/-! ## The hint in memory -/

/-- The words of `h` are the hint `hA` of the spec. -/
def HArr (s₀ : State) (m : Mem) (hA : Array (Vector Bool n)) : Prop :=
  hA.size = uk s₀ ∧ ∀ i < uk s₀, ∀ j < 256,
    coeffAt m (State.addr (uH s₀)) (256 * i + j) = BitVec.ofNat 32 ((hA.getD i noHint)[j]!).toNat

/-- The code's state is the spec's: a hint and its index, at most `ω`, or a
failed check, and 256 in `r1`. -/
def SRel (s₀ : State) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => s.gpr .r1 = BitVec.ofNat 32 idx ∧ idx ≤ uω s₀ ∧ HArr s₀ s.mem hA
  | none, s => s.gpr .r1 = 256

/-- What the loops need of the state they start from: permission to read `y`
and write `h`, and the bytes of `y` of the entry state. -/
structure MainPre (s₀ sA : State) : Prop where
  rd : uyR s₀ ∈ sA.rd
  wr : uhR s₀ ∈ sA.wr
  y : ∀ t < uLen s₀, sA.mem (State.addr (uY s₀) + BitVec.ofNat 64 t) = s₀.mem (State.addr (uY s₀) + BitVec.ofNat 64 t)

/-- What stays the same in the loops that start from `sA`. -/
structure UCom (s₀ sA s : State) : Prop where
  r0 : s.gpr .r0 = uY s₀
  r2 : s.gpr .r2 = uW s₀
  rd : s.rd = sA.rd
  wr : s.wr = sA.wr
  sp : s.sp = sA.sp
  frame : Frame [uhR s₀] sA.mem s.mem

/-- A step of the loops over the coefficients: it writes at most `r1`, `r7`
and `r12`. -/
def KeepC (s s' : State) : Prop :=
  (∀ r, r ≠ .r1 → r ≠ .r7 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem KeepC.refl (s : State) : KeepC s s := ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl⟩

theorem KeepC.trans {s s' s'' : State} (h : KeepC s s') (h' : KeepC s' s'') : KeepC s s'' :=
  ⟨fun r a b c => (h'.1 r a b c).trans (h.1 r a b c), h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.trans h.2.2.2⟩

theorem UCom.of {s₀ sA s s' : State} (h : UCom s₀ sA s) (hk : KeepC s s') (hm : Frame [uhR s₀] s.mem s'.mem) :
    UCom s₀ sA s' :=
  ⟨(hk.1 _ (by decide) (by decide) (by decide)).trans h.r0, (hk.1 _ (by decide) (by decide) (by decide)).trans h.r2,
    hk.2.1.trans h.rd, hk.2.2.1.trans h.wr, hk.2.2.2.trans h.sp, h.frame.trans hm⟩

/-- Where the loops of polynomial `i` are. -/
structure PCom (s₀ sA : State) (i bound : Nat) (s : State) : Prop where
  com : UCom s₀ sA s
  r3 : s.gpr .r3 = uH s₀ + BitVec.ofNat 32 (1024 * i)
  r4 : s.gpr .r4 = BitVec.ofNat 32 bound

theorem PCom.of {s₀ sA s s' : State} {i bound : Nat} (h : PCom s₀ sA i bound s) (hk : KeepC s s')
    (hm : Frame [uhR s₀] s.mem s'.mem) : PCom s₀ sA i bound s' :=
  ⟨h.com.of hk hm, (hk.1 _ (by decide) (by decide) (by decide)).trans h.r3,
    (hk.1 _ (by decide) (by decide) (by decide)).trans h.r4⟩

theorem harr_set {s₀ : State} (hp : UPre s₀) {m : Mem} {hA : Array (Vector Bool n)} (hh : HArr s₀ m hA) {i b : Nat}
    (hi : i < uk s₀) (hb : b < 256) :
    HArr s₀ (m.writeW (coeffAddr (State.addr (uH s₀)) (256 * i + b)) (1 : BitVec 32)) (huSet i b hA) := by
  obtain ⟨hk4, hk8, -, -, -, -⟩ := ufacts hp
  refine ⟨by rw [huSet_size, hh.1], fun i' hi' j hj => ?_⟩
  rw [huSet_get (by rw [hh.1]; exact hi) (show j < n from hj)]
  by_cases e : i' = i ∧ j = b
  · obtain ⟨rfl, rfl⟩ := e
    rw [coeffAt_eq, Mem.readW_writeW_self32, ite_pos' ⟨rfl, rfl⟩]; rfl
  · rw [ite_neg' e, coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by
      have : 256 * i' + j ≠ 256 * i + b := fun h' => e ⟨by omega, by omega⟩
      omega) (by omega) (by omega)) (by decide), ← coeffAt_eq, hh.2 i' hi' j hj]

theorem harr_zero {s₀ : State} {m : Mem} (hz : ∀ t < 256 * uk s₀, coeffAt m (State.addr (uH s₀)) t = 0) :
    HArr s₀ m (Array.replicate (uk s₀) noHint) := by
  refine ⟨Array.size_replicate, fun i hi j hj => ?_⟩
  rw [hz _ (by omega)]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hi, ite_true, Option.getD_some, noHint]
  rw [getElem!_pos _ j (show j < n from hj), Vector.getElem_replicate]
  rfl

/-- A byte of `y`, unchanged by the writes to `h`. -/
theorem yByte {s₀ : State} (hp : UPre s₀) {sA s : State} (hA : MainPre s₀ sA) (hc : UCom s₀ sA s) {t : Nat}
    (ht : t < uLen s₀) : s.mem (State.addr (uY s₀) + BitVec.ofNat 64 t) = (uYs s₀).getD t 0 := by
  have fY := hp.fitY
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD, bytesAt_getD _ _ ht,
    ← hA.y t ht]
  refine hc.frame _ fun r hr hc' => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.d_yh _ (Offset.contains_base _ (by omega) (by omega)) hc'

/-! ## Blocks -/

theorem ltBit_ok (t x y : Reg) (s : State) :
    WP isa (.block (ltBit t x y)) s fun s' => s'.gpr t = (s.gpr x - s.gpr y) >>> 31 ∧
      s'.z = ((s.gpr x - s.gpr y) >>> 31 - 0 == 0) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ ∀ r, r ≠ t → s'.gpr r = s.gpr r := by
  run_block [ltBit, eq_self_iff_true, true_and, and_true]
  intro r hr; rw [ite_neg' hr, ite_neg' hr]

theorem set_blk {s : State} {y i h : BitVec 32} {b : Byte} (h0 : s.gpr .r0 = y) (h1 : s.gpr .r1 = i)
    (h3 : s.gpr .r3 = h) (ib : InRegions (s.rd ++ s.wr) (State.addr (y + i + BitVec.ofNat 32 0)) 1)
    (hb : s.mem (State.addr (y + i + BitVec.ofNat 32 0)) = b)
    (ow : InRegions s.wr (State.addr (h + (b.setWidth 32 <<< 2) + BitVec.ofNat 32 0)) 4) :
    WP isa (.block hbuSet) s fun s' => s'.gpr .r1 = i + 1 ∧
      s'.mem = s.mem.writeW (State.addr (h + (b.setWidth 32 <<< 2) + BitVec.ofNat 32 0)) (1 : BitVec 32) ∧
      KeepC s s' := by
  run_block [hbuSet, KeepC, h0, h1, h3, ib, hb, ow, true_and, and_true]
  intro r a b c; rw [ite_neg' a, ite_neg' b, ite_neg' c, ite_neg' c, ite_neg' c]

theorem fail_ok {s : State} :
    WP isa hbuFail s fun s' => s'.gpr .r1 = 256 ∧ s'.mem = s.mem ∧ KeepC s s' := by
  unfold hbuFail
  run_block [KeepC, true_and, and_true]
  intro r a _ _; rw [ite_neg' a]

theorem keepC_r7 {s s' : State} (h : ∀ r, r ≠ .r7 → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) : KeepC s s' := ⟨fun r _ b _ => h r b, hrd, hwr, hsp⟩

/-- The byte `strb`'s index of `h`, as a word offset. -/
theorem shl2_byte (b : Byte) : (b.setWidth 32 <<< 2 : BitVec 32) = BitVec.ofNat 32 (4 * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, toNat_ofNat32 (by have := b.isLt; omega),
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega), Nat.shiftLeft_eq]
  have := b.isLt
  omega

theorem nextLoad_blk {s : State} {y i : BitVec 32} (h0 : s.gpr .r0 = y) (h1 : s.gpr .r1 = i)
    (ic : InRegions (s.rd ++ s.wr) (State.addr (y + i + BitVec.ofNat 32 0)) 1)
    (ip : InRegions (s.rd ++ s.wr) (State.addr (y + i - 1 + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.dp .add .r12 .r0 (.reg .r1), .ldrb .r7 .r12 0, .dp .sub .r12 .r12 (.imm 1), .ldrb .r12 .r12 0])
      s fun s' => s'.gpr .r7 = (s.mem (State.addr (y + i + BitVec.ofNat 32 0))).setWidth 32 ∧
        s'.gpr .r12 = (s.mem (State.addr (y + i - 1 + BitVec.ofNat 32 0))).setWidth 32 ∧ s'.mem = s.mem ∧
        s'.gpr .r1 = i ∧ KeepC s s' := by
  run_block [KeepC, h0, h1, ic, ip, true_and, and_true]
  intro r _ b c; rw [ite_neg' c, ite_neg' c, ite_neg' b, ite_neg' c]

theorem ptr_pred (p : BitVec 32) {x : Nat} (h : 1 ≤ x) :
    p + BitVec.ofNat 32 x - 1 = p + BitVec.ofNat 32 (x - 1) := by
  rw [show x = (x - 1) + 1 by omega, ← ofNat_succ32, ← BitVec.add_assoc, BitVec.add_sub_cancel,
    Nat.add_sub_cancel]

section
variable {s₀ : State} (hp : UPre s₀) {sA : State} (hA : MainPre s₀ sA)
include hp hA

/-- Setting coefficient `y[index]` of polynomial `i`. -/
theorem set_ok {i bound idx : Nat} (hi : i < uk s₀) (hidx : idx < uLen s₀) {hA' : Array (Vector Bool n)}
    {s : State} (hP : PCom s₀ sA i bound s) (h1 : s.gpr .r1 = BitVec.ofNat 32 idx) (hh : HArr s₀ s.mem hA') :
    WP isa (.block hbuSet) s fun s' =>
      PCom s₀ sA i bound s' ∧ s'.gpr .r1 = BitVec.ofNat 32 (idx + 1) ∧
        HArr s₀ s'.mem (huSet i ((uYs s₀).getD idx 0).toNat hA') ∧ KeepC s s' := by
  obtain ⟨hk4, hk8, -, -, hsum, hL88⟩ := ufacts hp
  have fY := hp.fitY
  have fH := hp.fitH
  have hl := hp.hlen
  have hbl := ((uYs s₀).getD idx 0).isLt
  have ey : State.addr (uY s₀ + BitVec.ofNat 32 idx + BitVec.ofNat 32 0) = State.addr (uY s₀) + BitVec.ofNat 64 idx := by
    rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
  have hb : s.mem (State.addr (uY s₀ + BitVec.ofNat 32 idx + BitVec.ofNat 32 0)) = (uYs s₀).getD idx 0 := by
    rw [ey]; exact yByte hp hA hP.com hidx
  have eh : State.addr (uH s₀ + BitVec.ofNat 32 (1024 * i) + (((uYs s₀).getD idx 0).setWidth 32 <<< 2) +
      BitVec.ofNat 32 0) = coeffAddr (State.addr (uH s₀)) (256 * i + ((uYs s₀).getD idx 0).toNat) := by
    rw [shl2_byte, ptr_add, addr_ptr _ _ _ (by omega)]
    congr 2; omega
  have hin : (uhR s₀).Contains (coeffAddr (State.addr (uH s₀)) (256 * i + ((uYs s₀).getD idx 0).toNat)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (set_blk hP.com.r0 h1 hP.r3 (by
      rw [ey, hP.com.rd, hP.com.wr]
      exact ⟨_, List.mem_append_left _ hA.rd, Offset.contains_base _ (by omega) (by omega)⟩) hb
      (by rw [eh, hP.com.wr]; exact ⟨_, hA.wr, hin⟩))
    fun s' ⟨r1', m', k'⟩ => ⟨hP.of k' ?_, by rw [r1', ofNat_succ32], ?_, k'⟩
  · rw [m', eh]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hin
  · rw [m', eh]; exact harr_set hp hh hi hbl

/-- The first coefficient of polynomial `i`, from the index `first`. -/
theorem first_ok {i bound first : Nat} (hi : i < uk s₀) (hfb : first < bound) (hbω : bound ≤ uω s₀)
    {hA' : Array (Vector Bool n)} {s : State} (hP : PCom s₀ sA i bound s) (h1 : s.gpr .r1 = BitVec.ofNat 32 first)
    (hh : HArr s₀ s.mem hA') :
    WP isa (.block (hbuSet ++ hbuMore)) s fun s' =>
      PCom s₀ sA i bound s' ∧ s'.gpr .r1 = BitVec.ofNat 32 (first + 1) ∧
        HArr s₀ s'.mem (huSet i ((uYs s₀).getD first 0).toNat hA') ∧ s'.z = decide (bound ≤ first + 1) ∧
        KeepC s s' := by
  obtain ⟨-, -, -, hω80, hsum, -⟩ := ufacts hp
  rw [WP.block_append_iff]
  refine WP.mono (set_ok hp hA hi (by omega) hP h1 hh) fun s₁ ⟨hP₁, r1₁, hh₁, k₁⟩ => ?_
  refine WP.mono (ltBit_ok .r7 .r1 .r4 s₁) fun s₂ ⟨_, z₂, m₂, rd₂, wr₂, sp₂, g₂⟩ => ?_
  have k₂ := keepC_r7 g₂ rd₂ wr₂ sp₂
  refine ⟨hP₁.of k₂ (by rw [m₂]; exact Frame.refl _ _), by rw [g₂ _ (by decide), r1₁], by rw [m₂]; exact hh₁, ?_,
    k₁.trans k₂⟩
  rw [z₂, r1₁, hP₁.r4, ltBit_z (by rw [toNat_ofNat32 (by omega)]; omega) (by rw [toNat_ofNat32 (by omega)]; omega),
    toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]

/-- A coefficient after the first: checked against the previous one. -/
theorem next_ok {i bound first idx : Nat} (hi : i < uk s₀) (hfi : first < idx) (hib : idx < bound)
    (hbω : bound ≤ uω s₀) {hA' : Array (Vector Bool n)} {s : State} (hP : PCom s₀ sA i bound s)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 idx) (hh : HArr s₀ s.mem hA') :
    WP isa hbuNext s fun s' => PCom s₀ sA i bound s' ∧
      (match huStep (uYs s₀) i first (hA', idx) 0 with
        | some (hA'', idx') => s'.gpr .r1 = BitVec.ofNat 32 idx' ∧ HArr s₀ s'.mem hA'' ∧
          s'.z = decide (bound ≤ idx')
        | none => s'.gpr .r1 = 256 ∧ s'.z = true) ∧ KeepC s s' := by
  obtain ⟨-, -, -, hω80, hsum, hL88⟩ := ufacts hp
  have fY := hp.fitY
  have ec : State.addr (uY s₀ + BitVec.ofNat 32 idx + BitVec.ofNat 32 0) = State.addr (uY s₀) + BitVec.ofNat 64 idx := by
    rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
  have ep : State.addr (uY s₀ + BitVec.ofNat 32 idx - 1 + BitVec.ofNat 32 0) =
      State.addr (uY s₀) + BitVec.ofNat 64 (idx - 1) := by
    rw [ptr_pred _ (by omega), addr_ptr _ _ _ (by omega), Nat.add_zero]
  have hrw : s.rd ++ s.wr = sA.rd ++ sA.wr := by rw [hP.com.rd, hP.com.wr]
  unfold hbuNext
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (nextLoad_blk hP.com.r0 h1 (by
      rw [ec, hrw]; exact ⟨_, List.mem_append_left _ hA.rd, Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [ep, hrw]; exact ⟨_, List.mem_append_left _ hA.rd, Offset.contains_base _ (by omega) (by omega)⟩))
    fun s₁ ⟨r7₁, r12₁, m₁, r1₁, k₁⟩ => ?_
  rw [ec, yByte hp hA hP.com (by omega)] at r7₁
  rw [ep, yByte hp hA hP.com (by omega)] at r12₁
  have hP₁ : PCom s₀ sA i bound s₁ := hP.of k₁ (by rw [m₁]; exact Frame.refl _ _)
  refine WP.mono (ltBit_ok .r7 .r12 .r7 s₁) fun s₂ ⟨_, z₂, m₂, rd₂, wr₂, sp₂, g₂⟩ => ?_
  have k₂ := keepC_r7 g₂ rd₂ wr₂ sp₂
  have hP₂ : PCom s₀ sA i bound s₂ := hP₁.of k₂ (by rw [m₂]; exact Frame.refl _ _)
  have hcb := ((uYs s₀).getD idx 0).isLt
  have hpb := ((uYs s₀).getD (idx - 1) 0).isLt
  rw [r7₁, r12₁, ltBit_z (by rw [byte_toNat32]; omega) (by rw [byte_toNat32]; omega), byte_toNat32,
    byte_toNat32] at z₂
  have h1₂ : s₂.gpr .r1 = BitVec.ofNat 32 idx := by rw [g₂ _ (by decide), r1₁]
  refine WP.seq (WP.ite (M := isa) _ (show some s₂.z = _ from rfl) (fun hge => ?_) (fun hlt => ?_))
  · -- Not increasing: fail.
    have hge : ((uYs s₀).getD idx 0).toNat ≤ ((uYs s₀).getD (idx - 1) 0).toNat := by
      rw [z₂] at hge; simpa using hge
    have hs : huStep (uYs s₀) i first (hA', idx) 0 = none := by
      simp only [huStep]; rw [ite_pos' ⟨hfi, hge⟩]
    rw [hs]
    refine WP.mono fail_ok fun s₃ ⟨r1₃, m₃, k₃⟩ => ?_
    refine WP.mono (ltBit_ok .r7 .r1 .r4 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_
    have k₄ := keepC_r7 g₄ rd₄ wr₄ sp₄
    refine ⟨hP₂.of (k₃.trans k₄) (by rw [m₄, m₃]; exact Frame.refl _ _), ⟨by rw [g₄ _ (by decide), r1₃], ?_⟩,
      ((k₁.trans k₂).trans k₃).trans k₄⟩
    rw [z₄, r1₃, (hP₂.of k₃ (by rw [m₃]; exact Frame.refl _ _)).r4,
      ltBit_z (by decide) (by rw [toNat_ofNat32 (by omega)]; omega), toNat_ofNat32 (by omega),
      show (256 : BitVec 32).toNat = 256 from rfl]
    exact decide_eq_true (by omega)
  · -- `y[index - 1] < y[index]`: set it.
    have hlt : ((uYs s₀).getD (idx - 1) 0).toNat < ((uYs s₀).getD idx 0).toNat := by
      rw [z₂] at hlt; simpa using hlt
    have hs : huStep (uYs s₀) i first (hA', idx) 0 = some (huSet i ((uYs s₀).getD idx 0).toNat hA', idx + 1) := by
      simp only [huStep]; rw [ite_neg' (by omega)]
    rw [hs]
    refine WP.mono (set_ok hp hA hi (hA' := hA') (by omega) hP₂ h1₂ (by rw [m₂, m₁]; exact hh))
      fun s₃ ⟨hP₃, r1₃, hh₃, k₃⟩ => ?_
    refine WP.mono (ltBit_ok .r7 .r1 .r4 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_
    have k₄ := keepC_r7 g₄ rd₄ wr₄ sp₄
    refine ⟨hP₃.of k₄ (by rw [m₄]; exact Frame.refl _ _), ⟨by rw [g₄ _ (by decide), r1₃], by rw [m₄]; exact hh₃, ?_⟩,
      ((k₁.trans k₂).trans k₃).trans k₄⟩
    rw [z₄, r1₃, hP₃.r4, ltBit_z (by rw [toNat_ofNat32 (by omega)]; omega) (by rw [toNat_ofNat32 (by omega)]; omega),
      toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]

end

end VG.Proof.MlDsa.Arm.Pack.Hint.Unpack
