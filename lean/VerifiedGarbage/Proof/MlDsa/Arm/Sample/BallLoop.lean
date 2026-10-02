import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
import VerifiedGarbage.Impl.MlDsa.Arm.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask

/-!
# ML-DSA on 32-bit ARM: the loops of `vg_mldsa_sample_in_ball`

A call is described by `spOf σ` (`c̃`, its length, `scratch`, `c` and `τ`),
and the XOF output is `X σ`, `H(c̃, 272)`. The polynomial `c` is kept in
memory as the words that represent its coefficients modulo `q` (`CStored`);
the first loop zeroes it (`zero_ok`). Iteration `t` of the second starts from
`BAt σ t`: with the polynomial and `i` (in `r2`) that `bFold` computes from
the first `t` bytes after the sign bits, and the sign bits not yet used in
`r1` (low word) and `r4` (high word), whose value `r1 + 2³² r4` is that of the
first 8 bytes shifted right once per coefficient set (`Sg`). The pieces of an
iteration are `pieceA` (`i ≥ 256`?), `tryA` (the byte `j`, and `j ≤ i`?),
`setOk` (`c[i] ← c[j]`, `c[j] ← ±1`) and `pieceC` (the step).
-/

namespace VG.Proof.MlDsa.Arm.Sample.Ball

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H IPoly n ofInt coeffAt)
open VG.Spec.Sha3 (bytesAt)

/-- The call, from the entry state: `ctilde = r0`, `len = r1`, `tau = r2`,
`c = r3` and `scratch` on the stack. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r0, (σ.gpr .r1).toNat, stackArg σ 0, σ.gpr .r3, σ.gpr .r2⟩

/-- `τ`. -/
abbrev tau (σ : State) : Nat := (σ.gpr .r2).toNat

/-- `c̃`. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r0)) (σ.gpr .r1).toNat

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H (B σ) 272

/-- The first `i`. -/
abbrev i0 (σ : State) : Nat := 256 - tau σ

/-- The sign bits, as a number. -/
abbrev Wn (σ : State) : Nat := leNat ((X σ).take 8)

/-- The polynomial and `i` after `t` iterations. -/
abbrev St (σ : State) (t : Nat) : IPoly × Nat :=
  bFold (tau σ) (signs (X σ)) (Vector.replicate n 0, i0 σ) (((X σ).drop 8).take t)

/-- The polynomial `c` of `R` is stored at `p`, as elements of `ℤ_q`. -/
def CStored (m : Mem) (p : Addr) (c : IPoly) : Prop := ∀ k < 256, coeffAt m p k = zw (ofInt c[k]!)

/-- What the proofs need of the entry state. -/
structure Pre (σ : State) : Prop where
  ok : SpOk (spOf σ) σ
  arg : InRegions (σ.rd ++ σ.wr) (stackArgAddr σ 0) 4
  tau_ge : 39 ≤ tau σ
  tau_le : tau σ ≤ 60

theorem X_length (σ : State) : (X σ).length = 272 := H_length _ _

theorem St_le (σ : State) (t : Nat) : (St σ t).2 ≤ 256 := bFold_le (by simp) _

theorem St_ge (σ : State) (t : Nat) : i0 σ ≤ (St σ t).2 :=
  bFold_ge (τ := tau σ) (h := signs (X σ)) (Vector.replicate n 0, i0 σ) _

/-- The sign bits not yet used, from their value. -/
abbrev Sg (σ : State) (i : Nat) (s : State) : Prop :=
  (s.gpr .r1).toNat + 2 ^ 32 * (s.gpr .r4).toNat = Wn σ / 2 ^ (i - i0 σ)

/-! ## Zeroing -/

/-- After `k` iterations of the zeroing loop. -/
structure ZAt (σ : State) (k : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  r7 : s.gpr .r7 = σ.gpr .r2
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  r12 : s.gpr .r12 = 0
  r0 : s.gpr .r0 = σ.gpr .r3 + BitVec.ofNat 32 (4 * k)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (256 - k))
  zero : ∀ j < k, coeffAt s.mem (spOf σ).A j = 0

/-- After the zeroing. -/
structure ZDone (σ : State) (s : State) : Prop where
  env : Env (spOf σ) σ s
  r7 : s.gpr .r7 = σ.gpr .r2
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  st : CStored s.mem (spOf σ).A (Vector.replicate n 0)

theorem zInit_ok (s : State) :
    WP isa (.block [.mov .r12 (.imm 0), .mov .r0 (.reg .r5), .mov .r3 (.imm 256)]) s fun s' =>
      s'.gpr .r12 = 0 ∧ s'.gpr .r0 = s.gpr .r5 ∧ s'.gpr .r3 = BitVec.ofNat 32 256 ∧
        (∀ r, r ≠ .r12 → r ≠ .r0 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [and_self, and_true, true_and]
  exact fun r h12 h0 h3 => by simp [h12, h0, h3]

theorem zStep_ok (s : State) {a : Addr} (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (hw : InRegions s.wr a 4) :
    WP isa (.block [.str .r12 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]) s fun s' =>
      s'.mem = s.mem.writeW a (s.gpr .r12) ∧ s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 4 ∧
        s'.gpr .r3 = s.gpr .r3 - BitVec.ofNat 32 1 ∧ s'.z = (s.gpr .r3 - BitVec.ofNat 32 1 == 0) ∧
        (∀ r, r ≠ .r0 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [ha, hw, and_self, and_true, true_and]
  refine ⟨rfl, rfl, rfl, fun r h0 h3 => ?_⟩
  simp [h0, h3]

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

theorem zBody_ok {k : Nat} (hk : k < 256) {s : State} (h : ZAt σ k s) :
    WP isa (.block [.str .r12 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]) s fun s' =>
      ZAt σ (k + 1) s' ∧ s'.z = decide (k + 1 = 256) := by
  have ea : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = coeffAddr (spOf σ).A k := by
    rw [h.r0]; exact addr_coeff hp.fa (by omega) hk
  have hin : InRegions s.wr (coeffAddr (spOf σ).A k) 4 := by
    rw [h.env.wr, hp.wr]; exact ⟨(spOf σ).aR, by simp, coeff_contains _ hk⟩
  refine WP.mono (zStep_ok s ea hin) fun s' ⟨m, r0, r3, z, g, rd, wr, sp⟩ => ?_
  have hf : Frame [(spOf σ).aR] s.mem s'.mem := by
    rw [m]; exact (Frame.refl _ _).writeW (by simp) _ (coeff_contains _ hk)
  refine ⟨⟨h.env.step hp hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
    (g _ (by decide) (by decide)) (g _ (by decide) (by decide)) rd wr sp,
    by rw [g _ (by decide) (by decide)]; exact h.r7, ?_, by rw [g _ (by decide) (by decide)]; exact h.r12,
    by rw [r0, h.r0, ptr_add_add32, Nat.mul_succ], by rw [r3, h.r3]; exact count_sub (k := 1) hk, fun j hj => ?_⟩,
    by rw [z, h.r3]; exact count_z (k := 1) hk (by decide) (by decide)⟩
  · rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 272) (by omega))).symm) (by omega)]
    exact h.out
  · rw [m, coeffAt_writeW _ _ (by omega) hk, h.r12]
    by_cases e : k = j
    · rw [ifT e]
    · rw [ifF e]; exact h.zero j (by omega)

/-- The zeroing loop, from what the sponge leaves. -/
theorem zero_ok {s : State} (h : J6 136 272 (spOf σ) σ s) : WP isa bZero s (ZDone σ) := by
  refine WP.seq (WP.mono (zInit_ok s) fun s1 ⟨r12, r0, r3, g, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_ne (ZAt σ) (N := 256) (by decide) (fun k hk s h => zBody_ok hp hk h)
    (fun s h => ⟨h.env, h.r7, h.out, fun k hk => ?_⟩) ⟨h.env.same m (g _ (by decide) (by decide) (by decide))
      (g _ (by decide) (by decide) (by decide)) rd wr sp, by rw [g _ (by decide) (by decide) (by decide), h.r7],
      by rw [m, h.out]; exact (H_eq _ _).symm, r12, by rw [r0, h.env.r5]; simp, r3,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [h.zero k hk, getElem!_pos _ k (by simp only [n]; omega), Vector.getElem_replicate]
  rfl

end

/-! ## Setting a coefficient -/

/-- The word of the sign: 1, or `q - 1` for -1. -/
theorem sgn_word (b : Bool) :
    (if b then (BitVec.ofNat 32 8380416) else 1) = zw (ofInt (if b then -1 else 1)) := by
  cases b <;> decide

/-- `r1 & 1`, compared with zero. -/
theorem and1_beq (x : BitVec 32) : ((x &&& 1) - 0 == 0) = decide (x.toNat % 2 = 0) := by
  have h1 : (x &&& 1).toNat = x.toNat % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [show (x &&& 1) - 0 = x &&& 1 from BitVec.sub_zero _]
  by_cases h : x.toNat % 2 = 0
  · rw [decide_eq_true h, beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by rw [h1, h]; rfl)
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro e; have := congrArg BitVec.toNat e; rw [h1] at this; exact h this

/-- The sign bits shifted right by one, from `r4:r1`. -/
theorem shr_or (x y : BitVec 32) :
    (x >>> 1 ||| y <<< 31).toNat = x.toNat / 2 + 2 ^ 31 * (y.toNat % 2) := by
  have hx : (x >>> 1).toNat = x.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hy : (y <<< 31).toNat = 2 ^ 31 * (y.toNat % 2) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  rw [BitVec.toNat_or, hx, hy, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (by have := x.isLt; omega), Nat.add_comm]

theorem bSet1_ok (s : State) {A B : Addr} (hA : State.addr (s.gpr .r5 + s.gpr .r8 <<< 2 + BitVec.ofNat 32 0) = A)
    (hB : State.addr (s.gpr .r5 + s.gpr .r2 <<< 2 + BitVec.ofNat 32 0) = B)
    (hr : InRegions (s.rd ++ s.wr) A 4) (hw : InRegions s.wr B 4) :
    WP isa (.block [.dp .add .r10 .r5 (.shifted .r8 .lsl 2), .ldr .r11 .r10 0,
      .dp .add .r12 .r5 (.shifted .r2 .lsl 2), .str .r11 .r12 0, .dp .and .r11 .r1 (.imm 1), .cmp .r11 (.imm 0)]) s
      fun s' => s'.mem = s.mem.writeW B (s.mem.readW A 32) ∧ s'.gpr .r10 = s.gpr .r5 + s.gpr .r8 <<< 2 ∧
        s'.z = decide ((s.gpr .r1).toNat % 2 = 0) ∧
        (∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  have hA' : State.addr (s.gpr .r5 + s.gpr .r8 <<< 2 + 0) = A := hA
  have hB' : State.addr (s.gpr .r5 + s.gpr .r2 <<< 2 + 0) = B := hB
  run_block [hA, hB, hA', hB', hr, hw, and1_beq, and_self, and_true, true_and]
  exact fun r h10 h11 h12 => by simp [h10, h11, h12]

/-- The word of the sign, from `Z` = the sign bit is 0. -/
theorem bSign_ok (s : State) (b : Bool) (hz : s.z = !b) :
    WP isa (.ite .eq (.block [.mov .r11 (.imm 1)]) (.block [.movw .r11 0xE000, .movt .r11 0x7F])) s fun s' =>
      s'.gpr .r11 = (if b then (BitVec.ofNat 32 8380416) else 1) ∧ (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine WP.ite s.z rfl (fun e => ?_) (fun e => ?_)
  · have hb : b = false := by rw [hz] at e; simpa using e
    subst hb
    run_block [and_self, and_true, true_and]
    exact fun r h => by simp [h]
  · have hb : b = true := by rw [hz] at e; simpa using e
    subst hb
    run_block [and_self, and_true, true_and]
    exact fun r h => by simp [h]

theorem bSet3_ok (s : State) {A : Addr} (hA : State.addr (s.gpr .r10 + BitVec.ofNat 32 0) = A)
    (hw : InRegions s.wr A 4) :
    WP isa (.block [.str .r11 .r10 0, .mov .r1 (.shifted .r1 .lsr 1), .dp .orr .r1 .r1 (.shifted .r4 .lsl 31),
        .mov .r4 (.shifted .r4 .lsr 1), .dp .add .r2 .r2 (.imm 1)]) s fun s' =>
      s'.mem = s.mem.writeW A (s.gpr .r11) ∧ s'.gpr .r1 = s.gpr .r1 >>> 1 ||| s.gpr .r4 <<< 31 ∧
        s'.gpr .r4 = s.gpr .r4 >>> 1 ∧ s'.gpr .r2 = s.gpr .r2 + 1 ∧
        (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  run_block [hA, hw, and_self, and_true, true_and]
  exact fun r h1 h2 h4 => by simp [h1, h2, h4]

/-! ## An iteration -/

/-- Byte `t` after the sign bits. -/
abbrev Xb (σ : State) (t : Nat) : Byte := (X σ).getD (8 + t) 0

theorem take_succ' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem St_succ (σ : State) {t : Nat} (ht : t < 264) :
    St σ (t + 1) = bStep (tau σ) (signs (X σ)) (St σ t) (Xb σ t) := by
  simp only [St]
  rw [take_succ' _ (by rw [List.length_drop, X_length]; omega), bFold_snoc, List.getD_eq_getElem?_getD,
    List.getElem?_drop, ← List.getD_eq_getElem?_getD]

/-- At the start of iteration `t`. -/
structure BAt (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  r0 : s.gpr .r0 = stackArg σ 0 + BitVec.ofNat 32 (848 + t)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (St σ t).2
  sg : Sg σ (St σ t).2 s
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (264 - t))
  st : CStored s.mem (spOf σ).A (St σ t).1

/-- `BAt` after code that writes no memory and keeps `r0`–`r6`. -/
theorem BAt.same {σ s s' : State} {t : Nat} (h : BAt σ t s) (hm : s'.mem = s.mem)
    (g : ∀ r ∈ [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6], s'.gpr r = s.gpr r) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : BAt σ t s' :=
  ⟨h.env.same hm (g .r5 (by simp)) (g .r6 (by simp)) rd wr sp, by rw [hm]; exact h.out,
    (g .r0 (by simp)).trans h.r0, (g .r2 (by simp)).trans h.r2,
    by show _ = _; rw [g .r1 (by simp), g .r4 (by simp)]; exact h.sg, (g .r3 (by simp)).trans h.r3,
    by rw [hm]; exact h.st⟩

/-- After the test of `i`. -/
structure M1 (σ : State) (t : Nat) (s : State) : Prop where
  bat : BAt σ t s
  z : s.z = decide (256 ≤ (St σ t).2)

/-- After the test of the byte `j`, if `i < 256`. -/
structure T1 (σ : State) (t : Nat) (s : State) : Prop where
  bat : BAt σ t s
  lt : (St σ t).2 < 256
  r8 : s.gpr .r8 = BitVec.ofNat 32 (Xb σ t).toNat
  z : s.z = decide ((Xb σ t).toNat ≤ (St σ t).2)

/-- After the coefficients of iteration `t`. -/
structure M2 (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  r0 : s.gpr .r0 = stackArg σ 0 + BitVec.ofNat 32 (848 + t)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (St σ (t + 1)).2
  sg : Sg σ (St σ (t + 1)).2 s
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (264 - t))
  st : CStored s.mem (spOf σ).A (St σ (t + 1)).1

theorem pieceA {σ : State} {t : Nat} {s : State} (h : BAt σ t s) : WP isa (.block jFull) s (M1 σ t) :=
  WP.mono (jFull_ok s h.r2 (by have := St_le σ t; omega)) fun _ ⟨z, g, m, rd, wr, sp⟩ =>
    ⟨h.same m (fun r hr => g r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
      rd wr sp, z⟩

theorem ldrb_ok (s : State) {A : Addr} (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = A)
    (hr : InRegions (s.rd ++ s.wr) A 1) :
    WP isa (.block [.ldrb .r8 .r0 0]) s fun s' => s'.gpr .r8 = BitVec.ofNat 32 (s.mem A).toNat ∧
      (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [ha, hr, and_self, and_true, true_and]
  refine ⟨BitVec.eq_of_toNat_eq ?_, fun r h => by simp [h]⟩
  rw [setWidth32_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.mem A).isLt; omega)]

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

theorem tryA {t : Nat} (ht : t < 264) {s : State} (h : M1 σ t s) (hz : s.z = false) :
    WP isa (.block [.ldrb .r8 .r0 0, .dp .sub .r11 .r2 (.reg .r8), .mov .r11 (.shifted .r11 .lsr 31),
      .cmp .r11 (.imm 0)]) s (T1 σ t) := by
  have hl : (St σ t).2 < 256 := by
    have := h.z; rw [hz] at this; simp at this; omega
  have l := h.bat
  have ea : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = (spOf σ).at' (840 + (8 + t)) := by
    rw [l.r0, ptr_add_add32, show 848 + t + 0 = 840 + (8 + t) by omega]; exact at_eq hp (by omega)
  have hb : s.mem ((spOf σ).at' (840 + (8 + t))) = Xb σ t := by
    have := congrArg (fun L => L.getD (8 + t) 0) l.out
    rw [MlKem.bytesAt_getD _ _ (by omega), add_ofNat_add] at this
    exact this
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ldrb_ok s ea (inScrRd hp l.env (by omega))) fun s1 ⟨g8, g1, m1, rd1, wr1, sp1⟩ => ?_
  rw [hb] at g8
  have l1 : BAt σ t s1 := l.same m1 (fun r hr => g1 r (by
    simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) rd1 wr1 sp1
  have hj := (Xb σ t).isLt
  refine WP.mono (sgn_ok s1 .r2 (.reg .r8) (y := BitVec.ofNat 32 (Xb σ t).toNat) (by simp [Op2.eval, g8])
    (by rw [l1.r2, toNat_ofNat32 (by omega)]; omega) (by rw [toNat_ofNat32 (by omega)]; omega))
    fun s2 ⟨z2, g2, m2, rd2, wr2, sp2⟩ => ⟨l1.same m2 (fun r hr => g2 r (by
      simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) rd2 wr2 sp2, hl,
      by rw [g2 _ (by decide), g8], ?_⟩
  rw [z2, l1.r2, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]

omit hp in
/-- The sign bit of `i`, from the sign bits not yet used. -/
theorem sign_bit {i : Nat} (hτ : tau σ ≤ 256) (hi0 : i0 σ ≤ i) {s : State} (hs : Sg σ i s) :
    decide ((s.gpr .r1).toNat % 2 = 0) = !(signs (X σ)).getD (i + tau σ - 256) false := by
  have hs' : (s.gpr .r1).toNat + 2 ^ 32 * (s.gpr .r4).toNat = Wn σ / 2 ^ (i - i0 σ) := hs
  have e0 : i0 σ = 256 - tau σ := rfl
  rw [signs_getD, testBit_eq, show i + tau σ - 256 = i - i0 σ by omega]
  have e : (s.gpr .r1).toNat % 2 = Wn σ / 2 ^ (i - i0 σ) % 2 := by rw [← hs']; omega
  rw [e]
  by_cases h : Wn σ / 2 ^ (i - i0 σ) % 2 = 1
  · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
  · rw [decide_eq_true (by omega), decide_eq_false h]; rfl

omit hp in
theorem sg_succ {i : Nat} (hi0 : i0 σ ≤ i) {s s' : State} (hs : Sg σ i s)
    (g1 : s'.gpr .r1 = s.gpr .r1 >>> 1 ||| s.gpr .r4 <<< 31) (g4 : s'.gpr .r4 = s.gpr .r4 >>> 1) :
    Sg σ (i + 1) s' := by
  have hs' : (s.gpr .r1).toNat + 2 ^ 32 * (s.gpr .r4).toNat = Wn σ / 2 ^ (i - i0 σ) := hs
  show _ = _
  rw [g1, g4, shr_or, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show i + 1 - i0 σ = i - i0 σ + 1 by omega,
    Nat.pow_succ 2 (i - i0 σ), ← Nat.div_div_eq_div_mul, ← hs']
  omega

/-- `c[i] ← c[j]`, `c[j] ← ±1`, `i` incremented. -/
theorem setOk (hτ : tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : T1 σ t s) (hz : s.z = true) :
    WP isa bSet s (M2 σ t) := by
  have l := h.bat
  have hi := h.lt
  have hj : (Xb σ t).toNat ≤ (St σ t).2 := by have := h.z; rw [hz] at this; simpa using this
  have hA := addr_aJ hp (j := (Xb σ t).toNat) (by omega)
  have hB := addr_aJ hp (j := (St σ t).2) hi
  rw [← h.r8, ← l.env.r5] at hA
  rw [← l.r2, ← l.env.r5] at hB
  have inA : (spOf σ).aR.Contains (coeffAddr (spOf σ).A (Xb σ t).toNat) 4 := coeff_contains _ (by omega)
  have inB : (spOf σ).aR.Contains (coeffAddr (spOf σ).A (St σ t).2) 4 := coeff_contains _ hi
  have wA : (spOf σ).aR ∈ s.wr := by rw [l.env.wr, hp.wr]; simp
  refine WP.seq (WP.mono (bSet1_ok s hA hB ⟨_, List.mem_append_right _ wA, inA⟩ ⟨_, wA, inB⟩)
    fun s1 ⟨m1, g10, z1, g1, rd1, wr1, sp1⟩ => ?_)
  rw [sign_bit hτ (St_ge σ t) l.sg] at z1
  refine WP.seq (WP.mono (bSign_ok s1 _ z1) fun s2 ⟨g11, g2, m2, rd2, wr2, sp2⟩ => ?_)
  have e10 : State.addr (s2.gpr .r10 + BitVec.ofNat 32 0) = coeffAddr (spOf σ).A (Xb σ t).toNat := by
    rw [g2 _ (by decide), g10]; exact hA
  refine WP.mono (bSet3_ok s2 e10 (by rw [wr2, wr1]; exact ⟨_, wA, inA⟩))
    fun s3 ⟨m3, g1', g4', g2', g3, rd3, wr3, sp3⟩ => ?_
  have k : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s3.gpr r = s.gpr r :=
    fun r a b c d e f => by rw [g3 r a b c, g2 r e, g1 r d e f]
  have hst := St_succ σ ht
  rw [bStep, ifT hi, ifF (show ¬ (Xb σ t).toNat > (St σ t).2 by omega)] at hst
  have hf : Frame [(spOf σ).aR] s.mem s3.mem := by
    rw [m3, m2, m1]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ inB).writeW (List.mem_singleton_self _) _ inA
  refine ⟨l.env.step hp hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
    (k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [rd3, rd2, rd1]) (by rw [wr3, wr2, wr1]) (by rw [sp3, sp2, sp1]), ?_,
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l.r0, ?_, ?_,
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l.r3, ?_⟩
  · rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 272) (by omega))).symm) (by omega)]
    exact l.out
  · rw [g2', g2 _ (by decide), g1 _ (by decide) (by decide) (by decide), l.r2, hst, BitVec.ofNat_add]; rfl
  · rw [hst]
    refine sg_succ (St_ge σ t) l.sg ?_ ?_
    · rw [g1', g2 _ (by decide), g2 _ (by decide), g1 _ (by decide) (by decide) (by decide),
        g1 _ (by decide) (by decide) (by decide)]
    · rw [g4', g2 _ (by decide), g1 _ (by decide) (by decide) (by decide)]
  · intro k hk
    rw [hst, m3, m2, m1, g11, sgn_word, coeffAt_writeW _ _ hk (by omega), coeffAt_writeW _ _ hk hi,
      ipoly_set!_get _ _ (by simp only [n]; omega), ipoly_set!_get _ _ (by simp only [n]; omega)]
    by_cases ejk : (Xb σ t).toNat = k
    · rw [ifT ejk, ifT ejk]
    · rw [ifF ejk, ifF ejk]
      by_cases eik : (St σ t).2 = k
      · subst eik; rw [ifT rfl, ifT rfl, ← coeffAt_eq, l.st _ (by omega)]
      · rw [ifF eik, ifF eik]; exact l.st k hk

omit hp in
/-- `M2` when iteration `t` changes nothing. -/
theorem M2.of_same {t : Nat} {s : State} (l : BAt σ t s) (hst : St σ (t + 1) = St σ t) : M2 σ t s :=
  ⟨l.env, l.out, l.r0, by rw [hst]; exact l.r2, by rw [hst]; exact l.sg, l.r3, by rw [hst]; exact l.st⟩

theorem tryB (hτ : tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : T1 σ t s) :
    WP isa (.ite .eq bSet (.block [])) s (M2 σ t) := by
  refine WP.ite s.z rfl (fun e => setOk hp hτ ht h e) (fun e => ?_)
  have hj : (St σ t).2 < (Xb σ t).toNat := by
    have := h.z; rw [e] at this; exact Nat.lt_of_not_le (of_decide_eq_false this.symm)
  have hst := St_succ σ ht
  rw [bStep, ifT h.lt, ifT hj] at hst
  exact WP.block_nil (M2.of_same h.bat hst)

theorem pieceB (hτ : tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : M1 σ t s) :
    WP isa (.ite .eq (.block []) bTry) s (M2 σ t) := by
  refine WP.ite s.z rfl (fun e => ?_) (fun e => WP.seq (WP.mono (tryA hp ht h e) fun _ h1 => tryB hp hτ ht h1))
  have hl : (St σ t).2 = 256 := by
    have := h.z; rw [e] at this; simp at this; have := St_le σ t; omega
  exact WP.block_nil (M2.of_same h.bat (by rw [St_succ σ ht, bStep_full hl]))

omit hp in
theorem pieceC {t : Nat} (ht : t < 264) {s : State} (h : M2 σ t s) :
    WP isa (.block (step 1)) s fun s' => BAt σ (t + 1) s' ∧ s'.z = decide (t + 1 = 264) := by
  refine WP.mono (step_ok s (k := 1) (by decide)) fun s' ⟨r0, r3, z, g, m, rd, wr, sp⟩ =>
    ⟨⟨h.env.same m (g _ (by decide) (by decide)) (g _ (by decide) (by decide)) rd wr sp, by rw [m]; exact h.out,
      by rw [r0, h.r0, ptr_add_add32, Nat.add_assoc], by rw [g _ (by decide) (by decide)]; exact h.r2,
      by show _ = _; rw [g _ (by decide) (by decide), g _ (by decide) (by decide)]; exact h.sg,
      by rw [r3, h.r3]; exact count_sub (k := 1) ht, by rw [m]; exact h.st⟩, ?_⟩
  rw [z, h.r3]; exact count_z (k := 1) ht (by decide) (by decide)

/-- An iteration. -/
theorem body_ok (hτ : tau σ ≤ 256) {t : Nat} (ht : t < 264) {s : State} (h : BAt σ t s) :
    WP isa bBody s fun s' => BAt σ (t + 1) s' ∧ s'.z = decide (t + 1 = 264) :=
  WP.seq (WP.mono (pieceA h) fun _ h1 => WP.seq (WP.mono (pieceB hp hτ ht h1) fun _ h2 => pieceC ht h2))

end

end VG.Proof.MlDsa.Arm.Sample.Ball
