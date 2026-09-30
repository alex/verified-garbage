import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintBase

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_pack`, correct

Untrusted: everything here is checked by Lean. As on x86-64, the code
follows the fold form of `HintBitPack` (`Proof/MlDsa/Pack/Hint.lean`) step by
step: the bytes of `y` are the array of the spec, and `r1` its index, which
stays below `ω` because it counts the 1s before the current coefficient
(`hpIdx_lt`). The loops (`main_ok`) run from any state that permits reading
the hint and writing `y`, so that constant time can narrow the state to
those two regions (`HintPackCT.lean`).
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr)
open VG.Proof.MlKem (bytesAt_writeW8 bytesAt_length bytesAt_getD bytesAt_eq)
open VG.Proof.MlDsa.Pack

/-! ## The arguments -/

section
variable (s₀ : State)

/-- `h`, `ω`, `y` and `len`. -/
abbrev pH : BitVec 32 := s₀.gpr .r0
abbrev pW : BitVec 32 := s₀.gpr .r2
abbrev pY : BitVec 32 := s₀.gpr .r3
abbrev pL : BitVec 32 := stackArg s₀ 0
abbrev pω : Nat := (pW s₀).toNat
abbrev pLen : Nat := (pL s₀).toNat
abbrev pk : Nat := pLen s₀ - pω s₀
abbrev hR : Region := ⟨State.addr (pH s₀), (s₀.gpr .r1).toNat * 4⟩
abbrev yR : Region := ⟨State.addr (pY s₀), pLen s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
/-- The hint. -/
abbrev pHint : List (Vector Bool n) := hintAt s₀.mem (State.addr (pH s₀)) (pk s₀)

end

/-- The precondition, as `sig_pre` states it. -/
structure PPre (s : State) : Prop where
  sp : 8 ≤ s.sp.toNat
  spA : s.sp.toNat + 4 ≤ 2 ^ 32
  rd : s.rd = [hR s, argR s]
  wr : s.wr = [yR s]
  d_hy : (hR s).Disjoint (yR s)
  d_ya : (yR s).Disjoint (argR s)
  b_h : (⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (hR s)
  b_y : (⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (yR s)
  b_a : (⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (argR s)
  fitH : (pH s).toNat + (s.gpr .r1).toNat * 4 ≤ 2 ^ 32
  fitY : (pY s).toNat + pLen s ≤ 2 ^ 32
  par : (pω s, pk s) ∈ hintParams
  ωle : pω s ≤ pLen s
  hlen : (s.gpr .r1).toNat = 256 * pk s
  ones : hintOnes (pHint s) ≤ pω s

section
variable {s₀ : State} (hp : PPre s₀)
include hp

theorem pfacts : 4 ≤ pk s₀ ∧ pk s₀ ≤ 8 ∧ 55 ≤ pω s₀ ∧ pω s₀ ≤ 80 ∧ pω s₀ + pk s₀ = pLen s₀ ∧ pLen s₀ ≤ 88 := by
  have := mem_hintParams hp.par
  have := hp.ωle
  have e : pk s₀ = pLen s₀ - pω s₀ := rfl
  omega

/-! ## Zeroing `y` -/

omit hp in
theorem zeroPro_ok {s : State} :
    WP isa (.block [.dp .sub .r1 .r12 (.reg .r2), .mov .r4 (.reg .r12), .mov .r12 (.imm 0), .mov .r5 (.reg .r3)])
      s fun s' => s'.gpr .r1 = s.gpr .r12 - s.gpr .r2 ∧ s'.gpr .r4 = s.gpr .r12 ∧ s'.gpr .r12 = 0 ∧
        s'.gpr .r5 = s.gpr .r3 ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r3 = s.gpr .r3 ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block []

omit hp in
theorem zeroStep_ok {s : State} {y c : BitVec 32} (h5 : s.gpr .r5 = y) (h4 : s.gpr .r4 = c)
    (o : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.strb .r12 .r5 0, .dp .add .r5 .r5 (.imm 1), .subs .r4 .r4 (.imm 1)]) s fun s' =>
      s'.gpr .r5 = y + 1 ∧ s'.gpr .r4 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (y + BitVec.ofNat 32 0)) ((s.gpr .r12).setWidth 8) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r3 = s.gpr .r3 ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h5, h4, o]

/-- Zeroing the `len` bytes of `y`, from the entry values of the registers. -/
theorem zero_ok {s : State} (h0 : s.gpr .r0 = pH s₀) (h2 : s.gpr .r2 = pW s₀) (h3 : s.gpr .r3 = pY s₀)
    (h12 : s.gpr .r12 = pL s₀) (hwr : yR s₀ ∈ s.wr) :
    WP isa hbpZero s fun s' => s'.gpr .r0 = pH s₀ ∧ s'.gpr .r1 = BitVec.ofNat 32 (pk s₀) ∧
      s'.gpr .r2 = pW s₀ ∧ s'.gpr .r3 = pY s₀ ∧
      bytesAt s'.mem (State.addr (pY s₀)) (pLen s₀) = List.replicate (pLen s₀) 0 ∧
      Frame [yR s₀] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨hk4, -, -, -, hsum, hL88⟩ := pfacts hp
  have fY := hp.fitY
  have hL := (pL s₀).isLt
  unfold hbpZero
  refine WP.seq (WP.mono zeroPro_ok fun s₁ ⟨r1₁, r4₁, r12₁, r5₁, r0₁, r2₁, r3₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  refine wp_loop_ne (N := pLen s₀) (fun t s' => s'.gpr .r5 = pY s₀ + BitVec.ofNat 32 t ∧
      s'.gpr .r4 = BitVec.ofNat 32 (1 * (pLen s₀ - t)) ∧ s'.gpr .r12 = 0 ∧ s'.gpr .r0 = pH s₀ ∧
      s'.gpr .r1 = BitVec.ofNat 32 (pk s₀) ∧ s'.gpr .r2 = pW s₀ ∧ s'.gpr .r3 = pY s₀ ∧
      Frame [yR s₀] s.mem s'.mem ∧ (∀ u < t, s'.mem (State.addr (pY s₀) + BitVec.ofNat 64 u) = 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp) (by omega)
    (fun t ht s' ⟨i5, i4, i12, i0, i1, i2, i3, hf, hz, hrd, hwr', hsp⟩ => ?_)
    (fun s' ⟨_, _, _, i0, i1, i2, i3, hf, hz, hrd, hwr', hsp⟩ => ⟨i0, i1, i2, i3,
      VG.Proof.MlKem.bytesAt_eq (by simp) fun u hu => by rw [hz u hu]; simp, hf, hrd, hwr', hsp⟩)
    ⟨by rw [r5₁, h3]; simp, by rw [r4₁, h12, Nat.one_mul, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      r12₁, by rw [r0₁, h0], ?_, by rw [r2₁, h2], by rw [r3₁, h3], by rw [m₁]; exact Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _), rd₁, wr₁, sp₁⟩
  · have ea : State.addr (pY s₀ + BitVec.ofNat 32 t + BitVec.ofNat 32 0) = State.addr (pY s₀) + BitVec.ofNat 64 t :=
      addr_ptr _ _ _ (by omega)
    refine WP.mono (zeroStep_ok i5 i4 (by
        rw [ea, hwr']; exact ⟨_, hwr, Offset.contains_base _ (by omega) (by omega)⟩))
      fun s'' ⟨r5', r4', z', m', r0', r1', r2', r3', r12', rd', wr', sp'⟩ =>
        ⟨⟨by rw [r5', BitVec.add_assoc, ofNat_succ32], by rw [r4']; exact count_sub (k := 1) ht, by rw [r12', i12],
          by rw [r0', i0], by rw [r1', i1], by rw [r2', i2], by rw [r3', i3], ?_, fun u hu => ?_,
          by rw [rd', hrd], by rw [wr', hwr'], by rw [sp', hsp]⟩, by rw [z']; exact count_z (k := 1) ht (by decide) (by omega)⟩
    · rw [m', ea]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [m', ea, VG.Proof.MlKem.Arm.byte_writeW8 _ _ (by omega) (by omega)]
      split
      · rw [i12]; rfl
      · exact hz u (by omega)
  · rw [r1₁, h12, h2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by have := hp.ωle; exact this), toNat_ofNat32 (by omega)]

end

/-! ## The spec, step by step -/

/-- Coefficient `j` of polynomial `i` of the hint at `p`. -/
theorem hintAt_get {m : Mem} {p : Addr} {k i j : Nat} (hi : i < k) (hj : j < n) :
    ((hintAt m p k).getD i noHint)[j]! = decide (coeffAt m p (256 * i + j) ≠ 0) := by
  rw [hintAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some, getElem!_pos _ j hj, Vector.getElem_ofFn]

theorem hintAt_length (m : Mem) (p : Addr) (k : Nat) : (hintAt m p k).length = k := by simp [hintAt]

/-- The spec's state after `i` polynomials. -/
abbrev hpS (s₀ : State) (i : Nat) : Array Byte × Nat :=
  (List.range i).foldl (hpPoly (pω s₀) (pHint s₀)) (Array.replicate (pω s₀ + pk s₀) 0, 0)

/-- ... and `j` coefficients of polynomial `i`. -/
abbrev hpT (s₀ : State) (i j : Nat) : Array Byte × Nat :=
  (List.range j).foldl (hpStep ((pHint s₀).getD i noHint)) (hpS s₀ i)

theorem hpS_idx (s₀ : State) (i : Nat) : (hpS s₀ i).2 = onesBefore (pHint s₀) i 0 := by
  rw [hpS, hpPolys_idx]; exact Nat.zero_add _

theorem hpT_idx (s₀ : State) (i j : Nat) : (hpT s₀ i j).2 = onesBefore (pHint s₀) i j := by
  rw [hpT, hpSteps_idx, hpS_idx]; unfold onesBefore; rfl

theorem hpT_succ (s₀ : State) (i j : Nat) :
    hpT s₀ i (j + 1) = hpStep ((pHint s₀).getD i noHint) (hpT s₀ i j) j := by
  rw [hpT, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem hpS_succ (s₀ : State) (i : Nat) :
    hpS s₀ (i + 1) = ((hpT s₀ i n).1.set! (pω s₀ + i) (BitVec.ofNat 8 (hpT s₀ i n).2), (hpT s₀ i n).2) := by
  rw [hpS, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

/-! ## The polynomials -/

/-- Before coefficient `j` of polynomial `i`, in the loops that start from `sA`. -/
structure CInv (s₀ sA : State) (i j : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pH s₀ + BitVec.ofNat 32 (4 * (256 * i + j))
  r1 : s.gpr .r1 = BitVec.ofNat 32 (hpT s₀ i j).2
  r3 : s.gpr .r3 = pY s₀
  r4 : s.gpr .r4 = BitVec.ofNat 32 (1 * (pk s₀ - i))
  r5 : s.gpr .r5 = pY s₀ + BitVec.ofNat 32 (pω s₀ + i)
  r12 : s.gpr .r12 = BitVec.ofNat 32 j
  rd : s.rd = sA.rd
  wr : s.wr = sA.wr
  sp : s.sp = sA.sp
  frame : Frame [yR s₀] sA.mem s.mem
  y : bytesAt s.mem (State.addr (pY s₀)) (pLen s₀) = (hpT s₀ i j).1.toList

/-- What the loops need of the state they start from: permission to read the
hint and write `y`, and the hint of the entry state. -/
structure MainPre (s₀ sA : State) : Prop where
  rd : hR s₀ ∈ sA.rd
  wr : yR s₀ ∈ sA.wr
  hint : ∀ t < 256 * pk s₀, coeffAt sA.mem (State.addr (pH s₀)) t = coeffAt s₀.mem (State.addr (pH s₀)) t

theorem coefLoad_ok {s : State} {x : BitVec 32} (h0 : s.gpr .r0 = x)
    (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.ldr .r2 .r0 0, .cmp .r2 (.imm 0)]) s fun s' =>
      s'.z = (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 - 0 == 0) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r2 → s'.gpr r = s.gpr r := by
  run_block [h0, ia]
  simp only [true_and]; intro r hr; rw [ite_neg' hr]

theorem coefSet_ok {s : State} {y i j : BitVec 32} (h1 : s.gpr .r1 = i) (h3 : s.gpr .r3 = y)
    (h12 : s.gpr .r12 = j) (o : InRegions s.wr (State.addr (y + i + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.dp .add .r2 .r3 (.reg .r1), .strb .r12 .r2 0, .dp .add .r1 .r1 (.imm 1)]) s fun s' =>
      s'.gpr .r1 = i + 1 ∧ s'.mem = s.mem.writeW (State.addr (y + i + BitVec.ofNat 32 0)) (j.setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r := by
  run_block [h1, h3, h12, o]
  simp only [true_and]; intro r h1 h2; rw [ite_neg' h1, ite_neg' h2]

theorem coefNext_ok {s : State} {x j : BitVec 32} (h0 : s.gpr .r0 = x) (h12 : s.gpr .r12 = j) :
    WP isa (.block [.dp .add .r0 .r0 (.imm 4), .dp .add .r12 .r12 (.imm 1), .cmp .r12 (.imm 256)]) s fun s' =>
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r12 = j + 1 ∧ s'.z = (j + 1 - 256 == 0) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r0 → r ≠ .r12 → s'.gpr r = s.gpr r := by
  run_block [h0, h12]
  simp only [true_and]; intro r h1 h2; rw [ite_neg' h2, ite_neg' h1]

section
variable {s₀ : State} (hp : PPre s₀) {sA : State} (hA : MainPre s₀ sA)
include hp hA

/-- A coefficient. -/
theorem coef_ok {i j : Nat} (hi : i < pk s₀) (hj : j < 256) {s : State} (hI : CInv s₀ sA i j s) :
    WP isa hbpCoef s fun s' => CInv s₀ sA i (j + 1) s' ∧ s'.z = decide (j + 1 = 256) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := pfacts hp
  have fH := hp.fitH
  have fY := hp.fitY
  have hl := hp.hlen
  have t_lt : 256 * i + j < 256 * pk s₀ := by omega
  have hin : (hR s₀).Contains (coeffAddr (State.addr (pH s₀)) (256 * i + j)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  have ea : State.addr (pH s₀ + BitVec.ofNat 32 (4 * (256 * i + j)) + BitVec.ofNat 32 0) =
      coeffAddr (State.addr (pH s₀)) (256 * i + j) := by
    rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
  have hw : s.mem.readW (coeffAddr (State.addr (pH s₀)) (256 * i + j)) 32 =
      coeffAt s₀.mem (State.addr (pH s₀)) (256 * i + j) := by
    rw [← hA.hint _ t_lt, coeffAt_eq]
    exact hI.frame.readW hin (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.d_hy) (by decide)
  have hbit := hintAt_get (m := s₀.mem) (p := State.addr (pH s₀)) hi (show j < n from hj)
  have hT := hpT_succ s₀ i j
  have hidx := hpT_idx s₀ i j
  unfold hbpCoef
  refine WP.seq (WP.mono (coefLoad_ok hI.r0 (by
      rw [ea, hI.rd, hI.wr]; exact ⟨_, List.mem_append_left _ hA.rd, hin⟩))
    fun s₁ ⟨z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  rw [ea, hw, sub_zero32] at z₁
  refine WP.seq (WP.ite (M := isa) _ (show some s₁.z = _ from rfl) (fun h0 => ?_) (fun h1 => ?_))
  · -- A 0.
    have h0 : coeffAt s₀.mem (State.addr (pH s₀)) (256 * i + j) = 0 := by
      rw [z₁] at h0; exact beq_iff_eq.mp h0
    refine WP.block_nil (WP.mono (coefNext_ok (x := pH s₀ + BitVec.ofNat 32 (4 * (256 * i + j)))
        (j := BitVec.ofNat 32 j) (by rw [g₁ _ (by decide), hI.r0])
        (by rw [g₁ _ (by decide), hI.r12])) fun s₃ ⟨r0₃, r12₃, z₃, m₃, rd₃, wr₃, sp₃, g₃⟩ =>
      ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [rd₃, rd₁, hI.rd], by rw [wr₃, wr₁, hI.wr], by rw [sp₃, sp₁, hI.sp],
        by rw [m₃, m₁]; exact hI.frame, ?_⟩, ?_⟩)
    · rw [r0₃, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ptr_add, show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega]
    · rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), hI.r1, hT, hpStep, hbit]
      simp only [h0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    · rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), hI.r3]
    · rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), hI.r4]
    · rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), hI.r5]
    · rw [r12₃, ofNat_succ32]
    · rw [m₃, m₁, hI.y, hT, hpStep, hbit]
      simp only [h0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    · rw [z₃, ofNat_succ32]; exact cmp_const (by omega) (by decide)
  · -- A 1: `y[index] ← j`.
    have h1 : coeffAt s₀.mem (State.addr (pH s₀)) (256 * i + j) ≠ 0 := by
      rw [z₁] at h1; exact fun e => by rw [e] at h1; exact absurd h1 (by decide)
    have hlt : (hpT s₀ i j).2 < pω s₀ := by
      have : onesBefore (pHint s₀) i j < hintOnes (pHint s₀) :=
        hpIdx_lt (hintAt_length s₀.mem _ _) hi hj (by rw [hbit]; exact decide_eq_true h1)
      have := hp.ones
      omega
    have eb : State.addr (pY s₀ + BitVec.ofNat 32 (hpT s₀ i j).2 + BitVec.ofNat 32 0) =
        State.addr (pY s₀) + BitVec.ofNat 64 (hpT s₀ i j).2 := by
      rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
    have hinY : (yR s₀).Contains (State.addr (pY s₀) + BitVec.ofNat 64 (hpT s₀ i j).2) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    refine WP.mono (coefSet_ok (i := BitVec.ofNat 32 (hpT s₀ i j).2) (y := pY s₀) (j := BitVec.ofNat 32 j)
        (by rw [g₁ _ (by decide), hI.r1]) (by rw [g₁ _ (by decide), hI.r3])
        (by rw [g₁ _ (by decide), hI.r12]) (by rw [eb, wr₁, hI.wr]; exact ⟨_, hA.wr, hinY⟩))
      fun s₂ ⟨r1₂, m₂, rd₂, wr₂, sp₂, g₂⟩ => ?_
    refine WP.mono (coefNext_ok (x := pH s₀ + BitVec.ofNat 32 (4 * (256 * i + j)))
        (j := BitVec.ofNat 32 j) (by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r0])
        (by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r12]))
      fun s₃ ⟨r0₃, r12₃, z₃, m₃, rd₃, wr₃, sp₃, g₃⟩ =>
      ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [rd₃, rd₂, rd₁, hI.rd], by rw [wr₃, wr₂, wr₁, hI.wr],
        by rw [sp₃, sp₂, sp₁, hI.sp], ?_, ?_⟩, ?_⟩
    · rw [r0₃, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ptr_add, show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega]
    · rw [g₃ _ (by decide) (by decide), r1₂, hT, hpStep, hbit, ofNat_succ32]
      simp only [h1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r3]
    · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r4]
    · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r5]
    · rw [r12₃, ofNat_succ32]
    · rw [m₃, m₂, m₁, eb]
      exact hI.frame.writeW (List.mem_singleton_self _) _ hinY
    · rw [m₃, m₂, m₁, eb, bytesAt_writeW8 _ _ (by omega) (by omega), hI.y, hT, hpStep, hbit,
        setWidth8_ofNat]
      simp only [h1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, Array.set!_eq_setIfInBounds,
        Array.toList_setIfInBounds]
    · rw [z₃, ofNat_succ32]; exact cmp_const (by omega) (by decide)

/-- The coefficients of polynomial `i`. -/
theorem coefs_ok {i : Nat} (hi : i < pk s₀) {s : State} (hI : CInv s₀ sA i 0 s) :
    WP isa (.loop hbpCoef .ne) s (CInv s₀ sA i 256) :=
  wp_loop_ne (CInv s₀ sA i) (N := 256) (by decide) (fun j hj _ h => coef_ok hp hA hi hj h) (fun _ h => h) hI

end

/-- Before polynomial `i`, in the loops that start from `sA`. -/
structure HPInv (s₀ sA : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pH s₀ + BitVec.ofNat 32 (4 * (256 * i))
  r1 : s.gpr .r1 = BitVec.ofNat 32 (hpS s₀ i).2
  r3 : s.gpr .r3 = pY s₀
  r4 : s.gpr .r4 = BitVec.ofNat 32 (1 * (pk s₀ - i))
  r5 : s.gpr .r5 = pY s₀ + BitVec.ofNat 32 (pω s₀ + i)
  rd : s.rd = sA.rd
  wr : s.wr = sA.wr
  sp : s.sp = sA.sp
  frame : Frame [yR s₀] sA.mem s.mem
  y : bytesAt s.mem (State.addr (pY s₀)) (pLen s₀) = (hpS s₀ i).1.toList

theorem polyStart_ok {s : State} :
    WP isa (.block [.mov .r12 (.imm 0)]) s fun s' => s'.gpr .r12 = 0 ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r12 → s'.gpr r = s.gpr r := by
  run_block []
  simp only [true_and]; intro r hr; rw [ite_neg' hr]

theorem polyEnd_ok {s : State} {x y c : BitVec 32} (h1 : s.gpr .r1 = x) (h5 : s.gpr .r5 = y)
    (h4 : s.gpr .r4 = c) (o : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.strb .r1 .r5 0, .dp .add .r5 .r5 (.imm 1), .subs .r4 .r4 (.imm 1)]) s fun s' =>
      s'.gpr .r5 = y + 1 ∧ s'.gpr .r4 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (y + BitVec.ofNat 32 0)) (x.setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r := by
  run_block [h1, h5, h4, o]
  simp only [true_and]; intro r h4 h5; rw [ite_neg' h4, ite_neg' h5]

section
variable {s₀ : State} (hp : PPre s₀) {sA : State} (hA : MainPre s₀ sA)
include hp hA

/-- A polynomial. -/
theorem poly_ok {i : Nat} (hi : i < pk s₀) {s : State} (hP : HPInv s₀ sA i s) :
    WP isa hbpPoly s fun s' => HPInv s₀ sA (i + 1) s' ∧ s'.z = decide (i + 1 = pk s₀) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := pfacts hp
  have fY := hp.fitY
  unfold hbpPoly
  refine WP.seq (WP.mono polyStart_ok fun s₁ ⟨r12₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  refine WP.seq (WP.mono (coefs_ok hp hA hi (s := s₁) ⟨by rw [g₁ _ (by decide), hP.r0, Nat.add_zero], by rw [g₁ _ (by decide), hP.r1]; rfl,
    by rw [g₁ _ (by decide), hP.r3], by rw [g₁ _ (by decide), hP.r4], by rw [g₁ _ (by decide), hP.r5], by rw [r12₁]; rfl,
    by rw [rd₁, hP.rd], by rw [wr₁, hP.wr], by rw [sp₁, hP.sp], by rw [m₁]; exact hP.frame,
    by rw [m₁, hP.y]; rfl⟩) fun s₂ hI => ?_)
  have hidx : (hpT s₀ i 256).2 < 256 := by
    have := hpT_idx s₀ i 256
    have h1 : onesBefore (pHint s₀) i 256 ≤ hintOnes (pHint s₀) := onesBefore_n_le (hintAt_length _ _ _) hi
    have := hp.ones
    omega
  have ea : State.addr (pY s₀ + BitVec.ofNat 32 (pω s₀ + i) + BitVec.ofNat 32 0) =
      State.addr (pY s₀) + BitVec.ofNat 64 (pω s₀ + i) := by
    rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
  have hinY : (yR s₀).Contains (State.addr (pY s₀) + BitVec.ofNat 64 (pω s₀ + i)) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (polyEnd_ok hI.r1 hI.r5 hI.r4 (by rw [ea, hI.wr]; exact ⟨_, hA.wr, hinY⟩))
    fun s₃ ⟨r5₃, r4₃, z₃, m₃, rd₃, wr₃, sp₃, g₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, by rw [rd₃, hI.rd], by rw [wr₃, hI.wr],
      by rw [sp₃, hI.sp], ?_, ?_⟩, ?_⟩
  · rw [g₃ _ (by decide) (by decide), hI.r0, show 4 * (256 * i + 256) = 4 * (256 * (i + 1)) by omega]
  · rw [g₃ _ (by decide) (by decide), hI.r1, hpS_succ]
  · rw [g₃ _ (by decide) (by decide), hI.r3]
  · rw [r4₃]; exact count_sub (k := 1) hi
  · rw [r5₃, BitVec.add_assoc, ofNat_succ32, Nat.add_assoc]
  · rw [m₃, ea]
    exact hI.frame.writeW (List.mem_singleton_self _) _ hinY
  · rw [m₃, ea, bytesAt_writeW8 _ _ (by omega) (by omega), hI.y, hpS_succ, setWidth8_ofNat,
      Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  · rw [z₃]; exact count_z (k := 1) hi (by decide) (by omega)

end

theorem mainPro_ok {s : State} :
    WP isa (.block [.mov .r4 (.reg .r1), .dp .add .r5 .r3 (.reg .r2), .mov .r1 (.imm 0)]) s fun s' =>
      s'.gpr .r4 = s.gpr .r1 ∧ s'.gpr .r5 = s.gpr .r3 + s.gpr .r2 ∧ s'.gpr .r1 = 0 ∧ s'.gpr .r0 = s.gpr .r0 ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block []

/-- The polynomials, from the state after zeroing `y`. -/
theorem main_ok {s₀ : State} (hp : PPre s₀) {sA : State} (hA : MainPre s₀ sA) (h0 : sA.gpr .r0 = pH s₀)
    (h1 : sA.gpr .r1 = BitVec.ofNat 32 (pk s₀)) (h2 : sA.gpr .r2 = pW s₀) (h3 : sA.gpr .r3 = pY s₀)
    (hz : bytesAt sA.mem (State.addr (pY s₀)) (pLen s₀) = List.replicate (pLen s₀) 0) :
    WP isa hbpMain sA fun s' =>
      bytesAt s'.mem (State.addr (pY s₀)) (pLen s₀) = hintBitPack (pω s₀) (pk s₀) (pHint s₀) ∧
      Frame [yR s₀] sA.mem s'.mem ∧ s'.rd = sA.rd ∧ s'.wr = sA.wr ∧ s'.sp = sA.sp := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := pfacts hp
  unfold hbpMain
  refine WP.seq (WP.mono mainPro_ok fun s₁ ⟨r4₁, r5₁, r1₁, r0₁, r3₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  refine wp_loop_ne (HPInv s₀ sA) (N := pk s₀) (by omega) (fun i hi s h => poly_ok hp hA hi h)
    (fun s hP => ⟨hP.y.trans (hintBitPack_eq _ _ _).symm, hP.frame, hP.rd, hP.wr, hP.sp⟩)
    ⟨by rw [r0₁, h0]; simp, by rw [r1₁]; rfl, by rw [r3₁, h3], by rw [r4₁, h1, Nat.one_mul, Nat.sub_zero],
      by rw [r5₁, h3, h2, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq], rd₁, wr₁, sp₁,
      by rw [m₁]; exact Frame.refl _ _, ?_⟩
  rw [m₁, hz]
  show _ = (Array.replicate (pω s₀ + pk s₀) (0 : Byte)).toList
  rw [Array.toList_replicate, hsum]

/-! ## The function -/

theorem entry_ok {s : State} (ia : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.ldrSp .r12 0]) s fun s' =>
      s' = s.setReg .r12 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 0)) 32) := by
  run_block [ia]

theorem ldr5_ok {s : State} (ia : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 4)) 4) :
    WP isa (.block [.ldrSp .r5 4]) s fun s' =>
      s' = s.setReg .r5 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 4)) 32) := by
  run_block [ia]

theorem frameR2 {s : State} (h : 8 ≤ s.sp.toNat) :
    frameR s [.r4, .r5] = ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ := frameR_eq [.r4, .r5] h

/-- The whole function: `y`, and the registers it saves and restores. -/
theorem correct {s₀ : State} (hp : PPre s₀) :
    WP isa Impl.MlDsa.Arm.Pack.hintBitPack s₀ fun s' => s'.gpr .r4 = s₀.gpr .r4 ∧ s'.gpr .r5 = s₀.gpr .r5 ∧ s'.sp = s₀.sp ∧
      bytesAt s'.mem (State.addr (pY s₀)) (pLen s₀) = Spec.MlDsa.hintBitPack (pω s₀) (pk s₀) (pHint s₀) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := pfacts hp
  have fH := hp.fitH
  have hl := hp.hlen
  unfold Impl.MlDsa.Arm.Pack.hintBitPack
  refine WP.seq (WP.mono (entry_ok (s := s₀) (by
    rw [hp.rd]; exact ⟨argR s₀, by simp, Region.contains_self _ _⟩)) fun s₁ e₁ => ?_)
  subst e₁
  have hsp8 : 4 * [Reg.r4, Reg.r5].length ≤ s₀.sp.toNat := hp.sp
  have hfr : frameR (s₀.setReg .r12 (pL s₀)) [.r4, .r5] = ⟨State.addr s₀.sp - BitVec.ofNat 64 8, 8⟩ :=
    frameR2 (s := s₀.setReg .r12 (pL s₀)) hp.sp
  have hpf := pushed_frame [.r4, .r5] (s := s₀.setReg .r12 (pL s₀)) hsp8
  refine WP.frame (rs := [.r4, .r5]) (r := .r4) rfl hsp8 (by decide) ?_
  unfold hintBitPackBody
  refine WP.seq (WP.mono (zero_ok hp (s := pushed [.r4, .r5] (s₀.setReg .r12 (pL s₀))) rfl rfl rfl rfl
      (by simp [RegUpd.wr_setReg, hp.wr]))
    fun sa ⟨a0, a1, a2, a3, az, af, ard, awr, asp⟩ => ?_)
  have hA : MainPre s₀ sa := ⟨by rw [ard]; simp [RegUpd.rd_setReg, hp.rd], by rw [awr]; simp [RegUpd.wr_setReg, hp.wr], fun t ht => by
    rw [coeffAt_eq, coeffAt_eq, af.readW (r := hR s₀) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.d_hy) (by decide),
      hpf.readW (r := hR s₀) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by rw [List.mem_singleton] at hr; subst hr; rw [hfr]; exact hp.b_h.symm) (by decide)]; rfl⟩
  refine WP.seq (WP.mono (main_ok hp hA a0 a1 a2 a3 az) fun sb ⟨by', bf, brd, bwr, bsp⟩ => ?_)
  have hfb : Frame [yR s₀] (pushed [.r4, .r5] (s₀.setReg .r12 (pL s₀))).mem sb.mem := af.trans bf
  have hdy : ∀ r ∈ [yR s₀], (frameR (s₀.setReg .r12 (pL s₀)) [.r4, .r5]).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hfr]; exact hp.b_y
  have hsb : sb.sp = (pushed [.r4, .r5] (s₀.setReg .r12 (pL s₀))).sp := by rw [bsp, asp]
  refine WP.mono (ldr5_ok (by
      rw [bwr, awr, pushed_wr, hsb]
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), frameR_contains [.r4, .r5] (s := s₀.setReg .r12 (pL s₀)) hsp8 (i := 1) (by decide)⟩))
    fun s₂ e₂ => ?_
  subst e₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [popped, State.setReg, ite_true]
    rw [hsb, show State.addr ((pushed [.r4, .r5] (s₀.setReg .r12 (pL s₀))).sp) =
      State.addr ((pushed [.r4, .r5] (s₀.setReg .r12 (pL s₀))).sp + BitVec.ofNat 32 (4 * 0)) by simp,
      frame_saved [.r4, .r5] (s := s₀.setReg .r12 (pL s₀)) hsp8 hfb hdy (i := 0) (by decide)]
    rfl
  · rw [popped_gpr (by decide)]
    simp only [State.setReg, ite_true]
    rw [hsb, frame_saved [.r4, .r5] (s := s₀.setReg .r12 (pL s₀)) hsp8 hfb hdy (i := 1) (by decide)]
    rfl
  · simp only [popped_sp, State.setReg, hsb, pushed_sp]
    exact BitVec.sub_add_cancel _ _
  · simp only [popped_mem, State.setReg]
    exact by'

end VG.Proof.MlDsa.Arm.Pack.Hint
