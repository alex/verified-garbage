import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.MlKem.Encode

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_cbd2`

Untrusted: everything here is checked by Lean. One symbolic execution of
the loop body for any pointers (`body_ok`); the invariant says which
coefficients are written (`Inv`); their values are `samplePolyCBD2_val`:
the number of bits set in a 2-bit field `v` is `v - ⌊v / 2⌋`.
-/

namespace VG.Proof.MlKem.Arm.Cbd2

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## The loop body -/

/-- The number of bits set in the 2-bit field of `b` from bit `k`, as `pop2`
computes it. -/
def pc (b : Byte) (k : Nat) : BitVec 32 :=
  ((b.setWidth 32 <<< (30 - k)) >>> 30) - (((b.setWidth 32 <<< (30 - k)) >>> 30) >>> 1)

/-- The coefficient of the nibble of `b` from bit `k`. -/
def coef (b : Byte) (k : Nat) : BitVec 32 := fixq (pc b k - pc b (k + 2))

theorem body_ok {s : State} {x y c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y)
    (h2 : s.gpr .r2 = c)
    (i0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (o0 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 4)
    (o1 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 4)) 4)
    (hsep : ∀ (m : Mem) (v : BitVec 32),
      (m.writeW (State.addr (y + BitVec.ofNat 32 0)) v) (State.addr (x + BitVec.ofNat 32 0)) =
        m (State.addr (x + BitVec.ofNat 32 0))) :
    WP isa (.block cbd2Body) s fun s' =>
      s'.gpr .r0 = x + 1 ∧ s'.gpr .r1 = y + 8 ∧ s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = (s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
          (coef (s.mem (State.addr (x + BitVec.ofNat 32 0))) 0)).writeW
        (State.addr (y + BitVec.ofNat 32 4)) (coef (s.mem (State.addr (x + BitVec.ofNat 32 0))) 4) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [cbd2Body, cbdCoeff, pop2, fixup, coef, pc, fixq, h0, h1, h2, i0, o0, o1, hsep, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

/-! ## The values -/

theorem pc_toNat (b : Byte) {k : Nat} (hk : k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6) :
    (pc b k).toNat = b.toNat / 2 ^ k % 2 + b.toNat / 2 ^ k / 2 % 2 := by
  have hb := b.isLt
  have e : ((b.setWidth 32 <<< (30 - k)) >>> 30).toNat = b.toNat / 2 ^ k % 4 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, setWidth32_toNat, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq]
    rcases hk with rfl | rfl | rfl | rfl <;> simp only [Nat.reduceSub, Nat.reducePow] <;> omega
  unfold pc
  rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, e, Nat.shiftRight_eq_div_pow]
  omega

theorem coef_toNat (b : Byte) {k : Nat} (hk : k = 0 ∨ k = 4) :
    (coef b k).toNat = (cbdX (b.toNat / 2 ^ k) + q - cbdY (b.toNat / 2 ^ k)) % q := by
  have ex := pc_toNat b (k := k) (by omega)
  have ey := pc_toNat b (k := k + 2) (by omega)
  have hb := b.isLt
  unfold coef
  rw [fixq_sub (by rw [ex, q_eq]; omega) (by rw [ey, q_eq]; omega), ex, ey, cbdX, cbdY, Nat.pow_add]
  rw [← Nat.div_div_eq_div_mul, show (2 : Nat) ^ 2 = 4 from rfl]
  congr 1
  omega

/-! ## The loop -/

section
variable (s₀ : State)

abbrev pb : BitVec 32 := s₀.gpr .r0
abbrev pf : BitVec 32 := s₀.gpr .r1
abbrev B : Addr := State.addr (pb s₀)
abbrev F : Addr := State.addr (pf s₀)
abbrev inR : Region := ⟨B s₀, 128⟩
abbrev D : Poly := samplePolyCBD 2 (bytesAt s₀.mem (B s₀) 128)

/-- The value stored in coefficient `j`. -/
def out (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((D s₀)[j]!).val

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [inR s₀]
  wr : s₀.wr = [polyRegion (F s₀)]
  disj : (inR s₀).Disjoint (polyRegion (F s₀))
  fitB : (pb s₀).toNat + 128 ≤ 2 ^ 32
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pb s₀ + BitVec.ofNat 32 (1 * i)
  r1 : s.gpr .r1 = pf s₀ + BitVec.ofNat 32 (8 * i)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (128 - i))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j = if j < 2 * i then out s₀ j else coeffAt s₀.mem (F s₀) j

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 128) {s : State} (h : Inv s₀ i s) :
    WP isa (.block cbd2Body) s fun s' => Inv s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 128) := by
  have fB := hp.fitB
  have fF := hp.fitF
  have eb : State.addr (pb s₀ + BitVec.ofNat 32 (1 * i) + BitVec.ofNat 32 0) = B s₀ + BitVec.ofNat 64 i :=
    addr_byte fB (by omega) (by omega)
  have e0 : State.addr (pf s₀ + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 0) = coeffAddr (F s₀) (2 * i) :=
    addr_coeff fF (by omega) (by omega)
  have e1 : State.addr (pf s₀ + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4) =
      coeffAddr (F s₀) (2 * i + 1) := addr_coeff fF (by omega) (by omega)
  have hrw : s.rd ++ s.wr = [inR s₀, polyRegion (F s₀)] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hw : s.wr = [polyRegion (F s₀)] := by rw [h.wr, hp.wr]
  have c0 := coeff_contains (F s₀) (i := 2 * i) (by rw [n_eq]; omega)
  have c1 := coeff_contains (F s₀) (i := 2 * i + 1) (by rw [n_eq]; omega)
  have cb : (inR s₀).Contains (B s₀ + BitVec.ofNat 64 i) 1 := contains_off (by omega) (by omega)
  have rb : s.mem (B s₀ + BitVec.ofNat 64 i) = (bytesAt s₀.mem (B s₀) 128).getD i 0 := by
    rw [bytesAt_getD _ _ (by omega)]
    exact frame_byte h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
      (by decide) (by omega)
  refine WP.mono (body_ok h.r0 h.r1 h.r2 ?_ ?_ ?_ ?_) fun s' ⟨r0, r1, r2, z, m, rd, wr, sp, pres⟩ =>
    ⟨⟨?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr),
      ?_, ?_⟩, ?_⟩
  · rw [eb, hrw]; exact inRegions_of (by simp) cb
  · rw [e0, hw]; exact inRegions_of (by simp) c0
  · rw [e1, hw]; exact inRegions_of (by simp) c1
  · intro m v
    rw [e0, eb]
    exact byte_writeW_disj hp.disj v c0 cb
  · rw [r0]; exact ptr_succ _ 1 i
  · rw [r1]; exact ptr_succ _ 8 i
  · rw [r2]; exact count_sub (k := 1) hi
  · rw [m, e0, e1]
    exact (h.frame.writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  · intro j hj
    rw [m, e0, e1, eb, rb, coeffAt_writeW _ _ hj (by rw [n_eq]; omega),
      coeffAt_writeW _ _ hj (by rw [n_eq]; omega), h.coeff j hj]
    have v0 : coef ((bytesAt s₀.mem (B s₀) 128).getD i 0) 0 = out s₀ (2 * i) := by
      refine ofNat_val_eq ?_
      rw [coef_toNat _ (.inl rfl), samplePolyCBD2_val _ (by rw [n_eq]; omega), nibble,
        show 2 * i / 2 = i by omega, show 2 * i % 2 = 0 by omega]
    have v1 : coef ((bytesAt s₀.mem (B s₀) 128).getD i 0) 4 = out s₀ (2 * i + 1) := by
      refine ofNat_val_eq ?_
      rw [coef_toNat _ (.inr rfl), samplePolyCBD2_val _ (by rw [n_eq]; omega), nibble,
        show (2 * i + 1) / 2 = i by omega, show (2 * i + 1) % 2 = 1 by omega]
    rw [v0, v1]
    rcases (by omega : j < 2 * i ∨ j = 2 * i ∨ j = 2 * i + 1 ∨ 2 * i + 2 ≤ j) with hj' | rfl | rfl | hj'
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa cbd2 s₀ (Inv s₀ 128) := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, runBlock_cons.trans (by rfl), wp_loop_ne (Inv s₀) (N := 128) (by decide)
    (fun i hi s h => step hp hi h) (fun _ h => h) ?_⟩
  refine ⟨by simp [State.setReg], by simp [State.setReg], rfl, rfl, rfl, rfl,
    fun r hr => ?_, Frame.refl _ _, fun k _ => rfl⟩
  simp only [State.setReg]
  rw [ite_eq_right]
  intro e; subst e; simp [preserved] at hr

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.cbd2Contract Arm.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem.cbd2Contract, Spec.MlKem.cbd2Sig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 1024⟩]

theorem verified :
    Verified Arm.target Impl.MlKem.Arm.cbd2 (Spec.MlKem.cbd2Contract Arm.abi) := by
  refine ⟨fun s hs => ?_, Add.ct (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp
    refine ⟨t, s', he, ⟨h.pres, h.sp⟩, ?_⟩
    sig_post [Spec.MlKem.cbd2Contract, Spec.MlKem.cbd2Sig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    exact polyIs_of_coeffAt (p := F s) fun j hj => by
      rw [h.coeff j hj, ite_eq_left (by rw [n_eq] at hj; omega)]; rfl
  · sig_pub [Spec.MlKem.cbd2Contract, Spec.MlKem.cbd2Sig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact ⟨h.2.1, h.2.2⟩
  · refine ⟨satState, ?_⟩
    sig_sat_check [Spec.MlKem.cbd2Contract, Spec.MlKem.cbd2Sig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem.Arm.Cbd2
