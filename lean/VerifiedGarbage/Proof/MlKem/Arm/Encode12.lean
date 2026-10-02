import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.MlKem.Encode

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_encode12`

One symbolic execution of the loop body for any pointers (`body_ok`); the
invariant says which bytes of the output are written (`Inv`); the bytes are
those of `encode12_byte0`–`encode12_byte2`.
-/

namespace VG.Proof.MlKem.Arm.Encode12

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## The loop body -/

/-- The three bytes of a pair `a`, `b` of coefficients. -/
def b0 (a : BitVec 32) : Byte := a.setWidth 8
def b1 (a b : BitVec 32) : Byte := ((a >>> 8) + (b <<< 4)).setWidth 8
def b2 (b : BitVec 32) : Byte := (b >>> 4).setWidth 8

theorem body_ok {s : State} {x y c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y)
    (h2 : s.gpr .r2 = c)
    (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 4)) 4)
    (o0 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 1)
    (o1 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 1)) 1)
    (o2 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 2)) 1) :
    WP isa (.block encode12Body) s fun s' =>
      s'.gpr .r0 = x + 8 ∧ s'.gpr .r1 = y + 3 ∧ s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = ((s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
          (b0 (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32))).writeW
        (State.addr (y + BitVec.ofNat 32 1)) (b1 (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)
          (s.mem.readW (State.addr (x + BitVec.ofNat 32 4)) 32))).writeW
        (State.addr (y + BitVec.ofNat 32 2)) (b2 (s.mem.readW (State.addr (x + BitVec.ofNat 32 4)) 32)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [encode12Body, b0, b1, b2, h0, h1, h2, ia, ib, o0, o1, o2, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

/-! ## The loop -/

section
variable (s₀ : State)

abbrev pf : BitVec 32 := s₀.gpr .r0
abbrev po : BitVec 32 := s₀.gpr .r1
abbrev F : Addr := State.addr (pf s₀)
abbrev O : Addr := State.addr (po s₀)
abbrev outR : Region := ⟨O s₀, 384⟩
abbrev E : List Byte := encode12 (polyAt s₀.mem (F s₀))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (F s₀)]
  wr : s₀.wr = [outR s₀]
  disj : (polyRegion (F s₀)).Disjoint (outR s₀)
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitO : (po s₀).toNat + 384 ≤ 2 ^ 32
  red : Reduced s₀.mem (F s₀)

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pf s₀ + BitVec.ofNat 32 (8 * i)
  r1 : s.gpr .r1 = po s₀ + BitVec.ofNat 32 (3 * i)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (128 - i))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [outR s₀] s₀.mem s.mem
  bytes : ∀ k < 384, s.mem (O s₀ + BitVec.ofNat 64 k) =
    if k < 3 * i then (E s₀)[k]! else s₀.mem (O s₀ + BitVec.ofNat 64 k)

/-- The bytes of group `i`. -/
theorem bytes_eq {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 128) :
    b0 (coeffAt s₀.mem (F s₀) (2 * i)) = (E s₀)[3 * i]! ∧
    b1 (coeffAt s₀.mem (F s₀) (2 * i)) (coeffAt s₀.mem (F s₀) (2 * i + 1)) = (E s₀)[3 * i + 1]! ∧
    b2 (coeffAt s₀.mem (F s₀) (2 * i + 1)) = (E s₀)[3 * i + 2]! := by
  have ea := polyAt_val hp.red (i := 2 * i) (by rw [n_eq]; omega)
  have eb := polyAt_val hp.red (i := 2 * i + 1) (by rw [n_eq]; omega)
  have la := val_lt (polyAt s₀.mem (F s₀))[2 * i]!
  have lb := val_lt (polyAt s₀.mem (F s₀))[2 * i + 1]!
  rw [encode12_byte0 _ hi, encode12_byte1 _ hi, encode12_byte2 _ hi]
  simp only [b0, b1, b2, setWidth8]
  refine ⟨ofNat8_eq ?_, ofNat8_eq ?_, ofNat8_eq ?_⟩
  · rw [← ea, Nat.mod_mod]
  · rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, ← ea, ← eb,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega
  · rw [BitVec.toNat_ushiftRight, ← eb, Nat.shiftRight_eq_div_pow]

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 128) {s : State} (h : Inv s₀ i s) :
    WP isa (.block encode12Body) s fun s' => Inv s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 128) := by
  have fF := hp.fitF
  have fO := hp.fitO
  have eA : State.addr (pf s₀ + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 0) = coeffAddr (F s₀) (2 * i) :=
    addr_coeff fF (by omega) (by omega)
  have eB : State.addr (pf s₀ + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4) =
      coeffAddr (F s₀) (2 * i + 1) := addr_coeff fF (by omega) (by omega)
  have e0 : State.addr (po s₀ + BitVec.ofNat 32 (3 * i) + BitVec.ofNat 32 0) = O s₀ + BitVec.ofNat 64 (3 * i) :=
    addr_byte fO (by omega) (by omega)
  have e1 : State.addr (po s₀ + BitVec.ofNat 32 (3 * i) + BitVec.ofNat 32 1) =
      O s₀ + BitVec.ofNat 64 (3 * i + 1) := addr_byte fO rfl (by omega)
  have e2 : State.addr (po s₀ + BitVec.ofNat 32 (3 * i) + BitVec.ofNat 32 2) =
      O s₀ + BitVec.ofNat 64 (3 * i + 2) := addr_byte fO rfl (by omega)
  have hrw : s.rd ++ s.wr = [polyRegion (F s₀), outR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hw : s.wr = [outR s₀] := by rw [h.wr, hp.wr]
  have dF : ∀ r ∈ [outR s₀], (polyRegion (F s₀)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.disj
  have ra : s.mem.readW (coeffAddr (F s₀) (2 * i)) 32 = coeffAt s₀.mem (F s₀) (2 * i) :=
    frame_coeff h.frame dF (by rw [n_eq]; omega)
  have rb : s.mem.readW (coeffAddr (F s₀) (2 * i + 1)) 32 = coeffAt s₀.mem (F s₀) (2 * i + 1) :=
    frame_coeff h.frame dF (by rw [n_eq]; omega)
  obtain ⟨v0, v1, v2⟩ := bytes_eq hp hi
  refine WP.mono (body_ok h.r0 h.r1 h.r2 ?_ ?_ ?_ ?_ ?_) fun s' ⟨r0, r1, r2, z, m, rd, wr, sp, pres⟩ =>
    ⟨⟨?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr),
      ?_, ?_⟩, ?_⟩
  · rw [eA, hrw]; exact inRegions_of (by simp) (coeff_contains _ (by rw [n_eq]; omega))
  · rw [eB, hrw]; exact inRegions_of (by simp) (coeff_contains _ (by rw [n_eq]; omega))
  · rw [e0, hw]; exact inRegions_off (List.mem_singleton_self _) (by omega) (by omega)
  · rw [e1, hw]; exact inRegions_off (List.mem_singleton_self _) (by omega) (by omega)
  · rw [e2, hw]; exact inRegions_off (List.mem_singleton_self _) (by omega) (by omega)
  · rw [r0]; exact ptr_succ _ 8 i
  · rw [r1]; exact ptr_succ _ 3 i
  · rw [r2]; exact count_sub (k := 1) hi
  · rw [m, e0, e1, e2]
    exact ((h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))
  · intro k hk
    rw [m, e0, e1, e2, eA, eB, ra, rb, v0, v1, v2,
      byte_writeW8 _ _ (by omega) (by omega), byte_writeW8 _ _ (by omega) (by omega),
      byte_writeW8 _ _ (by omega) (by omega), h.bytes k hk]
    rcases (by omega : k < 3 * i ∨ k = 3 * i ∨ k = 3 * i + 1 ∨ k = 3 * i + 2 ∨ 3 * i + 3 ≤ k) with
      hk' | rfl | rfl | rfl | hk'
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa encode12 s₀ (Inv s₀ 128) := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, runBlock_cons.trans (by rfl), wp_loop_ne (Inv s₀) (N := 128) (by decide)
    (fun i hi s h => step hp hi h) (fun _ h => h) ?_⟩
  refine ⟨by simp [State.setReg], by simp [State.setReg], rfl, rfl, rfl, rfl,
    fun r hr => ?_, Frame.refl _ _, fun k _ => rfl⟩
  simp only [State.setReg]
  rw [ite_eq_right]
  intro e; subst e; simp [preserved] at hr

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.encode12Contract Arm.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem.encode12Contract, Spec.MlKem.encode12Sig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

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
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 384⟩]

theorem verified :
    Verified Arm.target Impl.MlKem.Arm.encode12 (Spec.MlKem.encode12Contract Arm.abi) := by
  refine ⟨fun s hs => ?_, Add.ct (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp
    refine ⟨t, s', he, ⟨h.pres, h.sp⟩, ?_⟩
    sig_post [Spec.MlKem.encode12Contract, Spec.MlKem.encode12Sig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    exact bytesAt_eq! (p := O s) (encode12_length _) fun k hk => by
      rw [h.bytes k hk, ite_eq_left (by omega)]; rfl
  · sig_pub [Spec.MlKem.encode12Contract, Spec.MlKem.encode12Sig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact ⟨h.2.1, h.2.2⟩
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.encode12Contract, Spec.MlKem.encode12Sig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.Arm.Encode12
