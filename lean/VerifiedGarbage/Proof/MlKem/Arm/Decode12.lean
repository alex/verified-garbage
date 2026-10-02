import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.MlKem.Encode

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_decode12`

One symbolic execution of the loop body for any pointers (`body_ok`), which
loads bytes after storing a coefficient: `hsep` says the store does not change
them. The invariant says which coefficients are written (`Inv`); their values
are `decode12_even` and `decode12_odd`, reduced by `fixq_subq`.
-/

namespace VG.Proof.MlKem.Arm.Decode12

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## The loop body -/

/-- The first field of the bytes `b₀`, `b₁`, reduced. -/
def fieldLo (b₀ b₁ : Byte) : BitVec 32 :=
  fixq (b₀.setWidth 32 + ((b₁.setWidth 32 <<< 28) >>> 20) - 3328 - 1)

/-- The second field of the bytes `b₁`, `b₂`, reduced. -/
def fieldHi (b₁ b₂ : Byte) : BitVec 32 :=
  fixq ((b₁.setWidth 32 >>> 4) + (b₂.setWidth 32 <<< 4) - 3328 - 1)

theorem body_ok {s : State} {x y c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y)
    (h2 : s.gpr .r2 = c)
    (i0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (i1 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 1)) 1)
    (i2 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 2)) 1)
    (o0 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 4)
    (o1 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 4)) 4)
    (hsep : ∀ (m : Mem) (v : BitVec 32) (k : Nat), k < 3 →
      (m.writeW (State.addr (y + BitVec.ofNat 32 0)) v) (State.addr (x + BitVec.ofNat 32 k)) =
        m (State.addr (x + BitVec.ofNat 32 k))) :
    WP isa (.block decode12Body) s fun s' =>
      s'.gpr .r0 = x + 3 ∧ s'.gpr .r1 = y + 8 ∧ s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = (s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
          (fieldLo (s.mem (State.addr (x + BitVec.ofNat 32 0))) (s.mem (State.addr (x + BitVec.ofNat 32 1))))).writeW
        (State.addr (y + BitVec.ofNat 32 4))
          (fieldHi (s.mem (State.addr (x + BitVec.ofNat 32 1))) (s.mem (State.addr (x + BitVec.ofNat 32 2)))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [decode12Body, decode12Lo, decode12Hi, subQ, fixup, fieldLo, fieldHi, fixq, h0, h1, h2, i0, i1, i2,
    o0, o1, hsep, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_self, and_true]

/-! ## The values -/

theorem lo_toNat (b₀ b₁ : Byte) : (fieldLo b₀ b₁).toNat = (b₀.toNat + 256 * (b₁.toNat % 16)) % q := by
  have h₀ := b₀.isLt
  have h₁ := b₁.isLt
  have e : (b₀.setWidth 32 + ((b₁.setWidth 32 <<< 28) >>> 20)).toNat = b₀.toNat + 256 * (b₁.toNat % 16) := by
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, setWidth32_toNat,
      setWidth32_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega
  unfold fieldLo
  rw [fixq_subq (by rw [e, q_eq]; omega), e]

theorem hi_toNat (b₁ b₂ : Byte) : (fieldHi b₁ b₂).toNat = (b₁.toNat / 16 + 16 * b₂.toNat) % q := by
  have h₁ := b₁.isLt
  have h₂ := b₂.isLt
  have e : ((b₁.setWidth 32 >>> 4) + (b₂.setWidth 32 <<< 4)).toNat = b₁.toNat / 16 + 16 * b₂.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, setWidth32_toNat,
      setWidth32_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega
  unfold fieldHi
  rw [fixq_subq (by rw [e, q_eq]; omega), e]

/-! ## The loop -/

section
variable (s₀ : State)

abbrev pb : BitVec 32 := s₀.gpr .r0
abbrev pf : BitVec 32 := s₀.gpr .r1
abbrev B : Addr := State.addr (pb s₀)
abbrev F : Addr := State.addr (pf s₀)
abbrev inR : Region := ⟨B s₀, 384⟩
abbrev D : Poly := decode12 (bytesAt s₀.mem (B s₀) 384)

/-- The value stored in coefficient `j`. -/
def out (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((D s₀)[j]!).val

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [inR s₀]
  wr : s₀.wr = [polyRegion (F s₀)]
  disj : (inR s₀).Disjoint (polyRegion (F s₀))
  fitB : (pb s₀).toNat + 384 ≤ 2 ^ 32
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pb s₀ + BitVec.ofNat 32 (3 * i)
  r1 : s.gpr .r1 = pf s₀ + BitVec.ofNat 32 (8 * i)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (128 - i))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j = if j < 2 * i then out s₀ j else coeffAt s₀.mem (F s₀) j

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 128) {s : State} (h : Inv s₀ i s) :
    WP isa (.block decode12Body) s fun s' => Inv s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 128) := by
  have fB := hp.fitB
  have fF := hp.fitF
  have eb : ∀ k < 3, State.addr (pb s₀ + BitVec.ofNat 32 (3 * i) + BitVec.ofNat 32 k) =
      B s₀ + BitVec.ofNat 64 (3 * i + k) := fun k hk => addr_byte fB rfl (by omega)
  have e0 : State.addr (pf s₀ + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 0) = coeffAddr (F s₀) (2 * i) :=
    addr_coeff fF (by omega) (by omega)
  have e1 : State.addr (pf s₀ + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4) =
      coeffAddr (F s₀) (2 * i + 1) := addr_coeff fF (by omega) (by omega)
  have hrw : s.rd ++ s.wr = [inR s₀, polyRegion (F s₀)] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hw : s.wr = [polyRegion (F s₀)] := by rw [h.wr, hp.wr]
  have c0 := coeff_contains (F s₀) (i := 2 * i) (by rw [n_eq]; omega)
  have c1 := coeff_contains (F s₀) (i := 2 * i + 1) (by rw [n_eq]; omega)
  have cb : ∀ k < 3, (inR s₀).Contains (B s₀ + BitVec.ofNat 64 (3 * i + k)) 1 :=
    fun k hk => contains_off (by omega) (by omega)
  -- The bytes read are those on entry.
  have rb : ∀ k < 3, s.mem (B s₀ + BitVec.ofNat 64 (3 * i + k)) = (bytesAt s₀.mem (B s₀) 384).getD (3 * i + k) 0 :=
    fun k hk => by
      rw [bytesAt_getD _ _ (by omega)]
      exact frame_byte h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
        (by decide) (by omega)
  have hB : (bytesAt s₀.mem (B s₀) 384).length = 384 := bytesAt_length _ _ _
  refine WP.mono (body_ok h.r0 h.r1 h.r2 ?_ ?_ ?_ ?_ ?_ ?_) fun s' ⟨r0, r1, r2, z, m, rd, wr, sp, pres⟩ =>
    ⟨⟨?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr),
      ?_, ?_⟩, ?_⟩
  · rw [eb 0 (by omega), hrw]; exact inRegions_of (by simp) (cb 0 (by omega))
  · rw [eb 1 (by omega), hrw]; exact inRegions_of (by simp) (cb 1 (by omega))
  · rw [eb 2 (by omega), hrw]; exact inRegions_of (by simp) (cb 2 (by omega))
  · rw [e0, hw]; exact inRegions_of (by simp) c0
  · rw [e1, hw]; exact inRegions_of (by simp) c1
  · intro m v k hk
    rw [e0, eb k hk]
    exact byte_writeW_disj hp.disj v c0 (cb k hk)
  · rw [r0]; exact ptr_succ _ 3 i
  · rw [r1]; exact ptr_succ _ 8 i
  · rw [r2]; exact count_sub (k := 1) hi
  · rw [m, e0, e1]
    exact (h.frame.writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  · intro j hj
    rw [m, e0, e1, eb 0 (by omega), eb 1 (by omega), eb 2 (by omega), rb 0 (by omega), rb 1 (by omega),
      rb 2 (by omega), coeffAt_writeW _ _ hj (by rw [n_eq]; omega),
      coeffAt_writeW _ _ hj (by rw [n_eq]; omega), h.coeff j hj]
    have v0 : fieldLo ((bytesAt s₀.mem (B s₀) 384).getD (3 * i + 0) 0)
        ((bytesAt s₀.mem (B s₀) 384).getD (3 * i + 1) 0) = out s₀ (2 * i) := by
      refine ofNat_val_eq ?_
      rw [lo_toNat, decode12_even _ hB hi, val_ofNat, Nat.add_zero]
    have v1 : fieldHi ((bytesAt s₀.mem (B s₀) 384).getD (3 * i + 1) 0)
        ((bytesAt s₀.mem (B s₀) 384).getD (3 * i + 2) 0) = out s₀ (2 * i + 1) := by
      refine ofNat_val_eq ?_
      rw [hi_toNat, decode12_odd _ hB hi, val_ofNat]
    rw [v0, v1]
    rcases (by omega : j < 2 * i ∨ j = 2 * i ∨ j = 2 * i + 1 ∨ 2 * i + 2 ≤ j) with hj' | rfl | rfl | hj'
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
    · resolve_ifs
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa decode12 s₀ (Inv s₀ 128) := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, runBlock_cons.trans (by rfl), wp_loop_ne (Inv s₀) (N := 128) (by decide)
    (fun i hi s h => step hp hi h) (fun _ h => h) ?_⟩
  refine ⟨by simp [State.setReg], by simp [State.setReg], rfl, rfl, rfl, rfl,
    fun r hr => ?_, Frame.refl _ _, fun k _ => rfl⟩
  simp only [State.setReg]
  rw [ite_eq_right]
  intro e; subst e; simp [preserved] at hr

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.decode12Contract Arm.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem.decode12Contract, Spec.MlKem.decode12Sig, Arm.abi, Arm.argRegs,
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
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 1024⟩]

theorem verified :
    Verified Arm.target Impl.MlKem.Arm.decode12 (Spec.MlKem.decode12Contract Arm.abi) := by
  refine ⟨fun s hs => ?_, Add.ct (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp
    refine ⟨t, s', he, ⟨h.pres, h.sp⟩, ?_⟩
    sig_post [Spec.MlKem.decode12Contract, Spec.MlKem.decode12Sig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    exact polyIs_of_coeffAt (p := F s) fun j hj => by
      rw [h.coeff j hj, ite_eq_left (by rw [n_eq] at hj; omega)]; rfl
  · sig_pub [Spec.MlKem.decode12Contract, Spec.MlKem.decode12Sig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact ⟨h.2.1, h.2.2⟩
  · refine ⟨satState, ?_⟩
    sig_sat_check [Spec.MlKem.decode12Contract, Spec.MlKem.decode12Sig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem.Arm.Decode12
