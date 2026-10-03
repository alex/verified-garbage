import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.AddSub

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_add` and `vg_mldsa_sub`

One symbolic execution of each loop body, for any pointers (`addBody_ok`,
`subBody_ok`); the loop invariant says which coefficients of `f` are done
(`Inv`); the arithmetic is `fixS_add` and `fixS_sub`.
-/

namespace VG.Proof.MlDsa.Arm.Arith.AddSub

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr inRegions_of)

/-! ## Values -/

/-- What `fixupS r t` leaves in `r`. -/
def fixS (u : BitVec 32) : BitVec 32 := u + (u >>> 31) <<< 23 - (u >>> 31) <<< 13 + u >>> 31

/-- `fixupS (a + b - q)`: the sum of reduced values, reduced. -/
theorem fixS_add {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (fixS (a + b - 0x800000 + 0x2000 - 1)).toNat = (a.toNat + b.toNat) % q := by
  unfold fixS
  rw [q_eq] at *
  by_cases h : a.toNat + b.toNat < 8380417
  · rw [Nat.mod_eq_of_lt h]; bv_omega
  · bv_omega

/-- `fixupS (a - b)`: the difference of reduced values, reduced. -/
theorem fixS_sub {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (fixS (a - b)).toNat = (a.toNat + q - b.toNat) % q := by
  unfold fixS
  rw [q_eq] at *
  by_cases h : b.toNat ≤ a.toNat
  · bv_omega
  · bv_omega

/-! ## The loop bodies -/

/-- What an iteration of either loop does, but for the value stored. -/
def Step (s : State) (x y c v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .r0 = x + 4 ∧ s'.gpr .r1 = y + 4 ∧ s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
    s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0)) v ∧
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {s : State} {x y c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = c)
  (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
  (ib : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4)
  (oa : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 ia ib oa

theorem addBody_ok :
    WP isa (.block addBody) s (Step s x y c (fixS (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 +
      s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 - 0x800000 + 0x2000 - 1))) := by
  run_block [addBody, subQ, fixupS, accTail, Step, fixS, h0, h1, h2, ia, ib, oa, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

theorem subBody_ok :
    WP isa (.block subBody) s (Step s x y c (fixS (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 -
      s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32))) := by
  run_block [subBody, fixupS, accTail, Step, fixS, h0, h1, h2, ia, ib, oa, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev pf : BitVec 32 := s₀.gpr .r0
abbrev pg : BitVec 32 := s₀.gpr .r1
abbrev F : Addr := State.addr (pf s₀)
abbrev G : Addr := State.addr (pg s₀)

end

/-- The precondition of both functions. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (G s₀)]
  wr : s₀.wr = [polyRegion (F s₀)]
  disj : (polyRegion (F s₀)).Disjoint (polyRegion (G s₀))
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitG : (pg s₀).toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s₀.mem (F s₀)
  redG : Reduced s₀.mem (G s₀)

/-- After `i` iterations, writing `out j` to coefficient `j`. -/
structure Inv (out : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pf s₀ + BitVec.ofNat 32 (4 * i)
  r1 : s.gpr .r1 = pg s₀ + BitVec.ofNat 32 (4 * i)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (256 - i))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j = if j < i then out j else coeffAt s₀.mem (F s₀) j

theorem ptr_succ (p : BitVec 32) (k i : Nat) :
    p + BitVec.ofNat 32 (k * i) + BitVec.ofNat 32 k = p + BitVec.ofNat 32 (k * (i + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

/-- One iteration, from the value the body stores. -/
theorem inv_step {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256)
    {s : State} (h : Inv out s₀ i s) {body : List Instr}
    (hb : ∀ {x y c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = y → s.gpr .r2 = c →
      InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
      WP isa (.block body) s (Step s x y c (out i))) :
    WP isa (.block body) s fun s' => Inv out s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256) := by
  have fF := hp.fitF
  have fG := hp.fitG
  have eF : State.addr (pf s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (F s₀) i :=
    addr_ptr _ _ _ (by omega)
  have eG : State.addr (pg s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (G s₀) i :=
    addr_ptr _ _ _ (by omega)
  have cF := coeff_contains (F s₀) (i := i) hi
  have cG := coeff_contains (G s₀) (i := i) hi
  refine WP.mono (hb h.r0 h.r1 h.r2 ?_ ?_ ?_) fun s' ⟨r0, r1, r2, z, m, rd, wr, sp, pres⟩ => ⟨⟨?_, ?_, ?_,
    rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [eF, h.rd, h.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) cF
  · rw [eG, h.rd, h.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) cG
  · rw [eF, h.wr, hp.wr]; exact inRegions_of (by simp) cF
  · rw [r0]; exact ptr_succ _ 4 i
  · rw [r1]; exact ptr_succ _ 4 i
  · rw [r2]; exact count_sub (k := 1) hi
  · rw [m, eF]
    exact h.frame.writeW (List.mem_singleton_self _) _ cF
  · intro j hj
    rw [m, eF, coeffAt_writeW _ _ hj hi, h.coeff j hj]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right hij]
      by_cases hj' : j < i
      · rw [ite_eq_left hj', ite_eq_left (by omega)]
      · rw [ite_eq_right hj', ite_eq_right (by omega)]
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-- The whole loop. -/
theorem loop_ok {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {body : List Instr}
    (hb : ∀ i < 256, ∀ s, Inv out s₀ i s → ∀ {x y c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = y →
      s.gpr .r2 = c → InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
      WP isa (.block body) s (Step s x y c (out i))) :
    WP isa (.seq (.block [.mov .r2 (.imm 256)]) (.loop (.block body) .ne)) s₀ (Inv out s₀ 256) := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, runBlock_cons.trans (by rfl), wp_loop_ne (Inv out s₀) (N := 256) (by decide)
    (fun i hi s h => inv_step hp hi h (hb i hi s h)) (fun _ h => h) ?_⟩
  refine ⟨by simp [State.setReg], by simp [State.setReg], rfl, rfl, rfl, rfl,
    fun r hr => ?_, Frame.refl _ _, fun j _ => rfl⟩
  simp only [State.setReg]
  rw [ite_eq_right]
  intro e; subst e; simp [preserved] at hr

/-! ## Correctness -/

/-- The value stored in coefficient `j` by `vg_mldsa_add`. -/
def addOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((add (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀)))[j]!).val

/-- The value stored in coefficient `j` by `vg_mldsa_sub`. -/
def subOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((sub (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀)))[j]!).val

/-- What an iteration reads: coefficient `i` of each polynomial, as on entry. -/
theorem reads {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : Inv out s₀ i s) {x y : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) :
    s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (F s₀) i ∧
      s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (G s₀) i := by
  have fF := hp.fitF
  have fG := hp.fitG
  rw [← h0, ← h1, h.r0, h.r1, addr_ptr _ _ _ (by omega), addr_ptr _ _ _ (by omega)]
  refine ⟨?_, ?_⟩
  · show coeffAt s.mem (F s₀) i = _
    rw [h.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]
  · show coeffAt s.mem (G s₀) i = _
    exact coeffAt_frame h.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) hi

theorem add_hb {s₀ : State} (hp : Pre s₀) : ∀ i < 256, ∀ s, Inv (addOut s₀) s₀ i s →
    ∀ {x y c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = y → s.gpr .r2 = c →
      InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
      WP isa (.block addBody) s (Step s x y c (addOut s₀ i)) := by
  intro i hi s h x y c h0 h1 h2 ia ib oa
  obtain ⟨ea, eb⟩ := reads hp hi h h0 h1
  refine WP.mono (addBody_ok h0 h1 h2 ia ib oa) fun s' hs => ?_
  rw [ea, eb] at hs
  refine (?_ : _ = addOut s₀ i) ▸ hs
  refine ofNat_val_eq ?_
  rw [fixS_add (hp.redF i hi) (hp.redG i hi), add_get _ _ hi, val_add', polyAt_val hp.redF hi,
    polyAt_val hp.redG hi]

theorem sub_hb {s₀ : State} (hp : Pre s₀) : ∀ i < 256, ∀ s, Inv (subOut s₀) s₀ i s →
    ∀ {x y c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = y → s.gpr .r2 = c →
      InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
      WP isa (.block subBody) s (Step s x y c (subOut s₀ i)) := by
  intro i hi s h x y c h0 h1 h2 ia ib oa
  obtain ⟨ea, eb⟩ := reads hp hi h h0 h1
  refine WP.mono (subBody_ok h0 h1 h2 ia ib oa) fun s' hs => ?_
  rw [ea, eb] at hs
  refine (?_ : _ = subOut s₀ i) ▸ hs
  refine ofNat_val_eq ?_
  rw [fixS_sub (hp.redF i hi) (hp.redG i hi), sub_get _ _ hi, val_sub', polyAt_val hp.redF hi,
    polyAt_val hp.redG hi, Nat.add_sub_assoc (by have := hp.redG i hi; omega)]

/-- The loop's result: `f` is `out` of each coefficient. -/
theorem polyIs_of_inv {out : Nat → BitVec 32} {s₀ s : State} {g : Poly}
    (h : Inv out s₀ 256 s) (hg : ∀ j < 256, out j = BitVec.ofNat 32 (g[j]!).val) :
    PolyIs s.mem (F s₀) g :=
  polyIs_of_toNat fun j hj => by rw [h.coeff j hj, ite_eq_left hj, hg j hj, toNat_val]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlDsa.addContract Arm.abi).pre s) : Pre s := by
  sig_pre [Spec.MlDsa.addContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem pre_of_sub {s : State} (h : (Spec.MlDsa.subContract Arm.abi).pre s) : Pre s := by
  sig_pre [Spec.MlDsa.subContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

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
  rd := [⟨0x2000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun i _ => by
  rw [coeffAt_eq]
  have : Mem.readW (fun _ => (0 : Byte)) (coeffAddr p i) 32 = 0 := by
    simp [Mem.readW, Mem.read]
  rw [this]; decide

/-- The taint analysis, with the registers `rs` public. -/
theorem ctRegs {k : Contract isa} (rs : List Reg)
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    ConstantTime isa k.pre k.pub c :=
  VG.Taint.constantTime (A := VG.Arm.taint) (Taint.ofRegs rs)
    (fun s₁ s₂ _ _ hp => Taint.agree_ofRegs (hpub s₁ s₂ hp)) h

theorem add_verified : Verified Arm.target Impl.MlDsa.Arm.Arith.add (Spec.MlDsa.addContract Arm.abi) := by
  refine ⟨fun s hs => ?_, ctRegs [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp (add_hb hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp⟩, ?_⟩
    sig_post [Spec.MlDsa.addContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact polyIs_of_inv h fun j _ => rfl
  · sig_pub [Spec.MlDsa.addContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.addContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

theorem sub_verified : Verified Arm.target Impl.MlDsa.Arm.Arith.sub (Spec.MlDsa.subContract Arm.abi) := by
  refine ⟨fun s hs => ?_, ctRegs [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of_sub hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp (sub_hb hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp⟩, ?_⟩
    sig_post [Spec.MlDsa.subContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact polyIs_of_inv h fun j _ => rfl
  · sig_pub [Spec.MlDsa.subContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.subContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Arith.AddSub
