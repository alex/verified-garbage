import VerifiedGarbage.Proof.MlKem.X86.Red
import VerifiedGarbage.Impl.MlDsa.X86.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.Arith.Mont
import VerifiedGarbage.Proof.MlDsa.Arith.Mem

/-!
# ML-DSA on x86 (32-bit): the reductions modulo `q`

What the pieces of code of `Impl/MlDsa/X86/Arith/Basic.lean` compute: `csubQ`
reduces a value less than `2q` (`csubQ_eq`), and `montRaw` and `mont` leave
the Montgomery reduction `mont x` (`Proof/MlDsa/Arith/Mont.lean`) of the
product `x` in `edx:eax` (`mredRaw_spec`, `mont_spec`).
-/

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q)
open VG.Proof.MlKem.X86 (Only wp_cons toNat_ofNat32 eq_ofNat_of_toNat E0 P0 frameR retR saveRegs_len
  execMul_eax execMul_other ea_add)

theorem qImm_toNat : qImm.toNat = q := rfl

theorem sub_val (x y : Spec.MlDsa.Zq) : (x - y).val = (x.val + q - y.val) % q := by
  rw [val_sub', show x.val + (q - y.val) = x.val + q - y.val by have := y.isLt; omega]

theorem mod_q_lt32 (x : Nat) : x % q < 2 ^ 32 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)

/-- `csubQ` as the code computes it, as a word. -/
theorem csubQ_eq (x d : BitVec 32) (hx : x.toNat < 2 * q) :
    x - qImm + ((d - d - (BitVec.ofBool (decide (x.toNat < qImm.toNat))).setWidth 32) &&& qImm) =
      BitVec.ofNat 32 (x.toNat % q) := by
  rw [qImm_toNat]
  apply BitVec.eq_of_toNat_eq
  rw [q_eq] at hx ⊢
  by_cases h : x.toNat < 8380417
  · rw [decide_eq_true h]
    have e : (d - d - (BitVec.ofBool true).setWidth 32) &&& qImm = qImm := by
      rw [BitVec.sub_self]; decide
    rw [e, BitVec.sub_add_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
  · rw [decide_eq_false h]
    have e : (d - d - (BitVec.ofBool false).setWidth 32) &&& qImm = 0 := by
      rw [BitVec.sub_self]; decide
    rw [e, show x - qImm + 0 = x - qImm from BitVec.add_zero _, BitVec.toNat_sub, qImm_toNat, q_eq,
      BitVec.toNat_ofNat]
    omega

/-- The value `mredRaw` leaves, from the halves `hi` and `lo` of `x`. -/
theorem mredRaw_val (hi lo : BitVec 32) (hx : hi.toNat * 2 ^ 32 + lo.toNat < q * 2 ^ 32) :
    (hi + BitVec.ofNat 32 ((BitVec.ofNat 32 (lo.toNat * qInvImm.toNat)).toNat * qImm.toNat / 2 ^ 32) +
      BitVec.setWidth 32 (BitVec.ofBool (decide (2 ^ 32 ≤
        (BitVec.ofNat 32 ((BitVec.ofNat 32 (lo.toNat * qInvImm.toNat)).toNat * qImm.toNat)).toNat +
          BitVec.toNat (4294967295 : BitVec 32))))).toNat = mont (hi.toNat * 2 ^ 32 + lo.toNat) := by
  have hl := lo.isLt
  have hm : (BitVec.ofNat 32 (lo.toNat * qInvImm.toNat)).toNat = montM (hi.toNat * 2 ^ 32 + lo.toNat) := by
    rw [BitVec.toNat_ofNat, montM, Nat.mul_add_mod_of_lt hl]; rfl
  rw [hm, qImm_toNat, BitVec.toNat_ofNat, show BitVec.toNat (4294967295 : BitVec 32) = 4294967295 from rfl]
  have hlt := mont_lt hx
  rw [mont_halves] at hlt ⊢
  have e1 : (hi.toNat * 2 ^ 32 + lo.toNat) / 2 ^ 32 = hi.toNat := by omega
  rw [e1] at hlt ⊢
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  have hP := Nat.mod_lt (montM (hi.toNat * 2 ^ 32 + lo.toNat) * q) (show 0 < 2 ^ 32 by decide)
  obtain ⟨P, hPd⟩ : ∃ P, montM (hi.toNat * 2 ^ 32 + lo.toNat) * q = P := ⟨_, rfl⟩
  rw [hPd] at hlt hP ⊢
  rw [q_eq] at hlt
  have hh := hi.isLt
  by_cases hc : 1 ≤ P % 2 ^ 32
  · rw [decide_eq_true (by omega), ite_eq_left_of_eq_true _ _ (eq_true hc)] at *
    simp only [Bool.toNat_true] at *
    omega
  · rw [decide_eq_false (by omega), ite_eq_right_of_eq_false _ _ (eq_false hc)] at *
    simp only [Bool.toNat_false] at *
    omega

/-- `mredRaw r` leaves `mont x` in `r` from `x` in `edx:eax`, changing only
`eax`, `edx`, `r` and the flags. -/
theorem mredRaw_spec {r : Reg} (h1 : r ≠ .eax) (h2 : r ≠ .edx) (is : List Instr) (s : State)
    (P : State → Prop) {x : Nat} (hx : (s.gpr .edx).toNat * 2 ^ 32 + (s.gpr .eax).toNat = x)
    (hlt : x < q * 2 ^ 32)
    (k : ∀ s', Only [.eax, .edx, r] s s' → (s'.gpr r).toNat = mont x → WP isa (.block is) s' P) :
    WP isa (.block (mredRaw r ++ is)) s P := by
  have h2' : Reg.edx ≠ r := fun e => h2 e.symm
  have h1' : Reg.eax ≠ r := fun e => h1 e.symm
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mredRaw, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, execMul, readSrc, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, Option.map_some, ite_true, ite_false, Option.some.injEq, exists_eq_left', h1, h2,
    h2', h1']
  refine k _ ⟨fun q hq => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [hq.1, hq.2.1, hq.2.2]
  · simp only [ite_true]
    rw [← hx] at hlt ⊢
    exact mredRaw_val _ _ hlt

/-- `csubQ r t` reduces `r < 2q`, changing only `r`, `t` and the flags. -/
theorem csubQ_spec {r t : Reg} (h : r ≠ t) (is : List Instr) (s : State) (P : State → Prop)
    (hr : (s.gpr r).toNat < 2 * q)
    (k : ∀ s', Only [r, t] s s' → (s'.gpr r).toNat = (s.gpr r).toNat % q → WP isa (.block is) s' P) :
    WP isa (.block (csubQ r t ++ is)) s P := by
  have h' : t ≠ r := fun e => h e.symm
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [csubQ, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.map_some, ite_true, ite_false,
    Option.some.injEq, exists_eq_left', h, h']
  refine k _ ⟨fun x hx => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hx.1, hx.2]
  · simp only [ite_true]
    have := Nat.mod_lt (s.gpr r).toNat (show q > 0 by decide)
    rw [q_eq] at this
    rw [csubQ_eq _ _ hr, toNat_ofNat32 (by rw [q_eq]; omega)]

/-- `mred r` leaves `mont x mod q` in `r` from `x` in `edx:eax`, changing
only `eax`, `edx`, `r` and the flags. -/
theorem mred_spec {r : Reg} (h1 : r ≠ .eax) (h2 : r ≠ .edx) (is : List Instr) (s : State)
    (P : State → Prop) {x : Nat} (hx : (s.gpr .edx).toNat * 2 ^ 32 + (s.gpr .eax).toNat = x)
    (hlt : x < q * 2 ^ 32)
    (k : ∀ s', Only [.eax, .edx, r] s s' → (s'.gpr r).toNat = mont x % q → WP isa (.block is) s' P) :
    WP isa (.block (mred r ++ is)) s P := by
  rw [mred, List.append_assoc]
  refine mredRaw_spec h1 h2 _ s P hx hlt fun s₁ o₁ v₁ => ?_
  refine csubQ_spec h2 _ s₁ P (by rw [v₁]; exact mont_lt hlt) fun s₂ o₂ v₂ => ?_
  refine k s₂ ((o₁.trans o₂).mono fun y hy => ?_) (by rw [v₂, v₁])
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
  rcases hy with (e | e | e) | (e | e) <;> simp [e]

/-! ## Products -/

theorem execMul_edx (r : Reg) (s : State) :
    (execMul r s).gpr .edx = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat / 2 ^ 32) := by
  simp [execMul, State.setReg, State.setFlags]

/-- `mul r` leaves the product in `edx:eax`. -/
theorem execMul_pair (r : Reg) (s : State) :
    ((execMul r s).gpr .edx).toNat * 2 ^ 32 + ((execMul r s).gpr .eax).toNat =
      (s.gpr .eax).toNat * (s.gpr r).toNat := by
  rw [execMul_edx, execMul_eax, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := Nat.mul_lt_mul_of_lt_of_lt (s.gpr .eax).isLt (s.gpr r).isLt
  generalize (s.gpr .eax).toNat * (s.gpr r).toNat = p at this ⊢
  omega

/-- `mov d, imm` -/
theorem wp_movi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : WP isa (.block is) (s.setReg d v) Q) : WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  wp_cons (by simp only [exec, readSrc, Option.map_some]) k

/-! ## Memory -/

theorem polyLen (p : Addr) : (polyRegion p).len ≤ 2 ^ 64 := by show 1024 ≤ 2 ^ 64; decide

/-- The stack below the return address, as the contracts state it, is the leaf's frame. -/
theorem stk_eq {s₀ : State} (h : 16 ≤ (E0 s₀).toNat) :
    (⟨(E0 s₀).setWidth 64 - 16#64, 16⟩ : Region) = frameR s₀ := by
  simp only [frameR, below]; rw [Taint.sub_setWidth h]

/-- The push changes nothing of a region apart from the frame. -/
theorem P0_mem {s₀ : State} (h : 16 ≤ (E0 s₀).toNat) : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := Impl.MlKem.X86.saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact h)
  rw [saveRegs_len] at hf
  exact hf

/-- Coefficient `k` at the pointer `x + 4k`. -/
theorem ea_ptr {x : BitVec 32} (hx : x.toNat + 1024 ≤ 2 ^ 32) {k : Nat} (hk : k < 256) :
    (x + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (x.setWidth 64) k := by
  rw [ea_add (by omega), Nat.add_zero]

/-- All-zero memory holds a reduced polynomial. -/
theorem reduced_of_zero {m : Mem} {p : Addr} (h : ∀ k < 1024, m (p + BitVec.ofNat 64 k) = 0) :
    Spec.MlDsa.Reduced m p := fun i hi => by
  rw [coeffAt_congr (m' := m) (m := fun _ => 0) (fun k hk => h k hk) hi]
  simp [Spec.MlDsa.coeffAt, Mem.readW, Mem.read]

/-- Memory that is zero below `0x5000` holds reduced polynomials there. -/
theorem reduced_below {m : Mem} (hm : ∀ a : Addr, a.toNat < 0x5000 → m a = 0) (p : Nat)
    (hp : p + 1024 ≤ 0x5000) : Spec.MlDsa.Reduced m (BitVec.ofNat 64 p) :=
  reduced_of_zero fun k hk => hm _ (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)

end VG.Proof.MlDsa.X86.Arith
