import VerifiedGarbage.Impl.MlKem.X86_64.Arith
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86-64: `vg_mlkem_add` and `vg_mlkem_sub`

Untrusted: everything here is checked by Lean. A doubleword of the result
is `condSub` of the sum (`add_lane`, `sub_lane`); the loop stores four of
them at a time to `f` (`AddSub.Inv`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## One doubleword -/

/-- `d + q` if `d` is negative (as a signed doubleword), else `d`: `dcadd` on one doubleword. -/
def cadd32 (d : BitVec 32) : BitVec 32 := d + (d.sshiftRight 31 &&& 3329#32)

theorem sshiftRight31 (d : BitVec 32) : d.sshiftRight 31 = if d.toNat < 2 ^ 31 then 0 else -1 := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, W.toInt32]
  have := d.isLt
  split
  · rw [show (0 : BitVec 32).toInt = 0 by decide, Int.shiftRight_eq_div_pow]; omega
  · rw [show (-1 : BitVec 32).toInt = -1 by decide, Int.shiftRight_eq_div_pow]; omega

theorem cadd32_toNat (d : BitVec 32) :
    (cadd32 d).toNat = if d.toNat < 2 ^ 31 then d.toNat else (d.toNat + 3329) % 2 ^ 32 := by
  rw [cadd32, sshiftRight31]
  split
  · rw [show (0 : BitVec 32) &&& 3329#32 = 0 by decide]; exact congrArg BitVec.toNat (BitVec.add_zero d)
  · rw [show (-1 : BitVec 32) &&& 3329#32 = 3329#32 by decide, BitVec.toNat_add]; rfl

/-- A lane of `add`. -/
theorem add_lane {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (cadd32 (a + b - 3329#32)).toNat = condSub (a.toNat + b.toNat) := by
  have e : (a + b - 3329#32).toNat = (a.toNat + b.toNat + 2 ^ 32 - 3329) % 2 ^ 32 := by
    rw [BitVec.toNat_sub, BitVec.toNat_add]; rw [q_eq] at *; simp only [BitVec.toNat_ofNat]; omega
  rw [cadd32_toNat, e, condSub]; rw [q_eq] at *
  split <;> split <;> omega

/-- A lane of `sub`. -/
theorem sub_lane {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (cadd32 (a - b)).toNat = condSub (a.toNat + q - b.toNat) := by
  have e : (a - b).toNat = (a.toNat + 2 ^ 32 - b.toNat) % 2 ^ 32 := by
    rw [BitVec.toNat_sub]; have := b.isLt; omega
  rw [cadd32_toNat, e, condSub]; rw [q_eq] at *
  split <;> split <;> omega

/-! ## Four doublewords -/

theorem dword_psubd (a b : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .psubd a b) i = dword a i - dword b i := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XBinOp.eval]

theorem dword_pand (a b : BitVec 128) (i : Nat) :
    dword (XBinOp.eval .pand a b) i = dword a i &&& dword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, dword, hj]

theorem dword_psrad31 (a : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrad a 31) i = (dword a i).sshiftRight 31 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XShiftOp.eval]

/-- `q` in each doubleword. -/
def qD : BitVec 128 := 0x00000D0100000D0100000D0100000D01#128

theorem dword_qD {i : Nat} (hi : i < 4) : dword qD i = 3329#32 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> decide

theorem addBody_ok {s : State} (hq : s.xmm .xmm15 = qD) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16) (h3 : InRegions s.wr (s.gpr .rdi) 16) :
    WP isa (.block addBody) s fun s' => (∃ X, s'.mem = s.mem.writeW (s.gpr .rdi) X ∧
      ∀ j < 4, dword X j = cadd32 (dword (s.mem.readW (s.gpr .rdi) 128) j +
        dword (s.mem.readW (s.gpr .rsi) 128) j - 3329#32)) ∧
      s'.gpr .rdi = s.gpr .rdi + 16 ∧ s'.gpr .rsi = s.gpr .rsi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.xmm .xmm15 = qD ∧ Keep [.rdi, .rsi, .rcx] s s' := by
  simp only [addBody, dcadd, dstep]
  vrunm [h1, h2, h3, eval_movdqa]
  refine ⟨⟨_, rfl, fun j hj => ?_⟩, hq, fun r hr => ?_, rfl, rfl⟩
  · simp only [dword_paddd _ _ hj, dword_psubd _ _ hj, dword_pand, dword_psrad31 _ hj, hq, dword_qD hj]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
theorem subBody_ok {s : State} (hq : s.xmm .xmm15 = qD) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16) (h3 : InRegions s.wr (s.gpr .rdi) 16) :
    WP isa (.block subBody) s fun s' => (∃ X, s'.mem = s.mem.writeW (s.gpr .rdi) X ∧
      ∀ j < 4, dword X j = cadd32 (dword (s.mem.readW (s.gpr .rdi) 128) j -
        dword (s.mem.readW (s.gpr .rsi) 128) j)) ∧
      s'.gpr .rdi = s.gpr .rdi + 16 ∧ s'.gpr .rsi = s.gpr .rsi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.xmm .xmm15 = qD ∧ Keep [.rdi, .rsi, .rcx] s s' := by
  simp only [subBody, dcadd, dstep]
  vrunm [h1, h2, h3, eval_movdqa]
  refine ⟨⟨_, rfl, fun j hj => ?_⟩, hq, fun r hr => ?_, rfl, rfl⟩
  · simp only [dword_paddd _ _ hj, dword_psubd _ _ hj, dword_pand, dword_psrad31 _ hj, hq, dword_qD hj]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]

/-! ## The loop -/

namespace AddSub

/-- After `i` groups of four coefficients, each one `v k`. -/
structure Inv (s₀ : State) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = coeffAddr (s₀.gpr .rdi) (4 * i)
  rsi : s.gpr .rsi = coeffAddr (s₀.gpr .rsi) (4 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  q : s.xmm .xmm15 = qD
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rdi) k = if k < 4 * i then v k else coeffAt s₀.mem (s₀.gpr .rdi) k

/-- What a body does: store `v` of the next four coefficients. -/
def Body (v : Nat → BitVec 32) (i : Nat) (s s' : State) : Prop :=
  (∃ X, s'.mem = s.mem.writeW (s.gpr .rdi) X ∧ ∀ j < 4, dword X j = v (4 * i + j)) ∧
    s'.gpr .rdi = s.gpr .rdi + 16 ∧ s'.gpr .rsi = s.gpr .rsi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
    s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.xmm .xmm15 = qD ∧ Keep [.rdi, .rsi, .rcx] s s'

theorem step16 (p : Addr) (i : Nat) : coeffAddr p (4 * i) + 16 = coeffAddr p (4 * (i + 1)) := by
  rw [show (16 : BitVec 64) = BitVec.ofNat 64 (4 * 4) from rfl, coeffAddr_off, Nat.mul_succ]

theorem inv_step {s₀ : State} {v : Nat → BitVec 32} {i : Nat} (hi : i < 64) {s s' : State}
    (hI : Inv s₀ v i s) (hb : Body v i s s') : Inv s₀ v (i + 1) s' := by
  obtain ⟨⟨X, hm, hX⟩, hdi, hsi, -, -, hq, hk⟩ := hb
  refine ⟨by rw [hdi, hI.rdi, step16], by rw [hsi, hI.rsi, step16], hk.2.1.trans hI.rd,
    hk.2.2.trans hI.wr, hq, ?_, fun k hk' => ?_⟩
  · rw [hm, hI.rdi]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm, hI.rdi, coeffAt_write128 _ _ (by omega) _ hk', hI.coeff k hk']
    by_cases e : 4 * i ≤ k ∧ k < 4 * i + 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true e), hX _ (by omega), ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
        show 4 * i + (k - 4 * i) = k by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false e)]
      by_cases e' : k < 4 * i
      · rw [ite_eq_left_of_eq_true _ _ (eq_true e'), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false e'), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

section
variable {t : Poly → Poly → Poly} {s₀ : State} (hp : (accK t).pre s₀)
include hp

theorem regions {v : Nat → BitVec 32} {i : Nat} (hi : i < 64) {s : State} (hI : Inv s₀ v i s) :
    InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16 ∧ InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16 ∧
      InRegions s.wr (s.gpr .rdi) 16 := by
  rw [hI.rd, hI.wr, hI.rdi, hI.rsi, hp.1, hp.2.1]
  exact ⟨⟨pR _, List.mem_append_right _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩,
    ⟨pR _, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩,
    ⟨pR _, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩⟩

/-- The coefficients a body reads. -/
theorem reads {v : Nat → BitVec 32} {i : Nat} (hi : i < 64) {s : State} (hI : Inv s₀ v i s) {j : Nat}
    (hj : j < 4) :
    dword (s.mem.readW (s.gpr .rdi) 128) j = coeffAt s₀.mem (s₀.gpr .rdi) (4 * i + j) ∧
      dword (s.mem.readW (s.gpr .rsi) 128) j = coeffAt s₀.mem (s₀.gpr .rsi) (4 * i + j) := by
  refine ⟨?_, ?_⟩
  · rw [dword_readW _ _ hj, hI.rdi, coeffAddr_off, ← coeffAt_eq, hI.coeff _ (by omega),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · rw [dword_readW _ _ hj, hI.rsi, coeffAddr_off, ← coeffAt_eq]
    exact coeffAt_congr (bytes_frame hI.frame (by simpa using hp.2.2.1.symm) (by decide)) (by rw [n_eq]; omega)

/-- The whole function, from its precondition. -/
theorem fn_ok {body : List Instr} {v : Nat → BitVec 32}
    (hbody : ∀ i < 64, ∀ s, Inv s₀ v i s → WP isa (.block body) s (Body v i s))
    (hv : ∀ i < 256, (v i).toNat = ((t (polyAt s₀.mem (s₀.gpr .rdi)) (polyAt s₀.mem (s₀.gpr .rsi)))[i]!).val)
    (hc : writesOnly [.rax, .rdi, .rsi, .rcx]
      (.seq (.block (dconsts ++ ([.mov32 .rcx (.imm 64)] : List Instr))) (.loop (.block body) .ne)) = true)
    (hm : Code.allInstrs (fun i => !loadsMxcsr i)
      (.seq (.block (dconsts ++ ([.mov32 .rcx (.imm 64)] : List Instr))) (.loop (.block body) .ne) : Prog isa) = true) :
    ∃ tr s', Exec isa (.seq (.block (dconsts ++ ([.mov32 .rcx (.imm 64)] : List Instr))) (.loop (.block body) .ne)) s₀ tr s' ∧
      abiPreserved s₀ s' ∧ (accK t).post s₀ s' := by
  have hL : WP isa (.seq (.block (dconsts ++ ([.mov32 .rcx (.imm 64)] : List Instr))) (.loop (.block body) .ne)) s₀
      (Inv s₀ v 64) := by
    refine WP.seq (WP.mono (Q := fun (s : State) => s.xmm .xmm15 = qD ∧ s.gpr .rcx = BitVec.ofNat 64 64 ∧
        s.mem = s₀.mem ∧ Keep [.rax, .rcx] s₀ s) (by
          simp only [dconsts]
          vrunm
          refine ⟨fun r hr => ?_, rfl, rfl⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false]) fun s ⟨hq, hcx, hm0, k0⟩ => ?_)
    refine wp_countdown (cnt := .rcx) (N := 64) (by decide) (by decide) (Inv s₀ v)
      (fun i hi s hI _ => WP.mono (hbody i hi s hI) fun s' hb => ⟨inv_step hi hI hb, hb.2.2.2.1, hb.2.2.2.2.1⟩)
      (fun _ h => h) ⟨?_, ?_, k0.2.1, k0.2.2, hq, by rw [hm0]; exact Frame.refl _ _, fun k _ => ?_⟩ hcx
    · rw [k0.gpr (by decide)]; exact (BitVec.add_zero _).symm
    · rw [k0.gpr (by decide)]; exact (BitVec.add_zero _).symm
    · rw [hm0]; exact (ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_lt_zero _))).symm
  obtain ⟨tr, s', he, hI, hk⟩ := WP.keep _ hL hc
  refine ⟨tr, s', he, abiPreserved_of_exec hm he (gprPreserved_of hk (by decide) hI.frame ?_),
    polyIs_of_toNat fun i hi => ?_⟩
  · simpa using hp.2.2.2.1
  · rw [n_eq] at hi
    rw [hI.coeff i hi, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; exact hv i hi

end

end AddSub

/-! ## The functions -/

theorem add_correct (s : State) (hs : (accK Spec.MlKem.add).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.add s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlKem.add).post s s' :=
  AddSub.fn_ok hs (v := fun i => cadd32 (coeffAt s.mem (s.gpr .rdi) i + coeffAt s.mem (s.gpr .rsi) i - 3329#32))
    (fun i hi s' hI => by
      obtain ⟨h1, h2, h3⟩ := AddSub.regions hs hi hI
      refine WP.mono (addBody_ok hI.q h1 h2 h3) fun s'' ⟨⟨X, hm, hX⟩, rest⟩ => ⟨⟨X, hm, fun j hj => ?_⟩, rest⟩
      obtain ⟨e1, e2⟩ := AddSub.reads hs hi hI hj
      rw [hX j hj, e1, e2])
    (fun i hi => by
      rw [add_lane (hs.2.2.2.2.2.1 i (by rw [n_eq]; exact hi)) (hs.2.2.2.2.2.2 i (by rw [n_eq]; exact hi)),
        add_get _ _ (by rw [n_eq]; exact hi), val_add,
        polyAt_val hs.2.2.2.2.2.1 (by rw [n_eq]; exact hi), polyAt_val hs.2.2.2.2.2.2 (by rw [n_eq]; exact hi)])
    (by decide) (by decide)

theorem sub_correct (s : State) (hs : (accK Spec.MlKem.sub).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.sub s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlKem.sub).post s s' :=
  AddSub.fn_ok hs (v := fun i => cadd32 (coeffAt s.mem (s.gpr .rdi) i - coeffAt s.mem (s.gpr .rsi) i))
    (fun i hi s' hI => by
      obtain ⟨h1, h2, h3⟩ := AddSub.regions hs hi hI
      refine WP.mono (subBody_ok hI.q h1 h2 h3) fun s'' ⟨⟨X, hm, hX⟩, rest⟩ => ⟨⟨X, hm, fun j hj => ?_⟩, rest⟩
      obtain ⟨e1, e2⟩ := AddSub.reads hs hi hI hj
      rw [hX j hj, e1, e2])
    (fun i hi => by
      rw [sub_lane (hs.2.2.2.2.2.1 i (by rw [n_eq]; exact hi)) (hs.2.2.2.2.2.2 i (by rw [n_eq]; exact hi)),
        sub_get _ _ (by rw [n_eq]; exact hi), val_sub,
        polyAt_val hs.2.2.2.2.2.1 (by rw [n_eq]; exact hi), polyAt_val hs.2.2.2.2.2.2 (by rw [n_eq]; exact hi)])
    (by decide) (by decide)

/-- The pointers and `rsp` are public. -/
def accτ : X86_64.Taint.T := X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]

theorem acc_agree {t : Poly → Poly → Poly} (s₁ s₂ : State) (_ : (accK t).pre s₁) (_ : (accK t).pre s₂)
    (hp : (accK t).pub s₁ s₂) : X86_64.Taint.Agree accτ s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2]

theorem add_ct : ConstantTime isa (accK Spec.MlKem.add).pre (accK Spec.MlKem.add).pub Impl.MlKem.X86_64.add :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

theorem sub_ct : ConstantTime isa (accK Spec.MlKem.sub).pre (accK Spec.MlKem.sub).pub Impl.MlKem.X86_64.sub :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def accSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem add_verified :
    Verified X86_64.target Impl.MlKem.X86_64.add (Spec.MlKem.addContract X86_64.abi) :=
  Verified.of_correct add_correct add_ct (by
    mlkem_implies [Spec.MlKem.addContract, Spec.MlKem.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using accSat)

theorem sub_verified :
    Verified X86_64.target Impl.MlKem.X86_64.sub (Spec.MlKem.subContract X86_64.abi) :=
  Verified.of_correct sub_correct sub_ct (by
    mlkem_implies [Spec.MlKem.subContract, Spec.MlKem.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using accSat)

end VG.Proof.MlKem.X86_64
