import VerifiedGarbage.Proof.MlKem1024.Arm.Encrypt
import VerifiedGarbage.Proof.MlKem1024.Arm.RowCT
import VerifiedGarbage.Proof.MlKem.Arm.EncryptCT

/-!
# ML-KEM-1024 on 32-bit ARM: K-PKE.Encrypt in constant time

Two runs of `encrypt` on the same buffers (`EncPre` of the same layout and
`EB`) whose encapsulation keys have the same `ρ` leak the same trace
(`encrypt_ct`): the blocks access no memory or only memory through the
pointers, the calls take the same pointers in both runs, and the rows'
`SampleNTT`s take the same seeds (`rowSum_ct`). What each run is at each point
comes from its correctness (`Encrypt.lean`).
-/

namespace VG.Proof.MlKem1024.Arm.Enc

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm VG.Proof.MlKem1024.Arm
open VG.Proof.MlKem.Arm.Enc (EB)
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

/-! ## Decoding four polynomials -/

theorem decT1_ok {L : Lay} {i o : Nat} {x s : State} (hc : Ctx L x) (g4 : x.gpr .r4 = L.ptr i + BitVec.ofNat 32 o)
    {j : Nat} (hj : j < 4) (h : DecInv L i o x j s) :
    WP isa (.block (at384 .r0 .r4 .r9 ++ slotAt .r1 .r9 (oPoly 0))) s fun s₁ =>
      s₁.gpr .r0 = L.ptr i + BitVec.ofNat 32 (o + 384 * j) ∧ s₁.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j) := by
  have hc' := h.kx.ctx (by decide) hc
  have g4' : s.gpr .r4 = L.ptr i + BitVec.ofNat 32 o := by
    rw [h.kx.cs .r4 (by decide) (by decide) (by decide), g4]
  refine WP.mono (decTArgs_ok hc'.r7 g4' h.r9) fun s₁ ⟨_, a0, a1⟩ => ⟨?_, ?_⟩
  · rw [a0, at384_eq _ (by omega), ptr_add_add32]
  · rw [a1, slot_eq _ (by offs4), show 2048 + 1024 * 0 + 1024 * j = 2048 + 1024 * j by omega]

theorem decT_ctG {L : Lay} {i o : Nat} {x y : State} (hcx : Ctx L x) (hcy : Ctx L y)
    (g4x : x.gpr .r4 = L.ptr i + BitVec.ofNat 32 o) (g4y : y.gpr .r4 = L.ptr i + BitVec.ofNat 32 o)
    (hs : sepAll L.sizes (i, o, 1536) [(0, 2048, 4096)] = true) (hrx : L.buf i ∈ x.rd ++ x.wr)
    (hry : L.buf i ∈ y.rd ++ y.wr) {j : Nat} (hj : j < 4) :
    RelCT isa (fun a₁ a₂ => DecInv L i o x j a₁ ∧ DecInv L i o y j a₂) decTBody4 fun a₁ a₂ =>
      (DecInv L i o x (j + 1) a₁ ∧ a₁.z = decide (j + 1 = 4)) ∧
      (DecInv L i o y (j + 1) a₂ ∧ a₂.z = decide (j + 1 = 4)) := by
  refine relct_wp (RelCT.pointwise fun u w ⟨hu, hw⟩ => ?_) fun a₁ a₂ hab =>
    ⟨decT_step hcx g4x hs hrx hj hab.1, decT_step hcy g4y hs hry hj hab.2⟩
  refine RelCT.seq (R := fun (a₁ a₂ : State) =>
      (a₁.gpr .r0 = L.ptr i + BitVec.ofNat 32 (o + 384 * j) ∧ a₁.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j)) ∧
      (a₂.gpr .r0 = L.ptr i + BitVec.ofNat 32 (o + 384 * j) ∧ a₂.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j)))
    (relct_wp (relct_noMem rfl) fun a₁ a₂ hab => ⟨by rw [hab.1]; exact decT1_ok hcx g4x hj hu,
      by rw [hab.2]; exact decT1_ok hcy g4y hj hw⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT decode12T (regs2 fun a₁ a₂ hab => ⟨by rw [hab.1.1, hab.2.1], by rw [hab.1.2, hab.2.2]⟩))
    (relct_noMem rfl)

section
variable {L : Lay} {b : EB} {s₀₁ s₀₂ : State} (hp₁ : EncPre L b s₀₁) (hp₂ : EncPre L b s₀₂)
include hp₁ hp₂

/-! ## `t̂` -/

theorem decT_ct {x y : State} (ex : EA L s₀₁ x) (ey : EA L s₀₂ y) {j : Nat} (hj : j < 4) :
    RelCT isa (fun a₁ a₂ => DecInv L b.iE b.oE x j a₁ ∧ DecInv L b.iE b.oE y j a₂) decTBody4 fun a b' =>
      (DecInv L b.iE b.oE x (j + 1) a ∧ a.z = decide (j + 1 = 4)) ∧
      (DecInv L b.iE b.oE y (j + 1) b' ∧ b'.z = decide (j + 1 = 4)) := by
  obtain ⟨hcx, g4x, hsx, hrx⟩ := dec_pre hp₁ ex
  obtain ⟨hcy, g4y, -, hry⟩ := dec_pre hp₂ ey
  exact decT_ctG hcx hcy g4x g4y hsx hrx hry hj

/-! ## The rows of `u` -/

theorem encRow_ct (hρ : ρE L b s₀₁ = ρE L b s₀₂) {i : Nat} (hi : i < 4) :
    RelCT isa (fun a b' => ERow L b s₀₁ i a ∧ ERow L b s₀₂ i b') encRowBody4 fun a b' =>
      (ERow L b s₀₁ (i + 1) a ∧ a.z = decide (i + 1 = 4)) ∧ (ERow L b s₀₂ (i + 1) b' ∧ b'.z = decide (i + 1 = 4)) := by
  refine relct_wp (RelCT.pointwise fun u w ⟨hu, hw⟩ => ?_) fun a b' hab =>
    ⟨encRow_step hp₁ hi hab.1, encRow_step hp₂ hi hab.2⟩
  have pw : RowPre L (ρE L b s₀₁) (VG.Proof.MlKem.encY (rB L s₀₂)) i (okE L b s₀₂ i) w := by
    have := hw.rowPre hp₂ hi; rwa [← hρ] at this
  -- `RowSum`
  refine RelCT.seq (R := fun (a b' : State) =>
      RowInv L true (ρE L b s₀₁) (VG.Proof.MlKem.encY (rB L s₀₁)) i (okE L b s₀₁ i) u 4 a ∧
      RowInv L true (ρE L b s₀₂) (VG.Proof.MlKem.encY (rB L s₀₂)) i (okE L b s₀₂ i) w 4 b')
    (relct_wp (rowSum_ct (hu.rowPre hp₁ hi) pw) fun a b' hab =>
      ⟨by rw [hab.1]; exact rowSum_ok (hu.rowPre hp₁ hi), by rw [hab.2]; exact rowSum_ok (hw.rowPre hp₂ hi)⟩) ?_
  -- `NTT⁻¹`
  refine RelCT.seq (R := fun (a b' : State) =>
      (RB L b s₀₁ i u (VG.Proof.MlKem.dot4 (fun j => aE L b s₀₁ j i) (VG.Proof.MlKem.encY (rB L s₀₁))) a ∧
        a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oNtt4) ∧
      (RB L b s₀₂ i w (VG.Proof.MlKem.dot4 (fun j => aE L b s₀₂ j i) (VG.Proof.MlKem.encY (rB L s₀₂))) b' ∧
        b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ b'.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oNtt4))
    (relct_wp (relct_noMem rfl) fun a b' hab => ⟨er2_ok hp₁ hu hab.1, er2_ok hp₂ hw hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b' : State) =>
      RB L b s₀₁ i u (nttInv (VG.Proof.MlKem.dot4 (fun j => aE L b s₀₁ j i) (VG.Proof.MlKem.encY (rB L s₀₁)))) a ∧
      RB L b s₀₂ i w (nttInv (VG.Proof.MlKem.dot4 (fun j => aE L b s₀₂ j i) (VG.Proof.MlKem.encY (rB L s₀₂)))) b')
    (relct_wp (RelCT.callT nttInvT (regs2 fun a b' hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨er3_ok hp₁ hu hab.1.1 hab.1.2.1 hab.1.2.2, er3_ok hp₂ hw hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- `+ e₁[i]`
  refine RelCT.seq (R := fun (a b' : State) =>
      (RB L b s₀₁ i u (nttInv (VG.Proof.MlKem.dot4 (fun j => aE L b s₀₁ j i) (VG.Proof.MlKem.encY (rB L s₀₁)))) a ∧
        a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧
        a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (4 + (4 + i)))) ∧
      (RB L b s₀₂ i w (nttInv (VG.Proof.MlKem.dot4 (fun j => aE L b s₀₂ j i) (VG.Proof.MlKem.encY (rB L s₀₂)))) b' ∧
        b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧
        b'.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (4 + (4 + i)))))
    (relct_wp (relct_noMem rfl) fun a b' hab => ⟨er4_ok hp₁ hi hu hab.1, er4_ok hp₂ hi hw hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b' : State) =>
      RB L b s₀₁ i u (VG.Proof.MlKem.encU1024 (aE L b s₀₁) (rB L s₀₁) i) a ∧
      RB L b s₀₂ i w (VG.Proof.MlKem.encU1024 (aE L b s₀₂) (rB L s₀₂) i) b')
    (relct_wp (RelCT.callT addT (regs2 fun a b' hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨er5_ok hp₁ hi hu hab.1.1 hab.1.2.1 hab.1.2.2, er5_ok hp₂ hi hw hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- its encoding
  refine RelCT.seq (R := fun (a b' : State) =>
      (RB L b s₀₁ i u (VG.Proof.MlKem.encU1024 (aE L b s₀₁) (rB L s₀₁) i) a ∧ a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧
        a.gpr .r1 = BitVec.ofNat 32 11 ∧ a.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + 352 * i) ∧
        a.gpr .r3 = BitVec.ofNat 32 (32 * 11)) ∧
      (RB L b s₀₂ i w (VG.Proof.MlKem.encU1024 (aE L b s₀₂) (rB L s₀₂) i) b' ∧ b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧
        b'.gpr .r1 = BitVec.ofNat 32 11 ∧ b'.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + 352 * i) ∧
        b'.gpr .r3 = BitVec.ofNat 32 (32 * 11)))
    (relct_wp (relct_noMem rfl) fun a b' hab => ⟨er6_ok hp₁ hi hu hab.1, er6_ok hp₂ hi hw hab.2⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT compress4T (regs4 fun a b' hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2.1, hab.2.2.2.1],
      by rw [hab.1.2.2.2.1, hab.2.2.2.2.1], by rw [hab.1.2.2.2.2, hab.2.2.2.2.2]⟩))
    (relct_noMem rfl)

/-! ## `v` -/

theorem v_ct {x y : State} (hx : VEnv L b s₀₁ x) (hy : VEnv L b s₀₂ y) :
    RelCT isa (fun a b' => a = x ∧ b' = y)
      (.seq dotP4 <|
      .seq (.block [ptrTo .r0 .r7 oAcc4, ptrTo .r1 .r7 oNtt4]) <|
      .seq callNttInv <|
      .seq (.block [ptrTo .r0 .r7 oAcc4, ptrTo .r1 .r7 (oPoly 12)]) <|
      .seq callAdd <|
      .seq (.block [ptrTo .r0 .r7 oAcc4, ptrTo .r1 .r7 (oPoly 13)]) <|
      .seq callAdd <|
      .seq (.block [ptrTo .r0 .r7 oAcc4, .mov .r1 (.imm 5), ptrTo .r2 .r8 1408, .mov .r3 (.imm 160)]) callCompress4)
      fun _ _ => True := by
  have hcx := hx.K.ctx (by decide) hp₁.ctx
  have hcy := hy.K.ctx (by decide) hp₂.ctx
  have va : ∀ {s₀ s : State}, VEnv L b s₀ s → ∀ j < 4,
      PolyIs s.mem (L.A 0 (oPoly j)) (VG.Proof.MlKem.ekT (ekB L b s₀) j) := fun h j hj => by
    have := h.d.v j (by omega); simp only [hj, ↓reduceIte] at this; exact this
  have vv : ∀ {s₀ s : State}, VEnv L b s₀ s → ∀ j < 4,
      PolyIs s.mem (L.A 0 (oPoly (4 + j))) (VG.Proof.MlKem.encY (rB L s₀) j) := fun h j hj => by
    have := h.d.v (4 + j) (by omega)
    have e : ¬ (4 + j < 4) := by omega
    simp only [e, ↓reduceIte, show 4 + j - 4 = j by omega] at this
    exact this
  -- `dot`
  refine RelCT.seq (R := fun (a b' : State) =>
      (VEnv L b s₀₁ a ∧ PolyIs a.mem (L.A 0 oAcc4)
        (VG.Proof.MlKem.dot4 (VG.Proof.MlKem.ekT (ekB L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁)))) ∧
      (VEnv L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 oAcc4)
        (VG.Proof.MlKem.dot4 (VG.Proof.MlKem.ekT (ekB L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂)))))
    (relct_wp (dot_ct hcx hcy (va hx) (vv hx) (va hy) (vv hy)) fun a b' hab =>
      ⟨by rw [hab.1]; exact ev1_ok hp₁ hx, by rw [hab.2]; exact ev1_ok hp₂ hy⟩) ?_
  -- `NTT⁻¹`
  refine RelCT.seq (R := fun (a b' : State) =>
      ((VEnv L b s₀₁ a ∧ PolyIs a.mem (L.A 0 oAcc4)
        (VG.Proof.MlKem.dot4 (VG.Proof.MlKem.ekT (ekB L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁)))) ∧
        a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oNtt4) ∧
      ((VEnv L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 oAcc4)
        (VG.Proof.MlKem.dot4 (VG.Proof.MlKem.ekT (ekB L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂)))) ∧
        b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ b'.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oNtt4))
    (relct_wp (relct_noMem rfl) fun a b' hab =>
      ⟨evArgs_ok hp₁ hab.1.1 hab.1.2 (by decide), evArgs_ok hp₂ hab.2.1 hab.2.2 (by decide)⟩) ?_
  refine RelCT.seq (R := fun (a b' : State) =>
      (VEnv L b s₀₁ a ∧ PolyIs a.mem (L.A 0 oAcc4)
        (nttInv (VG.Proof.MlKem.dot4 (VG.Proof.MlKem.ekT (ekB L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁))))) ∧
      (VEnv L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 oAcc4)
        (nttInv (VG.Proof.MlKem.dot4 (VG.Proof.MlKem.ekT (ekB L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂))))))
    (relct_wp (RelCT.callT nttInvT (regs2 fun a b' hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨ev3_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, ev3_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- `+ e₂`
  refine RelCT.seq (R := fun (a b' : State) =>
      ((VEnv L b s₀₁ a ∧ PolyIs a.mem (L.A 0 oAcc4)
        (nttInv (VG.Proof.MlKem.dot4 (VG.Proof.MlKem.ekT (ekB L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁))))) ∧
        a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly 12)) ∧
      ((VEnv L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 oAcc4)
        (nttInv (VG.Proof.MlKem.dot4 (VG.Proof.MlKem.ekT (ekB L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂))))) ∧
        b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ b'.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly 12)))
    (relct_wp (relct_noMem rfl) fun a b' hab =>
      ⟨evArgs_ok hp₁ hab.1.1 hab.1.2 (by decide), evArgs_ok hp₂ hab.2.1 hab.2.2 (by decide)⟩) ?_
  refine RelCT.seq (R := fun (a b' : State) =>
      (VEnv L b s₀₁ a ∧ PolyIs a.mem (L.A 0 oAcc4)
        (add (nttInv (VG.Proof.MlKem.dot4 (VG.Proof.MlKem.ekT (ekB L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁))))
          (VG.Proof.MlKem.cbd (rB L s₀₁) 8))) ∧
      (VEnv L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 oAcc4)
        (add (nttInv (VG.Proof.MlKem.dot4 (VG.Proof.MlKem.ekT (ekB L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂))))
          (VG.Proof.MlKem.cbd (rB L s₀₂) 8))))
    (relct_wp (RelCT.callT addT (regs2 fun a b' hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨evAdd_ok hp₁ (.inl rfl) hab.1.1 (hab.1.1.1.d.e 8 (by decide) (by decide)) hab.1.2.1 hab.1.2.2,
        evAdd_ok hp₂ (.inl rfl) hab.2.1 (hab.2.1.1.d.e 8 (by decide) (by decide)) hab.2.2.1 hab.2.2.2⟩) ?_
  -- `+ μ`
  refine RelCT.seq (R := fun (a b' : State) =>
      ((VEnv L b s₀₁ a ∧ PolyIs a.mem (L.A 0 oAcc4)
        (add (nttInv (VG.Proof.MlKem.dot4 (VG.Proof.MlKem.ekT (ekB L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁))))
          (VG.Proof.MlKem.cbd (rB L s₀₁) 8))) ∧
        a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly 13)) ∧
      ((VEnv L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 oAcc4)
        (add (nttInv (VG.Proof.MlKem.dot4 (VG.Proof.MlKem.ekT (ekB L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂))))
          (VG.Proof.MlKem.cbd (rB L s₀₂) 8))) ∧
        b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ b'.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly 13)))
    (relct_wp (relct_noMem rfl) fun a b' hab =>
      ⟨evArgs_ok hp₁ hab.1.1 hab.1.2 (by decide), evArgs_ok hp₂ hab.2.1 hab.2.2 (by decide)⟩) ?_
  refine RelCT.seq (R := fun (a b' : State) =>
      (VEnv L b s₀₁ a ∧ PolyIs a.mem (L.A 0 oAcc4) (VG.Proof.MlKem.encV1024 (ekB L b s₀₁) (mB L b s₀₁) (rB L s₀₁))) ∧
      (VEnv L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 oAcc4) (VG.Proof.MlKem.encV1024 (ekB L b s₀₂) (mB L b s₀₂) (rB L s₀₂))))
    (relct_wp (RelCT.callT addT (regs2 fun a b' hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨evAdd_ok hp₁ (.inr rfl) hab.1.1 hab.1.1.1.d.mu hab.1.2.1 hab.1.2.2,
        evAdd_ok hp₂ (.inr rfl) hab.2.1 hab.2.1.1.d.mu hab.2.2.1 hab.2.2.2⟩) ?_
  -- its encoding
  refine RelCT.seq (R := fun (a b' : State) =>
      (a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ a.gpr .r1 = BitVec.ofNat 32 5 ∧
        a.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + 1408) ∧ a.gpr .r3 = BitVec.ofNat 32 (32 * 5)) ∧
      (b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ b'.gpr .r1 = BitVec.ofNat 32 5 ∧
        b'.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + 1408) ∧ b'.gpr .r3 = BitVec.ofNat 32 (32 * 5)))
    (relct_wp (relct_noMem rfl) fun a b' hab =>
      ⟨WP.mono (ev8_ok hp₁ hab.1) fun _ h => h.2, WP.mono (ev8_ok hp₂ hab.2) fun _ h => h.2⟩) ?_
  exact RelCT.callT compress4T (regs4 fun a b' hab => ⟨by rw [hab.1.1, hab.2.1], by rw [hab.1.2.1, hab.2.2.1],
    by rw [hab.1.2.2.1, hab.2.2.2.1], by rw [hab.1.2.2.2, hab.2.2.2.2]⟩)


/-! ## The whole of K-PKE.Encrypt -/

theorem encrypt_ct (hρ : ρE L b s₀₁ = ρE L b s₀₂) :
    RelCT isa (fun a c => a = s₀₁ ∧ c = s₀₂) encrypt4 fun _ _ => True := by
  -- `ρ`
  refine RelCT.seq (R := fun (a c : State) =>
      (EA L s₀₁ a ∧ Frame (L.RL [(0, oSeed, 32)]) s₀₁.mem a.mem ∧ bytesAt a.mem (L.A 0 oSeed) 32 = ρE L b s₀₁) ∧
      (EA L s₀₂ c ∧ Frame (L.RL [(0, oSeed, 32)]) s₀₂.mem c.mem ∧ bytesAt c.mem (L.A 0 oSeed) 32 = ρE L b s₀₂))
    (relct_wp (taint_prog [.r4, .r7] (fun a c hac r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hac.1, hac.2, hp₁.r4, hp₂.r4]
        · rw [hac.1, hac.2, hp₁.ctx.r7, hp₂.ctx.r7]) (by taint_decide))
      fun a c hac => ⟨by rw [hac.1]; exact enc1_ok hp₁, by rw [hac.2]; exact enc1_ok hp₂⟩) ?_
  refine RelCT.pointwise fun x y ⟨⟨ex, _, ρx⟩, ⟨ey, _, ρy⟩⟩ => ?_
  -- `t̂`
  refine RelCT.seq (R := fun (a c : State) => DecInv L b.iE b.oE x 0 a ∧ DecInv L b.iE b.oE y 0 c)
    (relct_wp (relct_noMem rfl) fun a c hac => ⟨by rw [hac.1]; exact decT_init, by rw [hac.2]; exact decT_init⟩) ?_
  refine RelCT.seq (R := fun (a c : State) => DecInv L b.iE b.oE x 4 a ∧ DecInv L b.iE b.oE y 4 c)
    (relct_loop_ne (N := 4) (by decide) fun j hj => decT_ct hp₁ hp₂ ex ey hj) ?_
  -- `ŷ`
  refine RelCT.seq (R := fun (a c : State) =>
      (EA L s₀₁ a ∧ bytesAt a.mem (L.A 0 oSeed) 32 = ρE L b s₀₁ ∧
        (∀ k < 4, PolyIs a.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB L b s₀₁) k)) ∧
        ∀ j < 4, PolyIs a.mem (L.A 0 (oPoly (4 + j))) (VG.Proof.MlKem.encY (rB L s₀₁) j)) ∧
      (EA L s₀₂ c ∧ bytesAt c.mem (L.A 0 oSeed) 32 = ρE L b s₀₂ ∧
        (∀ k < 4, PolyIs c.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB L b s₀₂) k)) ∧
        ∀ j < 4, PolyIs c.mem (L.A 0 (oPoly (4 + j))) (VG.Proof.MlKem.encY (rB L s₀₂) j)))
    (relct_wp (RelCT.pointwise fun a c hac =>
      prfLoop_ct (L := L) true (N₀ := 0) (N₁ := 4) (by decide) (by decide)
        (EA.ctx hp₁ (enc2_ok hp₁ ex ρx hac.1).1) (EA.ctx hp₂ (enc2_ok hp₂ ey ρy hac.2).1) rfl rfl)
      fun a c hac =>
        ⟨let ⟨e, ρ', t⟩ := enc2_ok hp₁ ex ρx hac.1; enc3_ok hp₁ e ρ' t,
          let ⟨e, ρ', t⟩ := enc2_ok hp₂ ey ρy hac.2; enc3_ok hp₂ e ρ' t⟩) ?_
  -- `e₁` and `e₂`
  refine RelCT.seq (R := fun (a c : State) =>
      (EA L s₀₁ a ∧ bytesAt a.mem (L.A 0 oSeed) 32 = ρE L b s₀₁ ∧
        (∀ k < 8, PolyIs a.mem (L.A 0 (oPoly k)) (if k < 4 then VG.Proof.MlKem.ekT (ekB L b s₀₁) k
          else VG.Proof.MlKem.encY (rB L s₀₁) (k - 4))) ∧
        ∀ N, 4 ≤ N → N < 9 → PolyIs a.mem (L.A 0 (oPoly (4 + N))) (VG.Proof.MlKem.cbd (rB L s₀₁) N)) ∧
      (EA L s₀₂ c ∧ bytesAt c.mem (L.A 0 oSeed) 32 = ρE L b s₀₂ ∧
        (∀ k < 8, PolyIs c.mem (L.A 0 (oPoly k)) (if k < 4 then VG.Proof.MlKem.ekT (ekB L b s₀₂) k
          else VG.Proof.MlKem.encY (rB L s₀₂) (k - 4))) ∧
        ∀ N, 4 ≤ N → N < 9 → PolyIs c.mem (L.A 0 (oPoly (4 + N))) (VG.Proof.MlKem.cbd (rB L s₀₂) N)))
    (relct_wp (RelCT.pointwise fun a c hac =>
      prfLoop_ct (L := L) false (N₀ := 4) (N₁ := 9) (by decide) (by decide)
        (EA.ctx hp₁ hac.1.1) (EA.ctx hp₂ hac.2.1) rfl rfl)
      fun a c hac => ⟨enc4_ok hp₁ hac.1.1 hac.1.2.1 (v_of hac.1.2.2.1 hac.1.2.2.2),
        enc4_ok hp₂ hac.2.1 hac.2.2.1 (v_of hac.2.2.2.1 hac.2.2.2.2)⟩) ?_
  -- `μ`
  refine RelCT.pointwise fun x₄ y₄ ⟨⟨e₄, ρ₄, v₄, E₄⟩, ⟨e₄', ρ₄', v₄', E₄'⟩⟩ => ?_
  refine RelCT.seq (R := fun (a c : State) =>
      ((EA L s₀₁ a ∧ a.mem = x₄.mem) ∧ a.gpr .r0 = L.ptr b.iM + BitVec.ofNat 32 b.oM ∧
        a.gpr .r1 = BitVec.ofNat 32 (32 * 1) ∧ a.gpr .r2 = BitVec.ofNat 32 1 ∧
        a.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 (oPoly 13)) ∧
      ((EA L s₀₂ c ∧ c.mem = y₄.mem) ∧ c.gpr .r0 = L.ptr b.iM + BitVec.ofNat 32 b.oM ∧
        c.gpr .r1 = BitVec.ofNat 32 (32 * 1) ∧ c.gpr .r2 = BitVec.ofNat 32 1 ∧
        c.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 (oPoly 13)))
    (relct_wp (relct_noMem rfl) fun a c hac =>
      ⟨by rw [hac.1]; exact enc5a_ok hp₁ e₄, by rw [hac.2]; exact enc5a_ok hp₂ e₄'⟩) ?_
  refine RelCT.seq (R := fun (a c : State) =>
      (EA L s₀₁ a ∧ Frame (L.RL [(0, oPoly 13, 1024)]) x₄.mem a.mem ∧
        PolyIs a.mem (L.A 0 (oPoly 13)) (decodeDecompress 1 (mB L b s₀₁))) ∧
      (EA L s₀₂ c ∧ Frame (L.RL [(0, oPoly 13, 1024)]) y₄.mem c.mem ∧
        PolyIs c.mem (L.A 0 (oPoly 13)) (decodeDecompress 1 (mB L b s₀₂))))
    (relct_wp (RelCT.callT decompressT (regs4 fun a c hac => ⟨by rw [hac.1.2.1, hac.2.2.1],
      by rw [hac.1.2.2.1, hac.2.2.2.1], by rw [hac.1.2.2.2.1, hac.2.2.2.2.1], by rw [hac.1.2.2.2.2, hac.2.2.2.2.2]⟩))
      fun a c hac => ⟨enc5b_ok hp₁ e₄ hac.1.1 hac.1.2.1 hac.1.2.2.1 hac.1.2.2.2.1 hac.1.2.2.2.2,
        enc5b_ok hp₂ e₄' hac.2.1 hac.2.2.1 hac.2.2.2.1 hac.2.2.2.2.1 hac.2.2.2.2.2⟩) ?_
  -- the rows of `u`
  refine RelCT.seq (R := fun (a c : State) => ERow L b s₀₁ 0 a ∧ ERow L b s₀₂ 0 c)
    (relct_wp (relct_noMem rfl) fun a c hac =>
      ⟨rows_init hp₁ hac.1.1 (data5 hp₁ ρ₄ v₄ E₄ hac.1.2.1 hac.1.2.2),
        rows_init hp₂ hac.2.1 (data5 hp₂ ρ₄' v₄' E₄' hac.2.2.1 hac.2.2.2)⟩) ?_
  refine RelCT.seq (R := fun (a c : State) => ERow L b s₀₁ 4 a ∧ ERow L b s₀₂ 4 c)
    (relct_loop_ne (N := 4) (by decide) fun i hi => encRow_ct hp₁ hp₂ hρ hi) ?_
  -- `v`
  exact RelCT.pointwise fun x₇ y₇ ⟨h₇, h₇'⟩ => v_ct hp₁ hp₂ h₇.venv h₇'.venv

end

end VG.Proof.MlKem1024.Arm.Enc
