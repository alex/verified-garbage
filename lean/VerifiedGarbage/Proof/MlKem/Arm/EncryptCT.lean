import VerifiedGarbage.Proof.MlKem.Arm.Encrypt
import VerifiedGarbage.Proof.MlKem.Arm.RowCT

/-!
# ML-KEM on 32-bit ARM: K-PKE.Encrypt in constant time

Two runs of `encrypt` on the same buffers (`EncPre` of the same layout and
`EB`) whose encapsulation keys have the same `ρ` leak the same trace
(`encrypt_ct`): the blocks access no memory or only memory through the
pointers, the calls take the same pointers in both runs, and the rows'
`SampleNTT`s take the same seeds (`rowSum_ct`). What each run is at each point
comes from its correctness (`Encrypt.lean`).
-/

namespace VG.Proof.MlKem.Arm.Enc

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

theorem atShifts_noMem (d b c : Reg) : ∀ ts, (atShifts d b c ts).all noMem = true
  | [] => rfl
  | _ :: ts => by
    rw [atShifts, List.all_cons, List.all_map]
    exact List.all_eq_true.mpr fun _ _ => rfl

/-! ## Decoding `t̂` -/

theorem decT1_ok {K : KemLay} {L : Lay} {i o : Nat} {x s : State} (hc : Ctx L x)
    (g4 : x.gpr .r4 = L.ptr i + BitVec.ofNat 32 o) {j : Nat} (hj : j < 4) (h : DecInv K L i o x j s) :
    WP isa (.block (at384 .r0 .r4 .r9 ++ slotAt .r1 .r9 (oPoly 0))) s fun s₁ =>
      s₁.gpr .r0 = L.ptr i + BitVec.ofNat 32 (o + 384 * j) ∧ s₁.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j) := by
  have hc' := h.kx.ctx (by decide) hc
  have g4' : s.gpr .r4 = L.ptr i + BitVec.ofNat 32 o := by
    rw [h.kx.cs .r4 (by decide) (by decide) (by decide), g4]
  refine WP.mono (decTArgs_ok hc'.r7 g4' h.r9) fun s₁ ⟨_, a0, a1⟩ => ⟨?_, ?_⟩
  · rw [a0, at384_eq _ (by omega), ptr_add_add32]
  · rw [a1, slot_eq _ (by offs), show 2048 + 1024 * 0 + 1024 * j = 2048 + 1024 * j by omega]

theorem decT_ctG {K : KemLay} (hK : K.WF) {L : Lay} {i o : Nat} {x y : State} (hcx : Ctx L x) (hcy : Ctx L y)
    (g4x : x.gpr .r4 = L.ptr i + BitVec.ofNat 32 o) (g4y : y.gpr .r4 = L.ptr i + BitVec.ofNat 32 o)
    (hs : sepAll L.sizes (i, o, 384 * K.k) [(0, 2048, 1024 * K.k)] = true) (hrx : L.buf i ∈ x.rd ++ x.wr)
    (hry : L.buf i ∈ y.rd ++ y.wr) {j : Nat} (hj : j < K.k) :
    RelCT isa (fun a₁ a₂ => DecInv K L i o x j a₁ ∧ DecInv K L i o y j a₂) K.decTBody fun a₁ a₂ =>
      (DecInv K L i o x (j + 1) a₁ ∧ a₁.z = decide (j + 1 = K.k)) ∧
      (DecInv K L i o y (j + 1) a₂ ∧ a₂.z = decide (j + 1 = K.k)) := by
  have hj4 : j < 4 := by have := hK.k4; omega
  refine relct_wp (RelCT.pointwise fun u w ⟨hu, hw⟩ => ?_) fun a₁ a₂ hab =>
    ⟨decT_step hK hcx g4x hs hrx hj hab.1, decT_step hK hcy g4y hs hry hj hab.2⟩
  refine RelCT.seq (R := fun (a₁ a₂ : State) =>
      (a₁.gpr .r0 = L.ptr i + BitVec.ofNat 32 (o + 384 * j) ∧ a₁.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j)) ∧
      (a₂.gpr .r0 = L.ptr i + BitVec.ofNat 32 (o + 384 * j) ∧ a₂.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j)))
    (relct_wp (relct_noMem rfl) fun a₁ a₂ hab => ⟨by rw [hab.1]; exact decT1_ok hcx g4x hj4 hu,
      by rw [hab.2]; exact decT1_ok hcy g4y hj4 hw⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT decode12T (regs2 fun a₁ a₂ hab => ⟨by rw [hab.1.1, hab.2.1], by rw [hab.1.2, hab.2.2]⟩))
    (relct_noMem rfl)

section
variable {K : KemLay} {L : Lay} {b : EB} {s₀₁ s₀₂ : State} (hp₁ : EncPre K L b s₀₁) (hp₂ : EncPre K L b s₀₂)
include hp₁ hp₂

theorem decT_ct {x y : State} (ex : EA K L s₀₁ x) (ey : EA K L s₀₂ y) {j : Nat} (hj : j < K.k) :
    RelCT isa (fun a₁ a₂ => DecInv K L b.iE b.oE x j a₁ ∧ DecInv K L b.iE b.oE y j a₂) K.decTBody fun a b' =>
      (DecInv K L b.iE b.oE x (j + 1) a ∧ a.z = decide (j + 1 = K.k)) ∧
      (DecInv K L b.iE b.oE y (j + 1) b' ∧ b'.z = decide (j + 1 = K.k)) := by
  obtain ⟨hcx, g4x, hsx, hrx⟩ := dec_pre hp₁ ex
  obtain ⟨hcy, g4y, -, hry⟩ := dec_pre hp₂ ey
  exact decT_ctG hp₁.wf hcx hcy g4x g4y hsx hrx hry hj

/-! ## The rows of `u` -/

theorem encRow_ct (hρ : ρE K L b s₀₁ = ρE K L b s₀₂) {i : Nat} (hi : i < K.k) :
    RelCT isa (fun a b' => ERow K L b s₀₁ i a ∧ ERow K L b s₀₂ i b') K.encRowBody fun a b' =>
      (ERow K L b s₀₁ (i + 1) a ∧ a.z = decide (i + 1 = K.k)) ∧
      (ERow K L b s₀₂ (i + 1) b' ∧ b'.z = decide (i + 1 = K.k)) := by
  refine relct_wp (RelCT.pointwise fun u w ⟨hu, hw⟩ => ?_) fun a b' hab =>
    ⟨encRow_step hp₁ hi hab.1, encRow_step hp₂ hi hab.2⟩
  have pw : RowPre K L (ρE K L b s₀₁) (VG.Proof.MlKem.encY (rB L s₀₂)) i (okE K L b s₀₂ i) w := by
    have := hw.rowPre hp₂ hi; rwa [← hρ] at this
  -- `RowSum`
  refine RelCT.seq (R := fun (a b' : State) =>
      RowInv K L true (ρE K L b s₀₁) (VG.Proof.MlKem.encY (rB L s₀₁)) i (okE K L b s₀₁ i) u K.k a ∧
      RowInv K L true (ρE K L b s₀₂) (VG.Proof.MlKem.encY (rB L s₀₂)) i (okE K L b s₀₂ i) w K.k b')
    (relct_wp (rowSum_ct hp₁.calls (hu.rowPre hp₁ hi) pw) fun a b' hab =>
      ⟨by rw [hab.1]; exact rowSum_ok (hu.rowPre hp₁ hi), by rw [hab.2]; exact rowSum_ok (hw.rowPre hp₂ hi)⟩) ?_
  -- `NTT⁻¹`
  refine RelCT.seq (R := fun (a b' : State) =>
      (RB K L b s₀₁ i u (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀₁ j i) (VG.Proof.MlKem.encY (rB L s₀₁)) K.k) a ∧
        a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oNtt) ∧
      (RB K L b s₀₂ i w (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀₂ j i) (VG.Proof.MlKem.encY (rB L s₀₂)) K.k) b' ∧
        b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ b'.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oNtt))
    (relct_wp (relct_noMem rfl) fun a b' hab => ⟨er2_ok hp₁ hu hab.1, er2_ok hp₂ hw hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b' : State) =>
      RB K L b s₀₁ i u (nttInv (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀₁ j i) (VG.Proof.MlKem.encY (rB L s₀₁)) K.k)) a ∧
      RB K L b s₀₂ i w (nttInv (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀₂ j i) (VG.Proof.MlKem.encY (rB L s₀₂)) K.k)) b')
    (relct_wp (RelCT.callT nttInvT (regs2 fun a b' hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨er3_ok hp₁ hu hab.1.1 hab.1.2.1 hab.1.2.2, er3_ok hp₂ hw hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- `+ e₁[i]`
  refine RelCT.seq (R := fun (a b' : State) =>
      (RB K L b s₀₁ i u (nttInv (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀₁ j i) (VG.Proof.MlKem.encY (rB L s₀₁)) K.k)) a ∧
        a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧
        a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + (K.k + i)))) ∧
      (RB K L b s₀₂ i w (nttInv (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀₂ j i) (VG.Proof.MlKem.encY (rB L s₀₂)) K.k)) b' ∧
        b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧
        b'.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + (K.k + i)))))
    (relct_wp (relct_noMem rfl) fun a b' hab => ⟨er4_ok hp₁ hi hu hab.1, er4_ok hp₂ hi hw hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b' : State) =>
      RB K L b s₀₁ i u (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀₁) (rB L s₀₁) i) a ∧
      RB K L b s₀₂ i w (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀₂) (rB L s₀₂) i) b')
    (relct_wp (RelCT.callT addT (regs2 fun a b' hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨er5_ok hp₁ hi hu hab.1.1 hab.1.2.1 hab.1.2.2, er5_ok hp₂ hi hw hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- its encoding
  refine RelCT.seq (R := fun (a b' : State) =>
      (RB K L b s₀₁ i u (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀₁) (rB L s₀₁) i) a ∧
        a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ a.gpr .r1 = BitVec.ofNat 32 K.du ∧
        a.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + K.uLen * i) ∧ a.gpr .r3 = BitVec.ofNat 32 (32 * K.du)) ∧
      (RB K L b s₀₂ i w (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀₂) (rB L s₀₂) i) b' ∧
        b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ b'.gpr .r1 = BitVec.ofNat 32 K.du ∧
        b'.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + K.uLen * i) ∧ b'.gpr .r3 = BitVec.ofNat 32 (32 * K.du)))
    (relct_wp (relct_noMem (by rw [List.all_append, List.all_append, KemLay.atU, atShifts_noMem]; rfl)) fun a b' hab => ⟨er6_ok hp₁ hu hab.1, er6_ok hp₂ hw hab.2⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT hp₁.calls.cuT (regs4 fun a b' hab => ⟨by rw [hab.1.2.1, hab.2.2.1],
      by rw [hab.1.2.2.1, hab.2.2.2.1], by rw [hab.1.2.2.2.1, hab.2.2.2.2.1], by rw [hab.1.2.2.2.2, hab.2.2.2.2.2]⟩))
    (relct_noMem rfl)

/-! ## `v` -/

theorem v_ct {x y : State} (hx : VEnv K L b s₀₁ x) (hy : VEnv K L b s₀₂ y) :
    RelCT isa (fun a b' => a = x ∧ b' = y)
      (.seq K.dot <|
      .seq (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 K.oNtt]) <|
      .seq callNttInv <|
      .seq (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 (oPoly (3 * K.k))]) <|
      .seq callAdd <|
      .seq (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 (oPoly (3 * K.k + 1))]) <|
      .seq callAdd <|
      .seq (.block [ptrTo .r0 .r7 K.oAcc, .mov .r1 (.imm (BitVec.ofNat 32 K.dv)), ptrTo .r2 .r8 (K.uLen * K.k),
        .mov .r3 (.imm (BitVec.ofNat 32 K.vLen))]) K.callCU)
      fun _ _ => True := by
  have hK := hp₁.wf
  have hcx := hx.kx.ctx (by decide) hp₁.ctx
  have hcy := hy.kx.ctx (by decide) hp₂.ctx
  have va : ∀ {s₀ s : State}, VEnv K L b s₀ s → ∀ j < K.k,
      PolyIs s.mem (L.A 0 (oPoly j)) (VG.Proof.MlKem.ekT (ekB K L b s₀) j) := fun h j hj => by
    have := h.d.v j (by omega); simp only [hj, ↓reduceIte] at this; exact this
  have vv : ∀ {s₀ s : State}, VEnv K L b s₀ s → ∀ j < K.k,
      PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.encY (rB L s₀) j) := fun h j hj => by
    have := h.d.v (K.k + j) (by omega)
    have e : ¬ (K.k + j < K.k) := by omega
    simp only [e, ↓reduceIte, show K.k + j - K.k = j by omega] at this
    exact this
  -- `dot`
  refine RelCT.seq (R := fun (a b' : State) =>
      (VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁)) K.k)) ∧
      (VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂)) K.k)))
    (relct_wp (dot_ct hK hcx hcy (va hx) (vv hx) (va hy) (vv hy) hp₁.calls) fun a b' hab =>
      ⟨by rw [hab.1]; exact ev1_ok hp₁ hx, by rw [hab.2]; exact ev1_ok hp₂ hy⟩) ?_
  -- `NTT⁻¹`
  refine RelCT.seq (R := fun (a b' : State) =>
      ((VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁)) K.k)) ∧
        a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oNtt) ∧
      ((VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂)) K.k)) ∧
        b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ b'.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oNtt))
    (relct_wp (relct_noMem rfl) fun a b' hab =>
      ⟨evArgs_ok hp₁ hab.1.1 hab.1.2 (by kenc), evArgs_ok hp₂ hab.2.1 hab.2.2 (by kenc)⟩) ?_
  refine RelCT.seq (R := fun (a b' : State) =>
      (VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc) (nttInv (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁)) K.k))) ∧
      (VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc) (nttInv (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂)) K.k))))
    (relct_wp (RelCT.callT nttInvT (regs2 fun a b' hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨ev3_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, ev3_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- `+ e₂`
  refine RelCT.seq (R := fun (a b' : State) =>
      ((VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc) (nttInv (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁)) K.k))) ∧
        a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k))) ∧
      ((VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc) (nttInv (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂)) K.k))) ∧
        b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ b'.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k))))
    (relct_wp (relct_noMem rfl) fun a b' hab =>
      ⟨evArgs_ok hp₁ hab.1.1 hab.1.2 (by kenc), evArgs_ok hp₂ hab.2.1 hab.2.2 (by kenc)⟩) ?_
  have e₂ : ∀ {s₀ s : State}, VEnv K L b s₀ s →
      PolyIs s.mem (L.A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.cbd (rB L s₀) (2 * K.k)) := fun h => by
    have := h.d.e (2 * K.k) (by omega) (by omega)
    rwa [show K.k + 2 * K.k = 3 * K.k by omega] at this
  refine RelCT.seq (R := fun (a b' : State) =>
      (VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc)
        (add (nttInv (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁)) K.k)) (VG.Proof.MlKem.cbd (rB L s₀₁) (2 * K.k)))) ∧
      (VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc)
        (add (nttInv (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂)) K.k)) (VG.Proof.MlKem.cbd (rB L s₀₂) (2 * K.k)))))
    (relct_wp (RelCT.callT addT (regs2 fun a b' hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨evAdd_ok hp₁ (.inl rfl) hab.1.1 (e₂ hab.1.1.1) hab.1.2.1 hab.1.2.2,
        evAdd_ok hp₂ (.inl rfl) hab.2.1 (e₂ hab.2.1.1) hab.2.2.1 hab.2.2.2⟩) ?_
  -- `+ μ`
  refine RelCT.seq (R := fun (a b' : State) =>
      ((VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc)
        (add (nttInv (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁)) K.k)) (VG.Proof.MlKem.cbd (rB L s₀₁) (2 * K.k)))) ∧
        a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k + 1))) ∧
      ((VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc)
        (add (nttInv (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂)) K.k)) (VG.Proof.MlKem.cbd (rB L s₀₂) (2 * K.k)))) ∧
        b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ b'.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k + 1))))
    (relct_wp (relct_noMem rfl) fun a b' hab =>
      ⟨evArgs_ok hp₁ hab.1.1 hab.1.2 (by kenc), evArgs_ok hp₂ hab.2.1 hab.2.2 (by kenc)⟩) ?_
  refine RelCT.seq (R := fun (a b' : State) =>
      (VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc)
        (VG.Proof.MlKem.KPke.encV K.p (ekB K L b s₀₁) (mB L b s₀₁) (rB L s₀₁))) ∧
      (VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc)
        (VG.Proof.MlKem.KPke.encV K.p (ekB K L b s₀₂) (mB L b s₀₂) (rB L s₀₂))))
    (relct_wp (RelCT.callT addT (regs2 fun a b' hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨evAdd_ok hp₁ (.inr rfl) hab.1.1 hab.1.1.1.d.mu hab.1.2.1 hab.1.2.2,
        evAdd_ok hp₂ (.inr rfl) hab.2.1 hab.2.1.1.d.mu hab.2.2.1 hab.2.2.2⟩) ?_
  -- its encoding
  refine RelCT.seq (R := fun (a b' : State) =>
      (a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ a.gpr .r1 = BitVec.ofNat 32 K.dv ∧
        a.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + K.uLen * K.k) ∧ a.gpr .r3 = BitVec.ofNat 32 (32 * K.dv)) ∧
      (b'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ b'.gpr .r1 = BitVec.ofNat 32 K.dv ∧
        b'.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + K.uLen * K.k) ∧ b'.gpr .r3 = BitVec.ofNat 32 (32 * K.dv)))
    (relct_wp (relct_noMem rfl) fun a b' hab =>
      ⟨WP.mono (ev8_ok hp₁ hab.1) fun _ h => h.2, WP.mono (ev8_ok hp₂ hab.2) fun _ h => h.2⟩) ?_
  exact RelCT.callT hp₁.calls.cuT (regs4 fun a b' hab => ⟨by rw [hab.1.1, hab.2.1], by rw [hab.1.2.1, hab.2.2.1],
    by rw [hab.1.2.2.1, hab.2.2.2.1], by rw [hab.1.2.2.2, hab.2.2.2.2]⟩)

/-! ## The whole of K-PKE.Encrypt -/

theorem encrypt_ct (hρ : ρE K L b s₀₁ = ρE K L b s₀₂) :
    RelCT isa (fun a c => a = s₀₁ ∧ c = s₀₂) K.encrypt fun _ _ => True := by
  have hK := hp₁.wf
  -- `ρ`
  refine RelCT.seq (R := fun (a c : State) =>
      (EA K L s₀₁ a ∧ Frame (L.RL [(0, oSeed, 32)]) s₀₁.mem a.mem ∧ bytesAt a.mem (L.A 0 oSeed) 32 = ρE K L b s₀₁) ∧
      (EA K L s₀₂ c ∧ Frame (L.RL [(0, oSeed, 32)]) s₀₂.mem c.mem ∧ bytesAt c.mem (L.A 0 oSeed) 32 = ρE K L b s₀₂))
    (relct_wp (hp₁.calls.encSeedT.relct (fun a c hac r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hac.1, hac.2, hp₁.r4, hp₂.r4]
        · rw [hac.1, hac.2, hp₁.ctx.r7, hp₂.ctx.r7]))
      fun a c hac => ⟨by rw [hac.1]; exact enc1_ok hp₁, by rw [hac.2]; exact enc1_ok hp₂⟩) ?_
  refine RelCT.pointwise fun x y ⟨⟨ex, _, ρx⟩, ⟨ey, _, ρy⟩⟩ => ?_
  -- `t̂`
  refine RelCT.seq (R := fun (a c : State) => DecInv K L b.iE b.oE x 0 a ∧ DecInv K L b.iE b.oE y 0 c)
    (relct_wp (relct_noMem rfl) fun a c hac => ⟨by rw [hac.1]; exact decT_init, by rw [hac.2]; exact decT_init⟩) ?_
  refine RelCT.seq (R := fun (a c : State) => DecInv K L b.iE b.oE x K.k a ∧ DecInv K L b.iE b.oE y K.k c)
    (relct_loop_ne (N := K.k) hK.k1 fun j hj => decT_ct hp₁ hp₂ ex ey hj) ?_
  -- `ŷ`
  refine RelCT.seq (R := fun (a c : State) =>
      (EA K L s₀₁ a ∧ bytesAt a.mem (L.A 0 oSeed) 32 = ρE K L b s₀₁ ∧
        (∀ k < K.k, PolyIs a.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀₁) k)) ∧
        ∀ j < K.k, PolyIs a.mem (L.A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.encY (rB L s₀₁) j)) ∧
      (EA K L s₀₂ c ∧ bytesAt c.mem (L.A 0 oSeed) 32 = ρE K L b s₀₂ ∧
        (∀ k < K.k, PolyIs c.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀₂) k)) ∧
        ∀ j < K.k, PolyIs c.mem (L.A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.encY (rB L s₀₂) j)))
    (relct_wp (RelCT.pointwise fun a c hac =>
      prfLoop_ct hK (L := L) true (N₀ := 0) (N₁ := K.k) hK.k1 (by omega)
        (EA.ctx hp₁ (enc2_ok hp₁ ex ρx hac.1).1) (EA.ctx hp₂ (enc2_ok hp₂ ey ρy hac.2).1) rfl rfl)
      fun a c hac =>
        ⟨let ⟨e, ρ', t⟩ := enc2_ok hp₁ ex ρx hac.1; enc3_ok hp₁ e ρ' t,
          let ⟨e, ρ', t⟩ := enc2_ok hp₂ ey ρy hac.2; enc3_ok hp₂ e ρ' t⟩) ?_
  -- `e₁` and `e₂`
  refine RelCT.seq (R := fun (a c : State) =>
      (EA K L s₀₁ a ∧ bytesAt a.mem (L.A 0 oSeed) 32 = ρE K L b s₀₁ ∧
        (∀ k < 2 * K.k, PolyIs a.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀₁) k
          else VG.Proof.MlKem.encY (rB L s₀₁) (k - K.k))) ∧
        ∀ N, K.k ≤ N → N < 2 * K.k + 1 →
          PolyIs a.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.cbd (rB L s₀₁) N)) ∧
      (EA K L s₀₂ c ∧ bytesAt c.mem (L.A 0 oSeed) 32 = ρE K L b s₀₂ ∧
        (∀ k < 2 * K.k, PolyIs c.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀₂) k
          else VG.Proof.MlKem.encY (rB L s₀₂) (k - K.k))) ∧
        ∀ N, K.k ≤ N → N < 2 * K.k + 1 →
          PolyIs c.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.cbd (rB L s₀₂) N)))
    (relct_wp (RelCT.pointwise fun a c hac =>
      prfLoop_ct hK (L := L) false (N₀ := K.k) (N₁ := 2 * K.k + 1) (by omega) (by omega)
        (EA.ctx hp₁ hac.1.1) (EA.ctx hp₂ hac.2.1) rfl rfl)
      fun a c hac => ⟨enc4_ok hp₁ hac.1.1 hac.1.2.1 (v_of hac.1.2.2.1 hac.1.2.2.2),
        enc4_ok hp₂ hac.2.1 hac.2.2.1 (v_of hac.2.2.2.1 hac.2.2.2.2)⟩) ?_
  -- `μ`
  refine RelCT.pointwise fun x₄ y₄ ⟨⟨e₄, ρ₄, v₄, E₄⟩, ⟨e₄', ρ₄', v₄', E₄'⟩⟩ => ?_
  refine RelCT.seq (R := fun (a c : State) =>
      ((EA K L s₀₁ a ∧ a.mem = x₄.mem) ∧ a.gpr .r0 = L.ptr b.iM + BitVec.ofNat 32 b.oM ∧
        a.gpr .r1 = BitVec.ofNat 32 (32 * 1) ∧ a.gpr .r2 = BitVec.ofNat 32 1 ∧
        a.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k + 1))) ∧
      ((EA K L s₀₂ c ∧ c.mem = y₄.mem) ∧ c.gpr .r0 = L.ptr b.iM + BitVec.ofNat 32 b.oM ∧
        c.gpr .r1 = BitVec.ofNat 32 (32 * 1) ∧ c.gpr .r2 = BitVec.ofNat 32 1 ∧
        c.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k + 1))))
    (relct_wp (relct_noMem rfl) fun a c hac =>
      ⟨by rw [hac.1]; exact enc5a_ok hp₁ e₄, by rw [hac.2]; exact enc5a_ok hp₂ e₄'⟩) ?_
  refine RelCT.seq (R := fun (a c : State) =>
      (EA K L s₀₁ a ∧ Frame (L.RL [(0, oPoly (3 * K.k + 1), 1024)]) x₄.mem a.mem ∧
        PolyIs a.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (mB L b s₀₁))) ∧
      (EA K L s₀₂ c ∧ Frame (L.RL [(0, oPoly (3 * K.k + 1), 1024)]) y₄.mem c.mem ∧
        PolyIs c.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (mB L b s₀₂))))
    (relct_wp (RelCT.callT decompressT (regs4 fun a c hac => ⟨by rw [hac.1.2.1, hac.2.2.1],
      by rw [hac.1.2.2.1, hac.2.2.2.1], by rw [hac.1.2.2.2.1, hac.2.2.2.2.1], by rw [hac.1.2.2.2.2, hac.2.2.2.2.2]⟩))
      fun a c hac => ⟨enc5b_ok hp₁ e₄ hac.1.1 hac.1.2.1 hac.1.2.2.1 hac.1.2.2.2.1 hac.1.2.2.2.2,
        enc5b_ok hp₂ e₄' hac.2.1 hac.2.2.1 hac.2.2.2.1 hac.2.2.2.2.1 hac.2.2.2.2.2⟩) ?_
  -- the rows of `u`
  refine RelCT.seq (R := fun (a c : State) => ERow K L b s₀₁ 0 a ∧ ERow K L b s₀₂ 0 c)
    (relct_wp (relct_noMem rfl) fun a c hac =>
      ⟨rows_init hp₁ hac.1.1 (data5 hp₁ ρ₄ v₄ E₄ hac.1.2.1 hac.1.2.2),
        rows_init hp₂ hac.2.1 (data5 hp₂ ρ₄' v₄' E₄' hac.2.2.1 hac.2.2.2)⟩) ?_
  refine RelCT.seq (R := fun (a c : State) => ERow K L b s₀₁ K.k a ∧ ERow K L b s₀₂ K.k c)
    (relct_loop_ne (N := K.k) hK.k1 fun i hi => encRow_ct hp₁ hp₂ hρ hi) ?_
  -- `v`
  exact RelCT.pointwise fun x₇ y₇ ⟨h₇, h₇'⟩ => v_ct hp₁ hp₂ h₇.venv h₇'.venv

end

end VG.Proof.MlKem.Arm.Enc
