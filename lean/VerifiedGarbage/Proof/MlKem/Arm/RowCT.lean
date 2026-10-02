import VerifiedGarbage.Proof.MlKem.Arm.PrfCT

/-!
# ML-KEM-768 on 32-bit ARM: a row of `Â ∘ v̂` in constant time

Two runs of `rowSum` with the same `scratch`, the same `ρ` and the same row
leak the same trace (`rowSum_ct`): the seeds of the `SampleNTT`s are the same
(`ρ ‖ j ‖ i`), so their calls leak the same trace and return the same value,
on which the selection of the entry branches; every other address is `scratch`
plus an offset of the indices. What each run is at each step comes from its
correctness (`rowA_ok`, …).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

/-- Constant time from any two states related by `P`, proved for each pair. -/
theorem RelCT.pointwise {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa (fun a b => a = s₁ ∧ b = s₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ _ _ _ _ hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

section
variable {L : Lay} {ρ : List Byte} {v₁ v₂ : Nat → Poly} {i : Nat} {fl₁ fl₂ : Bool} {s₀₁ s₀₂ : State}

theorem rowBody_ct {transpose : Bool} (hp₁ : RowPre L ρ v₁ i fl₁ s₀₁) (hp₂ : RowPre L ρ v₂ i fl₂ s₀₂) {j : Nat}
    (hj : j < 3) :
    RelCT isa (fun a b => RowInv L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RowInv L transpose ρ v₂ i fl₂ s₀₂ j b)
      (rowBody transpose) fun _ _ => True := by
  -- the seed
  refine RelCT.seq (R := fun a b => RA L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RA L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp ?_ fun a b hab => ⟨rowA_ok hp₁ hj hab.1, rowA_ok hp₂ hj hab.2⟩) ?_
  · have h7 : ∀ a b, RowInv L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RowInv L transpose ρ v₂ i fl₂ s₀₂ j b →
        ∀ r ∈ [Reg.r7], a.gpr r = b.gpr r := fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr
      rw [(hab.1.kx.ctx (by decide) hp₁.ctx).r7, (hab.2.kx.ctx (by decide) hp₂.ctx).r7]
    cases transpose
    · exact taint_block [.r7] h7 (by taint_decide)
    · exact taint_block [.r7] h7 (by taint_decide)
  -- `SampleNTT`
  refine RelCT.seq (R := fun a b => RB L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RB L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (sample_ct (L := L) (i := 0) (o := oSeed) (j := 0) (o' := oAhat) (k := 0) (o'' := oSample)
      (fun a b hab => ?_) (by exact (hab_sep hp₁).1) (by exact (hab_sep hp₁).2.1) (by exact (hab_sep hp₁).2.2.1)
      (by exact (hab_sep hp₁).2.2.2.1) (by exact (hab_sep hp₁).2.2.2.2.1) (by exact (hab_sep hp₁).2.2.2.2.2))
      fun a b hab => ⟨rowB_ok hp₁ hab.1, rowB_ok hp₂ hab.2⟩) ?_
  · have ca := hab.1.rs.ctx hp₁
    have cb := hab.2.rs.ctx hp₂
    exact ⟨ca, cb, hab.1.r0, hab.1.r1, hab.1.r2, hab.2.r0, hab.2.r1, hab.2.r2, by rw [hab.1.seed, hab.2.seed],
      mem_rd_wr ca.buf0, ca.buf0, ca.buf0, mem_rd_wr cb.buf0, cb.buf0, cb.buf0⟩
  -- the flag
  refine RelCT.seq (R := fun a b => RC L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RC L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨rowC_ok hab.1, rowC_ok hab.2⟩) ?_
  -- the entry
  refine RelCT.seq (R := fun a b => RD L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RD L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (RelCT.ite (fun a b hab => by show some a.z = some b.z; rw [hab.1.z, hab.2.z])
      (relct_noMem rfl) (relct_noMem rfl)) fun a b hab => ⟨rowD_ok hp₁ hj hab.1, rowD_ok hp₂ hj hab.2⟩) ?_
  -- the product
  refine RelCT.seq (R := fun a b => RE L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RE L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨rowE_ok hp₁ hj hab.1, rowE_ok hp₂ hj hab.2⟩) ?_
  refine RelCT.seq (R := fun a b => RF L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RF L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (RelCT.callT mulT (regs4 fun a b hab => ⟨by rw [hab.1.r0, hab.2.r0], by rw [hab.1.rd.r1, hab.2.rd.r1],
      by rw [hab.1.r2, hab.2.r2], by rw [hab.1.r3, hab.2.r3]⟩))
      fun a b hab => ⟨rowF_ok hp₁ hj hab.1, rowF_ok hp₂ hj hab.2⟩) ?_
  -- the sum, and the counter
  refine RelCT.seq (R := fun a b => RG L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RG L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨rowG_ok hp₁ hab.1, rowG_ok hp₂ hab.2⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT addT (regs2 fun a b hab => ⟨by rw [hab.1.r0, hab.2.r0], by rw [hab.1.r1, hab.2.r1]⟩))
    (relct_noMem rfl)
where
  hab_sep (hp : RowPre L ρ v₁ i fl₁ s₀₁) :
      sepB L.sizes (0, oSeed, 34) (0, oAhat, 1024) = true ∧ sepB L.sizes (0, oSeed, 34) (0, oSample, 2048) = true ∧
      sepB L.sizes (0, oAhat, 1024) (0, oSample, 2048) = true ∧ sepB L.sizes (0, oSeed, 34) (1, 0, 8) = true ∧
      sepB L.sizes (0, oAhat, 1024) (1, 0, 8) = true ∧ sepB L.sizes (0, oSample, 2048) (1, 0, 8) = true :=
    ⟨hp.ctx.sep00 (by decide) (by decide) (by decide), hp.ctx.sep00 (by decide) (by decide) (by decide),
      hp.ctx.sep00 (by decide) (by decide) (by decide), hp.ctx.sep01 (by decide) (by decide),
      hp.ctx.sep01 (by decide) (by decide), hp.ctx.sep01 (by decide) (by decide)⟩

theorem rowSum_ct {transpose : Bool} (hp₁ : RowPre L ρ v₁ i fl₁ s₀₁) (hp₂ : RowPre L ρ v₂ i fl₂ s₀₂) :
    RelCT isa (fun a b => a = s₀₁ ∧ b = s₀₂) (rowSum transpose) fun _ _ => True := by
  let Z : State → State → Prop := fun s₀ s₁ => Kept (L.RL [(0, oAcc, 1024)]) s₀ s₁ ∧ PolyIs s₁.mem (L.A 0 oAcc) zero
  refine RelCT.seq (R := fun a b => Z s₀₁ a ∧ Z s₀₂ b) (relct_wp (taint_prog [.r7] (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1, hab.2, hp₁.ctx.r7, hp₂.ctx.r7]) (by taint_decide))
    fun a b hab => ⟨by rw [hab.1]; exact zeroPoly_ok hp₁.ctx (by decide) (by decide),
      by rw [hab.2]; exact zeroPoly_ok hp₂.ctx (by decide) (by decide)⟩) ?_
  have init : ∀ {v : Nat → Poly} {fl : Bool} {s₀ : State}, RowPre L ρ v i fl s₀ → ∀ s₁, Z s₀ s₁ →
      WP isa (.block [.mov .r10 (.imm 0)]) s₁ (RowInv L transpose ρ v i fl s₀ 0) :=
    fun {v fl s₀} hp s₁ ⟨k₁, z₁⟩ => WP.mono (movc_ok .r10 (N := 0) (by decide)) fun s₂ ⟨k₂, g₂, m₂⟩ =>
      ⟨((k₁.x _).subL hp.ctx (by decide)).trans ((k₂.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil)),
        g₂, by rw [k₂.cs .r11 (by decide) (by decide) (by decide), k₁.cs .r11 (by decide) (by decide), hp.r11]
               simp [okRow],
        by rw [m₂]; exact z₁⟩
  refine RelCT.seq (R := fun a b => RowInv L transpose ρ v₁ i fl₁ s₀₁ 0 a ∧ RowInv L transpose ρ v₂ i fl₂ s₀₂ 0 b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨init hp₁ a hab.1, init hp₂ b hab.2⟩) ?_
  exact RelCT.mono (relct_loop_ne (N := 3) (by decide) fun j hj =>
    relct_wp (rowBody_ct hp₁ hp₂ hj) fun a b hab => ⟨rowBody_ok hp₁ hj hab.1, rowBody_ok hp₂ hj hab.2⟩)
    (fun _ _ h => h) fun _ _ _ => trivial

end

/-! ## `dot` -/

section
variable {L : Lay} {a₁ v₁ a₂ v₂ : Nat → Poly} {x y : State} (hc₁ : Ctx L x) (hc₂ : Ctx L y)
    (ha₁ : ∀ j < 3, PolyIs x.mem (L.A 0 (oPoly j)) (a₁ j)) (hv₁ : ∀ j < 3, PolyIs x.mem (L.A 0 (oPoly (3 + j))) (v₁ j))
    (ha₂ : ∀ j < 3, PolyIs y.mem (L.A 0 (oPoly j)) (a₂ j)) (hv₂ : ∀ j < 3, PolyIs y.mem (L.A 0 (oPoly (3 + j))) (v₂ j))
include hc₁ hc₂ ha₁ hv₁ ha₂ hv₂

theorem dotBody_ct {j : Nat} (hj : j < 3) :
    RelCT isa (fun a b => DotInv L a₁ v₁ x j a ∧ DotInv L a₂ v₂ y j b) dotBody fun a b =>
      (DotInv L a₁ v₁ x (j + 1) a ∧ a.z = decide (j + 1 = 3)) ∧
      (DotInv L a₂ v₂ y (j + 1) b ∧ b.z = decide (j + 1 = 3)) := by
  refine relct_wp (RelCT.pointwise fun u w ⟨hu, hw⟩ => ?_) fun a b hab =>
    ⟨dotBody_ok hc₁ ha₁ hv₁ hj hab.1, dotBody_ok hc₂ ha₂ hv₂ hj hab.2⟩
  refine RelCT.seq (R := fun (a b : State) =>
      (Only u a ∧ a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oTmp ∧ a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j) ∧
        a.gpr .r2 = L.ptr 0 + BitVec.ofNat 32 (oPoly (3 + j)) ∧ a.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 oNtt) ∧
      (Only w b ∧ b.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oTmp ∧ b.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j) ∧
        b.gpr .r2 = L.ptr 0 + BitVec.ofNat 32 (oPoly (3 + j)) ∧ b.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 oNtt))
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨by rw [hab.1]; exact dot1_ok hc₁ hj hu,
      by rw [hab.2]; exact dot1_ok hc₂ hj hw⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DB L a₁ v₁ x j a ∧ DB L a₂ v₂ y j b)
    (relct_wp (RelCT.callT mulT (regs4 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2.1, hab.2.2.2.1],
      by rw [hab.1.2.2.2.1, hab.2.2.2.2.1], by rw [hab.1.2.2.2.2, hab.2.2.2.2.2]⟩))
      fun a b ⟨⟨o₁, m0, m1, m2, m3⟩, ⟨o₂, n0, n1, n2, n3⟩⟩ =>
        ⟨dot2_ok hc₁ ha₁ hv₁ hj hu o₁ m0 m1 m2 m3, dot2_ok hc₂ ha₂ hv₂ hj hw o₂ n0 n1 n2 n3⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (DB L a₁ v₁ x j a ∧ a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc ∧ a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oTmp) ∧
      (DB L a₂ v₂ y j b ∧ b.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc ∧ b.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oTmp))
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨dot3_ok hc₁ hab.1, dot3_ok hc₂ hab.2⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT addT (regs2 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
    (relct_noMem rfl)

theorem dot_ct : RelCT isa (fun a b => a = x ∧ b = y) dot fun _ _ => True := by
  let Z : State → State → Prop := fun s₀ s₁ => Kept (L.RL [(0, oAcc, 1024)]) s₀ s₁ ∧ PolyIs s₁.mem (L.A 0 oAcc) zero
  refine RelCT.seq (R := fun a b => Z x a ∧ Z y b) (relct_wp (taint_prog [.r7] (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1, hab.2, hc₁.r7, hc₂.r7]) (by taint_decide))
    fun a b hab => ⟨by rw [hab.1]; exact zeroPoly_ok hc₁ (by decide) (by decide),
      by rw [hab.2]; exact zeroPoly_ok hc₂ (by decide) (by decide)⟩) ?_
  have init : ∀ {a v : Nat → Poly} {s₀ : State}, Ctx L s₀ → ∀ s₁, Z s₀ s₁ →
      WP isa (.block [.mov .r10 (.imm 0)]) s₁ (DotInv L a v s₀ 0) :=
    fun {a v s₀} hc s₁ ⟨k₁, z₁⟩ => WP.mono (movc_ok .r10 (N := 0) (by decide)) fun s₂ ⟨k₂, g₂, m₂⟩ =>
      ⟨((k₁.x _).subL hc (by decide)).trans (k₂.mono (fun _ h => absurd h List.not_mem_nil)), g₂,
        by rw [m₂]; exact z₁⟩
  refine RelCT.seq (R := fun a b => DotInv L a₁ v₁ x 0 a ∧ DotInv L a₂ v₂ y 0 b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨init hc₁ a hab.1, init hc₂ b hab.2⟩) ?_
  exact RelCT.mono (relct_loop_ne (N := 3) (by decide) fun j hj => dotBody_ct hc₁ hc₂ ha₁ hv₁ ha₂ hv₂ hj)
    (fun _ _ h => h) fun _ _ _ => trivial

end

end VG.Proof.MlKem.Arm
