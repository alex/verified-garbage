import VerifiedGarbage.Proof.MlKem1024.Arm.RowSum
import VerifiedGarbage.Proof.MlKem.Arm.RowCT

/-!
# ML-KEM-1024 on 32-bit ARM: the `PRF`s and the rows in constant time

Untrusted: everything here is checked by Lean. `Proof/MlKem/Arm/PrfCT.lean`
and `Proof/MlKem/Arm/RowCT.lean` for ML-KEM-1024's layout: two runs of
`prfLoop4` with the same `scratch` leak the same trace (`prfLoop_ct`), as
do two runs of `rowSum4` with the same `ρ` and row (`rowSum_ct`) and of
`dotP4` (`dot_ct`).
-/

namespace VG.Proof.MlKem1024.Arm

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

theorem prfBody_ct {L : Lay} (withNtt : Bool) {N₁ N : Nat} (hN : N < N₁) (hN₁ : N₁ ≤ 9) :
    RelCT isa (fun a b => PS L N a ∧ PS L N b) (prfBody4 withNtt N₁) fun _ _ => True := by
  -- the counter
  refine RelCT.seq (R := fun a b => PS L N a ∧ PS L N b)
    (relct_wp (taint_block [.r7] (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1.1.r7, hab.2.1.r7]) (by taint_decide))
      fun a b hab => ⟨WP.mono (strb9_ok hab.1.1 (by omega) hab.1.2) fun s' ⟨k', _⟩ =>
          ⟨k'.ctx (by decide) hab.1.1, by rw [k'.cs .r9 (by decide) (by decide) (by decide), hab.1.2]⟩,
        WP.mono (strb9_ok hab.2.1 (by omega) hab.2.2) fun s' ⟨k', _⟩ =>
          ⟨k'.ctx (by decide) hab.2.1, by rw [k'.cs .r9 (by decide) (by decide) (by decide), hab.2.2]⟩⟩) ?_
  -- `PRF`
  have hh : ∀ s, PS L N s → WP isa (hash 136 0x1f [⟨.r7, oSigma, 33⟩] [⟨.r7, oPrf, 128⟩]) s (PS L N) :=
    fun s h => WP.mono (hash_ok MlKem.rate136 (by decide) (by decide) (by decide) h.1 (List.cons_ne_nil _ _)
      (prf_hashOk h.1).ins (prf_hashOk h.1).outs (List.pairwise_singleton _ _)) fun s' ⟨k', _⟩ =>
      ⟨h.1.kept k', by rw [k'.cs .r9 (by decide) (by decide), h.2]⟩
  refine RelCT.seq (R := fun a b => PS L N a ∧ PS L N b)
    (relct_wp (hash_ct MlKem.rate136 (by decide) (by decide) (List.cons_ne_nil _ _) fun a b hab =>
      ⟨prf_hashOk hab.1.1, prf_hashOk hab.2.1, hab.1.1.sp_eq hab.2.1⟩) fun a b hab => ⟨hh a hab.1, hh b hab.2⟩) ?_
  -- `SamplePolyCBD₂`
  let F : State → Prop := fun s => PS L N s ∧ s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oPrf ∧
    s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (4 + N))
  have eo : oPoly (4 + N) = oPoly 4 + 1024 * N := by simp only [oPoly]; omega
  have ha : ∀ s, PS L N s → WP isa (.block (ptrTo .r0 .r7 oPrf :: slotAt .r1 .r9 (oPoly 4))) s F :=
    fun s h => WP.mono (cbdArgs_ok h.1.r7 h.2) fun s' ⟨o', g0, g1⟩ =>
      ⟨⟨h.1.only o', by rw [o'.cs .r9 (by decide) (by decide), h.2]⟩, g0,
        by rw [g1, slot_eq _ (by offs4), ← eo]⟩
  refine RelCT.seq (R := fun a b => F a ∧ F b) (relct_wp (relct_noMem rfl) fun a b hab => ⟨ha a hab.1, ha b hab.2⟩) ?_
  have hcb : ∀ s, F s → WP isa callCbd2 s (PS L N) := fun s h =>
    cbd2L h.1.1.ok h.2.1 h.2.2 (h.1.1.sep00 (by offs4) (by offs4) (by offs4)) (mem_rd_wr h.1.1.buf0) h.1.1.buf0
      fun s' k' _ => ⟨h.1.1.kept k', by rw [k'.cs .r9 (by decide) (by decide), h.1.2]⟩
  refine RelCT.seq (R := fun a b => PS L N a ∧ PS L N b)
    (relct_wp (RelCT.callT cbd2T (regs2 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b hab => ⟨hcb a hab.1, hcb b hab.2⟩) ?_
  -- the NTT, and the counter
  cases withNtt
  · exact RelCT.seq (R := fun _ _ => True) (relct_noMem rfl) (relct_noMem rfl)
  · refine RelCT.seq (R := fun _ _ => True) ?_ (relct_noMem rfl)
    let G : State → Prop := fun s => s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 (oPoly (4 + N)) ∧
      s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oNtt4
    have hn : ∀ s, PS L N s → WP isa (.block (slotAt .r0 .r9 (oPoly 4) ++ [ptrTo .r1 .r7 oNtt4])) s G :=
      fun s h => WP.mono (nttArgs_ok h.1.r7 h.2) fun s' ⟨_, g0, g1⟩ => ⟨by rw [g0, slot_eq _ (by offs4), ← eo], g1⟩
    exact RelCT.seq (R := fun a b => G a ∧ G b) (relct_wp (relct_noMem rfl) fun a b hab => ⟨hn a hab.1, hn b hab.2⟩)
      (RelCT.callT nttT (regs2 fun a b hab => ⟨by rw [hab.1.1, hab.2.1], by rw [hab.1.2, hab.2.2]⟩))

theorem prfLoop_ct {L : Lay} (withNtt : Bool) {N₀ N₁ : Nat} (h01 : N₀ < N₁) (hN₁ : N₁ ≤ 9)
    {s₀₁ s₀₂ : State} (hc₁ : Ctx L s₀₁) (hc₂ : Ctx L s₀₂) {σ₁ σ₂ : List Byte}
    (hσ₁ : bytesAt s₀₁.mem (L.A 0 oSigma) 32 = σ₁) (hσ₂ : bytesAt s₀₂.mem (L.A 0 oSigma) 32 = σ₂) :
    RelCT isa (fun a b => a = s₀₁ ∧ b = s₀₂) (prfLoop4 withNtt N₀ N₁) fun _ _ => True := by
  refine RelCT.seq (R := fun a b => PrfInv L withNtt σ₁ N₀ N₁ s₀₁ 0 a ∧ PrfInv L withNtt σ₂ N₀ N₁ s₀₂ 0 b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨?_, ?_⟩) (RelCT.mono (relct_loop_ne (I₁ := PrfInv L withNtt σ₁ N₀ N₁ s₀₁) (I₂ := PrfInv L withNtt σ₂ N₀ N₁ s₀₂)
      (N := N₁ - N₀) (by omega) fun t ht => ?_)
      (fun _ _ h => h) fun _ _ _ => trivial)
  · rw [hab.1]
    exact WP.mono (mov9_ok (enc_le9 N₀ (by omega))) fun s₁ ⟨k₁, g₁, m₁⟩ =>
      ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ₁,
        fun N h1 h2 => absurd h2 (by omega)⟩
  · rw [hab.2]
    exact WP.mono (mov9_ok (enc_le9 N₀ (by omega))) fun s₁ ⟨k₁, g₁, m₁⟩ =>
      ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ₂,
        fun N h1 h2 => absurd h2 (by omega)⟩
  -- one iteration: the body's timing from where it runs, and each run by correctness
  exact relct_wp (RelCT.mono (prfBody_ct (N := N₀ + t) withNtt (by omega) hN₁) (fun a b hab =>
      ⟨⟨hab.1.kx.ctx (by decide) hc₁, hab.1.r9⟩, ⟨hab.2.kx.ctx (by decide) hc₂, hab.2.r9⟩⟩) fun _ _ h => h)
    fun a b hab => ⟨prfStep_ok hc₁ withNtt hN₁ ht hab.1, prfStep_ok hc₂ withNtt hN₁ ht hab.2⟩

section
variable {L : Lay} {ρ : List Byte} {v₁ v₂ : Nat → Poly} {i : Nat} {fl₁ fl₂ : Bool} {s₀₁ s₀₂ : State}

theorem rowBody_ct {transpose : Bool} (hp₁ : RowPre L ρ v₁ i fl₁ s₀₁) (hp₂ : RowPre L ρ v₂ i fl₂ s₀₂) {j : Nat}
    (hj : j < 4) :
    RelCT isa (fun a b => RowInv L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RowInv L transpose ρ v₂ i fl₂ s₀₂ j b)
      (rowBody4 transpose) fun _ _ => True := by
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
    (relct_wp (sample_ct (L := L) (i := 0) (o := oSeed) (j := 0) (o' := oAhat4) (k := 0) (o'' := oSample4)
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
      sepB L.sizes (0, oSeed, 34) (0, oAhat4, 1024) = true ∧ sepB L.sizes (0, oSeed, 34) (0, oSample4, 2048) = true ∧
      sepB L.sizes (0, oAhat4, 1024) (0, oSample4, 2048) = true ∧ sepB L.sizes (0, oSeed, 34) (1, 0, 8) = true ∧
      sepB L.sizes (0, oAhat4, 1024) (1, 0, 8) = true ∧ sepB L.sizes (0, oSample4, 2048) (1, 0, 8) = true :=
    ⟨hp.ctx.sep00 (by decide) (by decide) (by decide), hp.ctx.sep00 (by decide) (by decide) (by decide),
      hp.ctx.sep00 (by decide) (by decide) (by decide), hp.ctx.sep01 (by decide) (by decide),
      hp.ctx.sep01 (by decide) (by decide), hp.ctx.sep01 (by decide) (by decide)⟩

theorem rowSum_ct {transpose : Bool} (hp₁ : RowPre L ρ v₁ i fl₁ s₀₁) (hp₂ : RowPre L ρ v₂ i fl₂ s₀₂) :
    RelCT isa (fun a b => a = s₀₁ ∧ b = s₀₂) (rowSum4 transpose) fun _ _ => True := by
  let Z : State → State → Prop := fun s₀ s₁ => Kept (L.RL [(0, oAcc4, 1024)]) s₀ s₁ ∧ PolyIs s₁.mem (L.A 0 oAcc4) zero
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
  exact RelCT.mono (relct_loop_ne (N := 4) (by decide) fun j hj =>
    relct_wp (rowBody_ct hp₁ hp₂ hj) fun a b hab => ⟨rowBody_ok hp₁ hj hab.1, rowBody_ok hp₂ hj hab.2⟩)
    (fun _ _ h => h) fun _ _ _ => trivial

end

/-! ## `dot` -/

section
variable {L : Lay} {a₁ v₁ a₂ v₂ : Nat → Poly} {x y : State} (hc₁ : Ctx L x) (hc₂ : Ctx L y)
    (ha₁ : ∀ j < 4, PolyIs x.mem (L.A 0 (oPoly j)) (a₁ j)) (hv₁ : ∀ j < 4, PolyIs x.mem (L.A 0 (oPoly (4 + j))) (v₁ j))
    (ha₂ : ∀ j < 4, PolyIs y.mem (L.A 0 (oPoly j)) (a₂ j)) (hv₂ : ∀ j < 4, PolyIs y.mem (L.A 0 (oPoly (4 + j))) (v₂ j))
include hc₁ hc₂ ha₁ hv₁ ha₂ hv₂

theorem dotBody_ct {j : Nat} (hj : j < 4) :
    RelCT isa (fun a b => DotInv L a₁ v₁ x j a ∧ DotInv L a₂ v₂ y j b) dotBody4 fun a b =>
      (DotInv L a₁ v₁ x (j + 1) a ∧ a.z = decide (j + 1 = 4)) ∧
      (DotInv L a₂ v₂ y (j + 1) b ∧ b.z = decide (j + 1 = 4)) := by
  refine relct_wp (RelCT.pointwise fun u w ⟨hu, hw⟩ => ?_) fun a b hab =>
    ⟨dotBody_ok hc₁ ha₁ hv₁ hj hab.1, dotBody_ok hc₂ ha₂ hv₂ hj hab.2⟩
  refine RelCT.seq (R := fun (a b : State) =>
      (Only u a ∧ a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oTmp4 ∧ a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j) ∧
        a.gpr .r2 = L.ptr 0 + BitVec.ofNat 32 (oPoly (4 + j)) ∧ a.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 oNtt4) ∧
      (Only w b ∧ b.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oTmp4 ∧ b.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly j) ∧
        b.gpr .r2 = L.ptr 0 + BitVec.ofNat 32 (oPoly (4 + j)) ∧ b.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 oNtt4))
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨by rw [hab.1]; exact dot1_ok hc₁ hj hu,
      by rw [hab.2]; exact dot1_ok hc₂ hj hw⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DB L a₁ v₁ x j a ∧ DB L a₂ v₂ y j b)
    (relct_wp (RelCT.callT mulT (regs4 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2.1, hab.2.2.2.1],
      by rw [hab.1.2.2.2.1, hab.2.2.2.2.1], by rw [hab.1.2.2.2.2, hab.2.2.2.2.2]⟩))
      fun a b ⟨⟨o₁, m0, m1, m2, m3⟩, ⟨o₂, n0, n1, n2, n3⟩⟩ =>
        ⟨dot2_ok hc₁ ha₁ hv₁ hj hu o₁ m0 m1 m2 m3, dot2_ok hc₂ ha₂ hv₂ hj hw o₂ n0 n1 n2 n3⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (DB L a₁ v₁ x j a ∧ a.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ a.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oTmp4) ∧
      (DB L a₂ v₂ y j b ∧ b.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ b.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oTmp4))
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨dot3_ok hc₁ hab.1, dot3_ok hc₂ hab.2⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT addT (regs2 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
    (relct_noMem rfl)

theorem dot_ct : RelCT isa (fun a b => a = x ∧ b = y) dotP4 fun _ _ => True := by
  let Z : State → State → Prop := fun s₀ s₁ => Kept (L.RL [(0, oAcc4, 1024)]) s₀ s₁ ∧ PolyIs s₁.mem (L.A 0 oAcc4) zero
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
  exact RelCT.mono (relct_loop_ne (N := 4) (by decide) fun j hj => dotBody_ct hc₁ hc₂ ha₁ hv₁ ha₂ hv₂ hj)
    (fun _ _ h => h) fun _ _ _ => trivial

end

end VG.Proof.MlKem1024.Arm
