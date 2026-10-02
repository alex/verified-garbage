import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Steps
import VerifiedGarbage.Proof.MlKem.Arm.CallsCT

/-!
# ML-DSA on 32-bit ARM: two runs in the buffers of a `Site`

Two runs in the same layout, with the same stack pointer (`Two`): a part that
leaks the same, and changes only what `Kept` allows, leaves two runs in it
(`RelCT.two`); and two runs of a byte stored, a copy or the sponge leak the
same (`setB_tr`, `copy_tr`, `hashS_tr`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (Piece hash copy)
open VG.Spec.Sha3 (rates)

/-- Two runs in the layout `L`, with the same stack pointer. -/
def Two (L : Lay) (Wb : List Nat) (STK : Nat) (x y : State) : Prop :=
  Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp

section
variable {L : Lay} {Wb : List Nat} {STK : Nat}

theorem Two.r7 {x y : State} (h : Two L Wb STK x y) : ∀ r ∈ [Reg.r7], x.gpr r = y.gpr r := fun r hr => by
  rw [List.mem_singleton] at hr; subst hr; rw [h.1.r7, h.2.1.r7]

theorem Two.regs {x y : State} (h : Two L Wb STK x y) : ∀ r ∈ [Reg.r4, .r5, .r6, .r7], x.gpr r = y.gpr r :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.1.r4, h.2.1.r4]
    · rw [h.1.r5, h.2.1.r5]
    · rw [h.1.r6, h.2.1.r6]
    · rw [h.1.r7, h.2.1.r7]

/-- A part that leaks the same, and keeps the layout, leaves two runs in it. -/
theorem RelCT.two {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → Two L Wb STK x y)
    (htr : RelCT isa P c fun _ _ => True)
    (hok : ∀ x, Site L Wb STK x → WP isa c x fun x' => ∃ rs, Kept rs x x') : RelCT isa P c (Two L Wb STK) :=
  (RelCT.wpDep htr (F := fun x x' => ∃ rs, Kept rs x x')
    fun x y h => ⟨hok x (hP x y h).1, hok y (hP x y h).2.1⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, σ₁, σ₂, hp, ⟨_, hx⟩, ⟨_, hy⟩⟩ => ⟨(hP σ₁ σ₂ hp).1.kept hx, (hP σ₁ σ₂ hp).2.1.kept hy, by
      rw [hx.sp, hy.sp]; exact (hP σ₁ σ₂ hp).2.2⟩

/-- Taint analysis, from the pointer to `scratch`. -/
theorem taint7 {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → Two L Wb STK x y)
    {hc : VG.Taint.Hint VG.Arm.taint.T} (h : (VG.Arm.taint.check (Taint.ofRegs [.r7]) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  taint_prog [.r7] (fun x y hxy => (hP x y hxy).r7) h

/-- Taint analysis, from the pointers of the layout. -/
theorem taint4 {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → Two L Wb STK x y)
    {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r4, .r5, .r6, .r7]) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  taint_prog [.r4, .r5, .r6, .r7] (fun x y hxy => (hP x y hxy).regs) h

/-- Two runs of the sponge. -/
theorem hashS_tr {K : Nat → Bool}
    (hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb)
    {rate sfx : Nat} (hrate : rate ∈ rates) (hre : encodable (BitVec.ofNat 32 rate) = true)
    (hse : encodable (BitVec.ofNat 32 sfx) = true) {ins : List Piece} {q : Piece} (hne : ins ≠ [])
    (hin : ∀ s, Site L Wb STK s → ∀ p ∈ ins, PieceOk (hashLay L s K) ix s false p)
    (hq : ∀ s, Site L Wb STK s → PieceOk (hashLay L s K) ix s true q) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Two L Wb STK x y) : RelCT isa P (hash rate sfx ins [q]) fun _ _ => True :=
  RelCT.mono (RelCT.exists_ fun (s₀ : State) =>
    hash_ct (P := fun a b => s₀ = a ∧ P a b) (L := hashLay L s₀ K) (idx := ix) hrate hre hse hne
      fun a b ⟨e, hab⟩ => by
        subst e
        have ⟨ha, hb, hsp⟩ := hP s₀ b hab
        have hl : hashLay L s₀ K = hashLay L b K := by simp only [hashLay, hsp]
        refine ⟨⟨ha.ctx hK, hin s₀ ha, fun p hp => ?_⟩, ⟨hl ▸ hb.ctx hK, hl ▸ hin b hb, fun p hp => ?_⟩, hsp⟩ <;>
          rw [List.mem_singleton] at hp <;> subst hp
        · exact hq s₀ ha
        · exact hl ▸ hq b hb)
    (fun a b h => ⟨a, rfl, h⟩) fun _ _ h => h

end

end VG.Proof.MlDsa.Arm.KeyGen
