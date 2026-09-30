import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Blocks
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallPack

/-!
# ML-DSA verification on x86-64: the result in `r15`, and the samplers

Untrusted: everything here is checked by Lean. The result so far is kept in
`r15` as 1 or 0 (`flag`); `and15` and `mov32 r15, eax` update it from a
callee's result. A sampler's call, its result ANDed into `r15` and its
output masked with it (`sampled`) leaves a reduced polynomial either way,
the sampled one if the sampler succeeded (`sampledRej_ok`, `sampledBall_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlKem.X86_64 (at_)
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- 1 if `p`, 0 otherwise. -/
def flag (p : Prop) [Decidable p] : BitVec 64 := if p then 1 else 0

theorem and15_ok (s : State) :
    WP isa (.block and15) s fun s' =>
      (s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧ s'.mem = s.mem) ∧
        Keep [.r15] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold and15
  xrun

theorem mov15_ok (s : State) :
    WP isa (.block [.mov32 .r15 (.reg .rax)]) s fun s' =>
      (s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .rax).setWidth 32) ∧ s'.mem = s.mem) ∧ Keep [.r15] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- `r15 ∧ eax` of a flag and a result 0 or 1. -/
theorem and_flag {p : Prop} [Decidable p] {r : BitVec 32} (hr : r = 1 ∨ r = 0) :
    BitVec.setWidth 64 ((flag p).setWidth 32 &&& r) = flag (p ∧ r = 1) := by
  unfold flag
  rcases hr with rfl | rfl <;> by_cases hp : p <;> simp [hp]

theorem mov_flag {r : BitVec 32} (hr : r = 1 ∨ r = 0) : BitVec.setWidth 64 r = flag (r = 1) := by
  unfold flag
  rcases hr with rfl | rfl <;> simp

/-! ## The mask -/

theorem mask_one {m : Mem} {p : Addr} (x : BitVec 32) (h : x = 1) :
    ∀ i < n, coeffAt m p i &&& (0 - x) = coeffAt m p i := by
  intro i _; subst h
  rw [show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]

theorem mask_zero {m : Mem} {p : Addr} (x : BitVec 32) (h : x = 0) :
    ∀ i < n, coeffAt m p i &&& (0 - x) = 0 := by
  intro i _; subst h; simp

theorem polyAt_eq_of_coeffAt {m m' : Mem} {p : Addr} (h : ∀ i < n, coeffAt m' p i = coeffAt m p i) :
    polyAt m' p = polyAt m p := by
  apply Vector.ext
  intro i hi
  simp only [polyAt, Vector.getElem_ofFn, h i hi]

theorem reduced_of_coeffAt {m m' : Mem} {p : Addr} (h : ∀ i < n, coeffAt m' p i = coeffAt m p i) (hr : Reduced m p) :
    Reduced m' p := fun i hi => by rw [h i hi]; exact hr i hi


/-- A sampler's call, its result ANDed into `r15`, and its output masked. -/
theorem sampled_ok {call : Prog isa} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {a : Ptr}
    (hi : inB (rbs ++ wbs) a 1024 = true) (hw : inB wbs a 1024 = true) {p : Prop} [Decidable p]
    (h15 : s.gpr .r15 = flag p) {ws : List (Ptr × Nat)} (haw : (a, 1024) ∈ ws)
    {F : Bounds → Option Poly}
    (hcall : WP isa call s fun s' => PPostB s s' ws ∧ s'.gpr .r15 = s.gpr .r15 ∧
      (res s' = 1 → Reduced s'.mem (pa s a)) ∧ Outcome F (res s') (polyAt s'.mem (pa s a))) :
    WP isa (sampled call a) s fun s' => PPostB s s' ws ∧ Reduced s'.mem (pa s a) ∧
      ∃ r : BitVec 32, (r = 1 ∨ r = 0) ∧ s'.gpr .r15 = flag (p ∧ r = 1) ∧
        (r = 1 → ∃ b, F b = some (polyAt s'.mem (pa s a))) ∧ (r = 0 → F minBounds = none) := by
  unfold sampled
  refine WP.seq (WP.mono hcall fun s₁ ⟨hP₁, h15₁, hr₁, ho₁⟩ => ?_)
  have L₁ := L.post hP₁
  have hab := ptr_bs L.ok hi
  have e₁ : pa s₁ a = pa s a := hP₁.pa hab
  have hr : res s₁ = 1 ∨ res s₁ = 0 := by rcases ho₁ with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact .inl h; exact .inr h]
  refine WP.seq (WP.mono (and15_ok s₁) fun s₂ ⟨⟨h15₂, hm₂⟩, k₂⟩ => ?_)
  have hP₂ : PPostB s₁ s₂ [] := postB_of_keep k₂ (by decide) (by rw [hm₂]; exact Frame.refl _ _)
  have L₂ := L₁.post hP₂
  have e₂ : pa s₂ a = pa s₁ a := hP₂.pa hab
  have hax : (s₂.gpr .rax).setWidth 32 = res s₁ := by rw [k₂.gpr (by decide)]
  refine WP.mono (mask_ok L₂ hi hw) fun s₃ ⟨hP₃, h15₃, hc₃⟩ => ?_
  have hsub : ∀ w ∈ [(a, 1024)], w ∈ ws := by simp only [List.mem_singleton, forall_eq]; exact haw
  have hcs : ∀ w ∈ [(a, 1024)], w.1.1 ∈ bases := by simp only [List.mem_singleton, forall_eq]; exact hab
  have hP₁₂ : PPostB s s₂ ws := PPostB.trans hP₁ hP₂ (fun _ h => absurd h List.not_mem_nil) (fun w hw => hw)
    (fun _ h => absurd h List.not_mem_nil)
  have hP : PPostB s s₃ ws := PPostB.trans hP₁₂ hP₃ hcs (fun w hw => hw) hsub
  rw [e₂, e₁, hax, hm₂] at hc₃
  refine ⟨hP, ?_, res s₁, hr, by rw [h15₃, h15₂, h15₁, h15, and_flag hr], fun h1 => ?_, fun h0 => ?_⟩
  · rcases hr with h1 | h0
    · exact reduced_of_coeffAt (fun i hi => by rw [hc₃ i hi, mask_one _ h1 i hi]) (hr₁ h1)
    · exact (Proof.MlDsa.Verify.polyIs_zero fun i hi => by rw [hc₃ i hi, mask_zero _ h0 i hi]).1
  · rcases ho₁ with ⟨_, b, hb⟩ | ⟨h0, _⟩
    · refine ⟨b, ?_⟩
      rw [hb, polyAt_eq_of_coeffAt fun i hi => by rw [hc₃ i hi, mask_one _ h1 i hi]]
    · rw [h1] at h0; cases h0
  · rcases ho₁ with ⟨h1, _⟩ | ⟨_, hn⟩
    · rw [h1] at h0; cases h0
    · exact hn

end VG.Proof.MlDsa.X86_64.Verify
