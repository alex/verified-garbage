import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Lit

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid
open VG.Spec.Sha3 (stateAt keccakF rnd)
open VG.Proof.Sha3 (foldl_succ)

structure LInv (s₀ : VG.AArch64.State) (r : Nat) (s : VG.AArch64.State) : Prop where
  ptr : s.gpr .x0 = s₀.gpr .x0
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  state : Lanes s r ((List.range r).foldl rnd (stateAt s₀.mem (s₀.gpr .x0)))

theorem rounds_ok (s₀ s : VG.AArch64.State) (h : LInv s₀ 0 s) :
    WP isa (.block ((List.range 24).flatMap round)) s (LInv s₀ 24) := by
  refine wp_range_flatMap (M := isa) (LInv s₀) (fun r s hr hi => ?_) 24 (Nat.le_refl _) s h
  refine (round_ok r hr s _ hi.state).mono fun s' ⟨hx, hm, hr, hw, hp, ha⟩ => ?_
  refine ⟨hx.trans hi.ptr, hm.trans hi.mem, hr.trans hi.rd, hw.trans hi.wr, hp.trans hi.sp, ?_⟩
  rwa [foldl_succ]

theorem correct {s₀ : VG.AArch64.State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' => s'.sp = s₀.sp ∧ Proof.Sha3.permuteAArch64.post s₀ s' := by
  unfold permute
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (load_ok s₀ hp).mono fun s₁ ⟨hx, hm, hr, hw, hsp, ha⟩ => ?_
  refine (rounds_ok s₀ s₁ ⟨hx, hm, hr, hw, hsp, ha⟩).mono fun s₂ h₂ => ?_
  refine (store_ok s₂ ((List.range 24).foldl rnd (stateAt s₀.mem (s₀.gpr .x0))) h₂.state ?_).mono fun s' ⟨hsp', ha'⟩ => ?_
  · intro i hi
    rw [h₂.wr, h₂.ptr]
    exact hp.lane_in (i := i) (.inl rfl) hi
  · refine ⟨hsp'.trans h₂.sp, ?_⟩
    rwa [h₂.ptr] at ha'

theorem permute_preserved : ∀ r ∈ preserved, ∀ i ∈ instrs permute, dstOf i ≠ some r := by
  have h : ((instrs permute).all fun i => preserved.all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro r hr i hi
  have h' := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using h'

theorem permute_noCalls : permute.noCalls = true := by lit_decide

theorem permute_noFrames : permute.noFrames = true := by lit_decide

theorem permute_correct (s : VG.AArch64.State) (hs : Proof.Sha3.permuteAArch64.pre s) :
    ∃ t s', Exec isa permute s t s' ∧ abiPreserved s s' ∧ Proof.Sha3.permuteAArch64.post s s' := by
  obtain ⟨t, s', he, hsp, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he,
    ⟨fun r hr => Exec.gpr (permute_preserved r hr) he (.inl permute_noCalls), hsp, Exec.preservedV he (by lit_decide)⟩, h⟩

theorem permute_ct : ConstantTime isa Proof.Sha3.permuteAArch64.pre Proof.Sha3.permuteAArch64.pub permute := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

theorem permute_verified :
    Verified AArch64.target permute (Spec.Sha3.permuteContract AArch64.abi) :=
  Verified.of_correct permute_correct permute_ct (by
    sig_implies [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig, Proof.Sha3.permuteAArch64,
      AArch64.abi, AArch64.argRegs] [Proof.Sha3.AArch64.satState] using Proof.Sha3.AArch64.satState)

end VG.Proof.Sha3.AArch64.Sha3.Hybrid
