import VerifiedGarbage.Proof.MlKem.X86.NttSetup

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_ntt`

The seven layers of Algorithm 9 (`ntt_eq_layers`), each a `layer_piece`
(`NttLoop.lean`) of the butterfly `bflyBody` (`bfly_spec`), with the zetas
from `zetas[1]` up.
-/

namespace VG.Proof.MlKem.X86.NttFwd

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.NttLoop
open VG.Spec.MlKem

/-- The butterfly of Algorithm 9. -/
def bf : Bfly := ⟨bflyBody, bfly, bfly_spec⟩

/-- The zeta of block `c` of the layer with `len`. -/
def kf (len c : Nat) : Nat := 128 / len + c

theorem lay (len B : Nat) (hB : len * B = 128) (hBp : 0 < B) (hk : 128 / len + B ≤ 128) (P : State → Poly)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp 20))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr []) (.block (blockInit len)) h₂).isSome = true)
    {h₃ : Taint.Hint VG.X86.Taint.T}
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block bflyBody) h₃).isSome = true)
    {h₄ : Taint.Hint VG.X86.Taint.T}
    (t₄ : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd zUp)) h₄).isSome = true) :
    Piece Pre Pub (fun s₀ s => LB s₀ (P s₀) (kf len 0) s)
      (fun s₀ s => LB s₀ (layerN bfly kf (P s₀) len B) (kf len B) s) (layerCode bflyBody zUp len) :=
  layer_piece bf kf P true len B hB hBp (fun c _ => by simp [kf]; omega) (fun c hc => by simp only [kf]; omega)
    (fun h => absurd h (by decide)) t₁ t₂ t₃ t₄

/-- The input polynomial. -/
abbrev F (s₀ : State) : Poly := polyAt s₀.mem (fA s₀)

theorem nil_piece {A : State → State → Prop} : Piece Pre Pub A A (.block []) :=
  Piece.taint [] (fun _ _ _ h => WP.block_nil_iff.mpr h) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)

theorem nttLayer_eq (f : Poly) (len : Nat) : nttLayer f len = layerN bfly kf f len (128 / len) := rfl

theorem fold_eq (f : Poly) : nttLens.foldl nttLayer f =
    layerN bfly kf (layerN bfly kf (layerN bfly kf (layerN bfly kf (layerN bfly kf
      (layerN bfly kf (layerN bfly kf f 128 1) 64 2) 32 4) 16 8) 8 16) 4 32) 2 64 := by
  simp only [nttLens, List.foldl_cons, List.foldl_nil, nttLayer_eq, Nat.reduceDiv]

theorem layers_piece : Piece Pre Pub (fun s₀ s => LB s₀ (F s₀) 1 s)
    (fun s₀ s => LB s₀ (nttLens.foldl nttLayer (F s₀)) 128 s)
    (layers (layerCode bflyBody zUp) [128, 64, 32, 16, 8, 4, 2]) := by
  refine Piece.seq (lay 128 1 (by decide) (by decide) (by decide) F (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 64 2 (by decide) (by decide) (by decide) (fun s₀ => layerN bfly kf (F s₀) 128 1)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 32 4 (by decide) (by decide) (by decide)
    (fun s₀ => layerN bfly kf (layerN bfly kf (F s₀) 128 1) 64 2)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 16 8 (by decide) (by decide) (by decide)
    (fun s₀ => layerN bfly kf (layerN bfly kf (layerN bfly kf (F s₀) 128 1) 64 2) 32 4)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 8 16 (by decide) (by decide) (by decide)
    (fun s₀ => layerN bfly kf (layerN bfly kf (layerN bfly kf (layerN bfly kf (F s₀) 128 1) 64 2) 32 4) 16 8)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 4 32 (by decide) (by decide) (by decide)
    (fun s₀ => layerN bfly kf (layerN bfly kf (layerN bfly kf (layerN bfly kf (layerN bfly kf (F s₀) 128 1)
      64 2) 32 4) 16 8) 8 16)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 2 64 (by decide) (by decide) (by decide)
    (fun s₀ => layerN bfly kf (layerN bfly kf (layerN bfly kf (layerN bfly kf (layerN bfly kf
      (layerN bfly kf (F s₀) 128 1) 64 2) 32 4) 16 8) 8 16) 4 32)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  exact nil_piece.mono (fun _ _ _ h => h) fun s₀ _ _ h => by rw [fold_eq]; exact h

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀)
    (fun s₀ s => LB s₀ (nttLens.foldl nttLayer (F s₀)) 128 s)
    (.seq (.block ldScratch) (.seq (.block (nttSetup 1)) (layers (layerCode bflyBody zUp) [128, 64, 32, 16, 8, 4, 2]))) :=
  Piece.seq ld_piece (Piece.seq (setup_piece 1 (by taint_decide)) layers_piece)

/-- The regions the body writes. -/
abbrev W (s₀ : State) : List Region := [polyRegion (fA s₀), polyRegion (sA s₀), aR s₀]

theorem hW {s₀ : State} (hp : Pre s₀) : ∀ r ∈ W s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by rw [← hp.stk_eq]; exact hp.stk_f, hp.ret_f⟩
  · exact ⟨by rw [← hp.stk_eq]; exact hp.stk_s, hp.ret_s⟩
  · exact ⟨by rw [← hp.stk_eq]; exact hp.stk_a, hp.ret_a⟩

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => LB s₀ (nttLens.foldl nttLayer (F s₀)) 128 s) s₀ s') Impl.MlKem.X86.ntt :=
  Piece.leaf W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp => hW hp) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.mem.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- Memory with the arguments `0` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 4 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.ntt (nttContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of (t := VG.Spec.MlKem.ntt) h rfl) fun s s' _ _ h => by
      sig_pub [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm, ntt_eq_layers]
    exact hinv.mem.poly
  · let st := satState satMem [] [⟨0, 1024⟩, ⟨0x400, 1024⟩, ⟨0x5004, 8⟩]
    refine ⟨st, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg st 0) = BitVec.ofNat 64 0 by decide]
           refine reduced_below (fun a ha => ?_) 0 (by decide)
           simp only [satMem]
           rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)])
        | decide +kernel

end VG.Proof.MlKem.X86.NttFwd
