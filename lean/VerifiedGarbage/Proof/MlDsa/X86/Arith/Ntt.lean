import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttSetup

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_ntt`

Untrusted: everything here is checked by Lean. The eight layers of
Algorithm 41 (`ntt_eq_layers`), each a `layer_piece` (`NttLoop.lean`) of the
butterfly `bflyBody` (`bfly_spec`), with the zetas from `zetas 1` up.
-/

namespace VG.Proof.MlDsa.X86.Arith.NttFwd

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_ ldScratch layerCode layers blockInit blockEnd zUp)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86.Arith
open VG.Proof.MlDsa.X86.Arith.NttLoop
open VG.Spec.MlDsa (q n Poly Zq PolyIs Reduced coeffAt polyAt nttContract inPlaceContract inPlaceSig zetas)
open VG.Proof.MlKem.X86 (E0 P0 frameR retR Piece LeafPost satState)

/-- The butterfly of Algorithm 41. -/
def bf : Bfly := ⟨bflyBody, bfly, bfly_spec⟩

/-- The table entry of block `c` of the layer with `len`. -/
def kf (len c : Nat) : Nat := 128 / len + c

theorem tab : TabOK montZetaTable zetas := fun _ hk => montZeta_eq hk

theorem lay (len B : Nat) (hB : len * B = 128) (hBp : 0 < B) (hk : 128 / len + B ≤ 256) (P : State → Poly)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp 20))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr []) (.block (blockInit len)) h₂).isSome = true)
    {h₃ : Taint.Hint VG.X86.Taint.T}
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block bflyBody) h₃).isSome = true)
    {h₄ : Taint.Hint VG.X86.Taint.T}
    (t₄ : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd zUp)) h₄).isSome = true) :
    Piece Pre Pub (fun s₀ s => LB s₀ montZetaTable (P s₀) (kf len 0) s)
      (fun s₀ s => LB s₀ montZetaTable (layerN bfly (P s₀) len (zf zetas kf len) B) (kf len B) s)
      (layerCode bflyBody zUp len) :=
  layer_piece bf montZetaTable zetas kf P tab true len B hB hBp (fun c _ => by simp [kf]; omega)
    (fun c hc => by simp only [kf]; omega) (fun h => absurd h (by decide)) t₁ t₂ t₃ t₄

/-- The input polynomial. -/
abbrev F (s₀ : State) : Poly := polyAt s₀.mem (fA s₀)

theorem nttLayer_eq (f : Poly) (len : Nat) : nttLayer f len = layerN bfly f len (zf zetas kf len) (128 / len) :=
  rfl

example : True := by
  have := lay 128 1 (by decide) (by decide) (by decide) F (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)
  trivial

theorem fold_eq (f : Poly) : nttLens.foldl nttLayer f =
    nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (nttLayer f 128) 64) 32) 16) 8) 4) 2) 1 := by
  simp only [nttLens, List.foldl_cons, List.foldl_nil]

theorem layers_piece : Piece Pre Pub (fun s₀ s => LB s₀ montZetaTable (F s₀) 1 s)
    (fun s₀ s => LB s₀ montZetaTable (nttLens.foldl nttLayer (F s₀)) 256 s)
    (layers (layerCode bflyBody zUp) [128, 64, 32, 16, 8, 4, 2, 1]) := by
  refine Piece.seq (lay 128 1 (by decide) (by decide) (by decide) F (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 64 2 (by decide) (by decide) (by decide) (fun s₀ => nttLayer (F s₀) 128)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 32 4 (by decide) (by decide) (by decide)
    (fun s₀ => nttLayer (nttLayer (F s₀) 128) 64)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 16 8 (by decide) (by decide) (by decide)
    (fun s₀ => nttLayer (nttLayer (nttLayer (F s₀) 128) 64) 32)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 8 16 (by decide) (by decide) (by decide)
    (fun s₀ => nttLayer (nttLayer (nttLayer (nttLayer (F s₀) 128) 64) 32) 16)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 4 32 (by decide) (by decide) (by decide)
    (fun s₀ => nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (F s₀) 128) 64) 32) 16) 8)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 2 64 (by decide) (by decide) (by decide)
    (fun s₀ => nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (F s₀) 128) 64) 32) 16) 8) 4)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 1 128 (by decide) (by decide) (by decide)
    (fun s₀ => nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (F s₀) 128) 64) 32) 16)
      8) 4) 2)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  exact nil_piece.mono (fun _ _ _ h => h) fun s₀ _ _ h => by rw [fold_eq]; exact h

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀)
    (fun s₀ s => LB s₀ montZetaTable (nttLens.foldl nttLayer (F s₀)) 256 s)
    (.seq (.block ldScratch) (.seq (.block (nttSetup montZetaTable 1))
      (layers (layerCode bflyBody zUp) [128, 64, 32, 16, 8, 4, 2, 1]))) :=
  Piece.seq ld_piece (Piece.seq (setup_piece montZetaTable 1 (by taint_decide)) layers_piece)

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => LB s₀ montZetaTable (nttLens.foldl nttLayer (F s₀)) 256 s) s₀ s')
    Impl.MlDsa.X86.Arith.ntt :=
  Piece.leaf W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp => hW hp) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.mem.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem verified : Verified X86.target Impl.MlDsa.X86.Arith.ntt (nttContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of (t := VG.Spec.MlDsa.ntt) h rfl) fun s s' _ _ h => by
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

end VG.Proof.MlDsa.X86.Arith.NttFwd
