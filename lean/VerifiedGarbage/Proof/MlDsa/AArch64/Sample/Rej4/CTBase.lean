import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Top
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample (Rel2 relStep relTaintStep relMem relTaint)
open VG.Proof.MlDsa.Sample (polyR coeffAddr G_length coeff_contains)
open VG.Proof.MlKem.AArch64 (ptr_zero)
open VG.Impl.MlDsa.AArch64.Sample (zeroPoly rnLoop retZ)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf)

/-- The four seeds are slices of the public 136-byte input. -/
theorem B_pub {σ τ : State} (hq : r4K.pub σ τ) {k : Nat} (hk : k < 4) : B σ k = B τ k := by
  unfold B Spec.MlDsa.seed4
  rw [← VG.Proof.MlKem.bytesAt_slice σ.mem (seedP σ) (show 34*k+34 ≤ 136 by omega),
    ← VG.Proof.MlKem.bytesAt_slice τ.mem (seedP τ) (show 34*k+34 ≤ 136 by omega),hq.2.2.2.2]

theorem X_pub {σ τ : State} (hq : r4K.pub σ τ) {k : Nat} (hk : k < 4) : X σ k = X τ k := by
  unfold X
  rw [B_pub hq hk]

structure ArgReady (σ : State) (k : Nat) (s : State) : Prop where
  ready : Ready σ s
  x25 : s.gpr .x25 = at' σ (1008*k)
  x26 : s.gpr .x26 = polyP σ k

structure ZeroReady (σ : State) (k : Nat) (s : State) : Prop extends ArgReady σ k s where
  zero : ∀ i < 256,Spec.MlDsa.coeffAt s.mem (polyP σ k) i = 0

theorem args_ready {σ s : State} {k : Nat} (hk : k < 4) (hp : Pre σ) (h : Ready σ s) :
    WP isa (.block ([.addImm .x .x25 .x19 (1008*k),.addImm .x .x26 .x21 (1024*k)] : List Instr)) s (ArgReady σ k) :=
  WP.mono (sampleArgs_ok h.env hk) fun _ ⟨ht,e25,e26⟩ =>
    ⟨h.polyStep hp hk (by rw [ht.mem]; exact Frame.refl _ _) ht.rd ht.wr ht.sp
      (fun r hr => ht.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)),e25,e26⟩

theorem zero_ready {σ s : State} {k : Nat} (hk : k < 4) (hp : Pre σ) (h : ArgReady σ k s) :
    WP isa zeroPoly s (ZeroReady σ k) :=
  WP.mono (VG.Proof.MlDsa.AArch64.Sample.zeroPoly_ok (coeffs_in hp h.ready.env.wr hk) h.x26)
    fun _ ⟨ht,hz,hf⟩ => ⟨⟨h.ready.polyStep hp hk hf ht.rd ht.wr ht.sp
      (fun r hr => ht.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)),
      (ht.get .x25).trans h.x25,(ht.get .x26).trans h.x26⟩,hz⟩

theorem zero_lpre {σ s : State} (hp : Pre σ) {k : Nat} (hk : k < 4) (h : ZeroReady σ k s) :
    VG.Proof.MlDsa.AArch64.Sample.RejNtt.LPre (X σ k) (bufP σ k) (polyP σ k) s :=
  ⟨h.ready.out k hk,fun j hj => by
    unfold bufP at'
    rw [Offset.add_add]
    exact in_scr_rd hp h.ready.env.rd h.ready.env.wr (by dsimp only [oBuf]; omega),
    coeffs_in hp h.ready.env.wr hk,buf_poly hp hk hk,by
      rw [h.x25]
      unfold at' bufP
      rw [Offset.add_add]
      exact congrArg (fun d => scr σ+BitVec.ofNat 64 d) (by dsimp only [oBuf]; omega),h.x26⟩

theorem loop_ready {σ s : State} (hp : Pre σ) {k : Nat} (hk : k < 4) (h : ZeroReady σ k s) :
    WP isa rnLoop s (Ready σ) :=
  WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejNtt.loop_ok (G_length _ _) (zero_lpre hp hk h))
    fun _ ht => h.ready.polyStep hp hk ht.frame ht.keep.rd ht.keep.wr ht.keep.sp (fun r hr => ht.keep.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
end VG.Proof.MlDsa.AArch64.Sample.Rej4
