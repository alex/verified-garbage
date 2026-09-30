import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.StepsCT
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Lay
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono

/-!
# ML-DSA key generation on 32-bit ARM: masking a sampled polynomial

Untrusted: everything here is checked by Lean. After each sampler, `r11`
is ANDed with its result (0 or 1, in `r0`), and each coefficient of the
polynomial it wrote with `-r0`: the polynomial is kept if the sampler
succeeded, and zeroed if it failed (`mask_ok`), without a branch
(`mask_tr`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (coeffAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Proof.MlKem.Arm.Add (ptr_succ)

/-! ## Coefficients in memory -/

theorem coeffAt_writeW32 (m : Mem) (q : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256) (v : BitVec 32) :
    coeffAt (m.writeW (q + BitVec.ofNat 64 (4 * j)) v) q i = if j = i then v else coeffAt m q i := by
  unfold coeffAt
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep q (by omega) (by omega) (by omega)) (by decide)

/-- The coefficients after masking with `-r`, for `r` 0 or 1. -/
theorem and_mask {r : BitVec 32} (hr : r = 0 ∨ r = 1) (x : BitVec 32) : x &&& (0 - r) = if r = 1 then x else 0 := by
  rcases hr with rfl | rfl
  · simp
  · rw [ifp rfl, show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide]
    exact BitVec.and_allOnes

/-! ## One coefficient -/

section
variable {s : State} {x c M : BitVec 32}

theorem maskBody_ok (h1 : s.gpr .r1 = x) (h2 : s.gpr .r2 = c) (h12 : s.gpr .r12 = M)
    (ir : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ow : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block maskBody) s fun s' =>
      s'.gpr .r1 = x + 4 ∧ s'.gpr .r2 = c - 1 ∧ s'.gpr .r12 = M ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0))
        (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 &&& M) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [maskBody, h1, h2, h12, ir, ow, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-- After masking `k` coefficients of the polynomial at `P` with `M`. -/
structure MaskInv (P M : BitVec 32) (s₀ : State) (k : Nat) (s : State) : Prop where
  r1 : s.gpr .r1 = P + BitVec.ofNat 32 (4 * k)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (256 - k))
  r12 : s.gpr .r12 = M
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [regA P 1024] s₀.mem s.mem
  co : ∀ t < 256, coeffAt s.mem (State.addr P) t =
    if t < k then coeffAt s₀.mem (State.addr P) t &&& M else coeffAt s₀.mem (State.addr P) t

theorem mask_step {P M : BitVec 32} {s₀ : State} (fP : P.toNat + 1024 ≤ 2 ^ 32) (cw : Covers [regA P 1024] s₀.wr)
    {k : Nat} (hk : k < 256) {s : State} (h : MaskInv P M s₀ k s) :
    WP isa (.block maskBody) s fun s' => MaskInv P M s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = 256) := by
  have eP : State.addr (P + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0) = State.addr P + BitVec.ofNat 64 (4 * k) := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have cP : (regA P 1024).Contains (State.addr P + BitVec.ofNat 64 (4 * k)) 4 := contains_off (by omega) (by omega)
  have ow : InRegions s.wr (State.addr (P + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 4 := by
    rw [eP, h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cP⟩
  have ir : InRegions (s.rd ++ s.wr) (State.addr (P + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 4 :=
    let ⟨r, hr, hc⟩ := ow; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (maskBody_ok h.r1 h.r2 h.r12 ir ow)
    fun s' ⟨r1, r2, r12, z, m, rd, wr, sp, cs⟩ => ⟨⟨?_, ?_, r12, fun r hr => (cs r hr).trans (h.cs r hr),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [r1]; exact ptr_succ _ 4 k
  · rw [r2]; exact count_sub (k := 1) hk
  · rw [m, eP]; exact h.frame.writeW (List.mem_singleton_self _) _ cP
  · rw [m, eP, coeffAt_writeW32 _ _ ht hk]
    by_cases e : k = t
    · subst e
      have := h.co k hk
      rw [ifn (Nat.lt_irrefl _)] at this
      rw [ifp rfl, ifp (Nat.lt_succ_self _), ← this]; rfl
    · rw [ifn e, h.co t ht]
      by_cases htk : t < k
      · rw [ifp htk, ifp (by omega)]
      · rw [ifn htk, ifn (by omega)]
  · rw [z]; exact count_z (k := 1) hk (by decide) (by decide)

theorem mask_loop {P M : BitVec 32} {s₀ : State} (fP : P.toNat + 1024 ≤ 2 ^ 32) (cw : Covers [regA P 1024] s₀.wr)
    (h1 : s₀.gpr .r1 = P) (h2 : s₀.gpr .r2 = BitVec.ofNat 32 256) (h12 : s₀.gpr .r12 = M) :
    WP isa (.loop (.block maskBody) .ne) s₀ fun s =>
      Kept [regA P 1024] s₀ s ∧ ∀ t < 256, coeffAt s.mem (State.addr P) t = coeffAt s₀.mem (State.addr P) t &&& M :=
  wp_loop_ne (MaskInv P M s₀) (N := 256) (by decide) (fun k hk s h => mask_step fP cw hk h)
    (fun s h => ⟨⟨fun r hr _ => h.cs r hr, h.sp, h.rd, h.wr, h.frame⟩, fun t ht => by
      rw [h.co t ht, ifp ht]⟩)
    ⟨by rw [h1]; simp, by rw [h2], h12, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun t _ => by rw [ifn (Nat.not_lt_zero t)]⟩

/-! ## The polynomial -/

abbrev maskPre (a : Ptr) : List Instr :=
  [.mov .r12 (.imm 0), .dp .sub .r12 .r12 (.reg .r0)] ++ Arg.instrs .r1 (.ptr a) ++ [.mov .r2 (.imm 256)]

theorem maskPre_ok {a : Ptr} (ha : argOk (.ptr a) = true) (s : State) :
    WP isa (.block (maskPre a)) s fun s' =>
      Only s s' ∧ s'.gpr .r12 = 0 - s.gpr .r0 ∧ s'.gpr .r1 = s.gpr a.1 + BitVec.ofNat 32 a.2 ∧
        s'.gpr .r2 = BitVec.ofNat 32 256 := by
  obtain ⟨-, n1, -, -, n12⟩ := pres_ne (base_pres (r := a.1) (by simpa [argOk] using ha)).1
    (base_pres (r := a.1) (by simpa [argOk] using ha)).2
  have n1' : ¬ a.1 = .r1 := n1
  have n12' : ¬ a.1 = .r12 := n12
  run_block [maskPre, Arg.instrs, ldc, n1', n12', ldc_eq]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, ?_⟩
  · obtain ⟨-, m1, m2, -, m12⟩ := pres_ne hr hl
    simp only [m1, m2, m12, ite_false]
  · simp

theorem mask_ok {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a : Ptr}
    (pa : PtrIn L a 1024) (hw : ix a.1 ∈ Wb) (hr : s.gpr .r0 = 0 ∨ s.gpr .r0 = 1) :
    WP isa (mask a) s fun s' => Kept (L.RL [tri a 1024]) s s' ∧
      ∀ t < 256, coeffAt s'.mem (lpa L a) t = if s.gpr .r0 = 1 then coeffAt s.mem (lpa L a) t else 0 := by
  have gb := hs.val pa.1
  simp only [argVal] at gb
  have ea := hs.addrE pa (by decide)
  have fa := hs.fitE pa (by decide)
  have cw := hs.cwE pa hw
  rw [← hs.regE pa (by decide)] at cw
  unfold mask
  refine WP.seq (WP.mono (maskPre_ok pa.1 s) fun s₁ ⟨o₁, g12, g1, g2⟩ => ?_)
  rw [gb] at g1
  refine WP.mono (mask_loop fa (by rw [o₁.wr]; exact cw) g1 g2 g12) fun s' ⟨k, co⟩ => ⟨?_, fun t ht => ?_⟩
  · refine (o₁.kept _).trans (k.mono fun r hr => ?_)
    rw [List.mem_singleton] at hr; subst hr
    rw [hs.regE pa (by decide)]
    exact List.mem_singleton_self _
  · rw [← ea, co t ht, o₁.mem, and_mask hr]

/-! ## Constant time -/

/-- The check is the same for every offset: its hint is computed once. -/
theorem mask_taint : ∀ j < 128, (VG.Arm.taint.check (Taint.ofRegs [.r7]) (mask (sc (oP j)))
    (VG.Taint.hintOf VG.Arm.taint (Taint.ofRegs [.r7]) (mask (sc 0)))).isSome = true := by decide +kernel

theorem mask_tr {j : Nat} (hj : j < 128) {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .r7 = y.gpr .r7) :
    RelCT isa P (mask (sc (oP j))) fun _ _ => True :=
  taint_prog [.r7] (fun x y hp r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h x y hp)
    (mask_taint j hj)

end VG.Proof.MlDsa.Arm.KeyGen
