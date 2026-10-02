import VerifiedGarbage.Proof.MlKem.Arm.HashCT

/-!
# ML-KEM-768 on 32-bit ARM: calling the primitives in constant time

The taint analysis proves the primitives constant time from any state whose
argument registers are public (`addT`, …), so two runs that call one with the
same arguments leak the same trace (`RelCT.callT`), whatever else holds of
them. `vg_mlkem_sample_ntt` leaks its seed, so two runs that call it must also
have the same seed (`sample_ct`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

/-- A call of code that is constant time from any state with public `pub`. -/
theorem RelCT.callT {n : String} {c : Prog isa} {pub : State → State → Prop}
    (hct : ConstantTime isa (fun _ => True) pub c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → pub s₁.callEntry s₂.callEntry) :
    RelCT isa P (.call n c) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      have ht := hct _ _ _ _ _ _ trivial trivial (hP _ _ hp) b₁ b₂
      exact ⟨by simp only [ht], trivial⟩

/-- Taint analysis of any code (not only a block). -/
theorem taint_prog {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs rs) (fun a b hab => Taint.agree_ofRegs (hP a b hab)) h

/-- A contract with no precondition, whose public data is the registers `rs`. -/
def kT (rs : List Reg) : Contract isa := mkK (fun _ => True) (fun _ _ => True) (regsEq rs)

theorem addT : ConstantTime isa (fun _ => True) (regsEq [.r0, .r1]) Impl.MlKem.Arm.add :=
  Add.ctRegs (k := kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem subT : ConstantTime isa (fun _ => True) (regsEq [.r0, .r1]) Impl.MlKem.Arm.sub :=
  Add.ctRegs (k := kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem mulT : ConstantTime isa (fun _ => True) (regsEq [.r0, .r1, .r2, .r3]) Impl.MlKem.Arm.multiplyNTTs :=
  Add.ctRegs (k := kT [.r0, .r1, .r2, .r3]) [.r0, .r1, .r2, .r3] (fun _ _ h => h) (by taint_decide)

theorem nttT : ConstantTime isa (fun _ => True) (regsEq [.r0, .r1]) Impl.MlKem.Arm.ntt :=
  Add.ctRegs (k := kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem nttInvT : ConstantTime isa (fun _ => True) (regsEq [.r0, .r1]) Impl.MlKem.Arm.nttInv :=
  Add.ctRegs (k := kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem cbd2T : ConstantTime isa (fun _ => True) (regsEq [.r0, .r1]) Impl.MlKem.Arm.cbd2 :=
  Add.ctRegs (k := kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem encode12T : ConstantTime isa (fun _ => True) (regsEq [.r0, .r1]) Impl.MlKem.Arm.encode12 :=
  Add.ctRegs (k := kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem decode12T : ConstantTime isa (fun _ => True) (regsEq [.r0, .r1]) Impl.MlKem.Arm.decode12 :=
  Add.ctRegs (k := kT [.r0, .r1]) [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem compressT : ConstantTime isa (fun _ => True) (regsEq [.r0, .r1, .r2, .r3]) Impl.MlKem.Arm.compressEncode :=
  Add.ctRegs (k := kT [.r0, .r1, .r2, .r3]) [.r0, .r1, .r2, .r3] (fun _ _ h => h) (by taint_decide)

theorem decompressT :
    ConstantTime isa (fun _ => True) (regsEq [.r0, .r1, .r2, .r3]) Impl.MlKem.Arm.decodeDecompress :=
  Add.ctRegs (k := kT [.r0, .r1, .r2, .r3]) [.r0, .r1, .r2, .r3] (fun _ _ h => h) (by taint_decide)

/-- Two runs that call a primitive with the same registers `rs`. -/
theorem callEq {rs : List Reg} (hl : ∀ r ∈ rs, r ∉ linkRegs) {a b : State} (h : ∀ r ∈ rs, a.gpr r = b.gpr r) :
    regsEq rs a.callEntry b.callEntry := fun r hr => by
  rw [State.callEntry_gpr _ (hl r hr), State.callEntry_gpr _ (hl r hr), h r hr]

theorem regs2 {P : State → State → Prop} (hP : ∀ a b, P a b → a.gpr .r0 = b.gpr .r0 ∧ a.gpr .r1 = b.gpr .r1) :
    ∀ a b, P a b → regsEq [.r0, .r1] a.callEntry b.callEntry := fun a b h =>
  callEq (by decide) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hP a b h).1
    · exact (hP a b h).2

theorem regs4 {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.gpr .r0 = b.gpr .r0 ∧ a.gpr .r1 = b.gpr .r1 ∧ a.gpr .r2 = b.gpr .r2 ∧
      a.gpr .r3 = b.gpr .r3) :
    ∀ a b, P a b → regsEq [.r0, .r1, .r2, .r3] a.callEntry b.callEntry := fun a b h =>
  callEq (by decide) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hP a b h).1
    · exact (hP a b h).2.1
    · exact (hP a b h).2.2.1
    · exact (hP a b h).2.2.2

/-! ## `vg_mlkem_sample_ntt` -/

theorem kSample_ct : ConstantTime isa kSample.pre kSample.pub Impl.MlKem.Arm.sampleNTT :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨hsp, hr, hb⟩ e₁ e₂ =>
    (Sample.all_ct ⟨h₁, h₂, hsp, hr .r0 (by simp), hr .r1 (by simp), hr .r2 (by simp), hb⟩
      s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1

theorem Ctx.sp_eq {L : Lay} {a b : State} (ha : Ctx L a) (hb : Ctx L b) : a.sp = b.sp := by
  have e := ha.sp.symm.trans hb.sp
  have := BitVec.sub_add_cancel a.sp (BitVec.ofNat 32 8)
  rw [e, BitVec.sub_add_cancel] at this
  exact this.symm

/-- What `vg_mlkem_sample_ntt` needs, as `sampleL` builds it. -/
theorem sample_view {L : Lay} {s : State} (hc : Ctx L s) {i o j o' k o'' : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = L.ptr j + BitVec.ofNat 32 o')
    (g2 : s.gpr .r2 = L.ptr k + BitVec.ofNat 32 o'')
    (s_ij : sepB L.sizes (i, o, 34) (j, o', 1024) = true) (s_ik : sepB L.sizes (i, o, 34) (k, o'', 2048) = true)
    (s_jk : sepB L.sizes (j, o', 1024) (k, o'', 2048) = true) (s_i1 : sepB L.sizes (i, o, 34) (1, 0, 8) = true)
    (s_j1 : sepB L.sizes (j, o', 1024) (1, 0, 8) = true) (s_k1 : sepB L.sizes (k, o'', 2048) (1, 0, 8) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) (wk : L.buf k ∈ s.wr) :
    Sample.Pre (view s [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]) ∧
      Covers ([⟨L.A i o, 34⟩] ++ [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]) (s.rd ++ s.wr) ∧
      Covers [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩] s.wr ∧
      Sample.B (view s [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]) = bytesAt s.mem (L.A i o) 34 := by
  have hL := hc.ok
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (sepB_bounds s_ij) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (sepB_bounds s_jk) (by decide)
  obtain ⟨ec, fc⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm s_ik)) (by decide)
  let V := view s [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩]
  have eS : Sample.SEED V = L.A i o := by simp only [V, Sample.SEED, Sample.pseed, view_r0, g0, ea]
  have eA : Sample.A V = L.A j o' := by simp only [V, Sample.A, Sample.pa, view_r1, g1, eb]
  have eC : Sample.S V = L.A k o'' := by simp only [V, Sample.S, Sample.pscr, view_r2, g2, ec]
  have eb8 : below V 8 = L.R 1 0 8 := hc.bel
  have cw : Covers [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩] s.wr :=
    covers_cons' (Lay.covers wj (sepB_bounds s_jk).2) (covers_cons' (Lay.covers wk (sepB_bounds (sepB_symm s_ik)).2)
      covers_nil')
  refine ⟨⟨hc.sp8, by simp only [V, eS, State.withRegions_rd], by simp only [V, eA, eC, State.withRegions_wr],
      by rw [eS, eA]; exact Lay.disj hL s_ij, by rw [eS, eC]; exact Lay.disj hL s_ik,
      by rw [eA, eC]; exact Lay.disj hL s_jk, by rw [eb8, eS]; exact Lay.disj hL (sepB_symm s_i1),
      by rw [eb8, eA]; exact Lay.disj hL (sepB_symm s_j1), by rw [eb8, eC]; exact Lay.disj hL (sepB_symm s_k1),
      by simp only [Sample.pseed, view_r0, g0]; exact fa, by simp only [Sample.pa, view_r1, g1]; exact fb,
      by simp only [Sample.pscr, view_r2, g2]; exact fc⟩,
    covers_append (Lay.covers wi (sepB_bounds s_ij).2) (covers_wr cw), cw, ?_⟩
  show bytesAt s.mem (Sample.SEED V) 34 = _
  rw [eS]

/-- Two runs that call `vg_mlkem_sample_ntt` on the same pointers and seed. -/
theorem sample_ct {L : Lay} {i o j o' k o'' : Nat} {P : State → State → Prop}
    (hP : ∀ a b, P a b → Ctx L a ∧ Ctx L b ∧
      a.gpr .r0 = L.ptr i + BitVec.ofNat 32 o ∧ a.gpr .r1 = L.ptr j + BitVec.ofNat 32 o' ∧
      a.gpr .r2 = L.ptr k + BitVec.ofNat 32 o'' ∧
      b.gpr .r0 = L.ptr i + BitVec.ofNat 32 o ∧ b.gpr .r1 = L.ptr j + BitVec.ofNat 32 o' ∧
      b.gpr .r2 = L.ptr k + BitVec.ofNat 32 o'' ∧
      bytesAt a.mem (L.A i o) 34 = bytesAt b.mem (L.A i o) 34 ∧
      L.buf i ∈ a.rd ++ a.wr ∧ L.buf j ∈ a.wr ∧ L.buf k ∈ a.wr ∧
      L.buf i ∈ b.rd ++ b.wr ∧ L.buf j ∈ b.wr ∧ L.buf k ∈ b.wr)
    (s_ij : sepB L.sizes (i, o, 34) (j, o', 1024) = true) (s_ik : sepB L.sizes (i, o, 34) (k, o'', 2048) = true)
    (s_jk : sepB L.sizes (j, o', 1024) (k, o'', 2048) = true) (s_i1 : sepB L.sizes (i, o, 34) (1, 0, 8) = true)
    (s_j1 : sepB L.sizes (j, o', 1024) (1, 0, 8) = true) (s_k1 : sepB L.sizes (k, o'', 2048) (1, 0, 8) = true) :
    RelCT isa P callSample fun _ _ => True :=
  RelCT.call kSample_ok kSample_ct [⟨L.A i o, 34⟩] [polyRegion (L.A j o'), ⟨L.A k o'', 2048⟩] fun a b hab => by
    obtain ⟨ca, cb, a0, a1, a2, b0, b1, b2, eb, wia, wja, wka, wib, wjb, wkb⟩ := hP a b hab
    obtain ⟨pa, c1a, c2a, ba⟩ := sample_view ca a0 a1 a2 s_ij s_ik s_jk s_i1 s_j1 s_k1 wia wja wka
    obtain ⟨pb, c1b, c2b, bb⟩ := sample_view cb b0 b1 b2 s_ij s_ik s_jk s_i1 s_j1 s_k1 wib wjb wkb
    refine ⟨pa, pb, ⟨by show a.sp = b.sp; exact Ctx.sp_eq ca cb, fun r hr => ?_, by rw [ba, bb, eb]⟩, c1a, c2a,
      c1b, c2b⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [view_r0, view_r0, a0, b0]
    · rw [view_r1, view_r1, a1, b1]
    · rw [view_r2, view_r2, a2, b2]

/-! ## Loops counted by a register -/

/-- A loop whose body runs `N` times, related in two runs by invariants at
the same iteration. -/
theorem relct_loop_ne {body : Prog isa} {I₁ I₂ : Nat → State → Prop} {N : Nat} (hN : 0 < N)
    (hstep : ∀ i < N, RelCT isa (fun a b => I₁ i a ∧ I₂ i b) body fun a b =>
      (I₁ (i + 1) a ∧ a.z = decide (i + 1 = N)) ∧ (I₂ (i + 1) b ∧ b.z = decide (i + 1 = N))) :
    RelCT isa (fun a b => I₁ 0 a ∧ I₂ 0 b) (.loop body .ne) fun a b => I₁ N a ∧ I₂ N b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := body) (c := .ne) (Q := fun a b => I₁ N a ∧ I₂ N b)
    (fun n a b => ∃ t, t < N ∧ n = N - t ∧ I₁ t a ∧ I₂ t b) (fun n => ?_) N) ?_ (fun _ _ h => h)
  · refine RelCT.mono (P := fun a b => ∃ t, t < N ∧ n = N - t ∧ I₁ t a ∧ I₂ t b)
      (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
    by_cases ht : t < N
    · by_cases hn : n = N - t
      · refine RelCT.mono (P := fun a b => I₁ t a ∧ I₂ t b) (hstep t ht) (fun _ _ hab => hab.2.2)
          fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
        · show some (!a.z) = some (!b.z); rw [z₁, z₂]
        · have : t + 1 = N := by
            have e' : (!a.z) = false := Option.some.inj e
            rw [z₁] at e'; simpa using e'
          rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
        · have : t + 1 ≠ N := by
            have e' : (!a.z) = true := Option.some.inj e
            rw [z₁] at e'; simpa using e'
          exact ⟨N - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
      · exact RelCT.of_false fun _ _ hab => hn hab.2.1
    · exact RelCT.of_false fun _ _ hab => ht hab.1
  · exact fun a b hab => ⟨0, hN, rfl, hab⟩

end VG.Proof.MlKem.Arm
