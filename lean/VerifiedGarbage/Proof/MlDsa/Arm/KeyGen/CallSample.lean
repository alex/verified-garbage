import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Call

/-!
# ML-DSA on 32-bit ARM: calling the samplers

Untrusted: everything here is checked by Lean. As `ip_ok` and `ip_tr`
(`Call.lean`), for `vg_mldsa_rej_ntt_poly` and `vg_mldsa_rej_bounded_poly`,
whose public data include what they leak of their seeds.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_rej_ntt_poly` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {sd a w : Ptr}

abbrev rnArgs (sd a w : Ptr) : List (Reg × Arg) := [(.r0, .ptr sd), (.r1, .ptr a), (.r2, .ptr w)]
abbrev rnRd (L : Lay) (sd : Ptr) : List Region := [L.R (ix sd.1) sd.2 34]
abbrev rnWr (L : Lay) (a w : Ptr) : List Region := [L.R (ix a.1) a.2 1024, L.R (ix w.1) w.2 2048]

/-- The facts `vg_mldsa_rej_ntt_poly` needs of its pointers. -/
structure RnOk (L : Lay) (Wb : List Nat) (sd a w : Ptr) : Prop where
  ps : PtrIn L sd 34
  pa : PtrIn L a 1024
  pw : PtrIn L w 2048
  wa : ix a.1 ∈ Wb
  ww : ix w.1 ∈ Wb
  d1 : sepB L.sizes (tri sd 34) (tri a 1024) = true
  d2 : sepB L.sizes (tri sd 34) (tri w 2048) = true
  d3 : sepB L.sizes (tri a 1024) (tri w 2048) = true

theorem RnOk.hg (m : RnOk L Wb sd a w) : glueOk (rnArgs sd a w) = true := by
  simp [glueOk, m.ps.1, m.pa.1, m.pw.1]

theorem rnArgs_nodup : ((rnArgs sd a w).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem rnG {s : State} (hs : Site L Wb STK s) (m : RnOk L Wb sd a w) (rd wr : List Region) :
    (view (glueSt s (rnArgs sd a w)) rd wr).gpr .r0 = L.ptr (ix sd.1) + BitVec.ofNat 32 sd.2 ∧
    (view (glueSt s (rnArgs sd a w)) rd wr).gpr .r1 = L.ptr (ix a.1) + BitVec.ofNat 32 a.2 ∧
    (view (glueSt s (rnArgs sd a w)) rd wr).gpr .r2 = L.ptr (ix w.1) + BitVec.ofNat 32 w.2 :=
  ⟨by rw [view_r0, hs.gE m.hg rnArgs_nodup (by simp) m.ps.1],
    by rw [view_r1, hs.gE m.hg rnArgs_nodup (by simp) m.pa.1],
    by rw [view_r2, hs.gE m.hg rnArgs_nodup (by simp) m.pw.1]⟩

theorem rn_cov {s : State} (hs : Site L Wb STK s) (m : RnOk L Wb sd a w) :
    Covers (rnRd L sd ++ rnWr L a w) (s.rd ++ s.wr) ∧ Covers (rnWr L a w) s.wr :=
  ⟨covers_append (covers_cons' (hs.crE m.ps) covers_nil')
    (covers_wr (covers_cons' (hs.cwE m.pa m.wa) (covers_cons' (hs.cwE m.pw m.ww) covers_nil'))),
    covers_cons' (hs.cwE m.pa m.wa) (covers_cons' (hs.cwE m.pw m.ww) covers_nil')⟩

theorem rn_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : RnOk L Wb sd a w) :
    (rejNTTContract Arm.abi stk).pre (view (glueSt s (rnArgs sd a w)) (rnRd L sd) (rnWr L a w)) := by
  have hsp := view_glue_sp s (rnArgs sd a w) (rnRd L sd) (rnWr L a w)
  obtain ⟨g0, g1, g2⟩ := rnG hs m (rnRd L sd) (rnWr L a w)
  refine rejNtt_pre g0 g1 g2 (by rw [State.withRegions_rd, hs.regE m.ps (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.pa (by decide), hs.regE m.pw (by decide)])
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_ ?_ ?_ ?_
    (hs.fitE m.ps (by decide)) (hs.fitE m.pa (by decide)) (hs.fitE m.pw (by decide))
  · rw [hs.regE m.ps (by decide), hs.regE m.pa (by decide)]; exact hs.dE m.d1 (.inr m.wa)
  · rw [hs.regE m.ps (by decide), hs.regE m.pw (by decide)]; exact hs.dE m.d2 (.inr m.ww)
  · rw [hs.regE m.pa (by decide), hs.regE m.pw (by decide)]; exact hs.dE m.d3 (.inl m.wa)
  · rw [hs.regE m.ps (by decide)]; exact hs.kE m.ps hstk hsp
  · rw [hs.regE m.pa (by decide)]; exact hs.kE m.pa hstk hsp
  · rw [hs.regE m.pw (by decide)]; exact hs.kE m.pw hstk hsp

theorem rn_ok {c : Prog isa} (hc : Callee c (fun stk => rejNTTContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : RnOk L Wb sd a w) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri a 1024, tri w 2048, (1, 0, STK)]) s s' →
      (s'.gpr .r0 = 1 → Reduced s'.mem (lpa L a)) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (lpa L sd) 34)) (s'.gpr .r0) (polyAt s'.mem (lpa L a)) →
      Q s') :
    WP isa (callAt name c (rnArgs sd a w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := rn_cov hs m
  refine callV hver.1 m.hg (rn_preS hs (Nat.le_trans hstk hS) m) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [tri a 1024, tri w 2048] (Nat.le_trans hc.stack hS) hk) ?_ ?_
  all_goals
    obtain ⟨g0, g1, -⟩ := rnG hs m (rnRd L sd) (rnWr L a w)
    have := rejNtt_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g0, g1, hs.addrE m.ps (by decide),
      hs.addrE m.pa (by decide), view_glue_mem] at this
  exacts [this.1, this.2]

theorem rn_tr {c : Prog isa} (hc : Callee c (fun stk => rejNTTContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : RnOk L Wb sd a w) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      bytesAt x.mem (lpa L sd) 34 = bytesAt y.mem (lpa L sd) 34) :
    RelCT isa P (callAt name c (rnArgs sd a w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2⟩ := rnG hx m (rnRd L sd) (rnWr L a w)
  obtain ⟨gy0, gy1, gy2⟩ := rnG hy m (rnRd L sd) (rnWr L a w)
  refine ⟨rnRd L sd, rnWr L a w, rn_preS hx (Nat.le_trans hstk hS) m, rn_preS hy (Nat.le_trans hstk hS) m,
    rejNtt_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]) ?_,
    (rn_cov hx m).1, (rn_cov hx m).2, (rn_cov hy m).1, (rn_cov hy m).2⟩
  rw [gx0, gy0, view_glue_mem, view_glue_mem, hx.addrE m.ps (by decide)]
  exact hl

end

/-! ## `vg_mldsa_rej_bounded_poly` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {sd a w : Ptr} {η : Nat}

abbrev rbArgs (sd : Ptr) (η : Nat) (a w : Ptr) : List (Reg × Arg) :=
  [(.r0, .ptr sd), (.r1, .imm η), (.r2, .ptr a), (.r3, .ptr w)]
abbrev rbRd (L : Lay) (sd : Ptr) : List Region := [L.R (ix sd.1) sd.2 66]

/-- The facts `vg_mldsa_rej_bounded_poly` needs of its pointers. -/
structure RbOk (L : Lay) (Wb : List Nat) (sd a w : Ptr) : Prop where
  ps : PtrIn L sd 66
  pa : PtrIn L a 1024
  pw : PtrIn L w 2048
  wa : ix a.1 ∈ Wb
  ww : ix w.1 ∈ Wb
  d1 : sepB L.sizes (tri sd 66) (tri a 1024) = true
  d2 : sepB L.sizes (tri sd 66) (tri w 2048) = true
  d3 : sepB L.sizes (tri a 1024) (tri w 2048) = true

theorem RbOk.hg (m : RbOk L Wb sd a w) : glueOk (rbArgs sd η a w) = true := by
  simp [glueOk, m.ps.1, m.pa.1, m.pw.1, show argOk (.imm η) = true from rfl]

theorem rbArgs_nodup : ((rbArgs sd η a w).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem rbG {s : State} (hs : Site L Wb STK s) (m : RbOk L Wb sd a w) (rd wr : List Region) :
    (view (glueSt s (rbArgs sd η a w)) rd wr).gpr .r0 = L.ptr (ix sd.1) + BitVec.ofNat 32 sd.2 ∧
    (view (glueSt s (rbArgs sd η a w)) rd wr).gpr .r1 = BitVec.ofNat 32 η ∧
    (view (glueSt s (rbArgs sd η a w)) rd wr).gpr .r2 = L.ptr (ix a.1) + BitVec.ofNat 32 a.2 ∧
    (view (glueSt s (rbArgs sd η a w)) rd wr).gpr .r3 = L.ptr (ix w.1) + BitVec.ofNat 32 w.2 :=
  ⟨by rw [view_r0, hs.gE m.hg rbArgs_nodup (by simp) m.ps.1],
    by rw [view_r1, glueSt_arg s m.hg rbArgs_nodup (a := .imm η) (by simp)]; rfl,
    by rw [view_r2, hs.gE m.hg rbArgs_nodup (by simp) m.pa.1],
    by rw [view_r3, hs.gE m.hg rbArgs_nodup (by simp) m.pw.1]⟩

theorem rb_cov {s : State} (hs : Site L Wb STK s) (m : RbOk L Wb sd a w) :
    Covers (rbRd L sd ++ rnWr L a w) (s.rd ++ s.wr) ∧ Covers (rnWr L a w) s.wr :=
  ⟨covers_append (covers_cons' (hs.crE m.ps) covers_nil')
    (covers_wr (covers_cons' (hs.cwE m.pa m.wa) (covers_cons' (hs.cwE m.pw m.ww) covers_nil'))),
    covers_cons' (hs.cwE m.pa m.wa) (covers_cons' (hs.cwE m.pw m.ww) covers_nil')⟩

theorem rb_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : RbOk L Wb sd a w)
    (hη : η = 2 ∨ η = 4) :
    (rejBoundedContract Arm.abi stk).pre (view (glueSt s (rbArgs sd η a w)) (rbRd L sd) (rnWr L a w)) := by
  have hsp := view_glue_sp s (rbArgs sd η a w) (rbRd L sd) (rnWr L a w)
  obtain ⟨g0, g1, g2, g3⟩ := rbG (η := η) hs m (rbRd L sd) (rnWr L a w)
  refine rejBounded_pre g0 g1 g2 g3 (by rw [State.withRegions_rd, hs.regE m.ps (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.pa (by decide), hs.regE m.pw (by decide)])
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_ ?_ ?_ ?_
    (hs.fitE m.ps (by decide)) (hs.fitE m.pa (by decide)) (hs.fitE m.pw (by decide))
    (by rw [imm_toNat (by omega)]; exact hη)
  · rw [hs.regE m.ps (by decide), hs.regE m.pa (by decide)]; exact hs.dE m.d1 (.inr m.wa)
  · rw [hs.regE m.ps (by decide), hs.regE m.pw (by decide)]; exact hs.dE m.d2 (.inr m.ww)
  · rw [hs.regE m.pa (by decide), hs.regE m.pw (by decide)]; exact hs.dE m.d3 (.inl m.wa)
  · rw [hs.regE m.ps (by decide)]; exact hs.kE m.ps hstk hsp
  · rw [hs.regE m.pa (by decide)]; exact hs.kE m.pa hstk hsp
  · rw [hs.regE m.pw (by decide)]; exact hs.kE m.pw hstk hsp

theorem rb_ok {c : Prog isa} (hc : Callee c (fun stk => rejBoundedContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : RbOk L Wb sd a w) (hη : η = 2 ∨ η = 4)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri a 1024, tri w 2048, (1, 0, STK)]) s s' →
      (s'.gpr .r0 = 1 → Reduced s'.mem (lpa L a)) →
      Outcome (fun b => (rejBoundedPoly η b.rejBounded (bytesAt s.mem (lpa L sd) 66)).map toRq) (s'.gpr .r0)
        (polyAt s'.mem (lpa L a)) → Q s') :
    WP isa (callAt name c (rbArgs sd η a w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := rb_cov hs m
  refine callV hver.1 m.hg (rb_preS hs (Nat.le_trans hstk hS) m hη) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [tri a 1024, tri w 2048] (Nat.le_trans hc.stack hS) hk) ?_ ?_
  all_goals
    obtain ⟨g0, g1, g2, -⟩ := rbG (η := η) hs m (rbRd L sd) (rnWr L a w)
    have := rejBounded_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g0, g1, g2, hs.addrE m.ps (by decide),
      hs.addrE m.pa (by decide), view_glue_mem, imm_toNat (by omega)] at this
  exacts [this.1, this.2]

theorem rb_tr {c : Prog isa} (hc : Callee c (fun stk => rejBoundedContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : RbOk L Wb sd a w) (hη : η = 2 ∨ η = 4) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      rejBoundedLeak η (bytesAt x.mem (lpa L sd) 66) = rejBoundedLeak η (bytesAt y.mem (lpa L sd) 66)) :
    RelCT isa P (callAt name c (rbArgs sd η a w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2, gx3⟩ := rbG (η := η) hx m (rbRd L sd) (rnWr L a w)
  obtain ⟨gy0, gy1, gy2, gy3⟩ := rbG (η := η) hy m (rbRd L sd) (rnWr L a w)
  refine ⟨rbRd L sd, rnWr L a w, rb_preS hx (Nat.le_trans hstk hS) m hη, rb_preS hy (Nat.le_trans hstk hS) m hη,
    rejBounded_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx0, gy0]) (by rw [gx1, gy1])
      (by rw [gx2, gy2]) (by rw [gx3, gy3]) ?_, (rb_cov hx m).1, (rb_cov hx m).2, (rb_cov hy m).1, (rb_cov hy m).2⟩
  rw [gx0, gy0, gx1, gy1, view_glue_mem, view_glue_mem, hx.addrE m.ps (by decide), imm_toNat (by omega)]
  exact hl

end

end VG.Proof.MlDsa.Arm.KeyGen
