import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Contracts
import VerifiedGarbage.Proof.MlDsa.Verify.Mem

/-!
# ML-DSA on 32-bit ARM: calling the primitives on the buffers of a `Site`

A call of each primitive, with its arguments pointers into the buffers of a
`Site` (`PtrIn`): the callee's precondition from the layout (`ip_preS`, …),
what the call changes and what its postcondition says (`ip_ok`, …), and that
two runs of it with the same pointers leak the same (`ip_tr`, …).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A pointer, in a register of the layout, to `l` bytes of a buffer (but the stack). -/
def PtrIn (L : Lay) (q : Ptr) (l : Nat) : Prop := argOk (.ptr q) = true ∧ inB L.sizes (tri q l) = true

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s)
include hs

theorem Site.regE {q : Ptr} {l : Nat} (pq : PtrIn L q l) (hl : 0 < l) :
    regA (L.ptr (ix q.1) + BitVec.ofNat 32 q.2) l = L.R (ix q.1) q.2 l := by
  simp only [regA, (hs.addr pq.2 hl).1]

theorem Site.fitE {q : Ptr} {l : Nat} (pq : PtrIn L q l) (hl : 0 < l) :
    (L.ptr (ix q.1) + BitVec.ofNat 32 q.2).toNat + l ≤ 2 ^ 32 := (hs.addr pq.2 hl).2

theorem Site.addrE {q : Ptr} {l : Nat} (pq : PtrIn L q l) (hl : 0 < l) :
    State.addr (L.ptr (ix q.1) + BitVec.ofNat 32 q.2) = lpa L q := (hs.addr pq.2 hl).1

/-- A pointer argument's register after the moves. -/
theorem Site.gE {as : List (Reg × Arg)} (hg : glueOk as = true) (hn : (as.map Prod.fst).Nodup) {d : Reg} {q : Ptr}
    (hm : (d, .ptr q) ∈ as) (hq : argOk (.ptr q) = true) :
    (glueSt s as).gpr d = L.ptr (ix q.1) + BitVec.ofNat 32 q.2 := by
  rw [glueSt_arg s hg hn hm, hs.val hq]

/-- A buffer the state may write. -/
theorem Site.cwE {q : Ptr} {l : Nat} (pq : PtrIn L q l) (wq : ix q.1 ∈ Wb) : Covers [L.R (ix q.1) q.2 l] s.wr :=
  Site.covW pq.2 (hs.cw _ wq (inB_bounds pq.2).1)

/-- A buffer the state may read. -/
theorem Site.crE {q : Ptr} {l : Nat} (pq : PtrIn L q l) : Covers [L.R (ix q.1) q.2 l] (s.rd ++ s.wr) :=
  Site.covR pq.2 (hs.cr _ (by have := (inB_bounds pq.2).2.1; rw [hs.len] at this; exact this) (inB_bounds pq.2).1)

/-- Two regions apart, one of them written. -/
theorem Site.dE {q q' : Ptr} {l l' : Nat} (hd : sepB L.sizes (tri q l) (tri q' l') = true)
    (hw : ix q.1 ∈ Wb ∨ ix q'.1 ∈ Wb) : (L.R (ix q.1) q.2 l).Disjoint (L.R (ix q'.1) q'.2 l') := disjW hs.ok hd hw

/-- The stack below the stack pointer is apart from a buffer. -/
theorem Site.kE {q : Ptr} {l : Nat} (pq : PtrIn L q l) {n : Nat} (hn : n ≤ STK) {x : State} (hx : x.sp = s.sp) :
    (below x n).Disjoint (L.R (ix q.1) q.2 l) := by
  have := (hs.stkD pq.2 hn).symm
  simp only [below, hx] at this ⊢
  exact this

end

theorem view_glue_sp (s : State) (as : List (Reg × Arg)) (rd wr : List Region) :
    (view (glueSt s as) rd wr).sp = s.sp := glueSt_sp s as

theorem view_glue_mem (s : State) (as : List (Reg × Arg)) (rd wr : List Region) :
    (view (glueSt s as) rd wr).mem = s.mem := glueSt_mem s as

/-- The registers of the layout, the stack pointer, and the pointers of both
runs are the same. -/
theorem Site.gpr_eq {L : Lay} {Wb : List Nat} {STK : Nat} {x y : State} (hx : Site L Wb STK x) (hy : Site L Wb STK y)
    {as : List (Reg × Arg)} (hg : glueOk as = true) (hn : (as.map Prod.fst).Nodup) {d : Reg} {a : Arg} (hm : (d, a) ∈ as) :
    (glueSt x as).gpr d = (glueSt y as).gpr d := by
  rw [glueSt_arg x hg hn hm, glueSt_arg y hg hn hm]
  cases a with
  | imm v => rfl
  | ptr q =>
    have ha : argOk (.ptr q) = true := by
      have := List.all_eq_true.mp hg _ hm; simp only [Bool.and_eq_true] at this; exact this.2
    rw [hx.val ha, hy.val ha]

/-- Kept, with the regions written those of the triples `W`. -/
theorem Site.keptW {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (hs : Site L Wb STK s)
    (W : List (Nat × Nat × Nat)) {n : Nat} (hn : n ≤ STK) (hk : Kept (L.RL W ++ [below s n]) s s') :
    Kept (L.RL (W ++ [(1, 0, STK)])) s s' :=
  hs.kept_stk (fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact ⟨w, hw, fun _ h => h⟩) hn hk

theorem imm_toNat {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## Calls in a frame that pushes the stack argument -/

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) (s1 : State)
  (e1 : s1.sp = s.sp) (rd wr : List Region)
include hs e1

omit hs in
theorem push_sp : (view (pushed [.r12] s1) rd wr).sp = s.sp - BitVec.ofNat 32 4 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e1]; rfl

omit hs in
theorem push_spN (h4 : 4 ≤ s.sp.toNat) : (view (pushed [.r12] s1) rd wr).sp.toNat = s.sp.toNat - 4 := by
  rw [push_sp s1 e1]; bv_omega

omit hs in
theorem push_argAddr : stackArgAddr (view (pushed [.r12] s1) rd wr) 0 = State.addr (s.sp - BitVec.ofNat 32 4) := by
  show State.addr ((view (pushed [.r12] s1) rd wr).sp + BitVec.ofNat 32 (4 * 0)) = _
  rw [push_sp s1 e1]; congr 1; bv_omega

omit hs e1 in
theorem push_arg : stackArg (view (pushed [.r12] s1) rd wr) 0 = s1.gpr .r12 := by
  have e : stackArgAddr (view (pushed [.r12] s1) rd wr) 0 = State.addr (s1.sp - BitVec.ofNat 32 4) := by
    show State.addr ((pushed [.r12] s1).sp + BitVec.ofNat 32 (4 * 0)) = _
    rw [pushed_sp]; congr 1; simp only [List.length_cons, List.length_nil]; bv_omega
  show (pushed [.r12] s1).mem.readW (stackArgAddr (view (pushed [.r12] s1) rd wr) 0) 32 = _
  rw [e]; exact pushed12_word s1

/-- The stack a callee in the frame may use is apart from a buffer. -/
theorem push_kE {q : Ptr} {l : Nat} (pq : PtrIn L q l) {n : Nat} (hn : 4 + n ≤ STK) :
    (below (view (pushed [.r12] s1) rd wr) n).Disjoint (L.R (ix q.1) q.2 l) := by
  have h4 : 4 + n ≤ s.sp.toNat := Nat.le_trans hn hs.spk
  refine ((hs.stkD pq.2 hn).symm).sub_left ?_
  intro x hx
  have := addr_toNat' s.sp
  have := addr_toNat' (s.sp - BitVec.ofNat 32 4)
  simp only [Region.Contains, push_sp s1 e1] at hx ⊢
  bv_omega

/-- The stack slot of the argument is apart from a buffer. -/
theorem push_aE {q : Ptr} {l : Nat} (pq : PtrIn L q l) :
    (L.R (ix q.1) q.2 l).Disjoint ⟨stackArgAddr (view (pushed [.r12] s1) rd wr) 0, 4⟩ := by
  rw [push_argAddr s1 e1 rd wr]
  refine (hs.stkD pq.2 (n := 4) (by have := hs.s8; omega)).sub_right ?_
  intro x hx
  have := addr_toNat' s.sp
  have := addr_toNat' (s.sp - BitVec.ofNat 32 4)
  have := hs.s8; have := hs.spk
  simp only [Region.Contains] at hx ⊢
  bv_omega

/-- The stack a callee in the frame may use is apart from the stack slot of its argument. -/
theorem push_kA {n : Nat} (hn : 4 + n ≤ STK) :
    (below (view (pushed [.r12] s1) rd wr) n).Disjoint ⟨stackArgAddr (view (pushed [.r12] s1) rd wr) 0, 4⟩ := by
  rw [push_argAddr s1 e1 rd wr]
  intro x hx hy
  have := addr_toNat' (s.sp - BitVec.ofNat 32 4)
  have := hs.s8; have := hs.spk
  simp only [Region.Contains, push_sp s1 e1] at hx hy
  bv_omega

/-- The memory of the frame: the pushed word below the stack pointer. -/
theorem push_frame (hm : s1.mem = s.mem) : Frame [below s 4] s.mem (view (pushed [.r12] s1) rd wr).mem := by
  have h4 : 4 ≤ s1.sp.toNat := by rw [e1]; have := hs.s8; have := hs.spk; omega
  have := pushed12_frame s1 h4
  simp only [below, e1, hm] at this
  exact this

/-- A buffer's bytes in the frame. -/
theorem push_bytes (hm : s1.mem = s.mem) {q : Ptr} {l : Nat} (pq : PtrIn L q l) (hl : l ≤ 2 ^ 64) :
    ∀ k < l, (view (pushed [.r12] s1) rd wr).mem (lpa L q + BitVec.ofNat 64 k) = s.mem (lpa L q + BitVec.ofNat 64 k) :=
  Proof.MlKem.bytes_frame (push_frame hs s1 e1 rd wr hm) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hs.stkD pq.2 (by have := hs.s8; omega)) hl

omit hs e1 in
theorem push_fit (h4 : 4 ≤ s.sp.toNat) (e1 : s1.sp = s.sp) :
    (view (pushed [.r12] s1) rd wr).sp.toNat + 4 ≤ 2 ^ 32 := by
  rw [push_spN s1 e1 rd wr h4]; have := s.sp.isLt; omega

end

theorem sp4 {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) : 4 ≤ s.sp.toNat := by
  have := hs.s8; have := hs.spk; omega

/-- A polynomial of a buffer in the frame. -/
theorem push_reduced {L : Lay} {Wb : List Nat} {STK : Nat} {s s1 : State} (hs : Site L Wb STK s) (e1 : s1.sp = s.sp)
    (hm : s1.mem = s.mem) (rd wr : List Region) {q : Ptr} (pq : PtrIn L q 1024) :
    Reduced (view (pushed [.r12] s1) rd wr).mem (lpa L q) ↔ Reduced s.mem (lpa L q) :=
  ⟨Proof.MlDsa.Verify.reduced_congr fun k hk => (push_bytes hs s1 e1 rd wr hm pq (by decide) k hk).symm,
    Proof.MlDsa.Verify.reduced_congr (push_bytes hs s1 e1 rd wr hm pq (by decide))⟩

theorem push_polyAt {L : Lay} {Wb : List Nat} {STK : Nat} {s s1 : State} (hs : Site L Wb STK s) (e1 : s1.sp = s.sp)
    (hm : s1.mem = s.mem) (rd wr : List Region) {q : Ptr} (pq : PtrIn L q 1024) :
    polyAt (view (pushed [.r12] s1) rd wr).mem (lpa L q) = polyAt s.mem (lpa L q) :=
  Proof.MlDsa.Verify.polyAt_congr (push_bytes hs s1 e1 rd wr hm pq (by decide))

theorem push_coeffAt {L : Lay} {Wb : List Nat} {STK : Nat} {s s1 : State} (hs : Site L Wb STK s) (e1 : s1.sp = s.sp)
    (hm : s1.mem = s.mem) (rd wr : List Region) {q : Ptr} (pq : PtrIn L q 1024) {i : Nat} (hi : i < n) :
    coeffAt (view (pushed [.r12] s1) rd wr).mem (lpa L q) i = coeffAt s.mem (lpa L q) i :=
  Proof.MlDsa.Verify.coeffAt_congr (push_bytes hs s1 e1 rd wr hm pq (by decide)) hi

theorem push_bytesAt {L : Lay} {Wb : List Nat} {STK : Nat} {s s1 : State} (hs : Site L Wb STK s) (e1 : s1.sp = s.sp)
    (hm : s1.mem = s.mem) (rd wr : List Region) {q : Ptr} {l : Nat} (pq : PtrIn L q l) (hl : l < 2 ^ 64) :
    bytesAt (view (pushed [.r12] s1) rd wr).mem (lpa L q) l = bytesAt s.mem (lpa L q) l := by
  have hb := push_bytes hs s1 e1 rd wr hm pq (Nat.le_of_lt hl)
  exact Proof.MlKem.bytesAt_eq! (by simp [bytesAt]) fun k hk => by
    rw [Proof.MlKem.bytesAt_getElem! _ _ hk, hb k hk]

/-! ## `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {t : Poly → Poly} {f w : Ptr}

abbrev ipArgs (f w : Ptr) : List (Reg × Arg) := [(.r0, .ptr f), (.r1, .ptr w)]
abbrev ipWr (L : Lay) (f w : Ptr) : List Region := [L.R (ix f.1) f.2 1024, L.R (ix w.1) w.2 1024]

theorem ip_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (pf : PtrIn L f 1024)
    (pw : PtrIn L w 1024) (wf : ix f.1 ∈ Wb) (hd : sepB L.sizes (tri f 1024) (tri w 1024) = true)
    (hr : Reduced s.mem (lpa L f)) :
    (inPlaceContract Arm.abi t stk).pre (view (glueSt s (ipArgs f w)) [] (ipWr L f w)) := by
  have hg : glueOk (ipArgs f w) = true := by simp [glueOk, pf.1, pw.1]
  have hn : ((ipArgs f w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  have hsp := view_glue_sp s (ipArgs f w) [] (ipWr L f w)
  refine ip_pre (by rw [view_r0, hs.gE hg hn (by simp) pf.1]) (by rw [view_r1, hs.gE hg hn (by simp) pw.1]) rfl
    (by rw [State.withRegions_wr, hs.regE pf (by decide), hs.regE pw (by decide)])
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_ (hs.fitE pf (by decide)) (hs.fitE pw (by decide)) ?_
  · rw [hs.regE pf (by decide), hs.regE pw (by decide)]; exact hs.dE hd (.inl wf)
  · rw [hs.regE pf (by decide)]; exact hs.kE pf hstk hsp
  · rw [hs.regE pw (by decide)]; exact hs.kE pw hstk hsp
  · rw [view_glue_mem, hs.addrE pf (by decide)]; exact hr

theorem ip_ok {c : Prog isa} (hc : Callee c (fun stk => inPlaceContract Arm.abi t stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (pf : PtrIn L f 1024) (pw : PtrIn L w 1024)
    (wf : ix f.1 ∈ Wb) (ww : ix w.1 ∈ Wb) (hd : sepB L.sizes (tri f 1024) (tri w 1024) = true)
    (hr : Reduced s.mem (lpa L f)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri f 1024, tri w 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L f) (t (polyAt s.mem (lpa L f))) → Q s') :
    WP isa (callAt name c (ipArgs f w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  have hg : glueOk (ipArgs f w) = true := by simp [glueOk, pf.1, pw.1]
  have hn : ((ipArgs f w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  have cw : Covers (ipWr L f w) s.wr := covers_cons' (hs.cwE pf wf) (covers_cons' (hs.cwE pw ww) covers_nil')
  refine callV hver.1 hg (ip_preS hs (Nat.le_trans hstk hS) pf pw wf hd hr) (covers_wr cw) cw
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.kept_stk (W := [tri f 1024, tri w 1024]) (fun r hr => ?_) (Nat.le_trans hc.stack hS) hk) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · have := ip_post hp
    rwa [State.withRegions_mem, view_r0, hs.gE hg hn (by simp) pf.1, hs.addrE pf (by decide), view_glue_mem] at this

theorem ip_tr {c : Prog isa} (hc : Callee c (fun stk => inPlaceContract Arm.abi t stk) S) (hS : S ≤ STK)
    {name : String} (pf : PtrIn L f 1024) (pw : PtrIn L w 1024) (wf : ix f.1 ∈ Wb) (ww : ix w.1 ∈ Wb)
    (hd : sepB L.sizes (tri f 1024) (tri w 1024) = true) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L f) ∧
      Reduced y.mem (lpa L f)) :
    RelCT isa P (callAt name c (ipArgs f w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  have hg : glueOk (ipArgs f w) = true := by simp [glueOk, pf.1, pw.1]
  have hn : ((ipArgs f w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  refine callV_tr hver.1 hver.2.1 hg fun x y h => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y h
  have cx : Covers (ipWr L f w) x.wr := covers_cons' (hx.cwE pf wf) (covers_cons' (hx.cwE pw ww) covers_nil')
  have cy : Covers (ipWr L f w) y.wr := covers_cons' (hy.cwE pf wf) (covers_cons' (hy.cwE pw ww) covers_nil')
  refine ⟨[], ipWr L f w, ip_preS hx (Nat.le_trans hstk hS) pf pw wf hd rx,
    ip_preS hy (Nat.le_trans hstk hS) pf pw wf hd ry, ip_pub ?_ ?_ ?_, covers_wr cx, cx, covers_wr cy, cy⟩
  · rw [view_glue_sp, view_glue_sp, hsp]
  · rw [view_r0, view_r0, hx.gE hg hn (by simp) pf.1, hy.gE hg hn (by simp) pf.1]
  · rw [view_r1, view_r1, hx.gE hg hn (by simp) pw.1, hy.gE hg hn (by simp) pw.1]

end

end VG.Proof.MlDsa.Arm.KeyGen
