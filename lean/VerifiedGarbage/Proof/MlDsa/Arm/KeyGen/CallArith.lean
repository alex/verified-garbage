import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Call

/-!
# ML-DSA on 32-bit ARM: calling the multiplications, additions and subtractions

As `ip_ok` and `ip_tr` (`Call.lean`), for `vg_mldsa_multiply_ntt`,
`vg_mldsa_multiply_add_ntt`, `vg_mldsa_add` and `vg_mldsa_sub`.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {h f g : Ptr}

abbrev mulArgs (h f g : Ptr) : List (Reg × Arg) := [(.r0, .ptr h), (.r1, .ptr f), (.r2, .ptr g)]
abbrev mulRd (L : Lay) (f g : Ptr) : List Region := [L.R (ix f.1) f.2 1024, L.R (ix g.1) g.2 1024]
abbrev mulWr (L : Lay) (h : Ptr) : List Region := [L.R (ix h.1) h.2 1024]

/-- The facts the multiplications need of their pointers. -/
structure MulOk (L : Lay) (Wb : List Nat) (h f g : Ptr) : Prop where
  ph : PtrIn L h 1024
  pf : PtrIn L f 1024
  pg : PtrIn L g 1024
  wh : ix h.1 ∈ Wb
  d1 : sepB L.sizes (tri h 1024) (tri f 1024) = true
  d2 : sepB L.sizes (tri h 1024) (tri g 1024) = true

theorem MulOk.hg (m : MulOk L Wb h f g) : glueOk (mulArgs h f g) = true := by
  simp [glueOk, m.ph.1, m.pf.1, m.pg.1]

theorem mulArgs_nodup : ((mulArgs h f g).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem mulG {s : State} (hs : Site L Wb STK s) (m : MulOk L Wb h f g) (rd wr : List Region) :
    (view (glueSt s (mulArgs h f g)) rd wr).gpr .r0 = L.ptr (ix h.1) + BitVec.ofNat 32 h.2 ∧
    (view (glueSt s (mulArgs h f g)) rd wr).gpr .r1 = L.ptr (ix f.1) + BitVec.ofNat 32 f.2 ∧
    (view (glueSt s (mulArgs h f g)) rd wr).gpr .r2 = L.ptr (ix g.1) + BitVec.ofNat 32 g.2 :=
  ⟨by rw [view_r0, hs.gE m.hg mulArgs_nodup (by simp) m.ph.1],
    by rw [view_r1, hs.gE m.hg mulArgs_nodup (by simp) m.pf.1],
    by rw [view_r2, hs.gE m.hg mulArgs_nodup (by simp) m.pg.1]⟩

theorem mul_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : MulOk L Wb h f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) :
    (mulContract Arm.abi stk).pre (view (glueSt s (mulArgs h f g)) (mulRd L f g) (mulWr L h)) := by
  have hsp := view_glue_sp s (mulArgs h f g) (mulRd L f g) (mulWr L h)
  obtain ⟨g0, g1, g2⟩ := mulG hs m (mulRd L f g) (mulWr L h)
  refine mul_pre g0 g1 g2 (by rw [State.withRegions_rd, hs.regE m.pf (by decide), hs.regE m.pg (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.ph (by decide)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    ?_ ?_ ?_ ?_ ?_ (hs.fitE m.ph (by decide)) (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_
  · rw [hs.regE m.ph (by decide), hs.regE m.pf (by decide)]; exact hs.dE m.d1 (.inl m.wh)
  · rw [hs.regE m.ph (by decide), hs.regE m.pg (by decide)]; exact hs.dE m.d2 (.inl m.wh)
  · rw [hs.regE m.ph (by decide)]; exact hs.kE m.ph hstk hsp
  · rw [hs.regE m.pf (by decide)]; exact hs.kE m.pf hstk hsp
  · rw [hs.regE m.pg (by decide)]; exact hs.kE m.pg hstk hsp
  · rw [view_glue_mem, hs.addrE m.pf (by decide)]; exact rf
  · rw [view_glue_mem, hs.addrE m.pg (by decide)]; exact rg

theorem mulAdd_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : MulOk L Wb h f g)
    (rh : Reduced s.mem (lpa L h)) (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) :
    (mulAddContract Arm.abi stk).pre (view (glueSt s (mulArgs h f g)) (mulRd L f g) (mulWr L h)) := by
  have hsp := view_glue_sp s (mulArgs h f g) (mulRd L f g) (mulWr L h)
  obtain ⟨g0, g1, g2⟩ := mulG hs m (mulRd L f g) (mulWr L h)
  refine mulAdd_pre g0 g1 g2 (by rw [State.withRegions_rd, hs.regE m.pf (by decide), hs.regE m.pg (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.ph (by decide)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    ?_ ?_ ?_ ?_ ?_ (hs.fitE m.ph (by decide)) (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_ ?_
  · rw [hs.regE m.ph (by decide), hs.regE m.pf (by decide)]; exact hs.dE m.d1 (.inl m.wh)
  · rw [hs.regE m.ph (by decide), hs.regE m.pg (by decide)]; exact hs.dE m.d2 (.inl m.wh)
  · rw [hs.regE m.ph (by decide)]; exact hs.kE m.ph hstk hsp
  · rw [hs.regE m.pf (by decide)]; exact hs.kE m.pf hstk hsp
  · rw [hs.regE m.pg (by decide)]; exact hs.kE m.pg hstk hsp
  · rw [view_glue_mem, hs.addrE m.ph (by decide)]; exact rh
  · rw [view_glue_mem, hs.addrE m.pf (by decide)]; exact rf
  · rw [view_glue_mem, hs.addrE m.pg (by decide)]; exact rg

theorem mul_cov {s : State} (hs : Site L Wb STK s) (m : MulOk L Wb h f g) :
    Covers (mulRd L f g ++ mulWr L h) (s.rd ++ s.wr) ∧ Covers (mulWr L h) s.wr :=
  ⟨Covers.append_left (covers_cons' (hs.crE m.pf) (covers_cons' (hs.crE m.pg) covers_nil'))
    (Covers.right (covers_cons' (hs.cwE m.ph m.wh) covers_nil')), covers_cons' (hs.cwE m.ph m.wh) covers_nil'⟩

theorem mul_ok {c : Prog isa} (hc : Callee c (fun stk => mulContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : MulOk L Wb h f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri h 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L h) (multiplyNTT (polyAt s.mem (lpa L f)) (polyAt s.mem (lpa L g))) → Q s') :
    WP isa (callAt name c (mulArgs h f g)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := mul_cov hs m
  refine callV hver.1 m.hg (mul_preS hs (Nat.le_trans hstk hS) m rf rg) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [tri h 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1, g2⟩ := mulG hs m (mulRd L f g) (mulWr L h)
  have := mul_post hp
  rwa [State.withRegions_mem, g0, g1, g2, hs.addrE m.ph (by decide), hs.addrE m.pf (by decide),
    hs.addrE m.pg (by decide), view_glue_mem] at this

theorem mulAdd_ok {c : Prog isa} (hc : Callee c (fun stk => mulAddContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : MulOk L Wb h f g)
    (rh : Reduced s.mem (lpa L h)) (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri h 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L h) (add (polyAt s.mem (lpa L h))
        (multiplyNTT (polyAt s.mem (lpa L f)) (polyAt s.mem (lpa L g)))) → Q s') :
    WP isa (callAt name c (mulArgs h f g)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := mul_cov hs m
  refine callV hver.1 m.hg (mulAdd_preS hs (Nat.le_trans hstk hS) m rh rf rg) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [tri h 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1, g2⟩ := mulG hs m (mulRd L f g) (mulWr L h)
  have := mulAdd_post hp
  rwa [State.withRegions_mem, g0, g1, g2, hs.addrE m.ph (by decide), hs.addrE m.pf (by decide),
    hs.addrE m.pg (by decide), view_glue_mem] at this

theorem mul_tr {c : Prog isa} (hc : Callee c (fun stk => mulContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : MulOk L Wb h f g) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L f) ∧
      Reduced x.mem (lpa L g) ∧ Reduced y.mem (lpa L f) ∧ Reduced y.mem (lpa L g)) :
    RelCT isa P (callAt name c (mulArgs h f g)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rfx, rgx, rfy, rgy⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2⟩ := mulG hx m (mulRd L f g) (mulWr L h)
  obtain ⟨gy0, gy1, gy2⟩ := mulG hy m (mulRd L f g) (mulWr L h)
  refine ⟨mulRd L f g, mulWr L h, mul_preS hx (Nat.le_trans hstk hS) m rfx rgx,
    mul_preS hy (Nat.le_trans hstk hS) m rfy rgy, mul_pub (by rw [view_glue_sp, view_glue_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]), (mul_cov hx m).1, (mul_cov hx m).2,
    (mul_cov hy m).1, (mul_cov hy m).2⟩

theorem mulAdd_tr {c : Prog isa} (hc : Callee c (fun stk => mulAddContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : MulOk L Wb h f g) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L h) ∧
      Reduced x.mem (lpa L f) ∧ Reduced x.mem (lpa L g) ∧ Reduced y.mem (lpa L h) ∧ Reduced y.mem (lpa L f) ∧
      Reduced y.mem (lpa L g)) :
    RelCT isa P (callAt name c (mulArgs h f g)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rhx, rfx, rgx, rhy, rfy, rgy⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2⟩ := mulG hx m (mulRd L f g) (mulWr L h)
  obtain ⟨gy0, gy1, gy2⟩ := mulG hy m (mulRd L f g) (mulWr L h)
  refine ⟨mulRd L f g, mulWr L h, mulAdd_preS hx (Nat.le_trans hstk hS) m rhx rfx rgx,
    mulAdd_preS hy (Nat.le_trans hstk hS) m rhy rfy rgy, mulAdd_pub (by rw [view_glue_sp, view_glue_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]), (mul_cov hx m).1, (mul_cov hx m).2,
    (mul_cov hy m).1, (mul_cov hy m).2⟩

end

/-! ## `vg_mldsa_add`, `vg_mldsa_sub` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {f g : Ptr}

abbrev accArgs (f g : Ptr) : List (Reg × Arg) := [(.r0, .ptr f), (.r1, .ptr g)]
abbrev accRd (L : Lay) (g : Ptr) : List Region := [L.R (ix g.1) g.2 1024]
abbrev accWr (L : Lay) (f : Ptr) : List Region := [L.R (ix f.1) f.2 1024]

/-- The facts the additions need of their pointers. -/
structure AccOk (L : Lay) (Wb : List Nat) (f g : Ptr) : Prop where
  pf : PtrIn L f 1024
  pg : PtrIn L g 1024
  wf : ix f.1 ∈ Wb
  d1 : sepB L.sizes (tri f 1024) (tri g 1024) = true

theorem AccOk.hg (m : AccOk L Wb f g) : glueOk (accArgs f g) = true := by
  simp [glueOk, m.pf.1, m.pg.1]

theorem accArgs_nodup : ((accArgs f g).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem accG {s : State} (hs : Site L Wb STK s) (m : AccOk L Wb f g) (rd wr : List Region) :
    (view (glueSt s (accArgs f g)) rd wr).gpr .r0 = L.ptr (ix f.1) + BitVec.ofNat 32 f.2 ∧
    (view (glueSt s (accArgs f g)) rd wr).gpr .r1 = L.ptr (ix g.1) + BitVec.ofNat 32 g.2 :=
  ⟨by rw [view_r0, hs.gE m.hg accArgs_nodup (by simp) m.pf.1],
    by rw [view_r1, hs.gE m.hg accArgs_nodup (by simp) m.pg.1]⟩

theorem acc_cov {s : State} (hs : Site L Wb STK s) (m : AccOk L Wb f g) :
    Covers (accRd L g ++ accWr L f) (s.rd ++ s.wr) ∧ Covers (accWr L f) s.wr :=
  ⟨Covers.append_left (covers_cons' (hs.crE m.pg) covers_nil') (Covers.right (covers_cons' (hs.cwE m.pf m.wf) covers_nil')),
    covers_cons' (hs.cwE m.pf m.wf) covers_nil'⟩

theorem add_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : AccOk L Wb f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) :
    (addContract Arm.abi stk).pre (view (glueSt s (accArgs f g)) (accRd L g) (accWr L f)) := by
  have hsp := view_glue_sp s (accArgs f g) (accRd L g) (accWr L f)
  obtain ⟨g0, g1⟩ := accG hs m (accRd L g) (accWr L f)
  refine add_pre g0 g1 (by rw [State.withRegions_rd, hs.regE m.pg (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.pf (by decide)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    ?_ ?_ ?_ (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_
  · rw [hs.regE m.pf (by decide), hs.regE m.pg (by decide)]; exact hs.dE m.d1 (.inl m.wf)
  · rw [hs.regE m.pf (by decide)]; exact hs.kE m.pf hstk hsp
  · rw [hs.regE m.pg (by decide)]; exact hs.kE m.pg hstk hsp
  · rw [view_glue_mem, hs.addrE m.pf (by decide)]; exact rf
  · rw [view_glue_mem, hs.addrE m.pg (by decide)]; exact rg

theorem sub_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : AccOk L Wb f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) :
    (subContract Arm.abi stk).pre (view (glueSt s (accArgs f g)) (accRd L g) (accWr L f)) := by
  have hsp := view_glue_sp s (accArgs f g) (accRd L g) (accWr L f)
  obtain ⟨g0, g1⟩ := accG hs m (accRd L g) (accWr L f)
  refine sub_pre g0 g1 (by rw [State.withRegions_rd, hs.regE m.pg (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.pf (by decide)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    ?_ ?_ ?_ (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_
  · rw [hs.regE m.pf (by decide), hs.regE m.pg (by decide)]; exact hs.dE m.d1 (.inl m.wf)
  · rw [hs.regE m.pf (by decide)]; exact hs.kE m.pf hstk hsp
  · rw [hs.regE m.pg (by decide)]; exact hs.kE m.pg hstk hsp
  · rw [view_glue_mem, hs.addrE m.pf (by decide)]; exact rf
  · rw [view_glue_mem, hs.addrE m.pg (by decide)]; exact rg

theorem add_ok {c : Prog isa} (hc : Callee c (fun stk => addContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : AccOk L Wb f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri f 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L f) (add (polyAt s.mem (lpa L f)) (polyAt s.mem (lpa L g))) → Q s') :
    WP isa (callAt name c (accArgs f g)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := acc_cov hs m
  refine callV hver.1 m.hg (add_preS hs (Nat.le_trans hstk hS) m rf rg) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [tri f 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1⟩ := accG hs m (accRd L g) (accWr L f)
  have := add_post hp
  rwa [State.withRegions_mem, g0, g1, hs.addrE m.pf (by decide), hs.addrE m.pg (by decide), view_glue_mem] at this

theorem sub_ok {c : Prog isa} (hc : Callee c (fun stk => subContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : AccOk L Wb f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri f 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L f) (sub (polyAt s.mem (lpa L f)) (polyAt s.mem (lpa L g))) → Q s') :
    WP isa (callAt name c (accArgs f g)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := acc_cov hs m
  refine callV hver.1 m.hg (sub_preS hs (Nat.le_trans hstk hS) m rf rg) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [tri f 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1⟩ := accG hs m (accRd L g) (accWr L f)
  have := sub_post hp
  rwa [State.withRegions_mem, g0, g1, hs.addrE m.pf (by decide), hs.addrE m.pg (by decide), view_glue_mem] at this

theorem add_tr {c : Prog isa} (hc : Callee c (fun stk => addContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : AccOk L Wb f g) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L f) ∧
      Reduced x.mem (lpa L g) ∧ Reduced y.mem (lpa L f) ∧ Reduced y.mem (lpa L g)) :
    RelCT isa P (callAt name c (accArgs f g)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rfx, rgx, rfy, rgy⟩ := hP x y hxy
  obtain ⟨gx0, gx1⟩ := accG hx m (accRd L g) (accWr L f)
  obtain ⟨gy0, gy1⟩ := accG hy m (accRd L g) (accWr L f)
  exact ⟨accRd L g, accWr L f, add_preS hx (Nat.le_trans hstk hS) m rfx rgx,
    add_preS hy (Nat.le_trans hstk hS) m rfy rgy, add_pub (by rw [view_glue_sp, view_glue_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]), (acc_cov hx m).1, (acc_cov hx m).2, (acc_cov hy m).1, (acc_cov hy m).2⟩

theorem sub_tr {c : Prog isa} (hc : Callee c (fun stk => subContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : AccOk L Wb f g) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L f) ∧
      Reduced x.mem (lpa L g) ∧ Reduced y.mem (lpa L f) ∧ Reduced y.mem (lpa L g)) :
    RelCT isa P (callAt name c (accArgs f g)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rfx, rgx, rfy, rgy⟩ := hP x y hxy
  obtain ⟨gx0, gx1⟩ := accG hx m (accRd L g) (accWr L f)
  obtain ⟨gy0, gy1⟩ := accG hy m (accRd L g) (accWr L f)
  exact ⟨accRd L g, accWr L f, sub_preS hx (Nat.le_trans hstk hS) m rfx rgx,
    sub_preS hy (Nat.le_trans hstk hS) m rfy rgy, sub_pub (by rw [view_glue_sp, view_glue_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]), (acc_cov hx m).1, (acc_cov hx m).2, (acc_cov hy m).1, (acc_cov hy m).2⟩

end

end VG.Proof.MlDsa.Arm.KeyGen
