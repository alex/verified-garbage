import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Call

/-!
# ML-DSA on 32-bit ARM: calling `Power2Round` and the encodings of key generation

Untrusted: everything here is checked by Lean. As `ip_ok` and `ip_tr`
(`Call.lean`), for `vg_mldsa_power2round`, `vg_mldsa_simple_bit_pack` and
`vg_mldsa_bit_pack`, whose fifth argument, the length, is on the stack.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_power2round` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {t t1 t0 : Ptr}

abbrev p2rArgs (t t1 t0 : Ptr) : List (Reg × Arg) := [(.r0, .ptr t), (.r1, .ptr t1), (.r2, .ptr t0)]
abbrev p2rRd (L : Lay) (t : Ptr) : List Region := [L.R (ix t.1) t.2 1024]
abbrev p2rWr (L : Lay) (t1 t0 : Ptr) : List Region := [L.R (ix t1.1) t1.2 1024, L.R (ix t0.1) t0.2 1024]

/-- The facts `vg_mldsa_power2round` needs of its pointers. -/
structure P2rOk (L : Lay) (Wb : List Nat) (t t1 t0 : Ptr) : Prop where
  pt : PtrIn L t 1024
  p1 : PtrIn L t1 1024
  p0 : PtrIn L t0 1024
  w1 : ix t1.1 ∈ Wb
  w0 : ix t0.1 ∈ Wb
  d1 : sepB L.sizes (tri t 1024) (tri t1 1024) = true
  d2 : sepB L.sizes (tri t 1024) (tri t0 1024) = true
  d3 : sepB L.sizes (tri t1 1024) (tri t0 1024) = true

theorem P2rOk.hg (m : P2rOk L Wb t t1 t0) : glueOk (p2rArgs t t1 t0) = true := by
  simp [glueOk, m.pt.1, m.p1.1, m.p0.1]

theorem p2rArgs_nodup : ((p2rArgs t t1 t0).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem p2rG {s : State} (hs : Site L Wb STK s) (m : P2rOk L Wb t t1 t0) (rd wr : List Region) :
    (view (glueSt s (p2rArgs t t1 t0)) rd wr).gpr .r0 = L.ptr (ix t.1) + BitVec.ofNat 32 t.2 ∧
    (view (glueSt s (p2rArgs t t1 t0)) rd wr).gpr .r1 = L.ptr (ix t1.1) + BitVec.ofNat 32 t1.2 ∧
    (view (glueSt s (p2rArgs t t1 t0)) rd wr).gpr .r2 = L.ptr (ix t0.1) + BitVec.ofNat 32 t0.2 :=
  ⟨by rw [view_r0, hs.gE m.hg p2rArgs_nodup (by simp) m.pt.1],
    by rw [view_r1, hs.gE m.hg p2rArgs_nodup (by simp) m.p1.1],
    by rw [view_r2, hs.gE m.hg p2rArgs_nodup (by simp) m.p0.1]⟩

theorem p2r_cov {s : State} (hs : Site L Wb STK s) (m : P2rOk L Wb t t1 t0) :
    Covers (p2rRd L t ++ p2rWr L t1 t0) (s.rd ++ s.wr) ∧ Covers (p2rWr L t1 t0) s.wr :=
  ⟨covers_append (covers_cons' (hs.crE m.pt) covers_nil')
    (covers_wr (covers_cons' (hs.cwE m.p1 m.w1) (covers_cons' (hs.cwE m.p0 m.w0) covers_nil'))),
    covers_cons' (hs.cwE m.p1 m.w1) (covers_cons' (hs.cwE m.p0 m.w0) covers_nil')⟩

theorem p2r_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : P2rOk L Wb t t1 t0)
    (hr : Reduced s.mem (lpa L t)) :
    (power2RoundContract Arm.abi stk).pre (view (glueSt s (p2rArgs t t1 t0)) (p2rRd L t) (p2rWr L t1 t0)) := by
  have hsp := view_glue_sp s (p2rArgs t t1 t0) (p2rRd L t) (p2rWr L t1 t0)
  obtain ⟨g0, g1, g2⟩ := p2rG hs m (p2rRd L t) (p2rWr L t1 t0)
  refine p2r_pre g0 g1 g2 (by rw [State.withRegions_rd, hs.regE m.pt (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.p1 (by decide), hs.regE m.p0 (by decide)])
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_ ?_ ?_ ?_
    (hs.fitE m.pt (by decide)) (hs.fitE m.p1 (by decide)) (hs.fitE m.p0 (by decide)) ?_
  · rw [hs.regE m.pt (by decide), hs.regE m.p1 (by decide)]; exact hs.dE m.d1 (.inr m.w1)
  · rw [hs.regE m.pt (by decide), hs.regE m.p0 (by decide)]; exact hs.dE m.d2 (.inr m.w0)
  · rw [hs.regE m.p1 (by decide), hs.regE m.p0 (by decide)]; exact hs.dE m.d3 (.inl m.w1)
  · rw [hs.regE m.pt (by decide)]; exact hs.kE m.pt hstk hsp
  · rw [hs.regE m.p1 (by decide)]; exact hs.kE m.p1 hstk hsp
  · rw [hs.regE m.p0 (by decide)]; exact hs.kE m.p0 hstk hsp
  · rw [view_glue_mem, hs.addrE m.pt (by decide)]; exact hr

theorem p2r_ok {c : Prog isa} (hc : Callee c (fun stk => power2RoundContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : P2rOk L Wb t t1 t0) (hr : Reduced s.mem (lpa L t))
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri t1 1024, tri t0 1024, (1, 0, STK)]) s s' →
      NatPolyIs s'.mem (lpa L t1) ((polyAt s.mem (lpa L t)).map fun c => (power2Round c).1.toNat) →
      PolyIs s'.mem (lpa L t0) ((polyAt s.mem (lpa L t)).map fun c => ofInt (power2Round c).2) → Q s') :
    WP isa (callAt name c (p2rArgs t t1 t0)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := p2r_cov hs m
  refine callV hver.1 m.hg (p2r_preS hs (Nat.le_trans hstk hS) m hr) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [tri t1 1024, tri t0 1024] (Nat.le_trans hc.stack hS) hk) ?_ ?_
  all_goals
    obtain ⟨g0, g1, g2⟩ := p2rG hs m (p2rRd L t) (p2rWr L t1 t0)
    have := p2r_post hp
    rw [State.withRegions_mem, g0, g1, g2, hs.addrE m.pt (by decide), hs.addrE m.p1 (by decide),
      hs.addrE m.p0 (by decide), view_glue_mem] at this
  exacts [this.1, this.2]

theorem p2r_tr {c : Prog isa} (hc : Callee c (fun stk => power2RoundContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : P2rOk L Wb t t1 t0) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L t) ∧
      Reduced y.mem (lpa L t)) :
    RelCT isa P (callAt name c (p2rArgs t t1 t0)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2⟩ := p2rG hx m (p2rRd L t) (p2rWr L t1 t0)
  obtain ⟨gy0, gy1, gy2⟩ := p2rG hy m (p2rRd L t) (p2rWr L t1 t0)
  exact ⟨p2rRd L t, p2rWr L t1 t0, p2r_preS hx (Nat.le_trans hstk hS) m rx, p2r_preS hy (Nat.le_trans hstk hS) m ry,
    p2r_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]),
    (p2r_cov hx m).1, (p2r_cov hx m).2, (p2r_cov hy m).1, (p2r_cov hy m).2⟩

end

/-! ## `vg_mldsa_simple_bit_pack` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {f o : Ptr} {b l : Nat}

abbrev sbpArgs (f : Ptr) (b : Nat) (o : Ptr) (l : Nat) : List (Reg × Arg) :=
  [(.r0, .ptr f), (.r1, .imm b), (.r2, .ptr o), (.r3, .imm l)]
abbrev sbpRd (L : Lay) (f : Ptr) : List Region := [L.R (ix f.1) f.2 1024]
abbrev sbpWr (L : Lay) (o : Ptr) (l : Nat) : List Region := [L.R (ix o.1) o.2 l]

/-- The facts `vg_mldsa_simple_bit_pack` needs of its arguments. -/
structure SbpOk (L : Lay) (Wb : List Nat) (f : Ptr) (b : Nat) (o : Ptr) (l : Nat) : Prop where
  pf : PtrIn L f 1024
  po : PtrIn L o l
  wo : ix o.1 ∈ Wb
  d1 : sepB L.sizes (tri f 1024) (tri o l) = true
  hb : b ∈ simpleBitPackBounds
  hl : l = 32 * bitlen b

theorem SbpOk.lt (m : SbpOk L Wb f b o l) : b < 2 ^ 32 ∧ 0 < l ∧ l < 2 ^ 32 := by
  have hb := m.hb
  simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
  rw [m.hl]
  rcases hb with rfl | rfl | rfl <;> decide

theorem SbpOk.hg (m : SbpOk L Wb f b o l) : glueOk (sbpArgs f b o l) = true := by
  simp [glueOk, m.pf.1, m.po.1, show ∀ v, argOk (.imm v) = true from fun _ => rfl]

theorem sbpArgs_nodup : ((sbpArgs f b o l).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem sbpG {s : State} (hs : Site L Wb STK s) (m : SbpOk L Wb f b o l) (rd wr : List Region) :
    (view (glueSt s (sbpArgs f b o l)) rd wr).gpr .r0 = L.ptr (ix f.1) + BitVec.ofNat 32 f.2 ∧
    (view (glueSt s (sbpArgs f b o l)) rd wr).gpr .r1 = BitVec.ofNat 32 b ∧
    (view (glueSt s (sbpArgs f b o l)) rd wr).gpr .r2 = L.ptr (ix o.1) + BitVec.ofNat 32 o.2 ∧
    (view (glueSt s (sbpArgs f b o l)) rd wr).gpr .r3 = BitVec.ofNat 32 l :=
  ⟨by rw [view_r0, hs.gE m.hg sbpArgs_nodup (by simp) m.pf.1],
    by rw [view_r1, glueSt_arg s m.hg sbpArgs_nodup (a := .imm b) (by simp)]; rfl,
    by rw [view_r2, hs.gE m.hg sbpArgs_nodup (by simp) m.po.1],
    by rw [view_r3, glueSt_arg s m.hg sbpArgs_nodup (a := .imm l) (by simp)]; rfl⟩

theorem sbp_cov {s : State} (hs : Site L Wb STK s) (m : SbpOk L Wb f b o l) :
    Covers (sbpRd L f ++ sbpWr L o l) (s.rd ++ s.wr) ∧ Covers (sbpWr L o l) s.wr :=
  ⟨covers_append (covers_cons' (hs.crE m.pf) covers_nil') (covers_wr (covers_cons' (hs.cwE m.po m.wo) covers_nil')),
    covers_cons' (hs.cwE m.po m.wo) covers_nil'⟩

theorem sbp_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : SbpOk L Wb f b o l)
    (hc : ∀ i < n, (coeffAt s.mem (lpa L f) i).toNat ≤ b) :
    (simpleBitPackContract Arm.abi stk).pre (view (glueSt s (sbpArgs f b o l)) (sbpRd L f) (sbpWr L o l)) := by
  have hsp := view_glue_sp s (sbpArgs f b o l) (sbpRd L f) (sbpWr L o l)
  obtain ⟨g0, g1, g2, g3⟩ := sbpG hs m (sbpRd L f) (sbpWr L o l)
  obtain ⟨lb, l0, ll⟩ := m.lt
  refine sbp_pre g0 g1 g2 g3 (by rw [State.withRegions_rd, hs.regE m.pf (by decide)])
    (by rw [State.withRegions_wr, imm_toNat ll, hs.regE m.po l0]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    ?_ ?_ ?_ (hs.fitE m.pf (by decide)) (by rw [imm_toNat ll]; exact hs.fitE m.po l0)
    (by rw [imm_toNat lb]; exact m.hb) (by rw [imm_toNat ll, imm_toNat lb]; exact m.hl) ?_
  · rw [imm_toNat ll, hs.regE m.pf (by decide), hs.regE m.po l0]; exact hs.dE m.d1 (.inr m.wo)
  · rw [hs.regE m.pf (by decide)]; exact hs.kE m.pf hstk hsp
  · rw [imm_toNat ll, hs.regE m.po l0]; exact hs.kE m.po hstk hsp
  · rw [view_glue_mem, hs.addrE m.pf (by decide), imm_toNat lb]; exact hc

theorem sbp_ok {c : Prog isa} (hc : Callee c (fun stk => simpleBitPackContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : SbpOk L Wb f b o l)
    (hcf : ∀ i < n, (coeffAt s.mem (lpa L f) i).toNat ≤ b) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri o l, (1, 0, STK)]) s s' →
      bytesAt s'.mem (lpa L o) l = simpleBitPack (natPolyAt s.mem (lpa L f)) b → Q s') :
    WP isa (callAt name c (sbpArgs f b o l)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := sbp_cov hs m
  obtain ⟨lb, l0, ll⟩ := m.lt
  refine callV hver.1 m.hg (sbp_preS hs (Nat.le_trans hstk hS) m hcf) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [tri o l] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1, g2, g3⟩ := sbpG hs m (sbpRd L f) (sbpWr L o l)
  have := sbp_post hp
  rwa [State.withRegions_mem, g0, g1, g2, g3, hs.addrE m.pf (by decide), hs.addrE m.po l0, view_glue_mem,
    imm_toNat lb, imm_toNat ll] at this

theorem sbp_tr {c : Prog isa} (hc : Callee c (fun stk => simpleBitPackContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : SbpOk L Wb f b o l) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      (∀ i < n, (coeffAt x.mem (lpa L f) i).toNat ≤ b) ∧ (∀ i < n, (coeffAt y.mem (lpa L f) i).toNat ≤ b)) :
    RelCT isa P (callAt name c (sbpArgs f b o l)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2, gx3⟩ := sbpG hx m (sbpRd L f) (sbpWr L o l)
  obtain ⟨gy0, gy1, gy2, gy3⟩ := sbpG hy m (sbpRd L f) (sbpWr L o l)
  exact ⟨sbpRd L f, sbpWr L o l, sbp_preS hx (Nat.le_trans hstk hS) m rx, sbp_preS hy (Nat.le_trans hstk hS) m ry,
    sbp_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2])
      (by rw [gx3, gy3]), (sbp_cov hx m).1, (sbp_cov hx m).2, (sbp_cov hy m).1, (sbp_cov hy m).2⟩

end

/-! ## `vg_mldsa_bit_pack` -/

/-- The stack slot of a fifth argument, below the stack pointer. -/
abbrev argR (s : State) : Region := ⟨State.addr (s.sp - BitVec.ofNat 32 4), 4⟩

/-- What a callee in a frame may access: its buffers, and its stack argument. -/
theorem push_cov {s : State} (as : List (Reg × Arg)) {rd wr : List Region}
    (c1 : Covers (rd ++ wr) (s.rd ++ s.wr)) (c2 : Covers wr s.wr) :
    Covers ((rd ++ [argR s]) ++ wr) ((pushed [.r12] (glueSt s as)).rd ++ (pushed [.r12] (glueSt s as)).wr) ∧
      Covers wr (pushed [.r12] (glueSt s as)).wr := by
  have hw : (pushed [.r12] (glueSt s as)).wr = argR s :: s.wr := by
    rw [pushed_wr, glueSt_sp, glueSt_wr]; rfl
  rw [pushed_rd, glueSt_rd, hw]
  refine ⟨fun x n ⟨r, hr, hc⟩ => ?_, fun x n ⟨r, hr, hc⟩ => ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (hr | rfl) | hr
    · obtain ⟨r', hr', hc'⟩ := c1 x n ⟨r, List.mem_append_left _ hr, hc⟩
      refine ⟨r', ?_, hc'⟩
      rcases List.mem_append.mp hr' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), hc⟩
    · obtain ⟨r', hr', hc'⟩ := c1 x n ⟨r, List.mem_append_right _ hr, hc⟩
      refine ⟨r', ?_, hc'⟩
      rcases List.mem_append.mp hr' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  · obtain ⟨r', hr', hc'⟩ := c2 x n ⟨r, hr, hc⟩
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {f o : Ptr} {a b l : Nat}

abbrev bpArgs (f : Ptr) (a b : Nat) (o : Ptr) : List (Reg × Arg) :=
  [(.r0, .ptr f), (.r1, .imm a), (.r2, .imm b), (.r3, .ptr o)]
abbrev bpAll (f : Ptr) (a b : Nat) (o : Ptr) (l : Nat) : List (Reg × Arg) := bpArgs f a b o ++ [(.r12, .imm l)]

/-- The facts `vg_mldsa_bit_pack` needs of its arguments. -/
structure BpOk (L : Lay) (Wb : List Nat) (f : Ptr) (a b : Nat) (o : Ptr) (l : Nat) : Prop where
  pf : PtrIn L f 1024
  po : PtrIn L o l
  wo : ix o.1 ∈ Wb
  d1 : sepB L.sizes (tri f 1024) (tri o l) = true
  hab : (a, b) ∈ bitPackParams
  hl : l = 32 * bitlen (a + b)

theorem BpOk.lt (m : BpOk L Wb f a b o l) : a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ 0 < l ∧ l < 2 ^ 32 := by
  have hab := m.hab
  simp only [bitPackParams, d, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
  rw [m.hl]
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem BpOk.hg (m : BpOk L Wb f a b o l) : glueOk (bpAll f a b o l) = true := by
  simp [glueOk, m.pf.1, m.po.1, show ∀ v, argOk (.imm v) = true from fun _ => rfl]

theorem bpAll_nodup : ((bpAll f a b o l).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]; decide

theorem bpG {s : State} (hs : Site L Wb STK s) (m : BpOk L Wb f a b o l) (rd wr : List Region) :
    (view (pushed [.r12] (glueSt s (bpAll f a b o l))) rd wr).gpr .r0 = L.ptr (ix f.1) + BitVec.ofNat 32 f.2 ∧
    (view (pushed [.r12] (glueSt s (bpAll f a b o l))) rd wr).gpr .r1 = BitVec.ofNat 32 a ∧
    (view (pushed [.r12] (glueSt s (bpAll f a b o l))) rd wr).gpr .r2 = BitVec.ofNat 32 b ∧
    (view (pushed [.r12] (glueSt s (bpAll f a b o l))) rd wr).gpr .r3 = L.ptr (ix o.1) + BitVec.ofNat 32 o.2 ∧
    stackArg (view (pushed [.r12] (glueSt s (bpAll f a b o l))) rd wr) 0 = BitVec.ofNat 32 l :=
  ⟨by rw [view_r0, pushed_gpr, hs.gE m.hg bpAll_nodup (by simp) m.pf.1],
    by rw [view_r1, pushed_gpr, glueSt_arg s m.hg bpAll_nodup (a := .imm a) (by simp)]; rfl,
    by rw [view_r2, pushed_gpr, glueSt_arg s m.hg bpAll_nodup (a := .imm b) (by simp)]; rfl,
    by rw [view_r3, pushed_gpr, hs.gE m.hg bpAll_nodup (by simp) m.po.1],
    by rw [push_arg, glueSt_arg s m.hg bpAll_nodup (a := .imm l) (by simp)]; rfl⟩

theorem bp_cov {s : State} (hs : Site L Wb STK s) (m : BpOk L Wb f a b o l) :
    Covers (sbpRd L f ++ sbpWr L o l) (s.rd ++ s.wr) ∧ Covers (sbpWr L o l) s.wr :=
  ⟨covers_append (covers_cons' (hs.crE m.pf) covers_nil') (covers_wr (covers_cons' (hs.cwE m.po m.wo) covers_nil')),
    covers_cons' (hs.cwE m.po m.wo) covers_nil'⟩

theorem bp_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : 4 + stk ≤ STK) (m : BpOk L Wb f a b o l)
    (hr : Reduced s.mem (lpa L f))
    (hc : ∀ i < n, -(a : Int) ≤ modPm (coeffAt s.mem (lpa L f) i).toNat q ∧ modPm (coeffAt s.mem (lpa L f) i).toNat q ≤ b) :
    (bitPackContract Arm.abi stk).pre
      (view (pushed [.r12] (glueSt s (bpAll f a b o l))) (sbpRd L f ++ [argR s]) (sbpWr L o l)) := by
  have e1 := glueSt_sp s (bpAll f a b o l)
  have hm := glueSt_mem s (bpAll f a b o l)
  obtain ⟨g0, g1, g2, g3, ga⟩ := bpG hs m (sbpRd L f ++ [argR s]) (sbpWr L o l)
  obtain ⟨la, lb, l0, ll⟩ := m.lt
  have h4 := sp4 hs
  refine bp_pre g0 g1 g2 g3 ga
    (by rw [State.withRegions_rd, hs.regE m.pf (by decide), push_argAddr _ e1]; rfl)
    (by rw [State.withRegions_wr, imm_toNat ll, hs.regE m.po l0])
    (by rw [push_spN _ e1 _ _ h4]; have := hs.spk; omega) (push_fit _ _ _ h4 e1)
    ?_ ?_ ?_ ?_ ?_ (hs.fitE m.pf (by decide)) (by rw [imm_toNat ll]; exact hs.fitE m.po l0)
    (by rw [imm_toNat la, imm_toNat lb]; exact m.hab) (by rw [imm_toNat la, imm_toNat lb, imm_toNat ll]; exact m.hl)
    (by rw [hs.addrE m.pf (by decide), push_reduced hs e1 hm _ _ m.pf]; exact hr) ?_
  · rw [imm_toNat ll, hs.regE m.pf (by decide), hs.regE m.po l0]; exact hs.dE m.d1 (.inr m.wo)
  · rw [imm_toNat ll, hs.regE m.po l0]; exact push_aE hs _ e1 _ _ m.po
  · rw [hs.regE m.pf (by decide)]; exact push_kE hs _ e1 _ _ m.pf hstk
  · rw [imm_toNat ll, hs.regE m.po l0]; exact push_kE hs _ e1 _ _ m.po hstk
  · exact push_kA hs _ e1 _ _ hstk
  · intro i hi
    rw [hs.addrE m.pf (by decide), push_coeffAt hs e1 hm _ _ m.pf hi, imm_toNat la, imm_toNat lb]
    exact hc i hi

theorem bp_ok {c : Prog isa} (hc : Callee c (fun stk => bitPackContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : 4 + S ≤ STK) {name : String} (m : BpOk L Wb f a b o l)
    (hr : Reduced s.mem (lpa L f))
    (hcf : ∀ i < n, -(a : Int) ≤ modPm (coeffAt s.mem (lpa L f) i).toNat q ∧
      modPm (coeffAt s.mem (lpa L f) i).toNat q ≤ b) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri o l, (1, 0, STK)]) s s' →
      bytesAt s'.mem (lpa L o) l = bitPack ((polyAt s.mem (lpa L f)).map fun c => modPm c.val q) a b → Q s') :
    WP isa (callAtS name c (bpArgs f a b o) (.imm l)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := bp_cov hs m
  obtain ⟨la, lb, l0, ll⟩ := m.lt
  have e1 := glueSt_sp s (bpAll f a b o l)
  have hm := glueSt_mem s (bpAll f a b o l)
  refine callVS hver.1 m.hg (bp_preS hs (by omega) m hr hcf) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk h3 =>
      hQ s' (hs.keptW [tri o l] (by have := hc.stack; omega) hk) ?_
  obtain ⟨s₃, hm₃, -, hp⟩ := h3
  obtain ⟨g0, g1, g2, g3, ga⟩ := bpG hs m (sbpRd L f ++ [argR s]) (sbpWr L o l)
  have := bp_post hp
  rwa [State.withRegions_mem, hm₃, g0, g1, g2, g3, ga, hs.addrE m.pf (by decide), hs.addrE m.po l0,
    push_polyAt hs e1 hm _ _ m.pf, imm_toNat la, imm_toNat lb, imm_toNat ll] at this

theorem bp_tr {c : Prog isa} (hc : Callee c (fun stk => bitPackContract Arm.abi stk) S) (hS : 4 + S ≤ STK)
    {name : String} (m : BpOk L Wb f a b o l) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L f) ∧
      Reduced y.mem (lpa L f) ∧
      (∀ i < n, -(a : Int) ≤ modPm (coeffAt x.mem (lpa L f) i).toNat q ∧
        modPm (coeffAt x.mem (lpa L f) i).toNat q ≤ b) ∧
      (∀ i < n, -(a : Int) ≤ modPm (coeffAt y.mem (lpa L f) i).toNat q ∧
        modPm (coeffAt y.mem (lpa L f) i).toNat q ≤ b)) :
    RelCT isa P (callAtS name c (bpArgs f a b o) (.imm l)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callVS_tr hver.1 hver.2.1 m.hg (fun x y h => (hP x y h).2.2.1)
    (fun x y h => ⟨sp4 (hP x y h).1, sp4 (hP x y h).2.1⟩) fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry, cx, cy⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2, gx3, gxa⟩ := bpG hx m (sbpRd L f ++ [argR x]) (sbpWr L o l)
  obtain ⟨gy0, gy1, gy2, gy3, gya⟩ := bpG hy m (sbpRd L f ++ [argR x]) (sbpWr L o l)
  have ex : argR y = argR x := by simp only [argR, hsp]
  refine ⟨sbpRd L f ++ [argR x], sbpWr L o l, bp_preS hx (by omega) m rx cx, ?_,
    bp_pub (by simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, glueSt_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]) (by rw [gx3, gy3]) (by rw [gxa, gya]),
    ?_, ?_, ?_, ?_⟩
  · rw [← ex]; exact bp_preS hy (by omega) m ry cy
  · exact (push_cov _ (bp_cov hx m).1 (bp_cov hx m).2).1
  · exact (push_cov _ (bp_cov hx m).1 (bp_cov hx m).2).2
  · rw [← ex]; exact (push_cov _ (bp_cov hy m).1 (bp_cov hy m).2).1
  · exact (push_cov _ (bp_cov hy m).1 (bp_cov hy m).2).2

end

end VG.Proof.MlDsa.Arm.KeyGen
