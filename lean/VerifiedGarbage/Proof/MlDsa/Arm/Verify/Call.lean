import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.CallPack

/-!
# ML-DSA on 32-bit ARM: calling the primitives only verification uses

Untrusted: everything here is checked by Lean. As `ip_ok` and `ip_tr`
(`KeyGen/Call.lean`), in the buffers of a `Site`: `vg_mldsa_hint_bit_unpack`,
`vg_mldsa_bit_unpack` and `vg_mldsa_sample_in_ball` (whose fifth argument
is on the stack), `vg_mldsa_norm_lt`, `vg_mldsa_use_hint` and
`vg_mldsa_unpack_t1`.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen (Ptr Arg callAt callAtS)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_hint_bit_unpack` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {y h : Ptr} {len om hl : Nat}

abbrev hbuArgs (y : Ptr) (len om : Nat) (h : Ptr) : List (Reg × Arg) :=
  [(.r0, .ptr y), (.r1, .imm len), (.r2, .imm om), (.r3, .ptr h)]
abbrev hbuAll (y : Ptr) (len om : Nat) (h : Ptr) (hl : Nat) : List (Reg × Arg) :=
  hbuArgs y len om h ++ [(.r12, .imm hl)]
abbrev hbuRd (L : Lay) (y : Ptr) (len : Nat) : List Region := [L.R (ix y.1) y.2 len]
abbrev hbuWr (L : Lay) (h : Ptr) (hl : Nat) : List Region := [L.R (ix h.1) h.2 (hl * 4)]

/-- The facts `vg_mldsa_hint_bit_unpack` needs of its arguments. -/
structure HbuOk (L : Lay) (Wb : List Nat) (y : Ptr) (len om : Nat) (h : Ptr) (hl : Nat) : Prop where
  py : PtrIn L y len
  ph : PtrIn L h (hl * 4)
  wh : ix h.1 ∈ Wb
  d1 : sepB L.sizes (tri y len) (tri h (hl * 4)) = true
  hp : (om, len - om) ∈ hintParams
  ho : om ≤ len
  hh : hl = 256 * (len - om)
  lt : 0 < len ∧ len < 2 ^ 32 ∧ om < 2 ^ 32 ∧ 0 < hl * 4 ∧ hl < 2 ^ 32

theorem HbuOk.hg (m : HbuOk L Wb y len om h hl) : glueOk (hbuAll y len om h hl) = true := by
  simp [glueOk, m.py.1, m.ph.1, show ∀ v, argOk (.imm v) = true from fun _ => rfl]

theorem hbuAll_nodup : ((hbuAll y len om h hl).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]; decide

theorem hbuG {s : State} (hs : Site L Wb STK s) (m : HbuOk L Wb y len om h hl) (rd wr : List Region) :
    (view (pushed [.r12] (glueSt s (hbuAll y len om h hl))) rd wr).gpr .r0 = L.ptr (ix y.1) + BitVec.ofNat 32 y.2 ∧
    (view (pushed [.r12] (glueSt s (hbuAll y len om h hl))) rd wr).gpr .r1 = BitVec.ofNat 32 len ∧
    (view (pushed [.r12] (glueSt s (hbuAll y len om h hl))) rd wr).gpr .r2 = BitVec.ofNat 32 om ∧
    (view (pushed [.r12] (glueSt s (hbuAll y len om h hl))) rd wr).gpr .r3 = L.ptr (ix h.1) + BitVec.ofNat 32 h.2 ∧
    stackArg (view (pushed [.r12] (glueSt s (hbuAll y len om h hl))) rd wr) 0 = BitVec.ofNat 32 hl :=
  ⟨by rw [view_r0, pushed_gpr, hs.gE m.hg hbuAll_nodup (by simp) m.py.1],
    by rw [view_r1, pushed_gpr, glueSt_arg s m.hg hbuAll_nodup (a := .imm len) (by simp)]; rfl,
    by rw [view_r2, pushed_gpr, glueSt_arg s m.hg hbuAll_nodup (a := .imm om) (by simp)]; rfl,
    by rw [view_r3, pushed_gpr, hs.gE m.hg hbuAll_nodup (by simp) m.ph.1],
    by rw [push_arg, glueSt_arg s m.hg hbuAll_nodup (a := .imm hl) (by simp)]; rfl⟩

theorem hbu_cov {s : State} (hs : Site L Wb STK s) (m : HbuOk L Wb y len om h hl) :
    Covers (hbuRd L y len ++ hbuWr L h hl) (s.rd ++ s.wr) ∧ Covers (hbuWr L h hl) s.wr :=
  ⟨covers_append (covers_cons' (hs.crE m.py) covers_nil') (covers_wr (covers_cons' (hs.cwE m.ph m.wh) covers_nil')),
    covers_cons' (hs.cwE m.ph m.wh) covers_nil'⟩

theorem hbu_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : 4 + stk ≤ STK) (m : HbuOk L Wb y len om h hl) :
    (hintBitUnpackContract Arm.abi stk).pre
      (view (pushed [.r12] (glueSt s (hbuAll y len om h hl))) (hbuRd L y len ++ [argR s]) (hbuWr L h hl)) := by
  have e1 := glueSt_sp s (hbuAll y len om h hl)
  obtain ⟨g0, g1, g2, g3, ga⟩ := hbuG hs m (hbuRd L y len ++ [argR s]) (hbuWr L h hl)
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  have h4 := sp4 hs
  refine hbu_pre g0 g1 g2 g3 ga
    (by rw [State.withRegions_rd, imm_toNat ll, hs.regE m.py l0, push_argAddr _ e1]; rfl)
    (by rw [State.withRegions_wr, imm_toNat lh, hs.regE m.ph h0])
    (by rw [push_spN _ e1 _ _ h4]; have := hs.spk; omega) (push_fit _ _ _ h4 e1)
    ?_ ?_ ?_ ?_ ?_ (by rw [imm_toNat ll]; exact hs.fitE m.py l0) (by rw [imm_toNat lh]; exact hs.fitE m.ph h0)
    (by rw [imm_toNat lo, imm_toNat ll]; exact m.hp) (by rw [imm_toNat lo, imm_toNat ll]; exact m.ho)
    (by rw [imm_toNat lo, imm_toNat ll, imm_toNat lh]; exact m.hh)
  · rw [imm_toNat ll, imm_toNat lh, hs.regE m.py l0, hs.regE m.ph h0]; exact hs.dE m.d1 (.inr m.wh)
  · rw [imm_toNat lh, hs.regE m.ph h0]; exact push_aE hs _ e1 _ _ m.ph
  · rw [imm_toNat ll, hs.regE m.py l0]; exact push_kE hs _ e1 _ _ m.py hstk
  · rw [imm_toNat lh, hs.regE m.ph h0]; exact push_kE hs _ e1 _ _ m.ph hstk
  · exact push_kA hs _ e1 _ _ hstk

theorem hbu_okS {c : Prog isa} (hc : Callee c (fun stk => hintBitUnpackContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : 4 + S ≤ STK) {name : String} (m : HbuOk L Wb y len om h hl) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri h (hl * 4), (1, 0, STK)]) s s' →
      (match hintBitUnpack om (len - om) (bytesAt s.mem (lpa L y) len) with
        | some hint => s'.gpr .r0 = 1 ∧ HintIs s'.mem (lpa L h) (len - om) hint
        | none => s'.gpr .r0 = 0) → Q s') :
    WP isa (callAtS name c (hbuArgs y len om h) (.imm hl)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := hbu_cov hs m
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  have e1 := glueSt_sp s (hbuAll y len om h hl)
  have hm := glueSt_mem s (hbuAll y len om h hl)
  refine callVS hver.1 m.hg (hbu_preS hs (by omega) m) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk h3 =>
      hQ s' (hs.keptW [tri h (hl * 4)] (by have := hc.stack; omega) hk) ?_
  obtain ⟨s₃, hm₃, hr₃, hp⟩ := h3
  obtain ⟨g0, g1, g2, g3, -⟩ := hbuG hs m (hbuRd L y len ++ [argR s]) (hbuWr L h hl)
  have := hbu_post hp
  have hb := push_bytesAt hs e1 hm (hbuRd L y len ++ [argR s]) (hbuWr L h hl) m.py (by omega)
  rw [g0, g1, g2, g3, hs.addrE m.py l0, hs.addrE m.ph h0, imm_toNat ll, imm_toNat lo, hb] at this
  simp only [State.withRegions_mem, State.withRegions_gpr, hm₃, hr₃ .r0 (by decide)] at this
  exact this

theorem hbu_tr {c : Prog isa} (hc : Callee c (fun stk => hintBitUnpackContract Arm.abi stk) S) (hS : 4 + S ≤ STK)
    {name : String} (m : HbuOk L Wb y len om h hl) {P : State → State → Prop}
    (hP : ∀ x y', P x y' → Site L Wb STK x ∧ Site L Wb STK y' ∧ x.sp = y'.sp ∧
      bytesAt x.mem (lpa L y) len = bytesAt y'.mem (lpa L y) len) :
    RelCT isa P (callAtS name c (hbuArgs y len om h) (.imm hl)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  refine callVS_tr hver.1 hver.2.1 m.hg (fun x y h => (hP x y h).2.2.1)
    (fun x y h => ⟨sp4 (hP x y h).1, sp4 (hP x y h).2.1⟩) fun x y' hxy => ?_
  obtain ⟨hx, hy, hsp, hl'⟩ := hP x y' hxy
  obtain ⟨gx0, gx1, gx2, gx3, gxa⟩ := hbuG hx m (hbuRd L y len ++ [argR x]) (hbuWr L h hl)
  obtain ⟨gy0, gy1, gy2, gy3, gya⟩ := hbuG hy m (hbuRd L y len ++ [argR x]) (hbuWr L h hl)
  have ex : argR y' = argR x := by simp only [argR, hsp]
  have bx := push_bytesAt hx (glueSt_sp x (hbuAll y len om h hl)) (glueSt_mem x _) (hbuRd L y len ++ [argR x])
    (hbuWr L h hl) m.py (by omega)
  have by' := push_bytesAt hy (glueSt_sp y' (hbuAll y len om h hl)) (glueSt_mem y' _) (hbuRd L y len ++ [argR x])
    (hbuWr L h hl) m.py (by omega)
  refine ⟨hbuRd L y len ++ [argR x], hbuWr L h hl, hbu_preS hx (by omega) m, ?_,
    hbu_pub (by simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, glueSt_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]) (by rw [gx3, gy3]) (by rw [gxa, gya]) ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← ex]; exact hbu_preS hy (by omega) m
  · rw [gx0, gy0, gx1, gy1, hx.addrE m.py l0, imm_toNat ll]
    exact bx.trans (hl'.trans by'.symm)
  · exact (push_cov _ (hbu_cov hx m).1 (hbu_cov hx m).2).1
  · exact (push_cov _ (hbu_cov hx m).1 (hbu_cov hx m).2).2
  · rw [← ex]; exact (push_cov _ (hbu_cov hy m).1 (hbu_cov hy m).2).1
  · exact (push_cov _ (hbu_cov hy m).1 (hbu_cov hy m).2).2

end

/-! ## `vg_mldsa_bit_unpack` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {v f : Ptr} {len a b : Nat}

abbrev buArgs (v : Ptr) (len a b : Nat) : List (Reg × Arg) :=
  [(.r0, .ptr v), (.r1, .imm len), (.r2, .imm a), (.r3, .imm b)]
abbrev buAll (v : Ptr) (len a b : Nat) (f : Ptr) : List (Reg × Arg) := buArgs v len a b ++ [(.r12, .ptr f)]
abbrev buRd (L : Lay) (v : Ptr) (len : Nat) : List Region := [L.R (ix v.1) v.2 len]
abbrev buWr (L : Lay) (f : Ptr) : List Region := [L.R (ix f.1) f.2 1024]

/-- The facts `vg_mldsa_bit_unpack` needs of its arguments. -/
structure BuOk (L : Lay) (Wb : List Nat) (v : Ptr) (len a b : Nat) (f : Ptr) : Prop where
  pv : PtrIn L v len
  pf : PtrIn L f 1024
  wf : ix f.1 ∈ Wb
  d1 : sepB L.sizes (tri v len) (tri f 1024) = true
  hab : (a, b) ∈ bitPackParams
  hl : len = 32 * bitlen (a + b)
  lt : 0 < len ∧ len < 2 ^ 32 ∧ a < 2 ^ 32 ∧ b < 2 ^ 32

theorem BuOk.hg (m : BuOk L Wb v len a b f) : glueOk (buAll v len a b f) = true := by
  simp [glueOk, m.pv.1, m.pf.1, show ∀ v, argOk (.imm v) = true from fun _ => rfl]

theorem buAll_nodup : ((buAll v len a b f).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]; decide

theorem buG {s : State} (hs : Site L Wb STK s) (m : BuOk L Wb v len a b f) (rd wr : List Region) :
    (view (pushed [.r12] (glueSt s (buAll v len a b f))) rd wr).gpr .r0 = L.ptr (ix v.1) + BitVec.ofNat 32 v.2 ∧
    (view (pushed [.r12] (glueSt s (buAll v len a b f))) rd wr).gpr .r1 = BitVec.ofNat 32 len ∧
    (view (pushed [.r12] (glueSt s (buAll v len a b f))) rd wr).gpr .r2 = BitVec.ofNat 32 a ∧
    (view (pushed [.r12] (glueSt s (buAll v len a b f))) rd wr).gpr .r3 = BitVec.ofNat 32 b ∧
    stackArg (view (pushed [.r12] (glueSt s (buAll v len a b f))) rd wr) 0 =
      L.ptr (ix f.1) + BitVec.ofNat 32 f.2 :=
  ⟨by rw [view_r0, pushed_gpr, hs.gE m.hg buAll_nodup (by simp) m.pv.1],
    by rw [view_r1, pushed_gpr, glueSt_arg s m.hg buAll_nodup (a := .imm len) (by simp)]; rfl,
    by rw [view_r2, pushed_gpr, glueSt_arg s m.hg buAll_nodup (a := .imm a) (by simp)]; rfl,
    by rw [view_r3, pushed_gpr, glueSt_arg s m.hg buAll_nodup (a := .imm b) (by simp)]; rfl,
    by rw [push_arg, hs.gE m.hg buAll_nodup (by simp) m.pf.1]⟩

theorem bu_cov {s : State} (hs : Site L Wb STK s) (m : BuOk L Wb v len a b f) :
    Covers (buRd L v len ++ buWr L f) (s.rd ++ s.wr) ∧ Covers (buWr L f) s.wr :=
  ⟨covers_append (covers_cons' (hs.crE m.pv) covers_nil') (covers_wr (covers_cons' (hs.cwE m.pf m.wf) covers_nil')),
    covers_cons' (hs.cwE m.pf m.wf) covers_nil'⟩

theorem bu_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : 4 + stk ≤ STK) (m : BuOk L Wb v len a b f) :
    (bitUnpackContract Arm.abi stk).pre
      (view (pushed [.r12] (glueSt s (buAll v len a b f))) (buRd L v len ++ [argR s]) (buWr L f)) := by
  have e1 := glueSt_sp s (buAll v len a b f)
  obtain ⟨g0, g1, g2, g3, ga⟩ := buG hs m (buRd L v len ++ [argR s]) (buWr L f)
  obtain ⟨l0, ll, la, lb⟩ := m.lt
  have h4 := sp4 hs
  refine bu_pre g0 g1 g2 g3 ga
    (by rw [State.withRegions_rd, imm_toNat ll, hs.regE m.pv l0, push_argAddr _ e1]; rfl)
    (by rw [State.withRegions_wr, hs.regE m.pf (by decide)])
    (by rw [push_spN _ e1 _ _ h4]; have := hs.spk; omega) (push_fit _ _ _ h4 e1)
    ?_ ?_ ?_ ?_ ?_ (by rw [imm_toNat ll]; exact hs.fitE m.pv l0) (hs.fitE m.pf (by decide))
    (by rw [imm_toNat la, imm_toNat lb]; exact m.hab) (by rw [imm_toNat la, imm_toNat lb, imm_toNat ll]; exact m.hl)
  · rw [imm_toNat ll, hs.regE m.pv l0, hs.regE m.pf (by decide)]; exact hs.dE m.d1 (.inr m.wf)
  · rw [hs.regE m.pf (by decide)]; exact push_aE hs _ e1 _ _ m.pf
  · rw [imm_toNat ll, hs.regE m.pv l0]; exact push_kE hs _ e1 _ _ m.pv hstk
  · rw [hs.regE m.pf (by decide)]; exact push_kE hs _ e1 _ _ m.pf hstk
  · exact push_kA hs _ e1 _ _ hstk

theorem bu_okS {c : Prog isa} (hc : Callee c (fun stk => bitUnpackContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : 4 + S ≤ STK) {name : String} (m : BuOk L Wb v len a b f) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri f 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L f) (toRq (bitUnpack (bytesAt s.mem (lpa L v) len) a b)) → Q s') :
    WP isa (callAtS name c (buArgs v len a b) (.ptr f)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := bu_cov hs m
  obtain ⟨l0, ll, la, lb⟩ := m.lt
  have e1 := glueSt_sp s (buAll v len a b f)
  have hm := glueSt_mem s (buAll v len a b f)
  refine callVS hver.1 m.hg (bu_preS hs (by omega) m) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk h3 =>
      hQ s' (hs.keptW [tri f 1024] (by have := hc.stack; omega) hk) ?_
  obtain ⟨s₃, hm₃, -, hp⟩ := h3
  obtain ⟨g0, g1, g2, g3, ga⟩ := buG hs m (buRd L v len ++ [argR s]) (buWr L f)
  have := bu_post hp
  have hb := push_bytesAt hs e1 hm (buRd L v len ++ [argR s]) (buWr L f) m.pv (by omega)
  rw [g0, g1, g2, g3, ga, hs.addrE m.pv l0, hs.addrE m.pf (by decide), imm_toNat ll, imm_toNat la, imm_toNat lb,
    hb] at this
  simp only [State.withRegions_mem, hm₃] at this
  exact this

theorem bu_tr {c : Prog isa} (hc : Callee c (fun stk => bitUnpackContract Arm.abi stk) S) (hS : 4 + S ≤ STK)
    {name : String} (m : BuOk L Wb v len a b f) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp) :
    RelCT isa P (callAtS name c (buArgs v len a b) (.ptr f)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callVS_tr hver.1 hver.2.1 m.hg (fun x y h => (hP x y h).2.2)
    (fun x y h => ⟨sp4 (hP x y h).1, sp4 (hP x y h).2.1⟩) fun x y hxy => ?_
  obtain ⟨hx, hy, hsp⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2, gx3, gxa⟩ := buG hx m (buRd L v len ++ [argR x]) (buWr L f)
  obtain ⟨gy0, gy1, gy2, gy3, gya⟩ := buG hy m (buRd L v len ++ [argR x]) (buWr L f)
  have ex : argR y = argR x := by simp only [argR, hsp]
  refine ⟨buRd L v len ++ [argR x], buWr L f, bu_preS hx (by omega) m, ?_,
    bu_pub (by simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, glueSt_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]) (by rw [gx3, gy3]) (by rw [gxa, gya]),
    ?_, ?_, ?_, ?_⟩
  · rw [← ex]; exact bu_preS hy (by omega) m
  · exact (push_cov _ (bu_cov hx m).1 (bu_cov hx m).2).1
  · exact (push_cov _ (bu_cov hx m).1 (bu_cov hx m).2).2
  · rw [← ex]; exact (push_cov _ (bu_cov hy m).1 (bu_cov hy m).2).1
  · exact (push_cov _ (bu_cov hy m).1 (bu_cov hy m).2).2

end

/-! ## `vg_mldsa_sample_in_ball` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {ct c w : Ptr} {len tau : Nat}

abbrev ballArgs (ct : Ptr) (len tau : Nat) (c : Ptr) : List (Reg × Arg) :=
  [(.r0, .ptr ct), (.r1, .imm len), (.r2, .imm tau), (.r3, .ptr c)]
abbrev ballAll (ct : Ptr) (len tau : Nat) (c w : Ptr) : List (Reg × Arg) := ballArgs ct len tau c ++ [(.r12, .ptr w)]
abbrev ballRd (L : Lay) (ct : Ptr) (len : Nat) : List Region := [L.R (ix ct.1) ct.2 len]
abbrev ballWr (L : Lay) (c w : Ptr) : List Region := [L.R (ix c.1) c.2 1024, L.R (ix w.1) w.2 2048]

/-- The facts `vg_mldsa_sample_in_ball` needs of its arguments. -/
structure BallOk (L : Lay) (Wb : List Nat) (ct : Ptr) (len tau : Nat) (c w : Ptr) : Prop where
  pct : PtrIn L ct len
  pc : PtrIn L c 1024
  pw : PtrIn L w 2048
  wc : ix c.1 ∈ Wb
  ww : ix w.1 ∈ Wb
  d1 : sepB L.sizes (tri ct len) (tri c 1024) = true
  d2 : sepB L.sizes (tri ct len) (tri w 2048) = true
  d3 : sepB L.sizes (tri c 1024) (tri w 2048) = true
  hp : (len, tau) ∈ ballParams
  lt : 0 < len ∧ len < 2 ^ 32 ∧ tau < 2 ^ 32

theorem BallOk.hg (m : BallOk L Wb ct len tau c w) : glueOk (ballAll ct len tau c w) = true := by
  simp [glueOk, m.pct.1, m.pc.1, m.pw.1, show ∀ v, argOk (.imm v) = true from fun _ => rfl]

theorem ballAll_nodup : ((ballAll ct len tau c w).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]; decide

theorem ballG {s : State} (hs : Site L Wb STK s) (m : BallOk L Wb ct len tau c w) (rd wr : List Region) :
    (view (pushed [.r12] (glueSt s (ballAll ct len tau c w))) rd wr).gpr .r0 = L.ptr (ix ct.1) + BitVec.ofNat 32 ct.2 ∧
    (view (pushed [.r12] (glueSt s (ballAll ct len tau c w))) rd wr).gpr .r1 = BitVec.ofNat 32 len ∧
    (view (pushed [.r12] (glueSt s (ballAll ct len tau c w))) rd wr).gpr .r2 = BitVec.ofNat 32 tau ∧
    (view (pushed [.r12] (glueSt s (ballAll ct len tau c w))) rd wr).gpr .r3 = L.ptr (ix c.1) + BitVec.ofNat 32 c.2 ∧
    stackArg (view (pushed [.r12] (glueSt s (ballAll ct len tau c w))) rd wr) 0 =
      L.ptr (ix w.1) + BitVec.ofNat 32 w.2 :=
  ⟨by rw [view_r0, pushed_gpr, hs.gE m.hg ballAll_nodup (by simp) m.pct.1],
    by rw [view_r1, pushed_gpr, glueSt_arg s m.hg ballAll_nodup (a := .imm len) (by simp)]; rfl,
    by rw [view_r2, pushed_gpr, glueSt_arg s m.hg ballAll_nodup (a := .imm tau) (by simp)]; rfl,
    by rw [view_r3, pushed_gpr, hs.gE m.hg ballAll_nodup (by simp) m.pc.1],
    by rw [push_arg, hs.gE m.hg ballAll_nodup (by simp) m.pw.1]⟩

theorem ball_cov {s : State} (hs : Site L Wb STK s) (m : BallOk L Wb ct len tau c w) :
    Covers (ballRd L ct len ++ ballWr L c w) (s.rd ++ s.wr) ∧ Covers (ballWr L c w) s.wr :=
  ⟨covers_append (covers_cons' (hs.crE m.pct) covers_nil')
    (covers_wr (covers_cons' (hs.cwE m.pc m.wc) (covers_cons' (hs.cwE m.pw m.ww) covers_nil'))),
    covers_cons' (hs.cwE m.pc m.wc) (covers_cons' (hs.cwE m.pw m.ww) covers_nil')⟩

theorem ball_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : 4 + stk ≤ STK)
    (m : BallOk L Wb ct len tau c w) :
    (sampleInBallContract Arm.abi stk).pre
      (view (pushed [.r12] (glueSt s (ballAll ct len tau c w))) (ballRd L ct len ++ [argR s]) (ballWr L c w)) := by
  have e1 := glueSt_sp s (ballAll ct len tau c w)
  obtain ⟨g0, g1, g2, g3, ga⟩ := ballG hs m (ballRd L ct len ++ [argR s]) (ballWr L c w)
  obtain ⟨l0, ll, lt⟩ := m.lt
  have h4 := sp4 hs
  refine ball_pre g0 g1 g2 g3 ga
    (by rw [State.withRegions_rd, imm_toNat ll, hs.regE m.pct l0, push_argAddr _ e1]; rfl)
    (by rw [State.withRegions_wr, hs.regE m.pc (by decide), hs.regE m.pw (by decide)])
    (by rw [push_spN _ e1 _ _ h4]; have := hs.spk; omega) (push_fit _ _ _ h4 e1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by rw [imm_toNat ll]; exact hs.fitE m.pct l0) (hs.fitE m.pc (by decide))
    (hs.fitE m.pw (by decide)) (by rw [imm_toNat ll, imm_toNat lt]; exact m.hp)
  · rw [imm_toNat ll, hs.regE m.pct l0, hs.regE m.pc (by decide)]; exact hs.dE m.d1 (.inr m.wc)
  · rw [imm_toNat ll, hs.regE m.pct l0, hs.regE m.pw (by decide)]; exact hs.dE m.d2 (.inr m.ww)
  · rw [hs.regE m.pc (by decide), hs.regE m.pw (by decide)]; exact hs.dE m.d3 (.inl m.wc)
  · rw [hs.regE m.pc (by decide)]; exact push_aE hs _ e1 _ _ m.pc
  · rw [hs.regE m.pw (by decide)]; exact push_aE hs _ e1 _ _ m.pw
  · rw [imm_toNat ll, hs.regE m.pct l0]; exact push_kE hs _ e1 _ _ m.pct hstk
  · rw [hs.regE m.pc (by decide)]; exact push_kE hs _ e1 _ _ m.pc hstk
  · rw [hs.regE m.pw (by decide)]; exact push_kE hs _ e1 _ _ m.pw hstk
  · exact push_kA hs _ e1 _ _ hstk

theorem ball_okS {cd : Prog isa} (hc : Callee cd (fun stk => sampleInBallContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : 4 + S ≤ STK) {name : String} (m : BallOk L Wb ct len tau c w) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri c 1024, tri w 2048, (1, 0, STK)]) s s' →
      (s'.gpr .r0 = 1 → Reduced s'.mem (lpa L c)) →
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (lpa L ct) len)).map toRq) (s'.gpr .r0)
        (polyAt s'.mem (lpa L c)) → Q s') :
    WP isa (callAtS name cd (ballArgs ct len tau c) (.ptr w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := ball_cov hs m
  obtain ⟨l0, ll, lt⟩ := m.lt
  have e1 := glueSt_sp s (ballAll ct len tau c w)
  have hm := glueSt_mem s (ballAll ct len tau c w)
  refine callVS hver.1 m.hg (ball_preS hs (by omega) m) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk h3 => ?_
  obtain ⟨s₃, hm₃, hr₃, hp⟩ := h3
  obtain ⟨g0, g1, g2, g3, -⟩ := ballG hs m (ballRd L ct len ++ [argR s]) (ballWr L c w)
  have := ball_post hp
  have hb := push_bytesAt hs e1 hm (ballRd L ct len ++ [argR s]) (ballWr L c w) m.pct (by omega)
  rw [g0, g1, g2, g3, hs.addrE m.pct l0, hs.addrE m.pc (by decide), imm_toNat ll, imm_toNat lt, hb] at this
  simp only [State.withRegions_mem, State.withRegions_gpr, hm₃, hr₃ .r0 (by decide)] at this
  exact hQ s' (hs.keptW [tri c 1024, tri w 2048] (by have := hc.stack; omega) hk) this.1 this.2

theorem ball_tr {cd : Prog isa} (hc : Callee cd (fun stk => sampleInBallContract Arm.abi stk) S) (hS : 4 + S ≤ STK)
    {name : String} (m : BallOk L Wb ct len tau c w) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      bytesAt x.mem (lpa L ct) len = bytesAt y.mem (lpa L ct) len) :
    RelCT isa P (callAtS name cd (ballArgs ct len tau c) (.ptr w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨l0, ll, lt⟩ := m.lt
  refine callVS_tr hver.1 hver.2.1 m.hg (fun x y h => (hP x y h).2.2.1)
    (fun x y h => ⟨sp4 (hP x y h).1, sp4 (hP x y h).2.1⟩) fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl'⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2, gx3, gxa⟩ := ballG hx m (ballRd L ct len ++ [argR x]) (ballWr L c w)
  obtain ⟨gy0, gy1, gy2, gy3, gya⟩ := ballG hy m (ballRd L ct len ++ [argR x]) (ballWr L c w)
  have ex : argR y = argR x := by simp only [argR, hsp]
  have bx := push_bytesAt hx (glueSt_sp x (ballAll ct len tau c w)) (glueSt_mem x _) (ballRd L ct len ++ [argR x])
    (ballWr L c w) m.pct (by omega)
  have by' := push_bytesAt hy (glueSt_sp y (ballAll ct len tau c w)) (glueSt_mem y _) (ballRd L ct len ++ [argR x])
    (ballWr L c w) m.pct (by omega)
  refine ⟨ballRd L ct len ++ [argR x], ballWr L c w, ball_preS hx (by omega) m, ?_,
    ball_pub (by simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, glueSt_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]) (by rw [gx3, gy3]) (by rw [gxa, gya]) ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← ex]; exact ball_preS hy (by omega) m
  · rw [gx0, gy0, gx1, gy1, hx.addrE m.pct l0, imm_toNat ll]
    exact bx.trans (hl'.trans by'.symm)
  · exact (push_cov _ (ball_cov hx m).1 (ball_cov hx m).2).1
  · exact (push_cov _ (ball_cov hx m).1 (ball_cov hx m).2).2
  · rw [← ex]; exact (push_cov _ (ball_cov hy m).1 (ball_cov hy m).2).1
  · exact (push_cov _ (ball_cov hy m).1 (ball_cov hy m).2).2

end

/-! ## `vg_mldsa_norm_lt` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {f : Ptr} {bd : Nat}

abbrev nlArgs (f : Ptr) (bd : Nat) : List (Reg × Arg) := [(.r0, .ptr f), (.r1, .imm bd)]

theorem nl_hg (pf : PtrIn L f 1024) : glueOk (nlArgs f bd) = true := by
  simp [glueOk, pf.1, show ∀ v, argOk (.imm v) = true from fun _ => rfl]

theorem nlArgs_nodup : ((nlArgs f bd).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem nl_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (pf : PtrIn L f 1024)
    (hr : Reduced s.mem (lpa L f)) :
    (normLtContract Arm.abi stk).pre (view (glueSt s (nlArgs f bd)) [L.R (ix f.1) f.2 1024] []) := by
  have hsp := view_glue_sp s (nlArgs f bd) [L.R (ix f.1) f.2 1024] []
  refine normLt_pre (by rw [view_r0, hs.gE (nl_hg pf) nlArgs_nodup (by simp) pf.1])
    (by rw [State.withRegions_rd, hs.regE pf (by decide)]) rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    (by rw [hs.regE pf (by decide)]; exact hs.kE pf hstk hsp) (hs.fitE pf (by decide)) ?_
  rw [view_glue_mem, hs.addrE pf (by decide)]; exact hr

theorem nl_ok {c : Prog isa} (hc : Callee c (fun stk => normLtContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (pf : PtrIn L f 1024) (hbd : bd < 2 ^ 32)
    (hr : Reduced s.mem (lpa L f)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(1, 0, STK)]) s s' →
      s'.gpr .r0 = (if normRq [polyAt s.mem (lpa L f)] < bd then 1 else 0) → Q s') :
    WP isa (callAt name c (nlArgs f bd)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV hver.1 (nl_hg pf) (nl_preS hs (Nat.le_trans hstk hS) pf hr)
    (covers_append (covers_cons' (hs.crE pf) covers_nil') covers_nil') covers_nil'
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [] (Nat.le_trans hc.stack hS) hk) ?_
  have := normLt_post hp
  rw [State.withRegions_gpr, view_r0, view_r1, hs.gE (nl_hg pf) nlArgs_nodup (by simp) pf.1,
    glueSt_arg s (nl_hg pf) nlArgs_nodup (a := .imm bd) (by simp), view_glue_mem, hs.addrE pf (by decide)] at this
  simp only [argVal, imm_toNat hbd] at this
  exact this

theorem nl_tr {c : Prog isa} (hc : Callee c (fun stk => normLtContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (pf : PtrIn L f 1024) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L f) ∧
      Reduced y.mem (lpa L f)) :
    RelCT isa P (callAt name c (nlArgs f bd)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 (nl_hg pf) fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  refine ⟨[L.R (ix f.1) f.2 1024], [], nl_preS hx (Nat.le_trans hstk hS) pf rx,
    nl_preS hy (Nat.le_trans hstk hS) pf ry, normLt_pub (by rw [view_glue_sp, view_glue_sp, hsp])
      (by rw [view_r0, view_r0, hx.gE (nl_hg pf) nlArgs_nodup (by simp) pf.1,
        hy.gE (nl_hg pf) nlArgs_nodup (by simp) pf.1])
      (by rw [view_r1, view_r1]; exact hx.gpr_eq hy (nl_hg pf) nlArgs_nodup (a := .imm bd) (by simp)),
    covers_append (covers_cons' (hx.crE pf) covers_nil') covers_nil', covers_nil',
    covers_append (covers_cons' (hy.crE pf) covers_nil') covers_nil', covers_nil'⟩

end

/-! ## `vg_mldsa_use_hint` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {h r o : Ptr} {g2 : Nat}

abbrev uhArgs (h r : Ptr) (g2 : Nat) (o : Ptr) : List (Reg × Arg) :=
  [(.r0, .ptr h), (.r1, .ptr r), (.r2, .imm g2), (.r3, .ptr o)]
abbrev uhRd (L : Lay) (h r : Ptr) : List Region := [L.R (ix h.1) h.2 1024, L.R (ix r.1) r.2 1024]
abbrev uhWr (L : Lay) (o : Ptr) : List Region := [L.R (ix o.1) o.2 1024]

/-- The facts `vg_mldsa_use_hint` needs of its arguments. -/
structure UhOk (L : Lay) (Wb : List Nat) (h r : Ptr) (g2 : Nat) (o : Ptr) : Prop where
  ph : PtrIn L h 1024
  pr : PtrIn L r 1024
  po : PtrIn L o 1024
  wo : ix o.1 ∈ Wb
  d1 : sepB L.sizes (tri h 1024) (tri o 1024) = true
  d2 : sepB L.sizes (tri r 1024) (tri o 1024) = true
  hg : g2 ∈ gamma2s
  lt : g2 < 2 ^ 32

theorem UhOk.hg' (m : UhOk L Wb h r g2 o) : glueOk (uhArgs h r g2 o) = true := by
  simp [glueOk, m.ph.1, m.pr.1, m.po.1, show ∀ v, argOk (.imm v) = true from fun _ => rfl]

theorem uhArgs_nodup : ((uhArgs h r g2 o).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem uhG {s : State} (hs : Site L Wb STK s) (m : UhOk L Wb h r g2 o) (rd wr : List Region) :
    (view (glueSt s (uhArgs h r g2 o)) rd wr).gpr .r0 = L.ptr (ix h.1) + BitVec.ofNat 32 h.2 ∧
    (view (glueSt s (uhArgs h r g2 o)) rd wr).gpr .r1 = L.ptr (ix r.1) + BitVec.ofNat 32 r.2 ∧
    (view (glueSt s (uhArgs h r g2 o)) rd wr).gpr .r2 = BitVec.ofNat 32 g2 ∧
    (view (glueSt s (uhArgs h r g2 o)) rd wr).gpr .r3 = L.ptr (ix o.1) + BitVec.ofNat 32 o.2 :=
  ⟨by rw [view_r0, hs.gE m.hg' uhArgs_nodup (by simp) m.ph.1],
    by rw [view_r1, hs.gE m.hg' uhArgs_nodup (by simp) m.pr.1],
    by rw [view_r2, glueSt_arg s m.hg' uhArgs_nodup (a := .imm g2) (by simp)]; rfl,
    by rw [view_r3, hs.gE m.hg' uhArgs_nodup (by simp) m.po.1]⟩

theorem uh_cov {s : State} (hs : Site L Wb STK s) (m : UhOk L Wb h r g2 o) :
    Covers (uhRd L h r ++ uhWr L o) (s.rd ++ s.wr) ∧ Covers (uhWr L o) s.wr :=
  ⟨covers_append (covers_cons' (hs.crE m.ph) (covers_cons' (hs.crE m.pr) covers_nil'))
    (covers_wr (covers_cons' (hs.cwE m.po m.wo) covers_nil')), covers_cons' (hs.cwE m.po m.wo) covers_nil'⟩

theorem uh_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : UhOk L Wb h r g2 o)
    (hr : Reduced s.mem (lpa L r)) :
    (useHintContract Arm.abi stk).pre (view (glueSt s (uhArgs h r g2 o)) (uhRd L h r) (uhWr L o)) := by
  have hsp := view_glue_sp s (uhArgs h r g2 o) (uhRd L h r) (uhWr L o)
  obtain ⟨g0, g1, gg, g3⟩ := uhG hs m (uhRd L h r) (uhWr L o)
  refine useHint_pre g0 g1 gg g3 (by rw [State.withRegions_rd, hs.regE m.ph (by decide), hs.regE m.pr (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.po (by decide)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    ?_ ?_ ?_ ?_ ?_ (hs.fitE m.ph (by decide)) (hs.fitE m.pr (by decide)) (hs.fitE m.po (by decide))
    (by rw [imm_toNat m.lt]; exact m.hg) ?_
  · rw [hs.regE m.ph (by decide), hs.regE m.po (by decide)]; exact hs.dE m.d1 (.inr m.wo)
  · rw [hs.regE m.pr (by decide), hs.regE m.po (by decide)]; exact hs.dE m.d2 (.inr m.wo)
  · rw [hs.regE m.ph (by decide)]; exact hs.kE m.ph hstk hsp
  · rw [hs.regE m.pr (by decide)]; exact hs.kE m.pr hstk hsp
  · rw [hs.regE m.po (by decide)]; exact hs.kE m.po hstk hsp
  · rw [view_glue_mem, hs.addrE m.pr (by decide)]; exact hr

theorem uh_ok {c : Prog isa} (hc : Callee c (fun stk => useHintContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : UhOk L Wb h r g2 o)
    (hr : Reduced s.mem (lpa L r)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri o 1024, (1, 0, STK)]) s s' →
      NatPolyIs s'.mem (lpa L o) (Vector.zipWith (fun hj rj => (useHint g2 hj rj).toNat)
        ((hintAt s.mem (lpa L h) 1).headD (Vector.replicate n false)) (polyAt s.mem (lpa L r))) → Q s') :
    WP isa (callAt name c (uhArgs h r g2 o)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := uh_cov hs m
  refine callV hver.1 m.hg' (uh_preS hs (Nat.le_trans hstk hS) m hr) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [tri o 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1, gg, g3⟩ := uhG hs m (uhRd L h r) (uhWr L o)
  have := useHint_post hp
  rwa [State.withRegions_mem, g0, g1, gg, g3, hs.addrE m.ph (by decide), hs.addrE m.pr (by decide),
    hs.addrE m.po (by decide), view_glue_mem, imm_toNat m.lt] at this

theorem uh_tr {c : Prog isa} (hc : Callee c (fun stk => useHintContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : UhOk L Wb h r g2 o) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L r) ∧
      Reduced y.mem (lpa L r)) :
    RelCT isa P (callAt name c (uhArgs h r g2 o)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg' fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2, gx3⟩ := uhG hx m (uhRd L h r) (uhWr L o)
  obtain ⟨gy0, gy1, gy2, gy3⟩ := uhG hy m (uhRd L h r) (uhWr L o)
  exact ⟨uhRd L h r, uhWr L o, uh_preS hx (Nat.le_trans hstk hS) m rx, uh_preS hy (Nat.le_trans hstk hS) m ry,
    useHint_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2])
      (by rw [gx3, gy3]), (uh_cov hx m).1, (uh_cov hx m).2, (uh_cov hy m).1, (uh_cov hy m).2⟩

end

/-! ## `vg_mldsa_unpack_t1` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {v f : Ptr}

abbrev t1Args (v f : Ptr) : List (Reg × Arg) := [(.r0, .ptr v), (.r1, .ptr f)]
abbrev t1Rd (L : Lay) (v : Ptr) : List Region := [L.R (ix v.1) v.2 320]
abbrev t1Wr (L : Lay) (f : Ptr) : List Region := [L.R (ix f.1) f.2 1024]

/-- The facts `vg_mldsa_unpack_t1` needs of its arguments. -/
structure T1Ok (L : Lay) (Wb : List Nat) (v f : Ptr) : Prop where
  pv : PtrIn L v 320
  pf : PtrIn L f 1024
  wf : ix f.1 ∈ Wb
  d1 : sepB L.sizes (tri v 320) (tri f 1024) = true

theorem T1Ok.hg (m : T1Ok L Wb v f) : glueOk (t1Args v f) = true := by
  simp [glueOk, m.pv.1, m.pf.1]

theorem t1Args_nodup : ((t1Args v f).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem t1G {s : State} (hs : Site L Wb STK s) (m : T1Ok L Wb v f) (rd wr : List Region) :
    (view (glueSt s (t1Args v f)) rd wr).gpr .r0 = L.ptr (ix v.1) + BitVec.ofNat 32 v.2 ∧
    (view (glueSt s (t1Args v f)) rd wr).gpr .r1 = L.ptr (ix f.1) + BitVec.ofNat 32 f.2 :=
  ⟨by rw [view_r0, hs.gE m.hg t1Args_nodup (by simp) m.pv.1], by rw [view_r1, hs.gE m.hg t1Args_nodup (by simp) m.pf.1]⟩

theorem t1_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : T1Ok L Wb v f) :
    (unpackT1Contract Arm.abi stk).pre (view (glueSt s (t1Args v f)) (t1Rd L v) (t1Wr L f)) := by
  have hsp := view_glue_sp s (t1Args v f) (t1Rd L v) (t1Wr L f)
  refine t1_pre (by rw [view_r0, hs.gE m.hg t1Args_nodup (by simp) m.pv.1])
    (by rw [view_r1, hs.gE m.hg t1Args_nodup (by simp) m.pf.1])
    (by rw [State.withRegions_rd, hs.regE m.pv (by decide)]) (by rw [State.withRegions_wr, hs.regE m.pf (by decide)])
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_ (hs.fitE m.pv (by decide)) (hs.fitE m.pf (by decide))
  · rw [hs.regE m.pv (by decide), hs.regE m.pf (by decide)]; exact hs.dE m.d1 (.inr m.wf)
  · rw [hs.regE m.pv (by decide)]; exact hs.kE m.pv hstk hsp
  · rw [hs.regE m.pf (by decide)]; exact hs.kE m.pf hstk hsp

theorem t1_ok {c : Prog isa} (hc : Callee c (fun stk => unpackT1Contract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : T1Ok L Wb v f) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri f 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L f) ((simpleBitUnpack (bytesAt s.mem (lpa L v) 320) t1Max).map
        fun c => ofInt (c * 2 ^ d : Nat)) → Q s') :
    WP isa (callAt name c (t1Args v f)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  have cw : Covers (t1Wr L f) s.wr := covers_cons' (hs.cwE m.pf m.wf) covers_nil'
  refine callV hver.1 m.hg (t1_preS hs (Nat.le_trans hstk hS) m)
    (covers_append (covers_cons' (hs.crE m.pv) covers_nil') (covers_wr cw)) cw
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [tri f 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1⟩ := t1G hs m (t1Rd L v) (t1Wr L f)
  have := t1_post hp
  rwa [State.withRegions_mem, g0, g1, hs.addrE m.pv (by decide), hs.addrE m.pf (by decide),
    view_glue_mem] at this

theorem t1_tr {c : Prog isa} (hc : Callee c (fun stk => unpackT1Contract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : T1Ok L Wb v f) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp) :
    RelCT isa P (callAt name c (t1Args v f)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp⟩ := hP x y hxy
  have cx : Covers (t1Wr L f) x.wr := covers_cons' (hx.cwE m.pf m.wf) covers_nil'
  have cy : Covers (t1Wr L f) y.wr := covers_cons' (hy.cwE m.pf m.wf) covers_nil'
  exact ⟨t1Rd L v, t1Wr L f, t1_preS hx (Nat.le_trans hstk hS) m, t1_preS hy (Nat.le_trans hstk hS) m,
    t1_pub (by rw [view_glue_sp, view_glue_sp, hsp])
      (by rw [view_r0, view_r0, hx.gE m.hg t1Args_nodup (by simp) m.pv.1, hy.gE m.hg t1Args_nodup (by simp) m.pv.1])
      (by rw [view_r1, view_r1, hx.gE m.hg t1Args_nodup (by simp) m.pf.1, hy.gE m.hg t1Args_nodup (by simp) m.pf.1]),
    covers_append (covers_cons' (hx.crE m.pv) covers_nil') (covers_wr cx), cx,
    covers_append (covers_cons' (hy.crE m.pv) covers_nil') (covers_wr cy), cy⟩

end

end VG.Proof.MlDsa.Arm.KeyGen
