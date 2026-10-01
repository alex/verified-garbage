import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2

/-!
# ML-KEM on x86-64: the NTT and its inverse on AVX2 registers, before and after the layers

Untrusted: everything here is checked by Lean. The packing of the 256
`u32`s of `f` into the words of `S`, sixteen at a time (`ypack_ok`), their
unpacking back (`yunpack_ok`), the multiplication by `3303` of `NTT⁻¹`
(`yscale_ok`), and the prologue and epilogue around them (`ypro_ok`,
`yepi_ok`); and the facts kept between the layers (`LIY`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## Packing -/

/-- The eight coefficients of a reduced polynomial, four at `coeffAddr p j`
and four at `coeffAddr p j'`, as the words `packssdw` makes of them. -/
theorem lanes_pack2 {m : Mem} {p : Addr} {F : Poly} (hF : PolyIs m p F) {j j' : Nat} (hj : j + 4 ≤ 256)
    (hj' : j' + 4 ≤ 256) :
    Lanes (XBinOp.eval .packssdw (m.readW (coeffAddr p j) 128) (m.readW (coeffAddr p j') 128))
      (fun e => if e < 4 then F[j + e]! else F[j' + (e - 4)]!) := fun e he => by
  have hc : ∀ k, k < 256 → (coeffAt m p k).toNat = (F[k]!).val := fun k hk =>
    polyIs_toNat hF (by rw [n_eq]; exact hk)
  rw [word_packssdw_small _ _ he (fun k hk => by
      rw [dword_readW _ _ hk, coeffAddr_off, ← coeffAt_eq, hc _ (by omega)]; have := val_lt F[j + k]!; omega)
    (fun k hk => by
      rw [dword_readW _ _ hk, coeffAddr_off, ← coeffAt_eq, hc _ (by omega)]; have := val_lt F[j' + k]!; omega)]
  split
  · rw [dword_readW _ _ (by omega), coeffAddr_off, ← coeffAt_eq, hc _ (by omega)]; dsimp only; rw [ifp ‹_›]
  · rw [dword_readW _ _ (by omega), coeffAddr_off, ← coeffAt_eq, hc _ (by omega)]; dsimp only; rw [ifn ‹_›]

/-- `vpackssdw ymm0, ymm0, ymm1` in each lane. -/
theorem zpack_ok (t : State) :
    WP isa (.block [xb .packssdw .xmm0 .xmm1]) t
      fun t' => t'.xmm .xmm0 = XBinOp.eval .packssdw (t.xmm .xmm0) (t.xmm .xmm1) ∧ XOnly [.xmm0] t t' := by
  simp only [xb]
  vrun
  exact ⟨trivial, by xonly⟩

theorem ypack_ok {fP sP : Addr} {F : Poly} {s : State} (hc : YConsts s) (hF : PolyIs s.mem fP F)
    (h9 : s.gpr .r9 = fP) (hdx : s.gpr .rdx = spW sP) (hrf : pR fP ∈ s.rd ++ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR fP).Disjoint (pR sP)) :
    WP isa ypack s fun s' => S16 s'.mem (spW sP) F ∧ Frame [sR (spW sP)] s.mem s'.mem ∧ YConsts s' ∧
      Keep [.r9, .rdx, .rcx] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hsub : Region.Sub (sR (spW sP)) (pR sP) := Offset.sub_base sP (by omega)
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun u w => S16p w.mem (spW sP) F (16 * u) ∧ w.gpr .r9 = coeffAddr fP (16 * u) ∧
      w.gpr .rdx = wAddr (spW sP) (16 * u) ∧ Frame [sR (spW sP)] s.mem w.mem ∧ YConsts w ∧
      Keep [.r9, .rdx, .rcx] s w ∧ w.mxcsr = s.mxcsr)
    (fun w o hy hcx => ⟨fun _ h => absurd h (by omega), by rw [o.keep.gpr (by decide), h9, coeffAddr]; simp,
      by rw [o.keep.gpr (by decide), hdx, wAddr]; simp, by rw [o.mem]; exact Frame.refl _ _,
      lanes_gpr (s := s) (GOnly.lane o hy) (YOnly.refl [] s) hc (by decide) (by decide),
      o.keep.mono (by simp), o.mxcsr⟩)
    (fun u hu w ⟨hP, h9', hdx', hf, hc', hk', hx'⟩ => ?_))
    fun w ⟨hP, _, _, hf, hc', hk', hx'⟩ => ⟨hP, hf, hc', hk', hx'⟩
  have hF' : PolyIs w.mem fP F := polyIs_frame hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd.sub_right hsub) hF
  have hrf' : pR fP ∈ w.rd ++ w.wr := by rw [hk'.2.1, hk'.2.2]; exact hrf
  have hw' : pR sP ∈ w.wr := by rw [hk'.2.2]; exact hw
  have a1 : coeffAddr fP (16 * u) + BitVec.ofNat 64 32 = coeffAddr fP (16 * u + 8) := coeffAddr_off _ _ 8
  have r0 : InRegions (w.rd ++ w.wr) (w.gpr .r9 + BitVec.ofNat 64 0) 32 :=
    ⟨_, hrf', by rw [h9', add_ofNat_zero]; exact Offset.contains_base fP (by omega) (by omega)⟩
  have r1 : InRegions (w.rd ++ w.wr) (w.gpr .r9 + BitVec.ofNat 64 32) 32 :=
    ⟨_, hrf', by rw [h9', a1]; exact Offset.contains_base fP (by omega) (by omega)⟩
  rw [show ∀ a b c d e f g : Instr, [a, b, c, d, e, f, g] ++ [.alu .sub .rcx (.imm 1)] =
      [a] ++ ([b] ++ ([c] ++ ([d] ++ [e, f, g, .alu .sub .rcx (.imm 1)]))) from fun _ _ _ _ _ _ _ => rfl,
    WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L0, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L1, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes (vs := [yb .vpackssdw .xmm0 .xmm0 .xmm1]) (by decide)
    (P := fun l t => t.xmm .xmm0 = XBinOp.eval .packssdw (s2.lane .xmm0 l) (s2.lane .xmm1 l))
    fun l _ => zpack_ok (s2.proj l)) fun s3 ⟨P3, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ypermq_ok s3) fun s4 ⟨Q0, Q1, o4⟩ => ?_
  have o14 := ((o1.trans o2).trans o3).trans o4
  have w0 : InRegions s4.wr (s4.gpr .rdx) 32 := by rw [o14.wr, o14.gpr, hdx']; exact sp_inY hw' (by omega)
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0, sx32, sx_ofNat (show 64 < 2 ^ 31 by decide)]
  -- the words of lane `l` of `ymm0`
  have lane0 : ∀ l < 2, s2.lane .xmm0 l = w.mem.readW (coeffAddr fP (16 * u + 4 * l)) 128 := fun l hl => by
    rw [o2.lane _ (by decide) l hl, L0 l hl, h9', add_ofNat_zero, show 16 * l = 4 * (4 * l) by omega, coeffAddr_off]
  have lane1 : ∀ l < 2, s2.lane .xmm1 l = w.mem.readW (coeffAddr fP (16 * u + 8 + 4 * l)) 128 := fun l hl => by
    rw [L1 l hl, o1.gpr, o1.mem, h9', a1, show 16 * l = 4 * (4 * l) by omega, coeffAddr_off]
  have pk : ∀ l < 2, Lanes (s3.lane .xmm0 l) (fun e => if e < 4 then F[16 * u + 4 * l + e]!
      else F[16 * u + 8 + 4 * l + (e - 4)]!) := fun l hl => by
    have e : s3.lane .xmm0 l = _ := P3 l hl
    rw [e, lane0 l hl, lane1 l hl]; exact lanes_pack2 hF' (by omega) (by omega)
  have Y : ∀ l < 2, Lanes (s4.lane .xmm0 l) (fun e => F[16 * u + 8 * l + e]!) := fun l hl => by
    rcases lane01 hl with rfl | rfl
    · rw [Q0]; intro e he; rw [word_punpcklqdq _ _ he]
      split
      · rw [pk 0 (by decide) e he]; dsimp only; rw [ite_eq_left_of_eq_true _ _ (eq_true ‹e < 4›)]
      · rw [pk 1 (by decide) (e - 4) (by omega)]; dsimp only
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show e - 4 < 4 by omega))]
        exact congrArg _ (congrArg _ (by omega))
    · rw [Q1]; intro e he; rw [word_punpckhqdq _ _ he]
      split
      · rw [pk 0 (by decide) (4 + e) (by omega)]; dsimp only
        rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + e < 4 by omega))]
        exact congrArg _ (congrArg _ (by omega))
      · rw [pk 1 (by decide) e he]; dsimp only
        rw [ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 4›)]
        exact congrArg _ (congrArg _ (by omega))
  have dx4 : s4.gpr .rdx = wAddr (spW sP) (16 * u) := by rw [o14.gpr, hdx']
  have r94 : s4.gpr .r9 = coeffAddr fP (16 * u) := by rw [o14.gpr, h9']
  rw [dx4, r94, o14.mem]
  refine ⟨⟨fun j hj => ?_, by rw [show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (4 * 16) by decide,
      coeffAddr_off, Nat.mul_succ], by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add,
      Nat.mul_succ], ?_, ?_, ?_, ?_⟩, by rw [o14.gpr], by rw [o14.gpr]⟩
  · rw [wordAt_write256 _ _ (by omega) _ (by omega)]
    split
    · rw [word_ymm _ _ (by omega), Y _ (by omega) _ (Nat.mod_lt _ (by omega))]
      exact congrArg _ (congrArg _ (by omega))
    · exact hP j (by omega)
  · exact hf.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sR_containsY _ (by omega)))
  · exact lanes_gpr (s := s4) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o14 hc'
      (by decide) (by decide)
  · refine ⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o14.rd]; exact hk'.2.1,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o14.wr]; exact hk'.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, State.setMem_gpr, hr, ite_false]
    rw [o14.gpr]; exact hk'.gpr (by simp [hr])
  · exact o14.mxcsr.trans hx'

/-! ## Unpacking -/

/-- Doubleword `q` of a 256-bit register, as stored. -/
theorem dword_ymm (s : State) (r : XReg) {q : Nat} (hq : q < 8) :
    (s.ymm r).extractLsb' (8 * (4 * q)) (8 * 4) = dword (s.lane r (q / 4)) (q % 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.ymm, State.lane, dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    decide_eq_true hj, Bool.true_and]
  by_cases h : q < 4
  · simp only [show 8 * (4 * q) + j < 128 by omega, ite_true, show q / 4 = 0 by omega]
    exact congrArg _ (by omega)
  · simp only [show ¬ 8 * (4 * q) + j < 128 by omega, ite_false, show q / 4 = 1 by omega, Nat.one_ne_zero]
    exact congrArg _ (by omega)

/-- `vpxor ymm4, ymm4, ymm4` in each lane. -/
theorem zxor_ok (t : State) :
    WP isa (.block [xb .pxor .xmm4 .xmm4]) t fun t' => t'.xmm .xmm4 = 0 ∧ XOnly [.xmm4] t t' := by
  simp only [xb]
  vrun
  exact ⟨by simp only [XBinOp.eval, BitVec.xor_self]; rfl, by xonly⟩

/-- `vpunpckhwd ymm1, ymm0, ymm4` and `vpunpcklwd ymm0, ymm0, ymm4` in each lane. -/
theorem zunpk_ok (t : State) :
    WP isa (.block [xb .movdqa .xmm1 .xmm0, xb .punpckhwd .xmm1 .xmm4, xb .punpcklwd .xmm0 .xmm4]) t fun t' =>
      (t'.xmm .xmm1 = XBinOp.eval .punpckhwd (t.xmm .xmm0) (t.xmm .xmm4) ∧
        t'.xmm .xmm0 = XBinOp.eval .punpcklwd (t.xmm .xmm0) (t.xmm .xmm4)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [xb]
  vrun
  exact ⟨⟨rfl, trivial⟩, by xonly⟩

theorem yunpack_ok {fP sP : Addr} {F : Poly} {s : State} (hc : YConsts s) (hS : S16 s.mem (spW sP) F)
    (h9 : s.gpr .r9 = fP) (hdx : s.gpr .rdx = spW sP) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR fP).Disjoint (pR sP)) :
    WP isa yunpack s fun s' => PolyIs s'.mem fP F ∧ Frame [pR fP] s.mem s'.mem ∧ YConsts s' ∧
      Keep [.r9, .rdx, .rcx] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hsub : Region.Sub (sR (spW sP)) (pR sP) := Offset.sub_base sP (by omega)
  refine WP.seq (WP.mono (ylanes (vs := [yb .vpxor .xmm4 .xmm4 .xmm4]) (by decide)
    (P := fun _ t => t.xmm .xmm4 = 0) fun l _ => zxor_ok (s.proj l)) fun w0 ⟨hz, o0⟩ => ?_)
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun u w => PolyP w.mem fP F (16 * u) ∧ w.gpr .r9 = coeffAddr fP (16 * u) ∧
      w.gpr .rdx = wAddr (spW sP) (16 * u) ∧ Frame [pR fP] s.mem w.mem ∧ YConsts w ∧
      (∀ l < 2, w.lane .xmm4 l = 0) ∧ Keep [.r9, .rdx, .rcx] s w ∧ w.mxcsr = s.mxcsr)
    (fun w o hy hcx => ⟨fun _ h => absurd h (by omega),
      by rw [o.keep.gpr (by decide), o0.gpr, h9, coeffAddr]; simp,
      by rw [o.keep.gpr (by decide), o0.gpr, hdx, wAddr]; simp, by rw [o.mem, o0.mem]; exact Frame.refl _ _,
      lanes_gpr (s := w0) (GOnly.lane o hy) o0 hc (by decide) (by decide),
      fun l hl => by rw [GOnly.lane o hy]; exact hz l hl,
      Keep.trans (⟨fun r _ => by rw [o0.gpr], o0.rd, o0.wr⟩ : Keep [] s w0) (o.keep) |>.mono (by simp),
      by rw [o.mxcsr, o0.mxcsr]⟩)
    (fun u hu w ⟨hP, h9', hdx', hf, hc', hz', hk', hx'⟩ => ?_))
    fun w ⟨hP, _, _, hf, hc', _, hk', hx'⟩ => ⟨polyIs_of_toNat fun i hi => hP i (by rw [n_eq] at hi; omega),
      hf, hc', hk', hx'⟩
  have hS' : S16 w.mem (spW sP) F := hS.frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hd.sub_right hsub).symm
  have hwf' : pR fP ∈ w.wr := by rw [hk'.2.2]; exact hwf
  have r0 : InRegions (w.rd ++ w.wr) (w.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx', add_ofNat_zero]; exact sp_inY (List.mem_append_right _ (by rw [hk'.2.2]; exact hw)) (by omega)
  have a1 : coeffAddr fP (16 * u) + BitVec.ofNat 64 32 = coeffAddr fP (16 * u + 8) := coeffAddr_off _ _ 8
  rw [show ∀ a b c d e f g h : Instr, [a, b, c, d, e, f, g, h] ++ [.alu .sub .rcx (.imm 1)] =
      [a] ++ ([b] ++ ([c, d] ++ [e, f, g, h, .alu .sub .rcx (.imm 1)])) from fun _ _ _ _ _ _ _ _ => rfl,
    WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L0, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ypermq_ok s1) fun s2 ⟨Q0, Q1, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes (vs := [yb .vpunpckhwd .xmm1 .xmm0 .xmm4, yb .vpunpcklwd .xmm0 .xmm0 .xmm4]) (by decide)
    (P := fun l t => t.xmm .xmm1 = XBinOp.eval .punpckhwd (s2.lane .xmm0 l) (s2.lane .xmm4 l) ∧
      t.xmm .xmm0 = XBinOp.eval .punpcklwd (s2.lane .xmm0 l) (s2.lane .xmm4 l))
    fun l _ => zunpk_ok (s2.proj l)) fun s3 ⟨P3, o3⟩ => ?_
  have o13 := (o1.trans o2).trans o3
  have w0' : InRegions s3.wr (s3.gpr .r9) 32 := by
    rw [o13.wr, o13.gpr, h9']; exact ⟨_, hwf', Offset.contains_base fP (by omega) (by omega)⟩
  have w1' : InRegions s3.wr (s3.gpr .r9 + 32#64) 32 := by
    rw [o13.wr, o13.gpr, h9', a1]; exact ⟨_, hwf', Offset.contains_base fP (by omega) (by omega)⟩
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0', w1', sx32, sx_ofNat (show 64 < 2 ^ 31 by decide)]
  have r93 : s3.gpr .r9 = coeffAddr fP (16 * u) := by rw [o13.gpr, h9']
  have dx3 : s3.gpr .rdx = wAddr (spW sP) (16 * u) := by rw [o13.gpr, hdx']
  have LA : ∀ l < 2, Lanes (s1.lane .xmm0 l) (fun e => F[16 * u + 8 * l + e]!) := fun l hl => by
    rw [L0 l hl, hdx', add_ofNat_zero]; exact lanes_loadY hS' (by omega) hl
  have Wlo : ∀ l < 2, ∀ e < 4, (word (s2.lane .xmm0 l) e).toNat = (F[16 * u + 4 * l + e]!).val := fun l hl e he => by
    rcases lane01 hl with rfl | rfl
    · rw [Q0, word_punpcklqdq _ _ (show e < 8 by omega), ifp he, LA 0 (by decide) e (by omega)]
    · rw [Q1, word_punpckhqdq _ _ (show e < 8 by omega), ifp he, LA 0 (by decide) _ (by omega)]
      exact congrArg _ (congrArg _ (by omega))
  have Whi : ∀ l < 2, ∀ e < 4, (word (s2.lane .xmm0 l) (4 + e)).toNat = (F[16 * u + 8 + 4 * l + e]!).val :=
    fun l hl e he => by
    rcases lane01 hl with rfl | rfl
    · rw [Q0, word_punpcklqdq _ _ (show 4 + e < 8 by omega), ifn (show ¬ 4 + e < 4 by omega), LA 1 (by decide) _ (by omega)]
      exact congrArg _ (congrArg _ (by omega))
    · rw [Q1, word_punpckhqdq _ _ (show 4 + e < 8 by omega), ifn (show ¬ 4 + e < 4 by omega), LA 1 (by decide) _ (by omega)]
      exact congrArg _ (congrArg _ (by omega))
  have Z2 : ∀ l < 2, s2.lane .xmm4 l = 0 := fun l hl => by
    rw [(o1.trans o2).lane _ (by decide) l hl]; exact hz' l hl
  have Y4 : ∀ l < 2, s3.lane .xmm4 l = 0 := fun l hl => by
    rw [o13.lane _ (by decide) l hl]; exact hz' l hl
  have Y0 : ∀ l < 2, s3.lane .xmm0 l = XBinOp.eval .punpcklwd (s2.lane .xmm0 l) 0 := fun l hl => by
    have e := (P3 l hl).2; rw [State.proj_xmm, Z2 l hl] at e; exact e
  have Y1 : ∀ l < 2, s3.lane .xmm1 l = XBinOp.eval .punpckhwd (s2.lane .xmm0 l) 0 := fun l hl => by
    have e := (P3 l hl).1; rw [State.proj_xmm, Z2 l hl] at e; exact e
  refine ⟨⟨fun j hj => ?_, by rw [r93, show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (4 * 16) by decide,
      coeffAddr_off, Nat.mul_succ], by rw [dx3, show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add,
      Nat.mul_succ], ?_, ?_, ?_, ?_, ?_⟩, by rw [o13.gpr], by rw [o13.gpr]⟩
  · rw [r93, a1, coeffAt_write256 _ _ (by omega) _ (by omega), coeffAt_write256 _ _ (by omega) _ (by omega)]
    split
    · rw [dword_ymm _ _ (by omega), Y1 _ (by omega), dword_punpckhwd0 _ (by omega), Whi _ (by omega) _ (by omega)]
      exact congrArg _ (congrArg _ (by omega))
    · split
      · rw [dword_ymm _ _ (by omega), Y0 _ (by omega), dword_punpcklwd0 _ (by omega), Wlo _ (by omega) _ (by omega)]
        exact congrArg _ (congrArg _ (by omega))
      · rw [o13.mem]; exact hP j (by omega)
  · rw [r93, a1, o13.mem]
    exact hf.trans (((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (show (pR fP).Contains (coeffAddr fP (16 * u)) (256 / 8) from Offset.contains_base fP (by omega)
        (by omega))).writeW (List.mem_singleton_self _) _
      (show (pR fP).Contains (coeffAddr fP (16 * u + 8)) (256 / 8) from Offset.contains_base fP (by omega)
        (by omega)))
  · exact lanes_gpr (s := s3) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o13 hc'
      (by decide) (by decide)
  · intro l hl; simp only [lane_setReg, lane_setFlags, State.setMem_lane]; exact Y4 l hl
  · refine ⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd]; exact hk'.2.1,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr]; exact hk'.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, State.setMem_gpr, hr, ite_false]
    rw [o13.gpr]; exact hk'.gpr (by simp [hr])
  · exact o13.mxcsr.trans hx'

/-! ## The multiplication by 3303 -/

theorem lane_vmulc : laneSseBlock (toY (vmont .xmm3 .xmm13 .xmm2 ++ vcadd .xmm3 .xmm2)) =
    some (vmont .xmm3 .xmm13 .xmm2 ++ vcadd .xmm3 .xmm2) := by decide +kernel

/-- `3303 · 2¹⁶ mod q = 512` in every word, as `yscale` makes it. -/
theorem zlanes_512Y : ZLanes (ofDwords 0x02000200 0x02000200 0x02000200 0x02000200) fun _ => (3303 : Zq) :=
  fun i hi => by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem yscale_ok {sP : Addr} {F : Poly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hw : pR sP ∈ s.wr) :
    WP isa yscale s fun s' => S16 s'.mem (spW sP) (F.map (· * 3303)) ∧ BInvY sP s s' := by
  simp only [yscale]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (w : State) => w.gpr .rdx = spW sP ∧ GOnly [.rdx] s w ∧ w.ymmHi = s.ymmHi)
    (by
      simp only [leaR, oS]
      vrunm [sx_ofNat (show 256 < 2 ^ 31 by decide), hsi, RegUpd.ymmHi_setReg]
      exact ⟨by gonly, rfl⟩) fun w1 ⟨hdx1, og, hy⟩ => ?_
  refine WP.mono (yconst_ok .xmm13 _ w1) fun w2 ⟨q2, k2, m2, x2, o2⟩ => ?_
  have hl1 := GOnly.lane og hy
  have cw2 : YConsts w2 := fun l hl => by
    have h15 := (hc l hl).q; have h14 := (hc l hl).qinv
    rw [State.proj_xmm] at h15 h14
    exact ⟨by rw [State.proj_xmm, o2 _ (by decide) l hl, hl1]; exact h15,
      by rw [State.proj_xmm, o2 _ (by decide) l hl, hl1]; exact h14⟩
  have kw2 : Keep [.r8, .rcx, .rdx, .rax] s w2 := (og.keep.trans k2).mono (by simp)
  have hdx2 : w2.gpr .rdx = spW sP := by rw [k2.gpr (by decide), hdx1]
  have mw2 : w2.mem = s.mem := by rw [m2, og.mem]
  have xw2 : w2.mxcsr = s.mxcsr := by rw [x2, og.mxcsr]
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun u v => (∀ j < 256, (wordAt v.mem (spW sP) j).toNat = (if j < 16 * u then F[j]! * 3303 else F[j]!).val) ∧
      v.gpr .rdx = wAddr (spW sP) (16 * u) ∧ (∀ l < 2, v.lane .xmm13 l = ofDwords 0x02000200 0x02000200 0x02000200 0x02000200) ∧
      BInvY sP s v)
    (fun v o hy' _ => ⟨fun j hj => by rw [ite_eq_right (by omega), o.mem, mw2]; exact hS j hj,
      by rw [o.keep.gpr (by decide), hdx2, wAddr]; simp,
      fun l hl => by rw [GOnly.lane o hy']; exact q2 l hl,
      ⟨(kw2.trans o.keep).mono (by simp), by rw [o.mem, mw2]; exact Frame.refl _ _,
        lanes_gpr (s := w2) (GOnly.lane o hy') (YOnly.refl [] w2) cw2 (by decide) (by decide),
        by rw [o.mxcsr, xw2]⟩⟩)
    (fun u hu v ⟨hP, hdx', hz', hb⟩ => ?_))
    fun v ⟨hP, _, _, hb⟩ => ⟨fun j hj => by
      rw [hP j hj, ite_eq_left (by omega), map_mul_get _ (by rw [n_eq]; exact hj)], hb⟩
  have hw' : pR sP ∈ v.wr := by rw [hb.keep.2.2]; exact hw
  have r0 : InRegions (v.rd ++ v.wr) (v.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx', add_ofNat_zero]; exact sp_inY (List.mem_append_right _ hw') (by omega)
  rw [show ∀ (a : Instr) (b : List Instr) (c d : Instr), [a] ++ b ++ [c, d] ++ [.alu .sub .rcx (.imm 1)] =
      [a] ++ (b ++ [c, d, .alu .sub .rcx (.imm 1)]) from fun _ _ _ _ => by simp,
    WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  have c1 : YConsts s1 := o1.consts hb.consts (by decide) (by decide)
  refine WP.mono (ylanes lane_vmulc (P := fun l t => Lanes (t.xmm .xmm3) (fun e => 3303 * F[16 * u + 8 * l + e]!))
    fun l hl => vmulc_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (c1 l hl)
      (fun e he => by
        rw [State.proj_xmm, L1 l hl, hdx', add_ofNat_zero, show 16 * l = 2 * (8 * l) by omega, wAddr_add,
          word_readW _ _ he, wAddr_add, ← wordAt, hP _ (by omega), ite_eq_right (by omega)])
      (by rw [State.proj_xmm, o1.lane _ (by decide) l hl, hz' l hl]; exact zlanes_512Y)) fun s2 ⟨l2, o2⟩ => ?_
  have o12 := o1.trans o2
  have w0 : InRegions s2.wr (s2.gpr .rdx) 32 := by rw [o12.wr, o12.gpr, hdx']; exact sp_inY hw' (by omega)
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    w0, sx32]
  have dx2 : s2.gpr .rdx = wAddr (spW sP) (16 * u) := by rw [o12.gpr, hdx']
  have l2' : ∀ l < 2, Lanes (s2.lane .xmm3 l) (fun e => 3303 * F[16 * u + 8 * l + e]!) := fun l hl => by
    have := l2 l hl; rwa [State.proj_xmm] at this
  rw [dx2, o12.mem]
  refine ⟨⟨fun j hj => ?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add, Nat.mul_succ],
    fun l hl => ?_, hb.trans ⟨⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd, o12.rd],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr, o12.wr]⟩,
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sR_containsY _ (by omega)), ?_,
      by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; exact o12.mxcsr⟩⟩,
    by rw [o12.gpr], by rw [o12.gpr]⟩
  · rw [wordAt_write256 _ _ (by omega) _ hj]
    split
    · rw [word_ymm _ _ (by omega), l2' _ (by omega) _ (Nat.mod_lt _ (by omega)), ite_eq_left (by omega),
        Fin.mul_comm]
      dsimp only; rw [show 16 * u + 8 * ((j - 16 * u) / 8) + (j - 16 * u) % 8 = j by omega]
    · rw [hP j hj]
      by_cases h : j < 16 * u
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]
  · simp only [lane_setReg, lane_setFlags, State.setMem_lane]
    rw [o12.lane _ (by decide) l hl]; exact hz' l hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, State.setMem_gpr, hr, ite_false]
    rw [o12.gpr]
  · exact lanes_gpr (s := s2) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o12
      hb.consts (by decide) (by decide)

/-! ## The prologue and the epilogue -/

theorem yconsts_ok (s : State) :
    WP isa (.block yconsts) s fun s' => YConsts s' ∧ s'.mem = s.mem ∧ Keep [.rax] s s' := by
  simp only [yconsts]
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm15 _ s) fun s1 ⟨q1, k1, m1, _, _⟩ => ?_
  refine WP.mono (yconst_ok .xmm14 _ s1) fun s2 ⟨q2, k2, m2, _, o2⟩ => ?_
  refine ⟨fun l hl => ⟨?_, ?_⟩, by rw [m2, m1], (k1.trans k2).mono (by simp)⟩
  · rw [State.proj_xmm, o2 _ (by decide) l hl, q1 l hl]; decide
  · rw [State.proj_xmm, q2 l hl]; decide

/-- The table `tab` of the zetas `z` at `scratch`, `f` as words in `S`, and the constants. -/
theorem ypro_ok (tab : Nat → Nat) {z : Nat → Zq} (htab : ∀ k, tab k = (z k).val * 65536 % 3329)
    {fP sP : Addr} {F : Poly} {s : State} (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hF : PolyIs s.mem fP F) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) (hd : (pR fP).Disjoint (pR sP)) :
    WP isa (ypro tab) s fun s' => S16 s'.mem (spW sP) F ∧ TZ s'.mem sP z ∧ YConsts s' ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.rax, .rcx, .rdx, .r9] s s' := by
  simp only [ypro, List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have htl : ∀ k, tab k < 65536 := fun k => by
    rw [htab k]; have := Nat.mod_lt ((z k).val * 65536) (show 3329 > 0 by decide); omega
  refine WP.mono (wordTab_gen tab htl (by decide) hsi hw) fun s1 ⟨hT, hf1, k1, _, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yconsts_ok s1) fun s2 ⟨hc2, hm2, k2⟩ => ?_
  have k12 := k1.trans k2
  have hsi2 : s2.gpr .rsi = sP := by rw [k12.gpr (by decide), hsi]
  have hdi2 : s2.gpr .rdi = fP := by rw [k12.gpr (by decide), hdi]
  refine WP.mono (Q := fun (s3 : State) => s3.gpr .r9 = fP ∧ s3.gpr .rdx = spW sP ∧ GOnly [.r9, .rdx] s2 s3 ∧
      s3.ymmHi = s2.ymmHi)
    (by
      simp only [leaR, oS]
      vrunm [hsi2, hdi2, sx_ofNat (show 256 < 2 ^ 31 by decide), RegUpd.ymmHi_setReg]
      exact ⟨by gonly, rfl⟩) fun s3 ⟨h9, hdx, og, hy⟩ => ?_
  have k13 := k12.trans og.keep
  have hF3 : PolyIs s3.mem fP F := by
    rw [og.mem, hm2]
    exact polyIs_frame hf1 (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (pR_sub_tab sP)) hF
  have hT3 : TZ s3.mem sP z := fun k hk => by rw [og.mem, hm2, hT k hk, htab]
  refine WP.mono (ypack_ok (lanes_gpr (s := s2) (GOnly.lane og hy) (YOnly.refl [] s2) hc2 (by decide) (by decide))
    hF3 h9 hdx (by rw [k13.2.2]; exact List.mem_append_right _ hwf) (by rw [k13.2.2]; exact hw) hd)
    fun s4 ⟨hS, hf4, hc4, k4, _⟩ => ⟨hS, hT3.frame hf4, hc4, ?_, (k13.trans k4).mono (by simp)⟩
  refine (hf1.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
    ((og.mem.trans hm2) ▸ hf4.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
  · rw [List.mem_singleton.mp hr]; exact pR_sub_tab sP
  · rw [List.mem_singleton.mp hr]; exact pR_sub_S sP

/-- `S` unpacked into `f`, and the upper halves cleared. -/
theorem yepi_ok {fP sP : Addr} {F : Poly} {s : State} (hc : YConsts s) (hS : S16 s.mem (spW sP) F)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR fP).Disjoint (pR sP)) :
    WP isa yepi s fun s' => PolyIs s'.mem fP F ∧ Frame [pR fP] s.mem s'.mem := by
  simp only [yepi]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r9 = fP ∧ s1.gpr .rdx = spW sP ∧
      GOnly [.r9, .rdx] s s1 ∧ s1.ymmHi = s.ymmHi)
    (by
      simp only [leaR, oS]
      vrunm [hsi, hdi, sx_ofNat (show 256 < 2 ^ 31 by decide), RegUpd.ymmHi_setReg]
      exact ⟨by gonly, rfl⟩) fun s1 ⟨h9, hdx, og, hy⟩ => ?_)
  refine WP.seq (WP.mono (yunpack_ok (F := F) (lanes_gpr (s := s) (GOnly.lane og hy) (YOnly.refl [] s) hc (by decide)
    (by decide)) (by rw [og.mem]; exact hS) h9 hdx (by rw [og.keep.2.2]; exact hwf) (by rw [og.keep.2.2]; exact hw)
    hd) fun s2 ⟨hP, hf, _, _, _⟩ => ?_)
  vrunm
  exact ⟨hP, og.mem ▸ hf⟩

/-! ## Between the layers -/

/-- Between the layers: `S` holds `F`, and the table of `z` and the
constants are in place. -/
structure LIY (sP : Addr) (s₀ : State) (z : Nat → Zq) (F : Poly) (s : State) : Prop where
  S : S16 s.mem (spW sP) F
  T : TZ s.mem sP z
  c : YConsts s
  keep : Keep [.rax, .rcx, .rdx, .r8] s₀ s
  frame : Frame [sR (spW sP)] s₀.mem s.mem

/-- A layer, then `c`. -/
theorem LIY.seq {sP : Addr} {s₀ : State} {z : Nat → Zq} (hsi : s₀.gpr .rsi = sP) (hw : pR sP ∈ s₀.wr)
    {l c : Prog isa} {F F' : Poly} {Q : State → Prop}
    (hl : ∀ s, YConsts s → s.gpr .rsi = sP → S16 s.mem (spW sP) F → TZ s.mem sP z → pR sP ∈ s.wr →
      WP isa l s fun s' => S16 s'.mem (spW sP) F' ∧ BInvY sP s s')
    (hc : ∀ s, LIY sP s₀ z F' s → WP isa c s Q) {s : State} (hI : LIY sP s₀ z F s) :
    WP isa (.seq l c) s Q :=
  WP.seq (WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hsi]) hI.S hI.T (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => hc s' ⟨hS, hI.T.frame hb.frame, hb.consts,
      (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩)

end VG.Proof.MlKem.X86_64
