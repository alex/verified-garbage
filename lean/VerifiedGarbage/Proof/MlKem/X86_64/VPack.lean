import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM on x86-64: polynomials between `u32`s and words

Untrusted: everything here is checked by Lean. `vpack` stores the 256
`u32`s of a reduced polynomial as words (`vpack_ok`), and `vunpack` the
words back as `u32`s (`vunpack_ok`), eight at a time.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## Doublewords and words -/

theorem satSignedWord_small {x : BitVec 32} (h : x.toNat < 32768) : satSignedWord x = x.setWidth 16 := by
  have e : x.toInt = x.toNat := by rw [BitVec.toInt_eq_toNat_cond, ite_eq_left (by omega)]
  rw [satSignedWord, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem word_packssdw_small (a b : BitVec 128) {e : Nat} (he : e < 8)
    (ha : ∀ j < 4, (dword a j).toNat < 32768) (hb : ∀ j < 4, (dword b j).toNat < 32768) :
    (word (XBinOp.eval .packssdw a b) e).toNat = if e < 4 then (dword a e).toNat else (dword b (e - 4)).toNat := by
  rw [word_packssdw _ _ he]
  split
  · rw [satSignedWord_small (ha e (by omega)), BitVec.toNat_setWidth]; have := ha e (by omega); omega
  · rw [satSignedWord_small (hb (e - 4) (by omega)), BitVec.toNat_setWidth]; have := hb (e - 4) (by omega); omega

theorem dword_eq_words (x : BitVec 128) {j : Nat} (hj : j < 4) :
    (dword x j).toNat = (word x (2 * j)).toNat + 65536 * (word x (2 * j + 1)).toNat := by
  have h0 := word_dword x hj 0 (by decide)
  have h1 := word_dword x hj 1 (by decide)
  rw [Nat.mul_zero, Nat.add_zero] at h0
  rw [h0, h1, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.shiftRight_eq_div_pow]
  have := (dword x j).isLt
  omega

/-- The `u32`s that `punpcklwd` with zeros leaves: the low words, zero-extended. -/
theorem dword_punpcklwd0 (a : BitVec 128) {j : Nat} (hj : j < 4) :
    (dword (XBinOp.eval .punpcklwd a 0) j).toNat = (word a j).toNat := by
  rw [dword_eq_words _ hj, word_punpcklwd _ _ (by omega), word_punpcklwd _ _ (by omega),
    ite_eq_left (by omega), ite_eq_right (by omega), show 2 * j / 2 = j by omega,
    show (2 * j + 1) / 2 = j by omega]
  have : (word (0 : BitVec 128) j).toNat = 0 := by
    rw [word, BitVec.extractLsb'_toNat]; simp
  omega

/-- The `u32`s that `punpckhwd` with zeros leaves: the high words, zero-extended. -/
theorem dword_punpckhwd0 (a : BitVec 128) {j : Nat} (hj : j < 4) :
    (dword (XBinOp.eval .punpckhwd a 0) j).toNat = (word a (4 + j)).toNat := by
  rw [dword_eq_words _ hj, word_punpckhwd _ _ (by omega), word_punpckhwd _ _ (by omega),
    ite_eq_left (by omega), ite_eq_right (by omega), show 4 + 2 * j / 2 = 4 + j by omega,
    show 4 + (2 * j + 1) / 2 = 4 + j by omega]
  have : (word (0 : BitVec 128) (4 + j)).toNat = 0 := by
    rw [word, BitVec.extractLsb'_toNat]; simp
  omega

/-! ## Packing -/

theorem coeffAddr_off (p : Addr) (j k : Nat) :
    coeffAddr p j + BitVec.ofNat 64 (4 * k) = coeffAddr p (j + k) := by
  rw [coeffAddr, coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

/-- The eight coefficients of a reduced polynomial at `coeffAddr p j`, as the
words `packssdw` makes of them. -/
theorem lanes_pack {m : Mem} {p : Addr} {F : Poly} (hF : PolyIs m p F) {j : Nat} (hj : j + 8 ≤ 256) :
    Lanes (XBinOp.eval .packssdw (m.readW (coeffAddr p j) 128) (m.readW (coeffAddr p (j + 4)) 128))
      (fun e => F[j + e]!) := fun e he => by
  have hc : ∀ k, k < 256 → (coeffAt m p k).toNat = (F[k]!).val := fun k hk =>
    polyIs_toNat hF (by rw [n_eq]; exact hk)
  rw [word_packssdw_small _ _ he (fun k hk => by
      rw [dword_readW _ _ hk, coeffAddr_off, ← coeffAt_eq, hc _ (by omega)]; have := val_lt F[j + k]!; omega)
    (fun k hk => by
      rw [dword_readW _ _ hk, coeffAddr_off, ← coeffAt_eq, hc _ (by omega)]; have := val_lt F[j + 4 + k]!; omega)]
  split
  · rw [dword_readW _ _ (by omega), coeffAddr_off, ← coeffAt_eq, hc _ (by omega)]
  · rw [dword_readW _ _ (by omega), coeffAddr_off, ← coeffAt_eq, hc _ (by omega),
      show j + 4 + (e - 4) = j + e by omega]

/-- The words of the polynomial below `t`. -/
def S16p (m : Mem) (p : Addr) (F : Poly) (t : Nat) : Prop := ∀ i < t, (wordAt m p i).toNat = (F[i]!).val

theorem polyR_contains (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) : (pR p).Contains (coeffAddr p j) 16 :=
  Offset.contains_base p (by omega) (by omega)

theorem vpack_ok {fP sP : Addr} {F : Poly} {s : State} (hc : VConsts s) (hF : PolyIs s.mem fP F)
    (h9 : s.gpr .r9 = fP) (hdx : s.gpr .rdx = spW sP) (hrf : pR fP ∈ s.rd ++ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR fP).Disjoint (pR sP)) :
    WP isa vpack s fun s' => S16 s'.mem (spW sP) F ∧ Frame [sR (spW sP)] s.mem s'.mem ∧ VConsts s' ∧
      Keep [.r9, .rdx, .rcx] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hsub : Region.Sub (sR (spW sP)) (pR sP) := Offset.sub_base sP (by omega)
  refine WP.mono (wp_rcxLoop (N := 32) (by decide) (by decide)
    (fun u w => S16p w.mem (spW sP) F (8 * u) ∧ w.gpr .r9 = coeffAddr fP (8 * u) ∧
      w.gpr .rdx = wAddr (spW sP) (8 * u) ∧ Frame [sR (spW sP)] s.mem w.mem ∧ VConsts w ∧
      Keep [.r9, .rdx, .rcx] s w ∧ w.mxcsr = s.mxcsr)
    (fun w o hcx => ⟨fun _ h => absurd h (by omega), by rw [o.keep.gpr (by decide), h9, coeffAddr]; simp,
      by rw [o.keep.gpr (by decide), hdx, wAddr]; simp, by rw [o.mem]; exact Frame.refl _ _, o.consts hc,
      o.keep.mono (by simp), o.mxcsr⟩)
    (fun u hu w ⟨hP, h9', hdx', hf, hc', hk', hx'⟩ => ?_))
    fun w ⟨hP, _, _, hf, hc', hk', hx'⟩ => ⟨hP, hf, hc', hk', hx'⟩
  have hF' : PolyIs w.mem fP F := polyIs_frame hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd.sub_right hsub) hF
  have hrf' : pR fP ∈ w.rd ++ w.wr := by rw [hk'.2.1, hk'.2.2]; exact hrf
  have hw' : pR sP ∈ w.wr := by rw [hk'.2.2]; exact hw
  have r0 : InRegions (w.rd ++ w.wr) (coeffAddr fP (8 * u)) 16 := ⟨_, hrf', polyR_contains fP (by omega)⟩
  have r1 : InRegions (w.rd ++ w.wr) (coeffAddr fP (8 * u + 4)) 16 := ⟨_, hrf', polyR_contains fP (by omega)⟩
  have w0 : InRegions w.wr (wAddr (spW sP) (8 * u)) 16 := sp_in hw' (by omega)
  have a1 : coeffAddr fP (8 * u) + BitVec.ofNat 64 16 = coeffAddr fP (8 * u + 4) := coeffAddr_off _ _ 4
  vrunm [h9', hdx', r0, r1, w0, a1, sx32]
  have lp := lanes_pack hF' (j := 8 * u) (by omega)
  refine ⟨fun j hj => ?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_off,
      Nat.mul_succ],
    by rw [show (16 : BitVec 64) = BitVec.ofNat 64 (2 * 8) from rfl, wAddr_add, Nat.mul_succ], ?_, ?_, ?_, ?_⟩
  · rw [wordAt_write128 _ _ (by omega) _ (by omega)]
    split
    · rw [lp _ (by omega)]; dsimp only; rw [show 8 * u + (j - 8 * u) = j by omega]
    · exact hP j (by omega)
  · exact hf.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sR_contains _ (by omega)))
  · constructor <;> simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false] <;>
      [exact hc'.q; exact hc'.qinv]
  · refine ⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hk'.2.1,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hk'.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
    exact hk'.gpr (by simp [hr])
  · exact hx'

/-! ## Unpacking -/

theorem S16.frame {m m' : Mem} {p : Addr} {F : Poly} (h : S16 m p F) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (sR p).Disjoint r) : S16 m' p F := fun i hi => by
  rw [wordAt, hf.readW (Offset.contains_base p (by omega) (by omega)) hd (by decide)]; exact h i hi

/-- Coefficient `i` after storing `x` at coefficient `j`. -/
theorem coeffAt_write128 (m : Mem) (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) (x : BitVec 128) {i : Nat}
    (hi : i < 256) :
    coeffAt (m.writeW (coeffAddr p j) x) p i = if j ≤ i ∧ i < j + 4 then dword x (i - j) else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr p i = coeffAddr p j + BitVec.ofNat 64 (4 * (i - j)) by
      rw [coeffAddr_off, show j + (i - j) = i by omega]]
    exact readW_writeW128 _ _ _ (by omega)
  · exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- The coefficients below `t`. -/
def PolyP (m : Mem) (p : Addr) (F : Poly) (t : Nat) : Prop := ∀ i < t, (coeffAt m p i).toNat = (F[i]!).val

theorem vunpack_ok {fP sP : Addr} {F : Poly} {s : State} (hc : VConsts s) (hS : S16 s.mem (spW sP) F)
    (h9 : s.gpr .r9 = fP) (hdx : s.gpr .rdx = spW sP) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR fP).Disjoint (pR sP)) :
    WP isa vunpack s fun s' => PolyIs s'.mem fP F ∧ Frame [pR fP] s.mem s'.mem ∧ VConsts s' ∧
      Keep [.r9, .rdx, .rcx] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hsub : Region.Sub (sR (spW sP)) (pR sP) := Offset.sub_base sP (by omega)
  refine WP.seq (WP.mono (Q := fun (w : State) => w.xmm .xmm4 = 0 ∧ XOnly [.xmm4] s w)
    (by vrunm; exact ⟨by simp only [XBinOp.eval, BitVec.xor_self]; rfl, by xonly⟩) fun w0 ⟨hz, o0⟩ => ?_)
  refine WP.mono (wp_rcxLoop (N := 32) (by decide) (by decide)
    (fun u w => PolyP w.mem fP F (8 * u) ∧ w.gpr .r9 = coeffAddr fP (8 * u) ∧
      w.gpr .rdx = wAddr (spW sP) (8 * u) ∧ Frame [pR fP] s.mem w.mem ∧ VConsts w ∧ w.xmm .xmm4 = 0 ∧
      Keep [.r9, .rdx, .rcx] s w ∧ w.mxcsr = s.mxcsr)
    (fun w o hcx => ⟨fun _ h => absurd h (by omega),
      by rw [o.keep.gpr (by decide), o0.gpr, h9, coeffAddr]; simp,
      by rw [o.keep.gpr (by decide), o0.gpr, hdx, wAddr]; simp, by rw [o.mem, o0.mem]; exact Frame.refl _ _,
      o.consts (o0.consts hc (by decide) (by decide)), by rw [o.xmm, hz],
      Keep.trans (⟨fun r _ => by rw [o0.gpr], o0.rd, o0.wr⟩ : Keep [] s w0) (o.keep) |>.mono (by simp),
      by rw [o.mxcsr, o0.mxcsr]⟩)
    (fun u hu w ⟨hP, h9', hdx', hf, hc', hz', hk', hx'⟩ => ?_))
    fun w ⟨hP, _, _, hf, hc', _, hk', hx'⟩ => ⟨polyIs_of_toNat fun i hi => hP i (by rw [n_eq] at hi; omega),
      hf, hc', hk', hx'⟩
  have hS' : S16 w.mem (spW sP) F := hS.frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hd.sub_right hsub).symm
  have hwf' : pR fP ∈ w.wr := by rw [hk'.2.2]; exact hwf
  have r0 : InRegions (w.rd ++ w.wr) (wAddr (spW sP) (8 * u)) 16 :=
    sp_in (List.mem_append_right _ (by rw [hk'.2.2]; exact hw)) (by omega)
  have w0 : InRegions w.wr (coeffAddr fP (8 * u)) 16 := ⟨_, hwf', polyR_contains fP (by omega)⟩
  have w1 : InRegions w.wr (coeffAddr fP (8 * u + 4)) 16 := ⟨_, hwf', polyR_contains fP (by omega)⟩
  have a1 : coeffAddr fP (8 * u) + BitVec.ofNat 64 16 = coeffAddr fP (8 * u + 4) := coeffAddr_off _ _ 4
  have ll := lanes_load hS' (j := 8 * u) (by omega)
  vrunm [h9', hdx', r0, w0, w1, a1, sx32, hz']
  refine ⟨fun j hj => ?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_off,
      Nat.mul_succ],
    by rw [show (16 : BitVec 64) = BitVec.ofNat 64 (2 * 8) from rfl, wAddr_add, Nat.mul_succ], ?_, ?_, ?_, ?_⟩
  · rw [coeffAt_write128 _ _ (by omega) _ (by omega), coeffAt_write128 _ _ (by omega) _ (by omega)]
    split
    · rw [dword_punpckhwd0 _ (by omega), word_movdqa, ll _ (by omega)]; dsimp only
      rw [show 8 * u + (4 + (j - (8 * u + 4))) = j by omega]
    · split
      · rw [dword_punpcklwd0 _ (by omega), ll _ (by omega)]; dsimp only
        rw [show 8 * u + (j - 8 * u) = j by omega]
      · exact hP j (by omega)
  · exact hf.trans (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (polyR_contains fP (by omega))).writeW
      (List.mem_singleton_self _) _ (polyR_contains fP (by omega)))
  · constructor <;> simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, reduceCtorEq, ite_false] <;>
      [exact hc'.q; exact hc'.qinv]
  · refine ⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hk'.2.1,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hk'.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
    exact hk'.gpr (by simp [hr])
  · exact hx'

/-! ## The multiplication by 3303 -/

/-- `vmont` then `vcadd`: each word of `d` times the constant `c`, reduced, with
`c · 2¹⁶ mod q` in the words of `z`. -/
theorem vmulc_ok {d z t : XReg} (h2 : t ≠ d) (h3 : z ≠ t) (h4 : XReg.xmm14 ≠ d) (h5 : XReg.xmm15 ≠ d)
    (h6 : XReg.xmm14 ≠ t) (h7 : XReg.xmm15 ≠ t) {s : State} (hc : VConsts s) {x : Nat → Zq} {c : Zq} (hx : Lanes (s.xmm d) x)
    (hz : ZLanes (s.xmm z) fun _ => c) :
    WP isa (.block (vmont d z t ++ vcadd d t)) s fun s' => Lanes (s'.xmm d) (fun i => c * x i) ∧
      XOnly [d, t] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (vmont_ok h2 h3 h5 h6 h7 hc) fun s1 ⟨l1, o1⟩ =>
    WP.mono (vcadd_ok h2 h7 (o1.consts hc
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h6⟩)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h5, h7⟩)))
      fun s2 ⟨l2, o2⟩ => ⟨fun i hi => ?_, (o1.trans o2).mono (by simp)⟩
  · rw [l2 i hi]; dsimp only; rw [l1 i hi]; dsimp only
    have hxl := val_lt (x i)
    have hxi := W.toInt_of_lt (a := word (s.xmm d) i) (by rw [hx i hi]; exact hxl)
    rw [hx i hi] at hxi
    have r := W.mulZ_spec (b := word (s.xmm d) i) (y := x i) (ζ := c) (by omega) (by omega)
      (by rw [hxi, Int.sub_self]; rfl) (hz i hi)
    have n := W.toNat_of_toInt (a := W.caddW (W.montW (word (s.xmm d) i) (word (s.xmm z) i)))
      (by rw [r]; exact Int.natCast_nonneg _)
    rw [r] at n
    exact Int.ofNat.inj n

/-- `3303 · 2¹⁶ mod q = 512` in every word, as `vscale` makes it. -/
theorem zlanes_512 : ZLanes (shufDwords ((0 : BitVec 64) ++ BitVec.setWidth 64 (0x02000200 : BitVec 32)) 0)
    fun _ => (3303 : Zq) := fun i hi => by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem vscale_ok {sP : Addr} {F : Poly} {s : State} (hc : VConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hw : pR sP ∈ s.wr) :
    WP isa vscale s fun s' => S16 s'.mem (spW sP) (F.map (· * 3303)) ∧ BInv sP s s' := by
  refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .rdx = spW sP ∧
      ZLanes (w.xmm .xmm13) (fun _ => (3303 : Zq)) ∧ GKeep [.rdx, .rax] s w ∧ VConsts w)
    (by
      simp only [leaR, oS]
      vrunm [sx_ofNat (show 256 < 2 ^ 31 by decide), hsi]
      refine ⟨zlanes_512, ⟨⟨fun r hr => ?_, rfl, rfl⟩, rfl, rfl⟩, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      · constructor <;> simp only [xmm_setXmm, RegUpd.xmm_setReg, reduceCtorEq, ite_false] <;>
          [exact hc.q; exact hc.qinv])
    fun w ⟨hdx, hz, og, hcw⟩ => ?_)
  refine WP.mono (wp_rcxLoop (N := 32) (by decide) (by decide)
    (fun u v => (∀ j < 256, (wordAt v.mem (spW sP) j).toNat = (if j < 8 * u then F[j]! * 3303 else F[j]!).val) ∧
      v.gpr .rdx = wAddr (spW sP) (8 * u) ∧ v.xmm .xmm13 = w.xmm .xmm13 ∧ BInv sP s v)
    (fun v o hcx => ⟨fun j hj => by rw [ite_eq_right (by omega), o.mem, og.mem]; exact hS j hj,
      by rw [o.keep.gpr (by decide), hdx, wAddr]; simp, by rw [o.xmm],
      ⟨(og.keep.trans o.keep).mono (by simp), by rw [o.mem, og.mem]; exact Frame.refl _ _, o.consts hcw,
        by rw [o.mxcsr, og.mxcsr]⟩⟩)
    (fun u hu v ⟨hP, hdx', hz', hb⟩ => ?_))
    fun v ⟨hP, _, _, hb⟩ => ⟨fun j hj => by rw [hP j hj, ite_eq_left (by omega), map_mul_get _ (by rw [n_eq]; exact hj)],
      hb⟩
  have hw' : pR sP ∈ v.wr := by rw [hb.keep.2.2]; exact hw
  have r0 := sp_in (List.mem_append_right v.rd hw') (j := 8 * u) (by omega)
  have w0 := sp_in hw' (j := 8 * u) (by omega)
  rw [show [Instr.movdquLoad .xmm3 (at_ .rdx 0)] ++ vmont .xmm3 .xmm13 .xmm2 ++ vcadd .xmm3 .xmm2 ++
      [.movdquStore (at_ .rdx 0) .xmm3, .alu .add .rdx (.imm 16)] ++ [.alu .sub .rcx (.imm 1)] =
      [Instr.movdquLoad .xmm3 (at_ .rdx 0)] ++ ((vmont .xmm3 .xmm13 .xmm2 ++ vcadd .xmm3 .xmm2) ++
        [.movdquStore (at_ .rdx 0) .xmm3, .alu .add .rdx (.imm 16), .alu .sub .rcx (.imm 1)]) by
      simp [List.append_assoc], WP.block_append_iff]
  vrunm [hdx', r0]
  rw [WP.block_append_iff]
  have lx : Lanes ((v.setXmm .xmm3 (v.mem.readW (wAddr (spW sP) (8 * u)) 128)).xmm .xmm3)
      (fun e => F[8 * u + e]!) := fun e he => by
    rw [xmm_setXmm, ifp rfl, word_readW _ _ he, wAddr_add, ← wordAt, hP _ (by omega), ite_eq_right (by omega)]
  refine WP.mono (vmulc_ok (d := .xmm3) (z := .xmm13) (t := .xmm2) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (hb.consts.setXmm (by decide) (by decide) _) lx (c := 3303)
    (by rw [xmm_setXmm, ifn (by decide), hz']; exact hz)) fun v2 ⟨l2, o2⟩ => ?_
  have g2 : v2.gpr .rdx = v.gpr .rdx := by rw [o2.gpr]; rfl
  have e2 : v2.rd = v.rd ∧ v2.wr = v.wr := ⟨o2.rd, o2.wr⟩
  have m2 : v2.mem = v.mem := o2.mem
  vrunm [g2, e2.1, e2.2, m2, hdx', w0]
  have rc2 : v2.gpr .rcx = v.gpr .rcx := by rw [o2.gpr]; rfl
  refine ⟨⟨fun j hj => ?_, by rw [show (16 : BitVec 64) = BitVec.ofNat 64 (2 * 8) from rfl, wAddr_add, Nat.mul_succ],
    by rw [o2.xmm _ (by decide), xmm_setXmm, ifn (by decide), hz'], ?_⟩, by rw [rc2], by rw [rc2]⟩
  · rw [wordAt_write128 _ _ (by omega) _ hj]
    split
    · rw [l2 _ (by omega)]; dsimp only
      rw [ite_eq_left (by omega), show 8 * u + (j - 8 * u) = j by omega, Fin.mul_comm]
    · rw [hP j hj]
      by_cases h : j < 8 * u
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]
  · refine hb.trans ⟨⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]⟩,
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sR_contains _ (by omega)), ?_,
      by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; exact o2.mxcsr⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      rw [o2.gpr]; rfl
    · exact ⟨by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact (o2.consts
          (hb.consts.setXmm (by decide) (by decide) _) (by decide) (by decide)).q,
        by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact (o2.consts
          (hb.consts.setXmm (by decide) (by decide) _) (by decide) (by decide)).qinv⟩

/-! ## The table of zetas -/

theorem readW_writeW64_16 (m : Mem) (a : Addr) (v : BitVec 64) {j : Nat} (hj : j < 4) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (2 * j)) 16 = v.extractLsb' (16 * j) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_read _ _ (by omega)]
  simp only [Mem.writeW, Mem.write]
  rw [show a + BitVec.ofNat 64 (2 * j) + BitVec.ofNat 64 (i / 8) - a = BitVec.ofNat 64 (2 * j + i / 8) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show 2 * j + i / 8 < 64 / 8 by omega, ite_true, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth]
  rw [decide_eq_true (by omega), decide_eq_true (by omega), Bool.true_and, Bool.true_and]
  exact congrArg _ (by omega)

/-- Four words packed into a quadword, as `wordTab` makes its immediates. -/
theorem quad_word {t0 t1 t2 t3 : Nat} (h0 : t0 < 65536) (h1 : t1 < 65536) (h2 : t2 < 65536) (h3 : t3 < 65536)
    {e : Nat} (he : e < 4) :
    ((BitVec.ofNat 64 (t0 + 2 ^ 16 * t1 + 2 ^ 32 * t2 + 2 ^ 48 * t3)).extractLsb' (16 * e) 16).toNat =
      [t0, t1, t2, t3][e]! := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow, Nat.reduceMul, List.getElem!_cons_zero, List.getElem!_cons_succ] <;> omega

theorem zmTab_lt (k : Nat) : zmTab k < 65536 := by
  have : zmTab k < 3329 := Nat.mod_lt _ (by decide)
  omega

theorem zmTab_eq (k : Nat) : zmTab k = (zeta k).val * 65536 % 3329 := by
  rw [zmTab, zeta, val_pow, Nat.mod_mul_mod]; rfl

/-- The table, stored at `scratch` (`rsi`), through `r9`. -/
theorem wordTab_ok {sP : Addr} {s : State} (hsi : s.gpr .rsi = sP) (hw : pR sP ∈ s.wr) :
    WP isa (.block (wordTab zmTab 128 .rsi 0)) s fun s' => T16 s'.mem sP ∧
      Frame [⟨sP, 256⟩] s.mem s'.mem ∧ Keep [.r9] s s' ∧ s'.mxcsr = s.mxcsr ∧ s'.xmm = s.xmm := by
  refine WP.mono (wp_range_flatMap (M := isa) (N := 32) (fun i w =>
      (∀ k < 4 * i, (wordAt w.mem sP k).toNat = zmTab k) ∧ Frame [⟨sP, 256⟩] s.mem w.mem ∧
        Keep [.r9] s w ∧ w.mxcsr = s.mxcsr ∧ w.xmm = s.xmm)
    (fun i w hi ⟨hT, hf, hk, hm, hx⟩ => ?_) 32 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega), Frame.refl _ _, Keep.refl _ _, rfl, rfl⟩)
    fun w ⟨hT, hf, hk, hm, hx⟩ => ⟨fun k hk' => by rw [hT k (by omega), zmTab_eq], hf, hk, hm, hx⟩
  have hsi' : w.gpr .rsi = sP := by rw [hk.gpr (by decide), hsi]
  have w0 : InRegions w.wr (sP + BitVec.ofNat 64 (0 + 8 * i)) 8 :=
    ⟨_, by rw [hk.2.2]; exact hw, Offset.contains_base sP (by omega) (by omega)⟩
  have hV : ∀ e < 4, ((BitVec.ofNat 64 (zmTab (4 * i) + 2 ^ 16 * zmTab (4 * i + 1) +
      2 ^ 32 * zmTab (4 * i + 2) + 2 ^ 48 * zmTab (4 * i + 3))).extractLsb' (16 * e) 16).toNat =
        zmTab (4 * i + e) := fun e he => by
    rw [quad_word (zmTab_lt _) (zmTab_lt _) (zmTab_lt _) (zmTab_lt _) he]
    rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;> rfl
  vrunm [hsi', w0]
  generalize BitVec.ofNat 64 (zmTab (4 * i) + 2 ^ 16 * zmTab (4 * i + 1) +
      2 ^ 32 * zmTab (4 * i + 2) + 2 ^ 48 * zmTab (4 * i + 3)) = V at hV ⊢
  refine ⟨fun k hk' => ?_, hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base sP (by omega) (by omega)),
    ⟨fun r hr => ?_, hk.2.1, hk.2.2⟩, hm, hx⟩
  · by_cases h : 4 * i ≤ k
    · rw [wordAt, wAddr, show sP + BitVec.ofNat 64 (2 * k) =
          sP + BitVec.ofNat 64 (0 + 8 * i) + BitVec.ofNat 64 (2 * (k - 4 * i)) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact congrArg _ (congrArg _ (by omega)),
        readW_writeW64_16 _ _ _ (by omega), hV _ (by omega), show 4 * i + (k - 4 * i) = k by omega]
    · rw [wordAt, Mem.readW_writeW_sep (Offset.sep sP (by omega) (by omega) (by omega)) (by decide)]
      exact hT k (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
    exact hk.1 r (by simp [hr])

end VG.Proof.MlKem.X86_64
