import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Impl.MlKem.X86_64.NttAvx2

/-!
# ML-KEM on x86-64: the NTT and its inverse on AVX2 registers, the pieces

Untrusted: everything here is checked by Lean. The layers' result
coefficient by coefficient (`layF_get`); the table of zetas, in whatever
order (`TZ`); polynomials as words loaded into and stored from both lanes of
a register (`lanes_loadY`, `s16_write2Y`); and the zetas the loads of
`NttAvx2.lean` leave in the lanes of `ymm13` (`yzeta1_ok`, `yzetaS_ok`,
`yzeta8_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## A layer, coefficient by coefficient -/

section
variable {op : Zq → Zq → Zq → Zq × Zq} {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hblk

/-- Each coefficient after the first `b` blocks of the layer with `len`. -/
theorem layF_get (F : Poly) {len : Nat} (hl : 0 < len) (zi : Nat → Nat) {b : Nat} (hb : 2 * len * b ≤ 256)
    {j : Nat} (hj : j < 256) :
    (layF blk F len zi b)[j]! = if j < 2 * len * b then
      (if j % (2 * len) < len then (op F[j]! F[j + len]! (zeta (zi (j / (2 * len))))).1
        else (op F[j - len]! F[j]! (zeta (zi (j / (2 * len))))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by omega)]; rfl
  | succ b ih =>
    have hb' : 2 * len * b + 2 * len ≤ 256 := by rw [Nat.mul_succ] at hb; exact hb
    rw [layF, foldl_range_succ, ← layF,
      hblk.get _ len _ _ len hl (Nat.le_refl _) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    have hd : ∀ i, 2 * len * b ≤ i → i < 2 * len * b + 2 * len → i / (2 * len) = b ∧
        i % (2 * len) = i - 2 * len * b := fun i h1 h2 => by
      have e1 : i / (2 * len) = b := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.mul_comm]; exact h1
        · rw [Nat.succ_mul, Nat.mul_comm b]; exact h2
      refine ⟨e1, ?_⟩
      have := Nat.div_add_mod i (2 * len)
      rw [e1] at this; omega
    by_cases h1 : 2 * len * b ≤ j ∧ j < 2 * len * b + len
    · obtain ⟨d1, d2⟩ := hd j h1.1 (by omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ih (by omega) hj, ih (by omega) (by omega), d1,
        ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show j % (2 * len) < len by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * b by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j + len < 2 * len * b by omega))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      by_cases h2 : 2 * len * b + len ≤ j ∧ j < 2 * len * b + len + len
      · obtain ⟨d1, d2⟩ := hd j (by omega) (by omega)
        rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ih (by omega) (by omega), ih (by omega) hj, d1,
          ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j % (2 * len) < len by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j - len < 2 * len * b by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * b by omega))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ih (by omega) hj]
        by_cases h3 : j < 2 * len * b
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h3),
            ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega))]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h3),
            ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega))]

end

/-! ## The table of zetas -/

/-- The 128 words `z k · 2¹⁶ mod q` at `p`. -/
def TZ (m : Mem) (p : Addr) (z : Nat → Zq) : Prop := ∀ k < 128, (wordAt m p k).toNat = (z k).val * 65536 % 3329

/-- Writes to the polynomial's words, 256 bytes above the table, keep it. -/
theorem TZ.frame {m m' : Mem} {p : Addr} {z : Nat → Zq} (h : TZ m p z) (hf : Frame [sR (p + BitVec.ofNat 64 256)] m m') :
    TZ m' p z := fun k hk => by
  rw [wordAt, hf.readW (r := ⟨p, 256⟩) (Offset.contains_base p (by omega) (by omega))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint p (by omega) (by omega))
    (by decide)]
  exact h k hk

/-- The zetas that `vpunpcklwd` and `vpshufd` with `o` leave in a lane, from the words at `wAddr zP k`. -/
theorem zeta_lanesZ (o : BitVec 8) {zP : Addr} {k : Nat} {z : Nat → Zq} (hk : ∀ j < 4, k + sel o j < 128) {m : Mem}
    (ht : TZ m zP z) :
    ZLanes (shufDwords (XBinOp.eval .punpcklwd (m.readW (wAddr zP k) 128) (m.readW (wAddr zP k) 128)) o)
      (fun i => z (k + sel o (i / 2))) := fun i hi => by
  dsimp only
  have hs := sel_lt o (i / 2)
  have hk' := hk (i / 2) (by omega)
  rw [word_shufDwords _ _ hi]
  generalize sel o (i / 2) = t at *
  rw [word_punpcklwd _ _ (by omega), ite_self, show (2 * t + i % 2) / 2 = t by omega,
    word_readW _ _ (by omega), wAddr_add]
  exact ht _ hk'

/-! ## Words in both lanes -/

/-- Lane `l` of a 256-bit load of the words of a polynomial. -/
theorem lanes_loadY {m : Mem} {p : Addr} {F : Poly} (h : S16 m p F) {j : Nat} (hj : j + 16 ≤ 256) {l : Nat}
    (hl : l < 2) : Lanes (m.readW (wAddr p j + BitVec.ofNat 64 (16 * l)) 128) (fun e => F[j + 8 * l + e]!) := by
  rw [show 16 * l = 2 * (8 * l) by omega, wAddr_add]
  exact lanes_load h (by omega)

/-- Word `e` of a 256-bit register, as stored. -/
theorem word_ymm (s : State) (r : XReg) {e : Nat} (he : e < 16) :
    (s.ymm r).extractLsb' (8 * (2 * e)) (8 * 2) = word (s.lane r (e / 8)) (e % 8) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.ymm, State.lane, word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    decide_eq_true hj, Bool.true_and]
  by_cases h : e < 8
  · simp only [show 8 * (2 * e) + j < 128 by omega, ite_true, show e / 8 = 0 by omega]
    exact congrArg _ (by omega)
  · simp only [show ¬ 8 * (2 * e) + j < 128 by omega, ite_false, show e / 8 = 1 by omega, Nat.one_ne_zero]
    exact congrArg _ (by omega)

/-- Word `i` after storing `x` (256 bits) at word `j`. -/
theorem wordAt_write256 (m : Mem) (p : Addr) {j : Nat} (hj : j + 16 ≤ 256) (x : BitVec 256) {i : Nat}
    (hi : i < 256) :
    wordAt (m.writeW (wAddr p j) x) p i =
      if j ≤ i ∧ i < j + 16 then x.extractLsb' (8 * (2 * (i - j))) (8 * 2) else wordAt m p i := by
  split
  · rename_i h
    rw [wordAt, show wAddr p i = wAddr p j + BitVec.ofNat 64 (2 * (i - j)) by
      rw [wAddr_add, show j + (i - j) = i by omega]]
    exact readW_writeW_inside (k := 2 * (i - j)) (n := 2) _ _ _ (by omega) (by decide)
  · exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- Two registers stored into the words of a polynomial, with the lanes `a` and `b`. -/
theorem s16_write2Y {m : Mem} {p : Addr} {P R : Poly} (hP : S16 m p P) {j j' : Nat}
    (hj : j + 16 ≤ 256) (hj' : j' + 16 ≤ 256) (hsep : j + 16 ≤ j' ∨ j' + 16 ≤ j) {s : State} {x y : XReg}
    {a b : Nat → Zq} (hx : ∀ l < 2, Lanes (s.lane x l) (fun e => a (8 * l + e)))
    (hy : ∀ l < 2, Lanes (s.lane y l) (fun e => b (8 * l + e)))
    (hR : ∀ i < 256, R[i]! = if j ≤ i ∧ i < j + 16 then a (i - j)
      else if j' ≤ i ∧ i < j' + 16 then b (i - j') else P[i]!) :
    S16 ((m.writeW (wAddr p j) (s.ymm x)).writeW (wAddr p j') (s.ymm y)) p R := fun i hi => by
  rw [wordAt_write256 _ _ hj' _ hi, wordAt_write256 _ _ hj _ hi, hR i hi]
  by_cases h1 : j' ≤ i ∧ i < j' + 16
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true h1), word_ymm _ _ (by omega)]
    have := hy ((i - j') / 8) (by omega) ((i - j') % 8) (Nat.mod_lt _ (by omega))
    rw [this]; exact congrArg _ (congrArg _ (by omega))
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : j ≤ i ∧ i < j + 16
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2), word_ymm _ _ (by omega)]
      have := hx ((i - j) / 8) (by omega) ((i - j) % 8) (Nat.mod_lt _ (by omega))
      rw [this]; exact congrArg _ (congrArg _ (by omega))
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false h2),
        ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact hP i hi

theorem sR_containsY (p : Addr) {j : Nat} (hj : j + 16 ≤ 256) : (sR p).Contains (wAddr p j) 32 :=
  Offset.contains_base p (by omega) (by omega)

theorem frame_write2Y {m m' : Mem} {p : Addr} (hf : Frame [sR p] m m') {j j' : Nat} (hj : j + 16 ≤ 256)
    (hj' : j' + 16 ≤ 256) (x y : BitVec 256) :
    Frame [sR p] m ((m'.writeW (wAddr p j) x).writeW (wAddr p j') y) :=
  (hf.writeW (List.mem_singleton_self _) x (sR_containsY p hj)).writeW (List.mem_singleton_self _) y
    (sR_containsY p hj')

/-! ## Across lanes -/

/-- `vperm2i128`. -/
theorem yperm_ok {d a b : XReg} {n : BitVec 8} (s : State) :
    WP isa (.block [.vop (.vperm2i128 d a b n)]) s fun s' =>
      (∀ l < 2, s'.lane d l = perm2Lanes (s.lane a) (s.lane b) n l) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl]; rcases lane01 hl with rfl | rfl <;> rfl
  · rw [State.lane_setV256, ifn (by simpa using hr)]

theorem perm20 (a b : Nat → BitVec 128) {l : Nat} (hl : l < 2) :
    perm2Lanes a b 0x20 l = if l = 0 then a 0 else b 0 := by
  rcases lane01 hl with rfl | rfl <;> rfl

theorem perm31 (a b : Nat → BitVec 128) {l : Nat} (hl : l < 2) :
    perm2Lanes a b 0x31 l = if l = 0 then a 1 else b 1 := by
  rcases lane01 hl with rfl | rfl <;> rfl

theorem q256lo (a b : BitVec 128) {i : Nat} (hi : i < 2) : qword256 (b ++ a) i = qword a i :=
  BitVec.extractLsb'_append_eq_of_add_le (by omega)

theorem q256hi (a b : BitVec 128) (i : Nat) : qword256 (b ++ a) (2 + i) = qword b i := by
  rw [qword256, BitVec.extractLsb'_append_eq_of_le (by omega), show 64 * (2 + i) - 128 = 64 * i by omega]; rfl

theorem lo4 (w x y z : BitVec 64) : (w ++ x ++ y ++ z).extractLsb' 0 128 = y ++ z := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and, Nat.zero_add]
  by_cases h : i < 64
  · simp only [h, ite_true]
  · simp only [h, ite_false, show i - 64 < 64 by omega, ite_true]

theorem hi4 (w x y z : BitVec 64) : (w ++ x ++ y ++ z).extractLsb' 128 128 = w ++ x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 128 + i < 64 by omega, ite_false, show ¬ 128 + i - 64 < 64 by omega]
  by_cases h : i < 64
  · simp only [h, ite_true, show 128 + i - 64 - 64 < 64 by omega]; exact congrArg _ (by omega)
  · simp only [h, ite_false, show ¬ 128 + i - 64 - 64 < 64 by omega]; exact congrArg _ (by omega)

theorem permD8 (a b : BitVec 128) :
    permQwords (b ++ a) 0xD8 = qword256 (b ++ a) (2 + 1) ++ qword256 (b ++ a) 1 ++
      qword256 (b ++ a) (2 + 0) ++ qword256 (b ++ a) 0 := rfl

/-- `vpermq` with `0xD8`: lane 0 is `punpcklqdq` of the two lanes. -/
theorem permD8_lo (a b : BitVec 128) :
    (permQwords (b ++ a) 0xD8).extractLsb' 0 128 = XBinOp.eval .punpcklqdq a b := by
  rw [permD8, q256hi, q256hi, q256lo _ _ (by decide), q256lo _ _ (by decide), lo4]; rfl

/-- `vpermq` with `0xD8`: lane 1 is `punpckhqdq` of the two lanes. -/
theorem permD8_hi (a b : BitVec 128) :
    (permQwords (b ++ a) 0xD8).extractLsb' 128 128 = XBinOp.eval .punpckhqdq a b := by
  rw [permD8, q256hi, q256hi, q256lo _ _ (by decide), q256lo _ _ (by decide), hi4]; rfl

/-- `vpermq d, r, 0xD8`. -/
theorem ypermq_ok {d r : XReg} (s : State) :
    WP isa (.block [.vop (.vpermq d r 0xD8)]) s fun s' =>
      s'.lane d 0 = XBinOp.eval .punpcklqdq (s.lane r 0) (s.lane r 1) ∧
      s'.lane d 1 = XBinOp.eval .punpckhqdq (s.lane r 0) (s.lane r 1) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r' hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl, ifp rfl, State.ymm_eq, permD8_lo]
  · rw [State.lane_setV256, ifp rfl, ifn (by decide), State.ymm_eq, permD8_hi]
  · rw [State.lane_setV256, ifn (by simpa using hr)]

/-! ## The zetas -/

theorem wp_cons_iff {i : Instr} {l : List Instr} {s : State} {Q : State → Prop} :
    WP isa (.block (i :: l)) s Q ↔ WP isa (.block [i]) s fun s1 => WP isa (.block l) s1 Q := by
  rw [← WP.block_append_iff]; rfl

/-- A 128-bit load into both lanes. -/
theorem ybcast_ok {s : State} {p : Reg} {off : Nat} {d : XReg}
    (h : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 off) 16) :
    WP isa (.block [.vbroadcasti128 d (at_ p off)]) s fun s' =>
      (∀ l < 2, s'.lane d l = s.mem.readW (s.gpr p + BitVec.ofNat 64 off) 128) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, ea_at, h, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl]; rcases lane01 hl with rfl | rfl <;> rfl
  · rw [State.lane_setV256, ifn (by simpa using hr)]

theorem blend0 (a b : BitVec 128) : blendDwords a b (BitVec.extractLsb' 0 4 (0xF0 : BitVec 8)) = a :=
  ext_dword (by simp [blendDwords]) (by simp [blendDwords]) (by simp [blendDwords]) (by simp [blendDwords])

theorem blendF (a b : BitVec 128) : blendDwords a b (BitVec.extractLsb' 4 4 (0xF0 : BitVec 8)) = b :=
  ext_dword (by simp [blendDwords]) (by simp [blendDwords]) (by simp [blendDwords]) (by simp [blendDwords])

/-- `vpblendd d, a, b, 0xF0`: lane 0 of `a` and lane 1 of `b`. -/
theorem yblend_ok {d a b : XReg} (s : State) :
    WP isa (.block [.vop (.vpblendd .l256 d a b 0xF0)]) s fun s' =>
      s'.lane d 0 = s.lane a 0 ∧ s'.lane d 1 = s.lane b 1 ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl, ifp rfl, blend0]
  · rw [State.lane_setV256, ifp rfl, ifn (by decide), blendF]
  · rw [State.lane_setV256, ifn (by simpa using hr)]

/-- `vzeta 0`'s shuffles (`Ntt.lean`). -/
theorem zsse1_ok (t : State) :
    WP isa (.block [xb .punpcklwd .xmm13 .xmm13, .xop (.pshufd .xmm13 .xmm13 0)]) t fun t' =>
      t'.xmm .xmm13 = shufDwords (XBinOp.eval .punpcklwd (t.xmm .xmm13) (t.xmm .xmm13)) 0 ∧ XOnly [.xmm13] t t' := by
  simp only [xb]
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

theorem yzeta1_ok {zP : Addr} {k : Nat} {z : Nat → Zq} (hk : k < 128) {s : State} (h8 : s.gpr .r8 = wAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (wAddr zP k) 16) (ht : TZ s.mem zP z) :
    WP isa (.block yzeta1) s fun s' => (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun _ => z k)) ∧ YOnly [.xmm13] s s' := by
  rw [yzeta1, wp_cons_iff]
  refine WP.mono (ybcast_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨b1, o1⟩ => ?_
  refine WP.mono (ylanes (by decide) (P := fun l t => t.xmm .xmm13 =
      shufDwords (XBinOp.eval .punpcklwd (s1.lane .xmm13 l) (s1.lane .xmm13 l)) 0)
    fun l _ => zsse1_ok (s1.proj l)) fun s2 ⟨l2, o2⟩ => ⟨fun l hl => ?_, (o1.trans o2).mono (by simp)⟩
  have e : s2.lane .xmm13 l = _ := l2 l hl
  rw [e, b1 l hl, h8, add_ofNat_zero]
  intro i hi
  rw [zeta_lanesZ 0 (k := k) (fun j _ => by rw [sel_zero]; omega) ht i hi]
  dsimp only; rw [sel_zero, Nat.add_zero]

/-- `yzetaS`'s shuffles in each lane. -/
theorem zsseS_ok (o₀ o₁ : BitVec 8) (t : State) :
    WP isa (.block [xb .punpcklwd .xmm13 .xmm13, .xop (.pshufd .xmm2 .xmm13 o₁), .xop (.pshufd .xmm13 .xmm13 o₀)]) t
      fun t' => (t'.xmm .xmm13 = shufDwords (XBinOp.eval .punpcklwd (t.xmm .xmm13) (t.xmm .xmm13)) o₀ ∧
        t'.xmm .xmm2 = shufDwords (XBinOp.eval .punpcklwd (t.xmm .xmm13) (t.xmm .xmm13)) o₁) ∧
        XOnly [.xmm13, .xmm2] t t' := by
  simp only [xb]
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

theorem yzetaS_ok (o₀ o₁ : BitVec 8) {zP : Addr} {k : Nat} {z : Nat → Zq} (hk0 : ∀ j < 4, k + sel o₀ j < 128)
    (hk1 : ∀ j < 4, k + sel o₁ j < 128) {s : State} (h8 : s.gpr .r8 = wAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (wAddr zP k) 16) (ht : TZ s.mem zP z) :
    WP isa (.block (yzetaS o₀ o₁)) s fun s' => ZLanes (s'.lane .xmm13 0) (fun i => z (k + sel o₀ (i / 2))) ∧
      ZLanes (s'.lane .xmm13 1) (fun i => z (k + sel o₁ (i / 2))) ∧ YOnly [.xmm13, .xmm2] s s' := by
  rw [yzetaS, WP.block_append_iff, wp_cons_iff]
  refine WP.mono (ybcast_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨b1, o1⟩ => ?_
  refine WP.mono (ylanes (by rfl) (P := fun l t =>
      t.xmm .xmm13 = shufDwords (XBinOp.eval .punpcklwd (s1.lane .xmm13 l) (s1.lane .xmm13 l)) o₀ ∧
      t.xmm .xmm2 = shufDwords (XBinOp.eval .punpcklwd (s1.lane .xmm13 l) (s1.lane .xmm13 l)) o₁)
    fun l _ => zsseS_ok o₀ o₁ (s1.proj l)) fun s2 ⟨l2, o2⟩ => ?_
  refine WP.mono (yblend_ok s2) fun s3 ⟨e0, e1, o3⟩ => ⟨?_, ?_, ((o1.trans o2).trans o3).mono (by simp)⟩
  · have e : s2.lane .xmm13 0 = _ := (l2 0 (by decide)).1
    rw [e0, e, b1 0 (by decide), h8, add_ofNat_zero]
    exact zeta_lanesZ o₀ hk0 ht
  · have e : s2.lane .xmm2 1 = _ := (l2 1 (by decide)).2
    rw [e1, e, b1 1 (by decide), h8, add_ofNat_zero]
    exact zeta_lanesZ o₁ hk1 ht

/-- `yzeta8`'s shuffles in each lane. -/
theorem zsse8_ok (t : State) :
    WP isa (.block [xmov .xmm1 .xmm2, xb .punpcklwd .xmm1 .xmm2, xb .punpckhwd .xmm2 .xmm2, xmov .xmm13 .xmm1,
      xb .punpcklqdq .xmm13 .xmm2, xb .punpckhqdq .xmm1 .xmm2]) t
      fun t' => (t'.xmm .xmm13 = XBinOp.eval .punpcklqdq (XBinOp.eval .punpcklwd (t.xmm .xmm2) (t.xmm .xmm2))
          (XBinOp.eval .punpckhwd (t.xmm .xmm2) (t.xmm .xmm2)) ∧
        t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (XBinOp.eval .punpcklwd (t.xmm .xmm2) (t.xmm .xmm2))
          (XBinOp.eval .punpckhwd (t.xmm .xmm2) (t.xmm .xmm2))) ∧
        XOnly [.xmm1, .xmm2, .xmm13] t t' := by
  simp only [xb, xmov]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

/-- The word `yzeta8` leaves at `i` of lane `l`, of the eight loaded words `x`. -/
theorem word_z8 (x : BitVec 128) {l i : Nat} (hl : l < 2) (hi : i < 8) :
    word ((if l = 0 then XBinOp.eval .punpcklqdq else XBinOp.eval .punpckhqdq)
      (XBinOp.eval .punpcklwd x x) (XBinOp.eval .punpckhwd x x)) i = word x (2 * l + i / 2 + 2 * (i / 4)) := by
  rcases lane01 hl with rfl | rfl
  · simp only [ite_true]
    rw [word_punpcklqdq _ _ hi]
    split
    · rw [word_punpcklwd _ _ (by omega), ite_self]; congr 1; omega
    · rw [word_punpckhwd _ _ (by omega), ite_self]; congr 1; omega
  · simp only [Nat.one_ne_zero, ite_false]
    rw [word_punpckhqdq _ _ hi]
    split
    · rw [word_punpcklwd _ _ (by omega), ite_self]; congr 1; omega
    · rw [word_punpckhwd _ _ (by omega), ite_self]; congr 1; omega

theorem yzeta8_ok {zP : Addr} {k : Nat} {z : Nat → Zq} (hk : k + 8 ≤ 128) {s : State} (h8 : s.gpr .r8 = wAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (wAddr zP k) 16) (ht : TZ s.mem zP z) :
    WP isa (.block yzeta8) s fun s' =>
      (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun i => z (k + (2 * l + i / 2 + 2 * (i / 4))))) ∧
        YOnly [.xmm2, .xmm1, .xmm13] s s' := by
  rw [yzeta8, WP.block_append_iff, wp_cons_iff]
  refine WP.mono (ybcast_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨b1, o1⟩ => ?_
  refine WP.mono (ylanes (by decide) (P := fun l t =>
      t.xmm .xmm13 = XBinOp.eval .punpcklqdq (XBinOp.eval .punpcklwd (s1.lane .xmm2 l) (s1.lane .xmm2 l))
          (XBinOp.eval .punpckhwd (s1.lane .xmm2 l) (s1.lane .xmm2 l)) ∧
        t.xmm .xmm1 = XBinOp.eval .punpckhqdq (XBinOp.eval .punpcklwd (s1.lane .xmm2 l) (s1.lane .xmm2 l))
          (XBinOp.eval .punpckhwd (s1.lane .xmm2 l) (s1.lane .xmm2 l)))
    fun l _ => zsse8_ok (s1.proj l)) fun s2 ⟨l2, o2⟩ => ?_
  refine WP.mono (yblend_ok s2) fun s3 ⟨e0, e1, o3⟩ => ⟨fun l hl i hi => ?_, ((o1.trans o2).trans o3).mono (by simp)⟩
  have hx : s1.lane .xmm2 l = s.mem.readW (wAddr zP k) 128 := by rw [b1 l hl, h8, add_ofNat_zero]
  have hw : s3.lane .xmm13 l = (if l = 0 then XBinOp.eval .punpcklqdq else XBinOp.eval .punpckhqdq)
      (XBinOp.eval .punpcklwd (s.mem.readW (wAddr zP k) 128) (s.mem.readW (wAddr zP k) 128))
      (XBinOp.eval .punpckhwd (s.mem.readW (wAddr zP k) 128) (s.mem.readW (wAddr zP k) 128)) := by
    rcases lane01 hl with rfl | rfl
    · rw [e0, ← hx]; exact (l2 0 (by decide)).1
    · rw [e1, ← hx]; exact (l2 1 (by decide)).2
  rw [hw, word_z8 _ hl hi, word_readW _ _ (by omega), wAddr_add]
  exact ht _ (by omega)

end VG.Proof.MlKem.X86_64
