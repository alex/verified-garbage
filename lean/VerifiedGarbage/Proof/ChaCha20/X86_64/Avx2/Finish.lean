import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2
import VerifiedGarbage.Proof.ChaCha20.Spec
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Omega

section

/-!
# ChaCha20 on x86-64 with AVX2: the rounds

Doubleword `i` of lane `l` of a register holds a word of block `4 l + i`; each
quarter round of the code is the specification's on every one of the eight
blocks.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)
open VG.Proof.ChaCha20

/-- Doubleword `i` of lane `l` of `r`. -/
abbrev vw (s : State) (r : XReg) (l i : Nat) : Word := dword (s.lane r l) i

theorem rot12 (x : Word) : x >>> 20 ||| x <<< 12 = x.rotateLeft 12 := shr_or_shl x (k := 12) (by decide) (by decide)
theorem rot7 (x : Word) : x >>> 25 ||| x <<< 7 = x.rotateLeft 7 := shr_or_shl x (k := 7) (by decide) (by decide)

theorem psrld_20 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x 20) i = dword x i >>> 20 := dword_psrld x 20 (by decide) hi
theorem pslld_12 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x 12) i = dword x i <<< 12 := dword_pslld x 12 (by decide) hi
theorem psrld_25 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x 25) i = dword x i >>> 25 := dword_psrld x 25 (by decide) hi
theorem pslld_7 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x 7) i = dword x i <<< 7 := dword_pslld x 7 (by decide) hi

/-- The rotation masks, as the code finds them: the one for 16 in both lanes
of `ymm15`, the one for 8 in both halves of the 32 bytes at `rcx + 160`. -/
structure Masks (s : State) : Prop where
  m16 : ∀ l, s.lane .xmm15 l = rot16Mask
  rd8 : InRegions (s.rd ++ s.wr) (s.ea (at_ .rcx rot8Off)) 32
  lo8 : (s.mem.readW (s.ea (at_ .rcx rot8Off)) 256).extractLsb' 0 128 = rot8Mask
  hi8 : (s.mem.readW (s.ea (at_ .rcx rot8Off)) 256).extractLsb' 128 128 = rot8Mask

theorem qr_ok {a b c d : XReg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (ha : a ≠ .xmm14) (hb : b ≠ .xmm14) (hc : c ≠ .xmm14)
    (hd : d ≠ .xmm14) (ha' : a ≠ .xmm15) (hd' : d ≠ .xmm15) (s : State) (hm : Masks s) :
    WP isa (.block (qr a b c d)) s fun s' =>
      (∀ l i, i < 4 →
        vw s' a l i = (quarterRound (vw s a l i) (vw s b l i) (vw s c l i) (vw s d l i)).1 ∧
        vw s' b l i = (quarterRound (vw s a l i) (vw s b l i) (vw s c l i) (vw s d l i)).2.1 ∧
        vw s' c l i = (quarterRound (vw s a l i) (vw s b l i) (vw s c l i) (vw s d l i)).2.2.1 ∧
        vw s' d l i = (quarterRound (vw s a l i) (vw s b l i) (vw s c l i) (vw s d l i)).2.2.2) ∧
      (∀ r l, r ≠ a → r ≠ b → r ≠ c → r ≠ d → r ≠ .xmm14 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [qr, v, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec_ea, VOp.exec_mem,
    VOp.exec_rd, VOp.exec_wr, State.load256, hm.rd8, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun l i hi => ?_, fun r l h₁ h₂ h₃ h₄ h₅ => ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [vw, lane_vbin256, lane_vshift256, State.lane_setV256,
      VBinOp.sse, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm,
      hcd.symm, ha, hb, hc, hd, ha.symm, hb.symm, hc.symm, hd.symm, ha'.symm, hd'.symm, hm.lo8, hm.hi8, hm.m16, ite_self,
      ite_true, ite_false]
    simp only [dword_paddd _ _ hi, dword_pxor, dword_por, psrld_20 _ hi, pslld_12 _ hi,
      psrld_25 _ hi, pslld_7 _ hi, dword_pshufb_rot16 _ hi, dword_pshufb_rot8 _ hi, rot12, rot7,
      quarterRound, and_self]
  · simp (config := {decide := true}) only [lane_vbin256, lane_vshift256, State.lane_setV256, h₁,
      h₂, h₃, h₄, h₅, ite_false]
  all_goals simp

/-! ## Addresses in `buf` -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  rw [← ofInt_natCast]; rfl

theorem add_ofNat (p : Addr) (d e : Nat) :
    p + BitVec.ofNat 64 d + BitVec.ofNat 64 e = p + BitVec.ofNat 64 (d + e) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- `buf`, as far as this code uses it. -/
abbrev bufR (buf : Addr) : Region := ⟨buf, 320⟩

theorem bufR_contains (buf : Addr) {d n : Nat} (h : d + n ≤ 320) :
    (bufR buf).Contains (buf + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat buf (by lit_omega)]; exact h

theorem in_buf {rs ws : List Region} {buf : Addr} (hw : bufR buf ∈ ws) {d n : Nat} (h : d + n ≤ 320) :
    InRegions (rs ++ ws) (buf + BitVec.ofNat 64 d) n :=
  ⟨bufR buf, List.mem_append_right _ hw, bufR_contains buf h⟩

theorem out_buf {ws : List Region} {buf : Addr} (hw : bufR buf ∈ ws) {d n : Nat} (h : d + n ≤ 320) :
    InRegions ws (buf + BitVec.ofNat 64 d) n :=
  ⟨bufR buf, hw, bufR_contains buf h⟩

/-! ## Swapping the pair of third-row words -/

theorem slotOff_succ {i : Nat} (hi : 8 ≤ i) : slotOff (i + 1) = slotOff i + 32 := by
  simp only [slotOff]; omega

theorem swap_ok {i j : Nat} (hi : i = 8 ∨ i = 10) (hj : j = 8 ∨ j = 10) {buf : Addr} {s : State}
    (hrcx : s.gpr .rcx = buf) (hw : bufR buf ∈ s.wr) :
    WP isa (swap i j) s fun s' =>
      (∀ l q, l < 2 → q < 4 →
        vw s' .xmm12 l q = (s.mem.writeW (buf + BitVec.ofNat 64 (slotOff i)) (s.ymm .xmm12) |>.writeW
          (buf + BitVec.ofNat 64 (slotOff i + 32)) (s.ymm .xmm13)).readW
            (buf + BitVec.ofNat 64 (slotOff j + (16 * l + 4 * q))) 32 ∧
        vw s' .xmm13 l q = (s.mem.writeW (buf + BitVec.ofNat 64 (slotOff i)) (s.ymm .xmm12) |>.writeW
          (buf + BitVec.ofNat 64 (slotOff i + 32)) (s.ymm .xmm13)).readW
            (buf + BitVec.ofNat 64 (slotOff j + 32 + (16 * l + 4 * q))) 32) ∧
      (∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.mem = (s.mem.writeW (buf + BitVec.ofNat 64 (slotOff i)) (s.ymm .xmm12)).writeW
        (buf + BitVec.ofNat 64 (slotOff i + 32)) (s.ymm .xmm13) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have si : slotOff i + 64 ≤ 128 := by rcases hi with rfl | rfl <;> decide
  have sj : slotOff j + 64 ≤ 128 := by rcases hj with rfl | rfl <;> decide
  have e1 := slotOff_succ (i := i) (by lit_omega)
  have e2 := slotOff_succ (i := j) (by lit_omega)
  have o1 := out_buf hw (d := slotOff i) (n := 32) (by lit_omega)
  have o2 := out_buf hw (d := slotOff i + 32) (n := 32) (by lit_omega)
  have i1 := in_buf (rs := s.rd) hw (d := slotOff j) (n := 32) (by lit_omega)
  have i2 := in_buf (rs := s.rd) hw (d := slotOff j + 32) (n := 32) (by lit_omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, e1, e2,
    State.store256, State.load256, o1, o2, i1, i2, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left', State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr,
    State.ymm]
  refine ⟨fun l q hl hq => ⟨?_, ?_⟩, fun r l h₁ h₂ => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [vw, State.lane_setV256, show (XReg.xmm12 = .xmm13) = False by decide, ite_false,
      ite_true]
    rw [dword_load256 _ _ hl hq, add_ofNat]
  · simp only [vw, State.lane_setV256, ite_true]
    rw [dword_load256 _ _ hl hq, add_ofNat]
  · simp only [State.lane_setV256, h₁, h₂, ite_false]
    rfl

/-! ## Where the words are -/

/-- Word `k` is in its register `vreg k` (rather than its slot): words 8 and 9
when `p = false`, words 10 and 11 when `p = true`, and always the others. -/
def inReg (p : Bool) (k : Nat) : Bool :=
  if k = 8 ∨ k = 9 then !p else if k = 10 ∨ k = 11 then p else true

/-- The eight states `vs 0, …, vs 7` are in the registers and slots of layout
`p`: word `k` of state `4 l + q` in doubleword `q` of lane `l`. -/
def Holds (buf : Addr) (p : Bool) (vs : Nat → CState) (s : State) : Prop :=
  ∀ k (hk : k < 16) l q, l < 2 → q < 4 →
    if inReg p k then vw s (vreg k) l q = (vs (4 * l + q))[k]
    else s.mem.readW (buf + BitVec.ofNat 64 (slotOff k + (16 * l + 4 * q))) 32 = (vs (4 * l + q))[k]

theorem vreg_ne14 (k : Nat) : vreg k ≠ .xmm14 := by
  unfold vreg; split <;> decide

theorem vreg_ne15 (k : Nat) : vreg k ≠ .xmm15 := by
  unfold vreg; split <;> decide

/-! ## One quarter round -/

/-- The side conditions of `quarter_ok`, decidable for concrete arguments:
the four words are in distinct registers, and no other word in a register
shares one of them. -/
def QSide (p : Bool) (x y z w : Nat) : Bool :=
  inReg p x && inReg p y && inReg p z && inReg p w && [x, y, z, w].Nodup &&
  [vreg x, vreg y, vreg z, vreg w].Nodup &&
  (List.range 16).all fun k => [x, y, z, w].contains k || !inReg p k ||
    !([vreg x, vreg y, vreg z, vreg w].contains (vreg k))

theorem quarter_ok {p : Bool} {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16)
    (hw : w < 16) (hq : QSide p x y z w = true) {buf : Addr} {vs : Nat → CState} {s : State}
    (h : Holds buf p vs s) (hm : Masks s) :
    WP isa (quarter x y z w) s fun s' =>
      Holds buf p (fun j => qround (vs j) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s' ∧
      s'.lane .xmm15 = s.lane .xmm15 ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  simp only [QSide, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hq
  obtain ⟨⟨⟨⟨⟨⟨ix, iy⟩, iz⟩, iw⟩, nd⟩, nr⟩, others⟩ := hq
  have nd' : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using nd
  have nr' : (vreg x ≠ vreg y ∧ vreg x ≠ vreg z ∧ vreg x ≠ vreg w) ∧
      (vreg y ≠ vreg z ∧ vreg y ≠ vreg w) ∧ vreg z ≠ vreg w := by simpa using nr
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd'
  obtain ⟨⟨rxy, rxz, rxw⟩, ⟨ryz, ryw⟩, rzw⟩ := nr'
  refine WP.mono (qr_ok rxy rxz rxw ryz ryw rzw (vreg_ne14 x) (vreg_ne14 y) (vreg_ne14 z)
    (vreg_ne14 w) (vreg_ne15 x) (vreg_ne15 w) s hm)
    fun s' ⟨hv, hr, hg, hmem, hrd, hwr⟩ => ⟨fun k hk l q hl hq => ?_,
      funext fun l => hr _ l (vreg_ne15 x).symm (vreg_ne15 y).symm (vreg_ne15 z).symm
        (vreg_ne15 w).symm (by decide), hg, hmem, hrd, hwr⟩
  have gx := h x hx l q hl hq; have gy := h y hy l q hl hq
  have gz := h z hz l q hl hq; have gw := h w hw l q hl hq
  simp only [ix, iy, iz, iw, ite_true] at gx gy gz gw
  obtain ⟨ha, hb, hc, hd⟩ := hv l q hq
  rw [gx, gy, gz, gw] at ha hb hc hd
  simp only [qround_get _ _ _ _ _ k hk]
  by_cases ew : w = k
  · subst ew; simp only [iw, ite_true]; exact hd
  by_cases ez : z = k
  · subst ez; simp only [iz, ite_true, ew]; exact hc
  by_cases ey : y = k
  · subst ey; simp only [iy, ite_true, ew, ez]; exact hb
  by_cases ex : x = k
  · subst ex; simp only [ix, ite_true, ew, ez, ey]; exact ha
  simp only [ew, ez, ey, ex, ite_false]
  have hk' := h k hk l q hl hq
  have ho := others k hk
  split
  · rename_i hin
    simp only [hin, ite_true] at hk'
    have ho' : vreg k ≠ vreg x ∧ vreg k ≠ vreg y ∧ vreg k ≠ vreg z ∧ vreg k ≠ vreg w := by
      simpa [Ne.symm ex, Ne.symm ey, Ne.symm ez, Ne.symm ew, hin] using ho
    simp only [vw] at hk' ⊢
    rw [hr _ l ho'.1 ho'.2.1 ho'.2.2.1 ho'.2.2.2 (vreg_ne14 k)]; exact hk'
  · rename_i hin
    simp only [hin] at hk'
    rw [hmem]; exact hk'

/-! ## The rounds invariant -/

/-- The four home slots. -/
abbrev slotsR (buf : Addr) : Region := ⟨buf, 128⟩

/-- The mask of the rotation by 8, in both halves of `buf[160, 192)`. -/
def M8 (m : Mem) (buf : Addr) : Prop :=
  (m.readW (buf + BitVec.ofNat 64 160) 256).extractLsb' 0 128 = rot8Mask ∧
  (m.readW (buf + BitVec.ofNat 64 160) 256).extractLsb' 128 128 = rot8Mask

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (buf : Addr) (p : Bool) (vs : Nat → CState) (s₀ s : State) : Prop where
  holds : Holds buf p vs s
  m16 : ∀ l, s.lane .xmm15 l = rot16Mask
  frame : Frame [slotsR buf] s₀.mem s.mem
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem slots_m8 (buf : Addr) : (⟨buf + BitVec.ofNat 64 160, 256 / 8⟩ : Region).Disjoint (slotsR buf) := Offset.disjoint_base buf (by lit_omega) (by lit_omega)

theorem RI.masks {buf : Addr} {p : Bool} {vs : Nat → CState} {s₀ s : State} (h : RI buf p vs s₀ s)
    (hrcx : s₀.gpr .rcx = buf) (hw : bufR buf ∈ s₀.wr) (h8 : M8 s₀.mem buf) : Masks s := by
  have ea : s.ea (at_ .rcx rot8Off) = buf + BitVec.ofNat 64 160 := by
    rw [ea_at, h.gpr, hrcx]; rfl
  have e : s.mem.readW (buf + BitVec.ofNat 64 160) 256 = s₀.mem.readW (buf + BitVec.ofNat 64 160) 256 :=
    h.frame.readW (Region.contains_self _ _) (by simpa using slots_m8 buf) (by decide)
  refine ⟨h.m16, ?_, ?_, ?_⟩
  · rw [ea, h.rd, h.wr]; exact in_buf hw (by lit_omega)
  · rw [ea, e]; exact h8.1
  · rw [ea, e]; exact h8.2

theorem quarter_step {p : Bool} {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16)
    (hw : w < 16) (hq : QSide p x y z w = true) {buf : Addr} {vs : Nat → CState} {s₀ s : State}
    (h : RI buf p vs s₀ s) (hrcx : s₀.gpr .rcx = buf) (hb : bufR buf ∈ s₀.wr) (h8 : M8 s₀.mem buf) :
    WP isa (quarter x y z w) s
      (RI buf p (fun j => qround (vs j) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) :=
  WP.mono (quarter_ok hx hy hz hw hq h.holds (h.masks hrcx hb h8))
    fun _ ⟨hh, h15, hg, hm, hrd, hwr⟩ =>
      ⟨hh, fun l => by rw [h15]; exact h.m16 l, hm ▸ h.frame, hg.trans h.gpr, hrd.trans h.rd,
        hwr.trans h.wr⟩

/-! ## Swapping -/

/-- Two 256-bit writes at slot `i` and the next. -/
abbrev W2 (m : Mem) (buf : Addr) (i : Nat) (y₁ y₂ : BitVec 256) : Mem :=
  (m.writeW (buf + BitVec.ofNat 64 (slotOff i)) y₁).writeW (buf + BitVec.ofNat 64 (slotOff i + 32)) y₂

theorem W2_first (m : Mem) (buf : Addr) {i : Nat} (hi : slotOff i + 64 ≤ 128) (y₁ y₂ : BitVec 256)
    {x : Nat} (hx : x + 4 ≤ 32) :
    (W2 m buf i y₁ y₂).readW (buf + BitVec.ofNat 64 (slotOff i + x)) 32 = y₁.extractLsb' (8 * x) (8 * 4) := by
  refine (readW_writeW_off _ buf y₂ (d := slotOff i + x) (e := slotOff i + 32) (n := 4) (by lit_omega)
    (by lit_omega) (by lit_omega)).trans ?_
  rw [← add_ofNat]
  exact readW_writeW_inside _ _ _ (by lit_omega) (by lit_omega)

theorem W2_second (m : Mem) (buf : Addr) (i : Nat) (y₁ y₂ : BitVec 256)
    {x : Nat} (hx : x + 4 ≤ 32) :
    (W2 m buf i y₁ y₂).readW (buf + BitVec.ofNat 64 (slotOff i + 32 + x)) 32 =
      y₂.extractLsb' (8 * x) (8 * 4) := by
  rw [← add_ofNat]
  exact readW_writeW_inside _ _ _ (k := x) (n := 4) (by lit_omega) (by lit_omega)

theorem W2_other (m : Mem) (buf : Addr) {i : Nat} (hi : slotOff i + 64 ≤ 128) (y₁ y₂ : BitVec 256)
    {d : Nat} (hd : d + 4 ≤ slotOff i ∨ slotOff i + 64 ≤ d) (hd' : d < 2 ^ 32) :
    (W2 m buf i y₁ y₂).readW (buf + BitVec.ofNat 64 d) 32 = m.readW (buf + BitVec.ofNat 64 d) 32 := by
  exact (readW_writeW_off _ buf y₂ (d := d) (e := slotOff i + 32) (n := 4) (by lit_omega) (by lit_omega)
    (by lit_omega)).trans (readW_writeW_off _ buf y₁ (d := d) (e := slotOff i) (n := 4) (by lit_omega)
    (by lit_omega) (by lit_omega))

theorem W2_frame {m m' : Mem} (buf : Addr) {i : Nat} (hi : slotOff i + 64 ≤ 128) (y₁ y₂ : BitVec 256)
    (h : Frame [slotsR buf] m m') : Frame [slotsR buf] m (W2 m' buf i y₁ y₂) := by
  have c : ∀ d, d + 32 ≤ 128 → (slotsR buf).Contains (buf + BitVec.ofNat 64 d) (256 / 8) := by
    intro d hd
    simp only [Region.Contains]
    rw [Mem.sub_ofNat_toNat buf (by lit_omega)]; omega
  exact (h.writeW (List.mem_singleton_self _) _ (c _ (by lit_omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by lit_omega))

theorem inReg_other (p : Bool) {k : Nat} (hk : k < 8 ∨ 12 ≤ k) : inReg p k = true := by
  simp only [inReg]; rw [ite_eq_right (by lit_omega), ite_eq_right (by lit_omega)]

theorem vreg_other {k : Nat} (hk : k < 16) (hk' : k < 8 ∨ 12 ≤ k) :
    vreg k ≠ .xmm12 ∧ vreg k ≠ .xmm13 :=
  (show ∀ k < 16, (k < 8 ∨ 12 ≤ k) → vreg k ≠ .xmm12 ∧ vreg k ≠ .xmm13 by decide) k hk hk'

set_option linter.unusedSimpArgs false in
theorem swap_holds {p : Bool} {buf : Addr} {vs : Nat → CState} {s s' : State}
    (h : Holds buf p vs s) {i j : Nat} (hij : i = (if p then 10 else 8) ∧ j = (if p then 8 else 10))
    (hv : ∀ l q, l < 2 → q < 4 →
      vw s' .xmm12 l q = (W2 s.mem buf i (s.ymm .xmm12) (s.ymm .xmm13)).readW
          (buf + BitVec.ofNat 64 (slotOff j + (16 * l + 4 * q))) 32 ∧
      vw s' .xmm13 l q = (W2 s.mem buf i (s.ymm .xmm12) (s.ymm .xmm13)).readW
          (buf + BitVec.ofNat 64 (slotOff j + 32 + (16 * l + 4 * q))) 32)
    (hl : ∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → s'.lane r l = s.lane r l)
    (hm : s'.mem = W2 s.mem buf i (s.ymm .xmm12) (s.ymm .xmm13)) :
    Holds buf (!p) vs s' := by
  intro k hk l q hl' hq
  have hx : 16 * l + 4 * q + 4 ≤ 32 := by omega
  have old := h k hk l q hl' hq
  obtain ⟨v12, v13⟩ := hv l q hl' hq
  have ym : ∀ r, (s.ymm r).extractLsb' (8 * (16 * l + 4 * q)) (8 * 4) = vw s r l q :=
    fun r => extract_ymm s r hl' hq
  have s9 : slotOff 9 = slotOff 8 + 32 := rfl
  have s11 : slotOff 11 = slotOff 10 + 32 := rfl
  obtain ⟨rfl, rfl⟩ := hij
  rw [hm]
  by_cases hk' : k < 8 ∨ 12 ≤ k
  · rw [inReg_other p hk'] at old
    rw [inReg_other _ hk', ite_eq_left rfl]
    simp only [ite_true, vw] at old ⊢
    obtain ⟨n12, n13⟩ := vreg_other hk hk'
    rw [hl _ _ n12 n13]; exact old
  rcases (by omega : k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11) with rfl | rfl | rfl | rfl <;> cases p <;>
    simp (config := {decide := true}) only [inReg, vreg, Bool.not_false, Bool.not_true, ite_true,
      ite_false, Bool.false_eq_true, s9, s11] at old v12 v13 ⊢
  all_goals first
    | rw [W2_first _ _ (by decide) _ _ hx, ym, old]
    | rw [W2_second _ _ _ _ _ hx, ym, old]
    | rw [v12, W2_other _ _ (by decide) _ _ (by simp only [slotOff]; omega)
        (by simp only [slotOff]; omega), old]
    | rw [v13, W2_other _ _ (by decide) _ _ (by simp only [slotOff]; omega)
        (by simp only [slotOff]; omega), old]

theorem swap_step {p : Bool} {buf : Addr} {vs : Nat → CState} {s₀ s : State} (h : RI buf p vs s₀ s)
    (hrcx : s₀.gpr .rcx = buf) (hb : bufR buf ∈ s₀.wr) :
    WP isa (swap (if p then 10 else 8) (if p then 8 else 10)) s (RI buf (!p) vs s₀) := by
  have hr : s.gpr .rcx = buf := by rw [h.gpr, hrcx]
  have hw : bufR buf ∈ s.wr := h.wr ▸ hb
  have si : slotOff (if p then 10 else 8) + 64 ≤ 128 := by cases p <;> decide
  exact WP.mono (swap_ok (by cases p <;> simp) (by cases p <;> simp) hr hw)
    fun s' ⟨hv, hl, hm, hg, hrd, hwr⟩ => ⟨swap_holds h.holds ⟨rfl, rfl⟩ hv hl hm,
      fun l => by rw [hl _ _ (by decide) (by decide)]; exact h.m16 l,
      hm ▸ W2_frame buf si _ _ h.frame, hg.trans h.gpr, hrd.trans h.rd, hwr.trans h.wr⟩

/-! ## Double rounds -/

theorem doubleRound_ok {buf : Addr} {vs : Nat → CState} {s₀ s : State} (h : RI buf false vs s₀ s)
    (hrcx : s₀.gpr .rcx = buf) (hb : bufR buf ∈ s₀.wr) (h8 : M8 s₀.mem buf) :
    WP isa doubleRound s (RI buf false (fun j => innerBlock (vs j)) s₀) := by
  unfold doubleRound
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h hrcx hb h8) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₁ hrcx hb h8) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (swap_step (p := false) h₂ hrcx hb) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₃ hrcx hb h8) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₄ hrcx hb h8) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₅ hrcx hb h8) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₆ hrcx hb h8) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (swap_step (p := true) h₇ hrcx hb) fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₈ hrcx hb h8) fun s₉ h₉ => ?_)
  exact WP.mono (quarter_step (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₉ hrcx hb h8) fun _ h => h

theorem rounds_ok {buf : Addr} {vs : Nat → CState} {s₀ : State} (h : Holds buf false vs s₀)
    (h15 : ∀ l, s₀.lane .xmm15 l = rot16Mask) (hrcx : s₀.gpr .rcx = buf) (hb : bufR buf ∈ s₀.wr)
    (h8 : M8 s₀.mem buf) :
    ∀ n, WP isa (rounds n) s₀ (RI buf false (fun j => Nat.repeat innerBlock n (vs j)) s₀)
  | 0 => WP.block_nil ⟨h, h15, Frame.refl _ _, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h h15 hrcx hb h8 n) fun _ h' => doubleRound_ok h' hrcx hb h8)

end VG.Proof.ChaCha20.X86_64.Avx2

end

/-!
# ChaCha20 on x86-64 with AVX2: the eight input states
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt)
open VG.Proof.ChaCha20

/-- What `buf[128, 224)` holds once the constants are stored: the rotation
masks, and the counter increments `0, …, 7` as doublewords. -/
structure Consts (m : Mem) (buf : Addr) : Prop where
  lo16 : (m.readW (buf + BitVec.ofNat 64 128) 256).extractLsb' 0 128 = rot16Mask
  hi16 : (m.readW (buf + BitVec.ofNat 64 128) 256).extractLsb' 128 128 = rot16Mask
  m8 : M8 m buf
  inc : ∀ l q, l < 2 → q < 4 →
    m.readW (buf + BitVec.ofNat 64 (192 + (16 * l + 4 * q))) 32 = BitVec.ofNat 32 (4 * l + q)

theorem shuf_00 (a : BitVec 128) {q : Nat} (hq : q < 4) : dword (shufDwords a 0x00) q = dword a 0 :=
  dword_shufDwords_bcast a (k := 0) (by decide) hq
theorem shuf_55 (a : BitVec 128) {q : Nat} (hq : q < 4) : dword (shufDwords a 0x55) q = dword a 1 :=
  dword_shufDwords_bcast a (k := 1) (by decide) hq
theorem shuf_aa (a : BitVec 128) {q : Nat} (hq : q < 4) : dword (shufDwords a 0xaa) q = dword a 2 :=
  dword_shufDwords_bcast a (k := 2) (by decide) hq
theorem shuf_ff (a : BitVec 128) {q : Nat} (hq : q < 4) : dword (shufDwords a 0xff) q = dword a 3 :=
  dword_shufDwords_bcast a (k := 3) (by decide) hq

theorem ctr_get (S : CState) (j k : Nat) (hk : k < 16) :
    (ctr S j)[k] = if k = 12 then S[12] + BitVec.ofNat 32 j else S[k] := by
  simp only [ctr, Vector.getElem_set]
  by_cases h : k = 12
  · subst h; simp
  · simp [h, Ne.symm h]

/-- Word `4 row + i` of the state at `st`, from a 128-bit read of row `row`. -/
theorem dword_row (m : Mem) (st : Addr) {row i : Nat} (hrow : row < 4) (hi : i < 4) :
    dword (m.readW (st + BitVec.ofNat 64 (16 * row)) 128) i =
      (stateAt m st)[4 * row + i]'(by lit_omega) := by
  rw [dword_readW _ _ hi, add_ofNat]
  simp only [stateAt, Vector.getElem_ofFn]
  congr 3; omega

/-- The state region. -/
abbrev stR (st : Addr) : Region := ⟨st, 64⟩

theorem in_st {rs ws : List Region} {st : Addr} (hw : stR st ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions (rs ++ ws) (st + BitVec.ofNat 64 d) n := by
  refine ⟨stR st, List.mem_append_right _ hw, ?_⟩
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat st (by lit_omega)]; exact h

theorem Consts.w2 {m : Mem} {buf : Addr} (h : Consts m buf) {i : Nat} (hi : slotOff i + 64 ≤ 128)
    (y₁ y₂ : BitVec 256) : Consts (W2 m buf i y₁ y₂) buf := by
  have k : ∀ d, 128 ≤ d → d ≤ 192 →
      (W2 m buf i y₁ y₂).readW (buf + BitVec.ofNat 64 d) 256 = m.readW (buf + BitVec.ofNat 64 d) 256 :=
    fun d h₁ h₂ => (readW_writeW_off _ buf y₂ (d := d) (e := slotOff i + 32) (n := 32) (by lit_omega)
      (by lit_omega) (by lit_omega)).trans (readW_writeW_off _ buf y₁ (d := d) (e := slotOff i) (n := 32)
      (by lit_omega) (by lit_omega) (by lit_omega))
  refine ⟨?_, ?_, ⟨?_, ?_⟩, fun l q hl hq => ?_⟩
  · rw [k 128 (by lit_omega) (by lit_omega)]; exact h.lo16
  · rw [k 128 (by lit_omega) (by lit_omega)]; exact h.hi16
  · rw [k 160 (by lit_omega) (by lit_omega)]; exact h.m8.1
  · rw [k 160 (by lit_omega) (by lit_omega)]; exact h.m8.2
  · exact (W2_other m buf hi y₁ y₂ (by lit_omega) (by lit_omega)).trans (h.inc l q hl hq)

/-! ## Broadcasting rows -/

/-- `vbroadcasti128 src, [rdi + off]` and the four `vpshufd` that spread its words. -/
def bcast (src d0 d1 d2 d3 : XReg) (off : Nat) : List Instr :=
  [.vbroadcasti128 src (at_ .rdi off), .vop (.vpshufd .l256 d0 src 0x00),
   .vop (.vpshufd .l256 d1 src 0x55), .vop (.vpshufd .l256 d2 src 0xaa),
   .vop (.vpshufd .l256 d3 src 0xff)]

theorem bcast_ok {src d0 d1 d2 d3 : XReg} (h0 : d0 ≠ src) (h1 : d1 ≠ src) (h2 : d2 ≠ src)
    (h3 : d3 ≠ src) (e01 : d0 ≠ d1) (e02 : d0 ≠ d2) (e03 : d0 ≠ d3) (e12 : d1 ≠ d2) (e13 : d1 ≠ d3)
    (e23 : d2 ≠ d3) {off : Nat} {s : State}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 off) 16) :
    WP isa (.block (bcast src d0 d1 d2 d3 off)) s fun s' =>
      (∀ l q, q < 4 →
        vw s' d0 l q = dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 off) 128) 0 ∧
        vw s' d1 l q = dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 off) 128) 1 ∧
        vw s' d2 l q = dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 off) 128) 2 ∧
        vw s' d3 l q = dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 off) 128) 3) ∧
      (∀ r l, r ≠ src → r ≠ d0 → r ≠ d1 → r ≠ d2 → r ≠ d3 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [bcast, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, State.load128, hin,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', VOp.exec_gpr, VOp.exec_mem,
    VOp.exec_rd, VOp.exec_wr, State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr]
  refine ⟨fun l q hq => ?_, fun r l n n0 n1 n2 n3 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [vw, lane_vpshufd256, State.lane_setV256, h0, h1, h2, h3, e01, e02, e03, e12, e13,
      e23, e01.symm, e02.symm, e03.symm, e12.symm, e13.symm, e23.symm, h0.symm, h1.symm, h2.symm,
      ite_true, ite_false, ite_self,
      shuf_00 _ hq, shuf_55 _ hq, shuf_aa _ hq, shuf_ff _ hq, and_self]
  · simp only [lane_vpshufd256, State.lane_setV256, n, n0, n1, n2, n3, ite_false]

/-! ## The counters, the third row and the mask -/

def incs : List Instr :=
  [.vmovdquLoad .l256 .xmm13 (at_ .rcx incOff), .vop (.vbin .vpaddd .l256 .xmm8 .xmm8 .xmm13)]

theorem incs_ok {buf : Addr} {s : State} (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr)
    (hc : Consts s.mem buf) :
    WP isa (.block incs) s fun s' =>
      (∀ l q, l < 2 → q < 4 → vw s' .xmm8 l q = vw s .xmm8 l q + BitVec.ofNat 32 (4 * l + q)) ∧
      (∀ r l, r ≠ .xmm8 → r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i1 := in_buf (rs := s.rd) hb (d := incOff) (n := 32) (by decide)
  apply WP.of_runBlock
  simp only [incs, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, State.load256, i1,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', VOp.exec_gpr, VOp.exec_mem,
    VOp.exec_rd, VOp.exec_wr, State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr]
  refine ⟨fun l q hl hq => ?_, fun r l n8 n13 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [vw, lane_vbin256, State.lane_setV256, reduceCtorEq, ite_true, ite_false, VBinOp.sse,
      dword_paddd _ _ hq, dword_load256 _ _ hl hq]
    rw [add_ofNat]; exact congrArg _ (hc.inc l q hl hq)
  · simp only [lane_vbin256, State.lane_setV256, n8, n13, ite_false]

def row2 : List Instr :=
  [.vbroadcasti128 .xmm14 (at_ .rdi 32),
   .vop (.vpshufd .l256 .xmm12 .xmm14 0x00), .vop (.vpshufd .l256 .xmm13 .xmm14 0x55),
   .vop (.vpshufd .l256 .xmm15 .xmm14 0xaa), .vmovdquStore .l256 (at_ .rcx (slotOff 10)) .xmm15,
   .vop (.vpshufd .l256 .xmm15 .xmm14 0xff), .vmovdquStore .l256 (at_ .rcx (slotOff 11)) .xmm15]

theorem row2_ok {st buf : Addr} {s : State} (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf)
    (hst : stR st ∈ s.wr) (hb : bufR buf ∈ s.wr) :
    WP isa (.block row2) s fun s' =>
      (∀ l q, l < 2 → q < 4 →
        vw s' .xmm12 l q = dword (s.mem.readW (st + BitVec.ofNat 64 32) 128) 0 ∧
        vw s' .xmm13 l q = dword (s.mem.readW (st + BitVec.ofNat 64 32) 128) 1 ∧
        s'.mem.readW (buf + BitVec.ofNat 64 (slotOff 10 + (16 * l + 4 * q))) 32 =
          dword (s.mem.readW (st + BitVec.ofNat 64 32) 128) 2 ∧
        s'.mem.readW (buf + BitVec.ofNat 64 (slotOff 11 + (16 * l + 4 * q))) 32 =
          dword (s.mem.readW (st + BitVec.ofNat 64 32) 128) 3) ∧
      (∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      (∃ y₁ y₂, s'.mem = W2 s.mem buf 10 y₁ y₂) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i2 := in_st (rs := s.rd) hst (d := 32) (n := 16) (by lit_omega)
  have o10 := out_buf hb (d := slotOff 10) (n := 32) (by decide)
  have o11 := out_buf hb (d := slotOff 10 + 32) (n := 32) (by decide)
  have s11 : slotOff 11 = slotOff 10 + 32 := rfl
  apply WP.of_runBlock
  simp only [row2, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrdi, hrcx, State.load128,
    State.store256_eq, i2, o10, o11, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
    VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, State.setV_gpr, State.setV_mem,
    State.setV_rd, State.setV_wr, State.setMem_gpr, State.setMem_mem, State.setMem_rd,
    State.setMem_wr, s11]
  refine ⟨fun l q hl hq => ?_, fun r l n12 n13 n14 n15 => ?_, ⟨_, _, rfl⟩, trivial, trivial, trivial⟩
  · have hx : 16 * l + 4 * q + 4 ≤ 32 := by omega
    rw [W2_first _ _ (i := 10) (by decide) _ _ hx, W2_second _ _ 10 _ _ hx, extract_ymm _ _ hl hq,
      extract_ymm _ _ hl hq]
    simp only [vw, lane_vpshufd256, State.lane_setV256, State.setMem_lane, reduceCtorEq, ite_true,
      ite_false, ite_self, shuf_00 _ hq, shuf_55 _ hq, shuf_aa _ hq, shuf_ff _ hq, and_self]
  · simp only [lane_vpshufd256, State.lane_setV256, State.setMem_lane, n12, n13, n14, n15, ite_false]

theorem mask_ok {buf : Addr} {s : State} (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr)
    (hc : Consts s.mem buf) :
    WP isa (.block [.vmovdquLoad .l256 .xmm15 (at_ .rcx rot16Off)]) s fun s' =>
      (∀ l, s'.lane .xmm15 l = rot16Mask) ∧ (∀ r l, r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i1 := in_buf (rs := s.rd) hb (d := rot16Off) (n := 32) (by decide)
  have l16 : (s.mem.readW (buf + BitVec.ofNat 64 rot16Off) 256).extractLsb' 0 128 = rot16Mask := hc.lo16
  have h16 : (s.mem.readW (buf + BitVec.ofNat 64 rot16Off) 256).extractLsb' 128 128 = rot16Mask :=
    hc.hi16
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, State.load256, i1,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', State.setV_gpr, State.setV_mem,
    State.setV_rd, State.setV_wr]
  exact ⟨fun l => by simp only [State.lane_setV256, ite_true, l16, h16, ite_self],
    fun r l n => by simp only [State.lane_setV256, n, ite_false], trivial, trivial, trivial, trivial⟩

/-! ## The whole setup -/

theorem setup_eq : setup =
    bcast .xmm12 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ (bcast .xmm12 .xmm4 .xmm5 .xmm6 .xmm7 16 ++
    (bcast .xmm12 .xmm8 .xmm9 .xmm10 .xmm11 48 ++ (incs ++ (row2 ++
    ([.vmovdquLoad .l256 .xmm15 (at_ .rcx rot16Off)] : List Instr))))) := rfl

theorem setup_ok {st buf : Addr} {s : State} (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf)
    (hst : stR st ∈ s.wr) (hb : bufR buf ∈ s.wr) (hc : Consts s.mem buf) :
    WP isa (.block setup) s fun s' =>
      Holds buf false (fun j => ctr (stateAt s.mem st) j) s' ∧ (∀ l, s'.lane .xmm15 l = rot16Mask) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∃ y₁ y₂, s'.mem = W2 s.mem buf 10 y₁ y₂ := by
  have row : ∀ r, r < 4 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * r)) 16 :=
    fun r hr => hrdi ▸ in_st hst (by lit_omega)
  rw [setup_eq]
  refine WP.block_append (WP.mono (bcast_ok (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (row 0 (by decide)))
    fun s₁ ⟨a₁, f₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.block_append (WP.mono (bcast_ok (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₁, rd₁, wr₁]; exact row 1 (by decide)))
    fun s₂ ⟨a₂, f₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.block_append (WP.mono (bcast_ok (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₂, g₁, rd₂, rd₁, wr₂, wr₁]; exact row 3 (by decide)))
    fun s₃ ⟨a₃, f₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have e₃ : s₃.gpr = s.gpr ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr :=
    ⟨by rw [g₃, g₂, g₁], by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  refine WP.block_append (WP.mono (incs_ok (by rw [e₃.1, hrcx]) (by rw [e₃.2.2.2]; exact hb)
    (by rw [e₃.2.1]; exact hc)) fun s₄ ⟨a₄, f₄, g₄, m₄, rd₄, wr₄⟩ => ?_)
  refine WP.block_append (WP.mono (row2_ok (st := st) (buf := buf) (by rw [g₄, e₃.1, hrdi]) (by rw [g₄, e₃.1, hrcx])
    (by rw [wr₄, e₃.2.2.2]; exact hst) (by rw [wr₄, e₃.2.2.2]; exact hb))
    fun s₅ ⟨a₅, f₅, ⟨y₁, y₂, m₅⟩, g₅, rd₅, wr₅⟩ => ?_)
  refine WP.mono (mask_ok (by rw [g₅, g₄, e₃.1, hrcx]) (by rw [wr₅, wr₄, e₃.2.2.2]; exact hb)
    (by rw [m₅, m₄, e₃.2.1]; exact hc.w2 (by decide) y₁ y₂)) fun s₆ ⟨a₆, f₆, g₆, m₆, rd₆, wr₆⟩ => ?_
  refine ⟨fun k hk l q hl hq => ?_, a₆, by rw [g₆, g₅, g₄, e₃.1], by rw [rd₆, rd₅, rd₄, e₃.2.2.1],
    by rw [wr₆, wr₅, wr₄, e₃.2.2.2], ⟨y₁, y₂, by rw [m₆, m₅, m₄, e₃.2.1]⟩⟩
  have R : ∀ r (hr : r < 4) i (hi : i < 4),
      dword (s.mem.readW (st + BitVec.ofNat 64 (16 * r)) 128) i = (stateAt s.mem st)[4 * r + i]'(by lit_omega) :=
    fun r hr i hi => dword_row s.mem st hr hi
  have R0 := R 0 (by decide); have R1 := R 1 (by decide)
  have R2 := R 2 (by decide); have R3 := R 3 (by decide)
  simp only [Nat.reduceMul, Nat.zero_add] at R0 R1 R2 R3
  obtain ⟨b₀, b₁, b₂, b₃⟩ := a₁ l q hq
  obtain ⟨b₄, b₅, b₆, b₇⟩ := a₂ l q hq
  obtain ⟨b₈, b₉, b₁₀, b₁₁⟩ := a₃ l q hq
  obtain ⟨c₈, c₉, c₁₀, c₁₁⟩ := a₅ l q hl hq
  have b₁₂ := a₄ l q hl hq
  simp only [hrdi, g₁, g₂, m₁, m₂] at b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  simp only [m₄, e₃.2.1] at c₈ c₉ c₁₀ c₁₁
  rcases (by omega : k < 4 ∨ (4 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 12) ∨ 12 ≤ k) with hg | hg | hg | hg
  · obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    all_goals
      simp (disch := decide) only [inReg, vreg, reduceCtorEq, or_self, Nat.reduceEqDiff, ite_true,
        ite_false, Bool.not_false, vw, f₆, f₅, f₄, f₃, f₂, b₀, b₁, b₂, b₃, R0, ctr_get _ _ _ hk,
        m₆]
  · obtain rfl | rfl | rfl | rfl : k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    all_goals
      simp (disch := decide) only [inReg, vreg, or_self, Nat.reduceEqDiff, ite_true, ite_false,
        Bool.not_false, vw, f₆, f₅, f₄, f₃, b₄, b₅, b₆, b₇, R1, ctr_get _ _ _ hk, m₆]
  · obtain rfl | rfl | rfl | rfl : k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
    all_goals
      simp (disch := decide) only [inReg, vreg, or_self, or_false, false_or, Nat.reduceEqDiff,
        ite_true, ite_false, Bool.false_eq_true, Bool.not_false, vw, f₆, c₈, c₉, c₁₀, c₁₁, R2,
        ctr_get _ _ _ hk, m₆]
  · obtain rfl | rfl | rfl | rfl : k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
    all_goals
      simp (disch := decide) only [inReg, vreg, or_self, Nat.reduceEqDiff, ite_true, ite_false,
        Bool.not_false, vw, f₆, f₅, f₄, b₈, b₉, b₁₀, b₁₁, b₁₂, R3, ctr_get _ _ _ hk, m₆]

end VG.Proof.ChaCha20.X86_64.Avx2

/-!
# ChaCha20 on x86-64 with AVX2: the constants

The prologue stores the rotation masks and the counter increments in `buf[128,
224)`, a quadword at a time.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2
open VG.Impl.ChaCha20.X86_64 (at_)

/-! ## Reading back quadwords -/

theorem readW_128 (m : Mem) (a : Addr) :
    m.readW a 128 = m.readW (a + BitVec.ofNat 64 8) 64 ++ m.readW a 64 := by
  have h1 : (m.readW a 128).extractLsb' 0 64 = m.readW a 64 := by
    have := readW_extract m a (w := 128) (k := 0) (n := 8) (by lit_omega)
    simpa using this
  have h2 : (m.readW a 128).extractLsb' 64 64 = m.readW (a + BitVec.ofNat 64 8) 64 :=
    readW_extract m a (w := 128) (k := 8) (n := 8) (by lit_omega)
  rw [← h1, ← h2]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp [h]
  · have e : 64 + (i - 64) = i := by omega
    simp only [h, decide_false, show i - 64 < 64 by omega, decide_true, Bool.true_and, e, ite_false]

theorem readW_256 (m : Mem) (a : Addr) :
    m.readW a 256 = m.readW (a + BitVec.ofNat 64 16) 128 ++ m.readW a 128 := by
  have h1 : (m.readW a 256).extractLsb' 0 128 = m.readW a 128 := by
    have := readW_extract m a (w := 256) (k := 0) (n := 16) (by lit_omega)
    simpa using this
  have h2 : (m.readW a 256).extractLsb' 128 128 = m.readW (a + BitVec.ofNat 64 16) 128 :=
    readW_extract m a (w := 256) (k := 16) (n := 16) (by lit_omega)
  rw [← h1, ← h2]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 128
  · simp [h]
  · have e : 128 + (i - 128) = i := by omega
    simp only [h, decide_false, show i - 128 < 128 by omega, decide_true, Bool.true_and, e, ite_false]

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 =
      m.readW (p + BitVec.ofNat 64 d) 64 :=
  readW_writeW_off m p v (d := d) (e := e) (n := 8) (by lit_omega) (by lit_omega) (by lit_omega)

/-! ## The stores -/

/-- The offsets in `buf` and values of the quadwords the prologue stores. -/
def constPairs : List (Nat × BitVec 64) :=
  [(128, 0x0504070601000302), (136, 0x0d0c0f0e09080b0a), (144, 0x0504070601000302),
   (152, 0x0d0c0f0e09080b0a), (160, 0x0605040702010003), (168, 0x0e0d0c0f0a09080b),
   (176, 0x0605040702010003), (184, 0x0e0d0c0f0a09080b), (192, 0x0000000100000000),
   (200, 0x0000000300000002), (208, 0x0000000500000004), (216, 0x0000000700000006)]

/-- Store each `(d, v)` at `buf + d`, through `rax`. -/
def pairsCode (ps : List (Nat × BitVec 64)) : List Instr :=
  ps.flatMap fun p => [.movImm64 .rax p.2, .store (at_ .rcx p.1) .rax]

theorem consts_eq : consts = pairsCode constPairs := by
  simp only [consts, storeQ, rot16Q, rot8Q, incQ, pairsCode, constPairs, rot16Off, rot8Off, incOff,
    List.length_cons, List.length_nil, List.range_succ, List.range_zero, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getD_cons_zero,
    List.getD_cons_succ, List.cons_append, List.nil_append, Nat.reduceAdd, Nat.reduceMul]

/-- Memory after the stores `ps`. -/
def storeAll (buf : Addr) (ps : List (Nat × BitVec 64)) (m : Mem) : Mem :=
  ps.foldl (fun m p => m.writeW (buf + BitVec.ofNat 64 p.1) p.2) m

theorem State.store64_eq (s : State) (a : Addr) (v : BitVec 64) :
    s.store64 a v = if InRegions s.wr a 8 then some (s.setMem (s.mem.writeW a v)) else none := by
  rw [State.store64]; rfl

theorem pairs_ok {buf : Addr} (ps : List (Nat × BitVec 64)) (hps : ∀ p ∈ ps, p.1 + 8 ≤ 320)
    {s : State} (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block (pairsCode ps)) s fun s' =>
      s'.mem = storeAll buf ps s.mem ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction ps generalizing s with
  | nil => exact WP.block_nil ⟨rfl, fun _ _ => rfl, rfl, rfl⟩
  | cons p ps ih =>
    have hp := hps p (List.mem_cons_self ..)
    have o := out_buf hb (d := p.1) (n := 8) hp
    rw [pairsCode, List.flatMap_cons, ← pairsCode]
    refine WP.block_append ?_
    apply WP.of_runBlock
    have g : (s.setReg .rax p.2).gpr .rcx = buf := by simp [State.setReg, hrcx]
    have o' : InRegions (s.setReg .rax p.2).wr (buf + BitVec.ofNat 64 p.1) 8 := o
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, State.store64_eq, g, o',
      ite_true, Option.some.injEq, exists_eq_left']
    refine WP.mono (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (by simpa using g)
      (by exact hb)) fun s' ⟨m', g', r', w'⟩ => ⟨?_, fun r hr => ?_, r', w'⟩
    · rw [m', storeAll, storeAll, List.foldl_cons]; rfl
    · rw [g' r hr]; simp [State.setReg, hr]

theorem storeAll_frame {buf : Addr} {rs : List Region} (hr : bufR buf ∈ rs) (ps : List (Nat × BitVec 64))
    (hps : ∀ p ∈ ps, p.1 + 8 ≤ 320) (m : Mem) : Frame rs m (storeAll buf ps m) := by
  induction ps generalizing m with
  | nil => exact Frame.refl _ _
  | cons p ps ih =>
    rw [storeAll, List.foldl_cons, ← storeAll]
    exact ((Frame.refl _ _).writeW hr _ (bufR_contains buf (hps p (List.mem_cons_self ..)))).trans
      (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _)

/-! ## The constants -/

/-- A 256-bit read of four stored quadwords. -/
theorem read4 {m : Mem} {buf : Addr} {d : Nat} {v0 v1 v2 v3 : BitVec 64}
    (h0 : m.readW (buf + BitVec.ofNat 64 d) 64 = v0)
    (h1 : m.readW (buf + BitVec.ofNat 64 (d + 8)) 64 = v1)
    (h2 : m.readW (buf + BitVec.ofNat 64 (d + 16)) 64 = v2)
    (h3 : m.readW (buf + BitVec.ofNat 64 (d + 24)) 64 = v3) :
    m.readW (buf + BitVec.ofNat 64 d) 256 = (v3 ++ v2) ++ (v1 ++ v0) := by
  rw [readW_256, readW_128, readW_128]
  simp only [add_ofNat, Nat.add_assoc, Nat.reduceAdd]
  rw [h0, h1, h2, h3]

/-- Read back a stored quadword. -/
local macro "qread" : tactic => `(tactic|
  simp (disch := decide) only [storeAll, constPairs, List.foldl_cons, List.foldl_nil, Nat.reduceAdd,
    readW64_off, Mem.readW_writeW_self64])

theorem consts_mem (m : Mem) (buf : Addr) : Consts (storeAll buf constPairs m) buf := by
  have R16 := read4 (m := storeAll buf constPairs m) (buf := buf) (d := 128)
    (v0 := 0x0504070601000302) (v1 := 0x0d0c0f0e09080b0a) (v2 := 0x0504070601000302)
    (v3 := 0x0d0c0f0e09080b0a) (by qread) (by qread) (by qread) (by qread)
  have R8 := read4 (m := storeAll buf constPairs m) (buf := buf) (d := 160)
    (v0 := 0x0605040702010003) (v1 := 0x0e0d0c0f0a09080b) (v2 := 0x0605040702010003)
    (v3 := 0x0e0d0c0f0a09080b) (by qread) (by qread) (by qread) (by qread)
  have RI := read4 (m := storeAll buf constPairs m) (buf := buf) (d := 192)
    (v0 := 0x0000000100000000) (v1 := 0x0000000300000002) (v2 := 0x0000000500000004)
    (v3 := 0x0000000700000006) (by qread) (by qread) (by qread) (by qread)
  refine ⟨by rw [R16]; decide, by rw [R16]; decide, ⟨by rw [R8]; decide, by rw [R8]; decide⟩,
    fun l q hl hq => ?_⟩
  have E := readW_extract (storeAll buf constPairs m) (buf + BitVec.ofNat 64 192) (w := 256)
    (k := 16 * l + 4 * q) (n := 4) (by lit_omega)
  rw [add_ofNat] at E
  refine E.symm.trans ?_
  rw [RI]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
    rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;> decide

end VG.Proof.ChaCha20.X86_64.Avx2

/-!
# ChaCha20 on x86-64 with AVX2: the output

The rounds' result plus the input states, transposed into blocks and XORed
into 512 bytes of data.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt serialize)
open VG.Proof.ChaCha20

/-! ## Adding a row of the input state -/

theorem addRow_eq (row : Nat) (x0 x1 x2 x3 : XReg) : addRow row [x0, x1, x2, x3] =
    [.vbroadcasti128 .xmm14 (at_ .rdi (16 * row)),
     .vop (.vpshufd .l256 .xmm15 .xmm14 0x00), .vop (.vbin .vpaddd .l256 x0 x0 .xmm15),
     .vop (.vpshufd .l256 .xmm15 .xmm14 0x55), .vop (.vbin .vpaddd .l256 x1 x1 .xmm15),
     .vop (.vpshufd .l256 .xmm15 .xmm14 0xaa), .vop (.vbin .vpaddd .l256 x2 x2 .xmm15),
     .vop (.vpshufd .l256 .xmm15 .xmm14 0xff), .vop (.vbin .vpaddd .l256 x3 x3 .xmm15)] := rfl

theorem addRow_ok {row : Nat} {x0 x1 x2 x3 : XReg} (e01 : x0 ≠ x1) (e02 : x0 ≠ x2) (e03 : x0 ≠ x3)
    (e12 : x1 ≠ x2) (e13 : x1 ≠ x3) (e23 : x2 ≠ x3) (h0 : x0 ≠ .xmm14) (h1 : x1 ≠ .xmm14)
    (h2 : x2 ≠ .xmm14) (h3 : x3 ≠ .xmm14) (k0 : x0 ≠ .xmm15) (k1 : x1 ≠ .xmm15) (k2 : x2 ≠ .xmm15)
    (k3 : x3 ≠ .xmm15) {s : State}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * row)) 16) :
    WP isa (.block (addRow row [x0, x1, x2, x3])) s fun s' =>
      (∀ l q, q < 4 →
        vw s' x0 l q = vw s x0 l q + dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * row)) 128) 0 ∧
        vw s' x1 l q = vw s x1 l q + dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * row)) 128) 1 ∧
        vw s' x2 l q = vw s x2 l q + dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * row)) 128) 2 ∧
        vw s' x3 l q = vw s x3 l q + dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * row)) 128) 3) ∧
      (∀ r l, r ≠ x0 → r ≠ x1 → r ≠ x2 → r ≠ x3 → r ≠ .xmm14 → r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  rw [addRow_eq]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, State.load128, hin,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', VOp.exec_gpr, VOp.exec_mem,
    VOp.exec_rd, VOp.exec_wr, State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr]
  refine ⟨fun l q hq => ?_, fun r l n0 n1 n2 n3 n14 n15 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [vw, lane_vpshufd256, lane_vbin256, State.lane_setV256, VBinOp.sse, e01, e02, e03,
      e12, e13, e23, e01.symm, e02.symm, e03.symm, e12.symm, e13.symm, e23.symm, h0, h1, h2, h3,
      k0, k1, k2, k3, h0.symm, h1.symm, h2.symm, k0.symm, k1.symm, k2.symm,
      reduceCtorEq, ite_true, ite_false, ite_self, dword_paddd _ _ hq, shuf_00 _ hq,
      shuf_55 _ hq, shuf_aa _ hq, shuf_ff _ hq, and_self]
  · simp only [lane_vpshufd256, lane_vbin256, State.lane_setV256, n0, n1, n2, n3, n14, n15,
      ite_false]

/-! ## Transposing -/

theorem transpose_ok {x0 x1 x2 x3 : XReg} (e01 : x0 ≠ x1) (e02 : x0 ≠ x2) (e03 : x0 ≠ x3)
    (e12 : x1 ≠ x2) (e13 : x1 ≠ x3) (e23 : x2 ≠ x3)
    (h0 : x0 ≠ .xmm12 ∧ x0 ≠ .xmm13 ∧ x0 ≠ .xmm14 ∧ x0 ≠ .xmm15)
    (h1 : x1 ≠ .xmm12 ∧ x1 ≠ .xmm13 ∧ x1 ≠ .xmm14 ∧ x1 ≠ .xmm15)
    (h2 : x2 ≠ .xmm12 ∧ x2 ≠ .xmm13 ∧ x2 ≠ .xmm14 ∧ x2 ≠ .xmm15)
    (h3 : x3 ≠ .xmm12 ∧ x3 ≠ .xmm13 ∧ x3 ≠ .xmm14 ∧ x3 ≠ .xmm15) {s : State} :
    WP isa (.block (transpose x0 x1 x2 x3)) s fun s' =>
      (∀ l,
        s'.lane x0 l = ofDwords (vw s x0 l 0) (vw s x1 l 0) (vw s x2 l 0) (vw s x3 l 0) ∧
        s'.lane x1 l = ofDwords (vw s x0 l 1) (vw s x1 l 1) (vw s x2 l 1) (vw s x3 l 1) ∧
        s'.lane x2 l = ofDwords (vw s x0 l 2) (vw s x1 l 2) (vw s x2 l 2) (vw s x3 l 2) ∧
        s'.lane x3 l = ofDwords (vw s x0 l 3) (vw s x1 l 3) (vw s x2 l 3) (vw s x3 l 3)) ∧
      (∀ r l, r ≠ x0 → r ≠ x1 → r ≠ x2 → r ≠ x3 → r ≠ .xmm12 → r ≠ .xmm13 → r ≠ .xmm14 →
        r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨a0, b0, c0, d0⟩ := h0; obtain ⟨a1, b1, c1, d1⟩ := h1
  obtain ⟨a2, b2, c2, d2⟩ := h2; obtain ⟨a3, b3, c3, d3⟩ := h3
  apply WP.of_runBlock
  simp only [transpose, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left', VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr]
  refine ⟨fun l => ?_, fun r l n0 n1 n2 n3 n12 n13 n14 n15 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [vw, lane_vbin256, VBinOp.sse, e01, e02, e03, e12, e13, e23, e01.symm, e02.symm,
      e03.symm, e12.symm, e13.symm, e23.symm, a0, b0, c0, d0, a1, b1, c1, d1, a2, b2, c2, d2, a3, b3,
      c3, d3, a0.symm, b0.symm, c0.symm, d0.symm, b1.symm, d1.symm,
      b2.symm, d2.symm, reduceCtorEq, ite_true,
      ite_false, punpcklqdq_eq, punpckhqdq_eq, dword_punpckldq, dword_punpckhdq, dword_ofDwords_0,
      dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, and_self]
  · simp only [lane_vbin256, n0, n1, n2, n3, n12, n13, n14, n15, ite_false]

/-! ## XORing 16 bytes into the data -/

/-- The 512 bytes of data of one iteration. -/
abbrev dR5 (a : Addr) : Region := ⟨a, 512⟩

theorem dR5_contains (a : Addr) {d n : Nat} (h : d + n ≤ 512) :
    (dR5 a).Contains (a + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat a (by lit_omega)]; exact h

/-- Every access within the 512 bytes at `a` is permitted by `ws`. -/
def DWin (ws : List Region) (a : Addr) : Prop :=
  ∀ off n, off + n ≤ 512 → InRegions ws (a + BitVec.ofNat 64 off) n

theorem State.xmm_lane (s : State) (r : XReg) : s.xmm r = s.lane r 0 := by
  simp [State.lane]

/-- A byte of the data after a 16-byte write at offset `off`. -/
theorem byte_write16 (m : Mem) (a : Addr) (v : BitVec 128) {off k : Nat} (ho : off + 16 ≤ 512)
    (hk : k < 512) : (m.writeW (a + BitVec.ofNat 64 off) v) (a + BitVec.ofNat 64 k) =
      if off ≤ k ∧ k < off + 16 then byte v (k - off) else m (a + BitVec.ofNat 64 k) := by
  by_cases h : off ≤ k ∧ k < off + 16
  · rw [ite_eq_left h, show a + BitVec.ofNat 64 k = a + BitVec.ofNat 64 off + BitVec.ofNat 64 (k - off) by
      rw [add_ofNat, Nat.add_sub_cancel' h.1]]
    exact writeW_byte _ _ _ (by lit_omega) (by lit_omega)
  · rw [ite_eq_right h]
    refine writeW_byte_off _ _ _ _ ?_
    rw [Offset.sub_toNat' a (by lit_omega) (by lit_omega)]
    split <;> omega

theorem xor16_ok {x : XReg} (hx : x ≠ .xmm12) {off : Nat} (ho : off + 16 ≤ 512) {a : Addr}
    {s : State} (hrsi : s.gpr .rsi = a) (hw : DWin s.wr a) :
    WP isa (.block (xor16 x off)) s fun s' =>
      (∀ k < 512, s'.mem (a + BitVec.ofNat 64 k) = if off ≤ k ∧ k < off + 16 then
        s.mem (a + BitVec.ofNat 64 k) ^^^ byte (s.lane x 0) (k - off) else s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dR5 a] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have c := dR5_contains a ho
  have o1 : InRegions s.wr (a + BitVec.ofNat 64 off) 16 := hw off 16 ho
  have i1 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 off) 16 :=
    let ⟨r, hr, hc⟩ := o1; ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.of_runBlock
  simp only [xor16, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrsi, State.load128,
    State.store128_eq, i1, o1, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left', VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, State.setV_gpr,
    State.setV_mem, State.setV_rd, State.setV_wr, State.setMem_gpr, State.setMem_mem,
    State.setMem_rd, State.setMem_wr, State.xmm_lane, lane_vbin128, State.lane_setV128, hx,
    ite_false, VBinOp.sse, XBinOp.eval]
  refine ⟨fun k hk => ?_, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c,
    fun r l hr => ?_, trivial, trivial, trivial⟩
  · rw [byte_write16 _ _ _ ho hk]
    by_cases h : off ≤ k ∧ k < off + 16
    · simp only [h.1, h.2, and_self, ite_true, byte]
      rw [BitVec.extractLsb'_xor, byte_readW _ _ (by lit_omega), add_ofNat, Nat.add_sub_cancel' h.1]
    · simp only [h, ite_false]
  · simp only [State.setMem_lane, lane_vbin128, State.lane_setV128, hr, ite_false]

/-! ## XORing a row of the eight blocks -/

/-- Row `row` of blocks `i` and `i + 4`, from lanes 0 and 1 of `x`. -/
def piece (row : Nat) (x : XReg) (i : Nat) : List Instr :=
  xor16 x (64 * i + 16 * row) ++ [.vop (.vextracti128 .xmm13 x 1)] ++ xor16 .xmm13 (64 * (i + 4) + 16 * row)

theorem piece_ok {row i : Nat} (hrow : row < 4) (hi : i < 4) {x : XReg} (hx12 : x ≠ .xmm12)
    {a : Addr} {s : State} (hrsi : s.gpr .rsi = a) (hw : DWin s.wr a) :
    WP isa (.block (piece row x i)) s fun s' =>
      (∀ k < 512, s'.mem (a + BitVec.ofNat 64 k) =
        if (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row then
          s.mem (a + BitVec.ofNat 64 k) ^^^ byte (s.lane x (k / 64 / 4)) (k % 16)
        else s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dR5 a] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.block_append (WP.mono (xor16_ok hx12 (by lit_omega) hrsi hw)
    fun s₁ ⟨m₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine WP.mono (xor16_ok (x := .xmm13) (by decide) (off := 64 * (i + 4) + 16 * row) (a := a) (by lit_omega)
    (by rw [VOp.exec_gpr, g₁, hrsi]) (by rw [VOp.exec_wr, w₁]; exact hw))
    fun s₃ ⟨m₃, f₃, l₃, g₃, r₃, w₃⟩ => ?_
  simp only [VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, lane_vextracti128_1, ite_true,
    l₁ x 1 hx12] at m₃ f₃ l₃ g₃ r₃ w₃
  refine ⟨fun k hk => ?_, f₁.trans f₃, fun r l h12 h13 => ?_, g₃.trans g₁, r₃.trans r₁, w₃.trans w₁⟩
  · rw [m₃ k hk, m₁ k hk]
    by_cases h1 : 64 * i + 16 * row ≤ k ∧ k < 64 * i + 16 * row + 16
    · have h2 : ¬ (64 * (i + 4) + 16 * row ≤ k ∧ k < 64 * (i + 4) + 16 * row + 16) := by omega
      have hc : (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row := by omega
      rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left hc, show k / 64 / 4 = 0 by omega,
        show k - (64 * i + 16 * row) = k % 16 by omega]
    · by_cases h2 : 64 * (i + 4) + 16 * row ≤ k ∧ k < 64 * (i + 4) + 16 * row + 16
      · have hc : (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row := by omega
        rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left hc, show k / 64 / 4 = 1 by omega,
          show k - (64 * (i + 4) + 16 * row) = k % 16 by omega]
      · have hc : ¬ ((k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row) := by omega
        rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right hc]
  · rw [l₃ r l h12, ite_eq_right h13, l₁ r l h12]

theorem xorRow_eq (row : Nat) (x0 x1 x2 x3 : XReg) : xorRow row [x0, x1, x2, x3] =
    piece row x0 0 ++ (piece row x1 1 ++ (piece row x2 2 ++ piece row x3 3)) := by
  simp only [xorRow, piece, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getD_cons_zero, List.getD_cons_succ,
    List.append_assoc]

theorem xorRow_ok {row : Nat} (hrow : row < 4) {x0 x1 x2 x3 : XReg}
    (h0 : x0 ≠ .xmm12 ∧ x0 ≠ .xmm13) (h1 : x1 ≠ .xmm12 ∧ x1 ≠ .xmm13)
    (h2 : x2 ≠ .xmm12 ∧ x2 ≠ .xmm13) (h3 : x3 ≠ .xmm12 ∧ x3 ≠ .xmm13) {a : Addr} {s : State}
    (hrsi : s.gpr .rsi = a) (hw : DWin s.wr a) :
    WP isa (.block (xorRow row [x0, x1, x2, x3])) s fun s' =>
      (∀ k < 512, s'.mem (a + BitVec.ofNat 64 k) =
        if k % 64 / 16 = row then
          s.mem (a + BitVec.ofNat 64 k) ^^^
            byte (s.lane ([x0, x1, x2, x3].getD (k / 64 % 4) .xmm0) (k / 64 / 4)) (k % 16)
        else s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dR5 a] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [xorRow_eq]
  refine WP.block_append (WP.mono (piece_ok hrow (i := 0) (by lit_omega) h0.1 hrsi hw)
    fun s₁ ⟨m₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_)
  refine WP.block_append (WP.mono (piece_ok hrow (i := 1) (a := a) (by lit_omega) h1.1 (by rw [g₁, hrsi])
    (by rw [w₁]; exact hw)) fun s₂ ⟨m₂, f₂, l₂, g₂, r₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (piece_ok hrow (i := 2) (a := a) (by lit_omega) h2.1 (by rw [g₂, g₁, hrsi])
    (by rw [w₂, w₁]; exact hw)) fun s₃ ⟨m₃, f₃, l₃, g₃, r₃, w₃⟩ => ?_)
  refine WP.mono (piece_ok hrow (i := 3) (a := a) (by lit_omega) h3.1 (by rw [g₃, g₂, g₁, hrsi])
    (by rw [w₃, w₂, w₁]; exact hw)) fun s₄ ⟨m₄, f₄, l₄, g₄, r₄, w₄⟩ => ?_
  have e1 : ∀ l, s₁.lane x1 l = s.lane x1 l := fun l => l₁ _ l h1.1 h1.2
  have e2 : ∀ l, s₂.lane x2 l = s.lane x2 l := fun l => (l₂ _ l h2.1 h2.2).trans (l₁ _ l h2.1 h2.2)
  have e3 : ∀ l, s₃.lane x3 l = s.lane x3 l := fun l =>
    ((l₃ _ l h3.1 h3.2).trans (l₂ _ l h3.1 h3.2)).trans (l₁ _ l h3.1 h3.2)
  refine ⟨fun k hk => ?_, ((f₁.trans f₂).trans f₃).trans f₄, fun r l n12 n13 => ?_,
    by rw [g₄, g₃, g₂, g₁], by rw [r₄, r₃, r₂, r₁], by rw [w₄, w₃, w₂, w₁]⟩
  · rw [m₄ k hk, m₃ k hk, m₂ k hk, m₁ k hk, e1, e2, e3]
    rcases (by omega : k / 64 = 0 ∨ k / 64 = 1 ∨ k / 64 = 2 ∨ k / 64 = 3 ∨
      k / 64 = 4 ∨ k / 64 = 5 ∨ k / 64 = 6 ∨ k / 64 = 7) with h | h | h | h | h | h | h | h <;>
      simp [h]
  · rw [l₄ r l n12 n13, l₃ r l n12 n13, l₂ r l n12 n13, l₁ r l n12 n13]

/-! ## A row of the eight blocks, into the data -/

theorem byte_ofDwords (a0 a1 a2 a3 : Word) (b : Nat) :
    byte (ofDwords a0 a1 a2 a3) b = (dword (ofDwords a0 a1 a2 a3) (b / 4)).extractLsb' (8 * (b % 4)) 8 := by
  rw [byte, dword_eq, extract_extract _ _ _ _ _ (by lit_omega), show 32 * (b / 4) + 8 * (b % 4) = 8 * b by omega]

/-- Byte `k % 64` of a serialized block, in row `row`. -/
theorem serialize_row (S : CState) {k row : Nat} (hrow : row < 4) (hk : k % 64 / 16 = row) :
    (serialize S).getD (k % 64) 0 =
      byte (ofDwords (S[4 * row]'(by lit_omega)) (S[4 * row + 1]'(by lit_omega)) (S[4 * row + 2]'(by lit_omega))
        (S[4 * row + 3]'(by lit_omega))) (k % 16) := by
  rw [serialize_getD _ (by lit_omega), byte_ofDwords, show k % 64 % 4 = k % 16 % 4 by omega]
  rcases (by omega : k % 16 / 4 = 0 ∨ k % 16 / 4 = 1 ∨ k % 16 / 4 = 2 ∨ k % 16 / 4 = 3) with h | h | h | h
  · have e : k % 64 / 4 = 4 * row := by omega
    simp only [h, e, dword_ofDwords_0]
  · have e : k % 64 / 4 = 4 * row + 1 := by omega
    simp only [h, e, dword_ofDwords_1]
  · have e : k % 64 / 4 = 4 * row + 2 := by omega
    simp only [h, e, dword_ofDwords_2]
  · have e : k % 64 / 4 = 4 * row + 3 := by omega
    simp only [h, e, dword_ofDwords_3]

/-- The registers `x0 … x3` hold row `row` of the blocks `B 0, …, B 7`. -/
def RowIn (row : Nat) (x0 x1 x2 x3 : XReg) (B : Nat → CState) (s : State) : Prop :=
  ∀ l q, l < 2 → q < 4 → (hrow : row < 4) →
    vw s x0 l q = (B (4 * l + q))[4 * row]'(by lit_omega) ∧ vw s x1 l q = (B (4 * l + q))[4 * row + 1]'(by lit_omega) ∧
    vw s x2 l q = (B (4 * l + q))[4 * row + 2]'(by lit_omega) ∧ vw s x3 l q = (B (4 * l + q))[4 * row + 3]'(by lit_omega)

theorem rowOut_ok {row : Nat} (hrow : row < 4) {x0 x1 x2 x3 : XReg} (e01 : x0 ≠ x1) (e02 : x0 ≠ x2)
    (e03 : x0 ≠ x3) (e12 : x1 ≠ x2) (e13 : x1 ≠ x3) (e23 : x2 ≠ x3)
    (h0 : x0 ≠ .xmm12 ∧ x0 ≠ .xmm13 ∧ x0 ≠ .xmm14 ∧ x0 ≠ .xmm15)
    (h1 : x1 ≠ .xmm12 ∧ x1 ≠ .xmm13 ∧ x1 ≠ .xmm14 ∧ x1 ≠ .xmm15)
    (h2 : x2 ≠ .xmm12 ∧ x2 ≠ .xmm13 ∧ x2 ≠ .xmm14 ∧ x2 ≠ .xmm15)
    (h3 : x3 ≠ .xmm12 ∧ x3 ≠ .xmm13 ∧ x3 ≠ .xmm14 ∧ x3 ≠ .xmm15) {B : Nat → CState} {a : Addr}
    {s : State} (hB : RowIn row x0 x1 x2 x3 B s) (hrsi : s.gpr .rsi = a) (hw : DWin s.wr a) :
    WP isa (.block (transpose x0 x1 x2 x3 ++ xorRow row [x0, x1, x2, x3])) s fun s' =>
      (∀ k < 512, s'.mem (a + BitVec.ofNat 64 k) =
        if k % 64 / 16 = row then
          s.mem (a + BitVec.ofNat 64 k) ^^^ (serialize (B (k / 64))).getD (k % 64) 0
        else s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dR5 a] s.mem s'.mem ∧
      (∀ r l, r ≠ x0 → r ≠ x1 → r ≠ x2 → r ≠ x3 → r ≠ .xmm12 → r ≠ .xmm13 → r ≠ .xmm14 →
        r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.mono (transpose_ok e01 e02 e03 e12 e13 e23 h0 h1 h2 h3)
    fun s₁ ⟨lt, lo, g₁, m₁, r₁, w₁⟩ => ?_)
  refine WP.mono (xorRow_ok hrow (a := a) ⟨h0.1, h0.2.1⟩ ⟨h1.1, h1.2.1⟩ ⟨h2.1, h2.2.1⟩ ⟨h3.1, h3.2.1⟩
    (by rw [g₁]; exact hrsi) (by rw [w₁]; exact hw)) fun s₂ ⟨m₂, f₂, l₂, g₂, r₂, w₂⟩ => ?_
  rw [m₁] at m₂ f₂
  refine ⟨fun k hk => ?_, f₂, fun r l n0 n1 n2 n3 n12 n13 n14 n15 => ?_, g₂.trans g₁, r₂.trans r₁,
    w₂.trans w₁⟩
  · rw [m₂ k hk]
    by_cases hr : k % 64 / 16 = row
    · rw [ite_eq_left hr, ite_eq_left hr, serialize_row _ hrow hr]
      obtain ⟨l, q, hl, hq, e⟩ : ∃ l q, l < 2 ∧ q < 4 ∧ k / 64 = 4 * l + q :=
        ⟨k / 64 / 4, k / 64 % 4, by omega, by omega, by omega⟩
      rw [e, show (4 * l + q) / 4 = l by omega, show (4 * l + q) % 4 = q by omega]
      obtain ⟨b0, b1, b2, b3⟩ := hB l q hl hq hrow
      rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
      · rw [List.getD_cons_zero, (lt l).1, b0, b1, b2, b3]
      · rw [List.getD_cons_succ, List.getD_cons_zero, (lt l).2.1, b0, b1, b2, b3]
      · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, (lt l).2.2.1, b0, b1, b2, b3]
      · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
          (lt l).2.2.2, b0, b1, b2, b3]
    · rw [ite_eq_right hr, ite_eq_right hr]
  · rw [l₂ r l n12 n13, lo r l n0 n1 n2 n3 n12 n13 n14 n15]

/-! ## The third row, through the slots -/

@[simp] theorem State.setMem_ymm (s : State) (m : Mem) (r : XReg) : (s.setMem m).ymm r = s.ymm r := by
  cases s; rfl

def store89 : List Instr :=
  [.vmovdquStore .l256 (at_ .rcx (slotOff 8)) .xmm12, .vmovdquStore .l256 (at_ .rcx (slotOff 9)) .xmm13]

/-- Words 8–11 of the eight states `vs`, in their slots. -/
def Slots (buf : Addr) (vs : Nat → CState) (m : Mem) : Prop :=
  ∀ r l q, (hr : r < 4) → l < 2 → q < 4 →
    m.readW (buf + BitVec.ofNat 64 (slotOff (8 + r) + (16 * l + 4 * q))) 32 = (vs (4 * l + q))[8 + r]'(by lit_omega)

theorem store89_ok {buf : Addr} {vs : Nat → CState} {s : State} (h : Holds buf false vs s)
    (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block store89) s fun s' =>
      Slots buf vs s'.mem ∧ (∀ r l, s'.lane r l = s.lane r l) ∧ Frame [slotsR buf] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o8 := out_buf hb (d := slotOff 8) (n := 32) (by decide)
  have o9 := out_buf hb (d := slotOff 8 + 32) (n := 32) (by decide)
  have s9 : slotOff 9 = slotOff 8 + 32 := rfl
  apply WP.of_runBlock
  simp only [store89, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, State.store256_eq,
    o8, o9, s9, ite_true, Option.some.injEq, exists_eq_left', State.setMem_gpr, State.setMem_mem,
    State.setMem_rd, State.setMem_wr, State.setMem_lane, State.setMem_ymm]
  refine ⟨fun r l q hr hl hq => ?_, fun r l => trivial, W2_frame buf (i := 8) (by decide) _ _
    (Frame.refl _ _), trivial, trivial, trivial⟩
  have hx : 16 * l + 4 * q + 4 ≤ 32 := by omega
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
  · have e := h 8 (by decide) l q hl hq
    simp only [inReg, vreg, vw, Bool.not_false] at e
    simp only [Nat.add_zero]
    rw [W2_first _ _ (i := 8) (by decide) _ _ hx, extract_ymm _ _ hl hq]; exact e
  · have e := h 9 (by decide) l q hl hq
    simp only [inReg, vreg, ite_true, vw, or_true, Bool.not_false] at e
    simp only [Nat.reduceAdd, s9]
    rw [W2_second _ _ 8 _ _ hx, extract_ymm _ _ hl hq]; exact e
  · have e := h 10 (by decide) l q hl hq
    simp only [inReg, Nat.reduceEqDiff, or_false, ite_true, ite_false,
      Bool.false_eq_true] at e
    simp only [Nat.reduceAdd]
    rw [W2_other _ _ (i := 8) (by decide) _ _ (d := slotOff 10 + (16 * l + 4 * q))
      (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)]; exact e
  · have e := h 11 (by decide) l q hl hq
    simp only [inReg, Nat.reduceEqDiff, or_false, or_true, ite_true, ite_false,
      Bool.false_eq_true] at e
    simp only [Nat.reduceAdd]
    rw [W2_other _ _ (i := 8) (by decide) _ _ (d := slotOff 11 + (16 * l + 4 * q))
      (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)]; exact e

def load4 : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rcx (slotOff 8)), .vmovdquLoad .l256 .xmm1 (at_ .rcx (slotOff 9)),
   .vmovdquLoad .l256 .xmm2 (at_ .rcx (slotOff 10)), .vmovdquLoad .l256 .xmm3 (at_ .rcx (slotOff 11))]

theorem load4_ok {buf : Addr} {vs : Nat → CState} {s : State} (h : Slots buf vs s.mem)
    (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block load4) s fun s' =>
      RowIn 2 .xmm0 .xmm1 .xmm2 .xmm3 vs s' ∧
      (∀ r l, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i8 := in_buf (rs := s.rd) hb (d := slotOff 8) (n := 32) (by decide)
  have i9 := in_buf (rs := s.rd) hb (d := slotOff 9) (n := 32) (by decide)
  have i10 := in_buf (rs := s.rd) hb (d := slotOff 10) (n := 32) (by decide)
  have i11 := in_buf (rs := s.rd) hb (d := slotOff 11) (n := 32) (by decide)
  apply WP.of_runBlock
  simp only [load4, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, State.load256, i8,
    i9, i10, i11, ite_true, Option.map_some, Option.some.injEq, exists_eq_left', State.setV_gpr,
    State.setV_mem, State.setV_rd, State.setV_wr]
  refine ⟨fun l q hl hq _ => ?_, fun r l n0 n1 n2 n3 => ?_, trivial, trivial, trivial, trivial⟩
  · have h0 := h 0 l q (by decide) hl hq
    have h1 := h 1 l q (by decide) hl hq
    have h2 := h 2 l q (by decide) hl hq
    have h3 := h 3 l q (by decide) hl hq
    simp only [Nat.reduceAdd, Nat.add_zero] at h0 h1 h2 h3
    simp only [vw, State.lane_setV256, reduceCtorEq, ite_true, ite_false, dword_load256 _ _ hl hq,
      add_ofNat, Nat.reduceMul, Nat.reduceAdd, h0, h1, h2, h3, and_self]
  · simp only [State.lane_setV256, n0, n1, n2, n3, ite_false]

/-! ## Adding the input state -/

/-- Row `row` of the input state `S`, read 128 bits at a time at `st`. -/
def RowS (row : Nat) (S : CState) (m : Mem) (st : Addr) : Prop :=
  (hrow : row < 4) →
    dword (m.readW (st + BitVec.ofNat 64 (16 * row)) 128) 0 = S[4 * row]'(by lit_omega) ∧
    dword (m.readW (st + BitVec.ofNat 64 (16 * row)) 128) 1 = S[4 * row + 1]'(by lit_omega) ∧
    dword (m.readW (st + BitVec.ofNat 64 (16 * row)) 128) 2 = S[4 * row + 2]'(by lit_omega) ∧
    dword (m.readW (st + BitVec.ofNat 64 (16 * row)) 128) 3 = S[4 * row + 3]'(by lit_omega)

theorem rowS_of (m : Mem) (st : Addr) (row : Nat) : RowS row (stateAt m st) m st := fun hrow =>
  ⟨dword_row m st hrow (i := 0) (by decide), dword_row m st hrow (i := 1) (by decide),
    dword_row m st hrow (i := 2) (by decide), dword_row m st hrow (i := 3) (by decide)⟩

/-- Block `j` of the eight, before the input state is added: `vs j` plus `ctr S j`. -/
abbrev plus (vs : Nat → CState) (S : CState) (j : Nat) : CState := Vector.zipWith (· + ·) (vs j) (ctr S j)

theorem ctr_ne12 (S : CState) (j : Nat) {k : Nat} (hk : k < 16) (h : k ≠ 12) : (ctr S j)[k] = S[k] := by
  rw [ctr_get _ _ _ hk, ite_eq_right h]

theorem addRow_in {row : Nat} (h3 : row ≠ 3) {x0 x1 x2 x3 : XReg} (e01 : x0 ≠ x1)
    (e02 : x0 ≠ x2) (e03 : x0 ≠ x3) (e12 : x1 ≠ x2) (e13 : x1 ≠ x3) (e23 : x2 ≠ x3)
    (h0 : x0 ≠ .xmm14) (h1 : x1 ≠ .xmm14) (h2 : x2 ≠ .xmm14) (h3' : x3 ≠ .xmm14) (k0 : x0 ≠ .xmm15)
    (k1 : x1 ≠ .xmm15) (k2 : x2 ≠ .xmm15) (k3 : x3 ≠ .xmm15) {vs : Nat → CState} {S : CState}
    {s : State} (hin : RowIn row x0 x1 x2 x3 vs s) (hS : RowS row S s.mem (s.gpr .rdi))
    (hrd : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * row)) 16) :
    WP isa (.block (addRow row [x0, x1, x2, x3])) s fun s' =>
      RowIn row x0 x1 x2 x3 (plus vs S) s' ∧
      (∀ r l, r ≠ x0 → r ≠ x1 → r ≠ x2 → r ≠ x3 → r ≠ .xmm14 → r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (addRow_ok e01 e02 e03 e12 e13 e23 h0 h1 h2 h3' k0 k1 k2 k3 hrd)
    fun _ ⟨ha, hl, hg, hm, hr, hw⟩ => ⟨fun l q hl' hq hrow' => by
      obtain ⟨a0, a1, a2, a3⟩ := ha l q hq
      obtain ⟨b0, b1, b2, b3⟩ := hin l q hl' hq hrow'
      obtain ⟨c0, c1, c2, c3⟩ := hS hrow'
      rw [a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3]
      simp only [plus, Vector.getElem_zipWith]
      rw [ctr_ne12 _ _ _ (by lit_omega), ctr_ne12 _ _ _ (by lit_omega), ctr_ne12 _ _ _ (by lit_omega),
        ctr_ne12 _ _ _ (by lit_omega)]
      exact ⟨rfl, rfl, rfl, rfl⟩, hl, hg, hm, hr, hw⟩

def incAdd : List Instr :=
  [.vmovdquLoad .l256 .xmm15 (at_ .rcx incOff), v .vpaddd .xmm8 .xmm8 .xmm15]

theorem incAdd_ok {buf : Addr} {s : State} (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr)
    (hc : ∀ l q, l < 2 → q < 4 →
      s.mem.readW (buf + BitVec.ofNat 64 (192 + (16 * l + 4 * q))) 32 = BitVec.ofNat 32 (4 * l + q)) :
    WP isa (.block incAdd) s fun s' =>
      (∀ l q, l < 2 → q < 4 → vw s' .xmm8 l q = vw s .xmm8 l q + BitVec.ofNat 32 (4 * l + q)) ∧
      (∀ r l, r ≠ .xmm8 → r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i1 := in_buf (rs := s.rd) hb (d := incOff) (n := 32) (by decide)
  apply WP.of_runBlock
  simp only [incAdd, v, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, State.load256, i1,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', VOp.exec_gpr, VOp.exec_mem,
    VOp.exec_rd, VOp.exec_wr, State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr]
  refine ⟨fun l q hl hq => ?_, fun r l n8 n15 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [vw, lane_vbin256, State.lane_setV256, reduceCtorEq, ite_true, ite_false, VBinOp.sse,
      dword_paddd _ _ hq, dword_load256 _ _ hl hq]
    rw [add_ofNat]; exact congrArg _ (hc l q hl hq)
  · simp only [lane_vbin256, State.lane_setV256, n8, n15, ite_false]

theorem addRow3_in {buf : Addr} {vs : Nat → CState} {S : CState} {s : State}
    (hin : RowIn 3 .xmm8 .xmm9 .xmm10 .xmm11 vs s) (hS : RowS 3 S s.mem (s.gpr .rdi))
    (hrd : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * 3)) 16)
    (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr)
    (hc : ∀ l q, l < 2 → q < 4 →
      s.mem.readW (buf + BitVec.ofNat 64 (192 + (16 * l + 4 * q))) 32 = BitVec.ofNat 32 (4 * l + q)) :
    WP isa (.block (addRow 3 ([.xmm8, .xmm9, .xmm10, .xmm11] : List XReg) ++ incAdd)) s fun s' =>
      RowIn 3 .xmm8 .xmm9 .xmm10 .xmm11 (plus vs S) s' ∧
      (∀ r l, r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → r ≠ .xmm14 → r ≠ .xmm15 →
        s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.mono (addRow_ok (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hrd) fun s₁ ⟨ha, hl, hg, hm, hr, hw⟩ => ?_)
  refine WP.mono (incAdd_ok (by rw [hg, hrcx]) (by rw [hw]; exact hb) (by rw [hm]; exact hc))
    fun s₂ ⟨ia, il, ig, im, ir, iw⟩ => ⟨fun l q hl' hq _ => ?_, fun r l n8 n9 n10 n11 n14 n15 => ?_,
      ig.trans hg, im.trans hm, ir.trans hr, iw.trans hw⟩
  · obtain ⟨a0, a1, a2, a3⟩ := ha l q hq
    obtain ⟨b0, b1, b2, b3⟩ := hin l q hl' hq (by decide)
    obtain ⟨c0, c1, c2, c3⟩ := hS (by decide)
    have jl : ∀ r, r ≠ .xmm8 → r ≠ .xmm15 → vw s₂ r l q = vw s₁ r l q := fun r h8 h15 => by
      simp only [vw]; rw [il r l h8 h15]
    rw [ia l q hl' hq, jl .xmm9 (by decide) (by decide), jl .xmm10 (by decide) (by decide),
      jl .xmm11 (by decide) (by decide), a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3]
    simp only [plus, Vector.getElem_zipWith]
    rw [ctr_get _ _ _ (by decide), ite_eq_left (by decide), ctr_ne12 _ _ _ (by decide),
      ctr_ne12 _ _ _ (by decide), ctr_ne12 _ _ _ (by decide), BitVec.add_assoc]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [il r l n8 n15, hl r l n8 n9 n10 n11 n14 n15]

/-! ## What survives the steps -/

/-- `buf[128, 320)`: the constants, never written after the prologue. -/
abbrev hiR (buf : Addr) : Region := ⟨buf + BitVec.ofNat 64 128, 192⟩

theorem hiR_contains (buf : Addr) {d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 320) :
    (hiR buf).Contains (buf + BitVec.ofNat 64 d) n := Offset.contains buf h₁ (by lit_omega) (by lit_omega)

theorem hiR_sub (buf : Addr) : Region.Sub (hiR buf) (bufR buf) := Offset.sub_base buf (by lit_omega)

theorem slotsR_sub (buf : Addr) : Region.Sub (slotsR buf) (bufR buf) := Region.sub_prefix (by lit_omega)

theorem hiR_slots (buf : Addr) : (hiR buf).Disjoint (slotsR buf) := Offset.disjoint_base buf (by lit_omega) (by lit_omega)

theorem slots_contains (buf : Addr) {d n : Nat} (h : d + n ≤ 128) :
    (slotsR buf).Contains (buf + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat buf (by lit_omega)]; exact h

theorem st_contains (st : Addr) {d n : Nat} (h : d + n ≤ 64) :
    (stR st).Contains (st + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat st (by lit_omega)]; exact h

theorem rowS_frame {rs : List Region} {m m' : Mem} {st : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (stR st).Disjoint r) (row : Nat) : RowS row (stateAt m st) m' st := fun hrow => by
  have e : m'.readW (st + BitVec.ofNat 64 (16 * row)) 128 = m.readW (st + BitVec.ofNat 64 (16 * row)) 128 :=
    hf.readW (st_contains st (by lit_omega)) hd (by decide)
  rw [e]; exact rowS_of m st row hrow

theorem slots_frame {rs : List Region} {m m' : Mem} {buf : Addr} {vs : Nat → CState}
    (h : Slots buf vs m) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsR buf).Disjoint r) :
    Slots buf vs m' := fun r l q hr hl hq => by
  rw [hf.readW (slots_contains buf (by simp only [slotOff]; omega)) hd (by decide)]
  exact h r l q hr hl hq

/-- The counter increments in `buf[192, 224)`. -/
def Incs (buf : Addr) (m : Mem) : Prop :=
  ∀ l q, l < 2 → q < 4 →
    m.readW (buf + BitVec.ofNat 64 (192 + (16 * l + 4 * q))) 32 = BitVec.ofNat 32 (4 * l + q)

theorem incs_frame {rs : List Region} {m m' : Mem} {buf : Addr} (h : Incs buf m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (hiR buf).Disjoint r) : Incs buf m' := fun l q hl hq => by
  rw [hf.readW (hiR_contains buf (by lit_omega) (by lit_omega)) hd (by decide)]
  exact h l q hl hq

theorem RowIn.lanes {row : Nat} {x0 x1 x2 x3 : XReg} {B : Nat → CState} {s s' : State}
    (h : RowIn row x0 x1 x2 x3 B s) (e0 : ∀ l, s'.lane x0 l = s.lane x0 l)
    (e1 : ∀ l, s'.lane x1 l = s.lane x1 l) (e2 : ∀ l, s'.lane x2 l = s.lane x2 l)
    (e3 : ∀ l, s'.lane x3 l = s.lane x3 l) : RowIn row x0 x1 x2 x3 B s' := fun l q hl hq hrow => by
  simp only [vw, e0, e1, e2, e3]; exact h l q hl hq hrow

theorem holds_reg {buf : Addr} {vs : Nat → CState} {s : State} (h : Holds buf false vs s) {k : Nat}
    (hk : k < 16) (hk' : k < 8 ∨ 12 ≤ k) {l q : Nat} (hl : l < 2) (hq : q < 4) :
    vw s (vreg k) l q = (vs (4 * l + q))[k] := by
  have e := h k hk l q hl hq
  rwa [inReg_other _ hk', ite_eq_left rfl] at e

theorem holds_rows {buf : Addr} {vs : Nat → CState} {s : State} (h : Holds buf false vs s) :
    RowIn 0 .xmm0 .xmm1 .xmm2 .xmm3 vs s ∧ RowIn 1 .xmm4 .xmm5 .xmm6 .xmm7 vs s ∧
    RowIn 3 .xmm8 .xmm9 .xmm10 .xmm11 vs s :=
  ⟨fun _ _ hl hq _ => ⟨holds_reg h (k := 0) (by decide) (by decide) hl hq,
      holds_reg h (k := 1) (by decide) (by decide) hl hq, holds_reg h (k := 2) (by decide) (by decide) hl hq,
      holds_reg h (k := 3) (by decide) (by decide) hl hq⟩,
    fun _ _ hl hq _ => ⟨holds_reg h (k := 4) (by decide) (by decide) hl hq,
      holds_reg h (k := 5) (by decide) (by decide) hl hq, holds_reg h (k := 6) (by decide) (by decide) hl hq,
      holds_reg h (k := 7) (by decide) (by decide) hl hq⟩,
    fun _ _ hl hq _ => ⟨holds_reg h (k := 12) (by decide) (by decide) hl hq,
      holds_reg h (k := 13) (by decide) (by decide) hl hq,
      holds_reg h (k := 14) (by decide) (by decide) hl hq,
      holds_reg h (k := 15) (by decide) (by decide) hl hq⟩⟩

/-! ## The whole output -/

theorem finish_eq : finish =
    store89 ++ (addRow 0 ([.xmm0, .xmm1, .xmm2, .xmm3] : List XReg) ++
    ((transpose .xmm0 .xmm1 .xmm2 .xmm3 ++ xorRow 0 ([.xmm0, .xmm1, .xmm2, .xmm3] : List XReg)) ++
    (addRow 1 ([.xmm4, .xmm5, .xmm6, .xmm7] : List XReg) ++
    ((transpose .xmm4 .xmm5 .xmm6 .xmm7 ++ xorRow 1 ([.xmm4, .xmm5, .xmm6, .xmm7] : List XReg)) ++
    ((addRow 3 ([.xmm8, .xmm9, .xmm10, .xmm11] : List XReg) ++ incAdd) ++
    ((transpose .xmm8 .xmm9 .xmm10 .xmm11 ++
      xorRow 3 ([.xmm8, .xmm9, .xmm10, .xmm11] : List XReg)) ++
    (load4 ++ (addRow 2 ([.xmm0, .xmm1, .xmm2, .xmm3] : List XReg) ++
    (transpose .xmm0 .xmm1 .xmm2 .xmm3 ++
      xorRow 2 ([.xmm0, .xmm1, .xmm2, .xmm3] : List XReg)))))))))) := by
  simp only [finish, store89, load4, incAdd, List.append_assoc, List.cons_append, List.nil_append]

theorem finish_ok {st buf a : Addr} {vs : Nat → CState} {s : State} (hh : Holds buf false vs s)
    (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf) (hrsi : s.gpr .rsi = a)
    (hwst : stR st ∈ s.wr) (hwb : bufR buf ∈ s.wr) (hwd : DWin s.wr a) (hinc : Incs buf s.mem)
    (dsd : (stR st).Disjoint (dR5 a)) (dsb : (stR st).Disjoint (bufR buf))
    (dbd : (bufR buf).Disjoint (dR5 a)) :
    WP isa (.block finish) s fun s' =>
      (∀ k < 512, s'.mem (a + BitVec.ofNat 64 k) = s.mem (a + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (stateAt s.mem st) (k / 64))).getD (k % 64) 0) ∧
      Frame [slotsR buf, dR5 a] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have sdd : ∀ r ∈ [slotsR buf, dR5 a], (stR st).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dsb.sub_right (slotsR_sub buf)
    · exact dsd
  have hdd : ∀ r ∈ [slotsR buf, dR5 a], (hiR buf).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hiR_slots buf
    · exact dbd.sub_left (hiR_sub buf)
  have ssd : ∀ r ∈ [dR5 a], (slotsR buf).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact dbd.sub_left (slotsR_sub buf)
  have sub₁ : ∀ r ∈ [slotsR buf], r ∈ [slotsR buf, dR5 a] := by simp
  have sub₂ : ∀ r ∈ [dR5 a], r ∈ [slotsR buf, dR5 a] := by simp
  have rdst : ∀ (t : State), t.gpr = s.gpr → t.rd = s.rd → t.wr = s.wr → ∀ row, row < 4 →
      InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofNat 64 (16 * row)) 16 := by
    intro t g r w row hrow
    rw [g, r, w, hrdi]; exact ⟨stR st, List.mem_append_right _ hwst, st_contains st (by lit_omega)⟩
  obtain ⟨r0, r1, r3⟩ := holds_rows hh
  rw [finish_eq]
  -- Words 8 and 9 to their slots.
  refine WP.block_append (WP.mono (store89_ok hh hrcx hwb) fun s₁ ⟨sl₁, l₁, f₁, g₁, rd₁, wr₁⟩ => ?_)
  have G₁ := f₁.mono sub₁
  -- Row 0.
  refine WP.block_append (WP.mono (addRow_in (row := 0) (S := stateAt s.mem st) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (r0.lanes (l₁ _) (l₁ _) (l₁ _) (l₁ _)) (by rw [g₁, hrdi]; exact rowS_frame G₁ sdd 0)
    (rdst s₁ g₁ rd₁ wr₁ 0 (by decide))) fun s₂ ⟨a₂, l₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.block_append (WP.mono (rowOut_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a₂ (a := a) (by rw [g₂, g₁, hrsi])
    (by rw [wr₂, wr₁]; exact hwd)) fun s₃ ⟨d₃, f₃, l₃, g₃, rd₃, wr₃⟩ => ?_)
  rw [m₂] at f₃ d₃
  have G₃ := G₁.trans (f₃.mono sub₂)
  -- Row 1.
  refine WP.block_append (WP.mono (addRow_in (row := 1) (S := stateAt s.mem st) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (r1.lanes (fun l => by simp (disch := decide) only [l₃, l₂, l₁])
      (fun l => by simp (disch := decide) only [l₃, l₂, l₁])
      (fun l => by simp (disch := decide) only [l₃, l₂, l₁])
      (fun l => by simp (disch := decide) only [l₃, l₂, l₁]))
    (by rw [g₃, g₂, g₁, hrdi]; exact rowS_frame G₃ sdd 1)
    (rdst s₃ (by rw [g₃, g₂, g₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) 1 (by decide)))
    fun s₄ ⟨a₄, l₄, g₄, m₄, rd₄, wr₄⟩ => ?_)
  refine WP.block_append (WP.mono (rowOut_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a₄ (a := a)
    (by rw [g₄, g₃, g₂, g₁, hrsi]) (by rw [wr₄, wr₃, wr₂, wr₁]; exact hwd))
    fun s₅ ⟨d₅, f₅, l₅, g₅, rd₅, wr₅⟩ => ?_)
  rw [m₄] at f₅ d₅
  have G₅ := G₃.trans (f₅.mono sub₂)
  -- Row 3, with the counters.
  refine WP.block_append (WP.mono (addRow3_in (buf := buf) (S := stateAt s.mem st)
    (r3.lanes (fun l => by simp (disch := decide) only [l₅, l₄, l₃, l₂, l₁])
      (fun l => by simp (disch := decide) only [l₅, l₄, l₃, l₂, l₁])
      (fun l => by simp (disch := decide) only [l₅, l₄, l₃, l₂, l₁])
      (fun l => by simp (disch := decide) only [l₅, l₄, l₃, l₂, l₁]))
    (by rw [g₅, g₄, g₃, g₂, g₁, hrdi]; exact rowS_frame G₅ sdd 3)
    (rdst s₅ (by rw [g₅, g₄, g₃, g₂, g₁]) (by rw [rd₅, rd₄, rd₃, rd₂, rd₁])
      (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]) 3 (by decide))
    (by rw [g₅, g₄, g₃, g₂, g₁, hrcx]) (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwb)
    (incs_frame hinc G₅ hdd)) fun s₆ ⟨a₆, l₆, g₆, m₆, rd₆, wr₆⟩ => ?_)
  refine WP.block_append (WP.mono (rowOut_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a₆ (a := a)
    (by rw [g₆, g₅, g₄, g₃, g₂, g₁, hrsi]) (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwd))
    fun s₇ ⟨d₇, f₇, l₇, g₇, rd₇, wr₇⟩ => ?_)
  rw [m₆] at f₇ d₇
  have G₇ := G₅.trans (f₇.mono sub₂)
  have H₇ : Frame [dR5 a] s₁.mem s₇.mem := (f₃.trans f₅).trans f₇
  -- Row 2, from the slots.
  refine WP.block_append (WP.mono (load4_ok (slots_frame sl₁ H₇ ssd)
    (by rw [g₇, g₆, g₅, g₄, g₃, g₂, g₁, hrcx]) (by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwb))
    fun s₈ ⟨a₈, l₈, g₈, m₈, rd₈, wr₈⟩ => ?_)
  refine WP.block_append (WP.mono (addRow_in (row := 2) (S := stateAt s.mem st) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a₈
    (by rw [g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁, hrdi, m₈]; exact rowS_frame G₇ sdd 2)
    (rdst s₈ (by rw [g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁]) (by rw [rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁])
      (by rw [wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]) 2 (by decide)))
    fun s₉ ⟨a₉, l₉, g₉, m₉, rd₉, wr₉⟩ => ?_)
  refine WP.mono (rowOut_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a₉ (a := a)
    (by rw [g₉, g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁, hrsi])
    (by rw [wr₉, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwd))
    fun s₁₀ ⟨d₁₀, f₁₀, _, g₁₀, rd₁₀, wr₁₀⟩ => ?_
  rw [m₉, m₈] at f₁₀ d₁₀
  refine ⟨fun k hk => ?_, G₇.trans (f₁₀.mono sub₂), by rw [g₁₀, g₉, g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁],
    by rw [rd₁₀, rd₉, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₁₀, wr₉, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  have e₁ : s₁.mem (a + BitVec.ofNat 64 k) = s.mem (a + BitVec.ofNat 64 k) :=
    f₁.bytes (R := dR5 a) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact (dbd.sub_left (slotsR_sub buf)).symm) (show 512 ≤ 2 ^ 64 by decide) hk
  rw [d₁₀ k hk, d₇ k hk, d₅ k hk, d₃ k hk, e₁]
  rcases (by omega : k % 64 / 16 = 0 ∨ k % 64 / 16 = 1 ∨ k % 64 / 16 = 2 ∨ k % 64 / 16 = 3)
    with h | h | h | h <;> simp only [h, Nat.reduceEqDiff, ite_true, ite_false]

end VG.Proof.ChaCha20.X86_64.Avx2
