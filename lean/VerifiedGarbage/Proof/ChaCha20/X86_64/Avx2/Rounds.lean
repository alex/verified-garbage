import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2
import VerifiedGarbage.Proof.ChaCha20.Spec
import Mathlib.Tactic.IntervalCases

/-!
# ChaCha20 on x86-64 with AVX2: the rounds

Untrusted: everything here is checked by Lean. Doubleword `i` of lane `l` of
a register holds a word of block `4 l + i`; each quarter round of the code is
the specification's on every one of the eight blocks.
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
  rw [Mem.sub_ofNat_toNat buf (by omega)]; exact h

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
  have e1 := slotOff_succ (i := i) (by omega)
  have e2 := slotOff_succ (i := j) (by omega)
  have o1 := out_buf hw (d := slotOff i) (n := 32) (by omega)
  have o2 := out_buf hw (d := slotOff i + 32) (n := 32) (by omega)
  have i1 := in_buf (rs := s.rd) hw (d := slotOff j) (n := 32) (by omega)
  have i2 := in_buf (rs := s.rd) hw (d := slotOff j + 32) (n := 32) (by omega)
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

theorem slots_m8 (buf : Addr) : (⟨buf + BitVec.ofNat 64 160, 256 / 8⟩ : Region).Disjoint (slotsR buf) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem RI.masks {buf : Addr} {p : Bool} {vs : Nat → CState} {s₀ s : State} (h : RI buf p vs s₀ s)
    (hrcx : s₀.gpr .rcx = buf) (hw : bufR buf ∈ s₀.wr) (h8 : M8 s₀.mem buf) : Masks s := by
  have ea : s.ea (at_ .rcx rot8Off) = buf + BitVec.ofNat 64 160 := by
    rw [ea_at, h.gpr, hrcx]; rfl
  have e : s.mem.readW (buf + BitVec.ofNat 64 160) 256 = s₀.mem.readW (buf + BitVec.ofNat 64 160) 256 :=
    h.frame.readW (Region.contains_self _ _) (by simpa using slots_m8 buf) (by decide)
  refine ⟨h.m16, ?_, ?_, ?_⟩
  · rw [ea, h.rd, h.wr]; exact in_buf hw (by omega)
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
  refine (readW_writeW_off _ buf y₂ (d := slotOff i + x) (e := slotOff i + 32) (n := 4) (by omega)
    (by omega) (by omega)).trans ?_
  rw [← add_ofNat]
  exact readW_writeW_inside _ _ _ (by omega) (by omega)

theorem W2_second (m : Mem) (buf : Addr) (i : Nat) (y₁ y₂ : BitVec 256)
    {x : Nat} (hx : x + 4 ≤ 32) :
    (W2 m buf i y₁ y₂).readW (buf + BitVec.ofNat 64 (slotOff i + 32 + x)) 32 =
      y₂.extractLsb' (8 * x) (8 * 4) := by
  rw [← add_ofNat]
  exact readW_writeW_inside _ _ _ (k := x) (n := 4) (by omega) (by omega)

theorem W2_other (m : Mem) (buf : Addr) {i : Nat} (hi : slotOff i + 64 ≤ 128) (y₁ y₂ : BitVec 256)
    {d : Nat} (hd : d + 4 ≤ slotOff i ∨ slotOff i + 64 ≤ d) (hd' : d < 2 ^ 32) :
    (W2 m buf i y₁ y₂).readW (buf + BitVec.ofNat 64 d) 32 = m.readW (buf + BitVec.ofNat 64 d) 32 := by
  exact (readW_writeW_off _ buf y₂ (d := d) (e := slotOff i + 32) (n := 4) (by omega) (by omega)
    (by omega)).trans (readW_writeW_off _ buf y₁ (d := d) (e := slotOff i) (n := 4) (by omega)
    (by omega) (by omega))

theorem W2_frame {m m' : Mem} (buf : Addr) {i : Nat} (hi : slotOff i + 64 ≤ 128) (y₁ y₂ : BitVec 256)
    (h : Frame [slotsR buf] m m') : Frame [slotsR buf] m (W2 m' buf i y₁ y₂) := by
  have c : ∀ d, d + 32 ≤ 128 → (slotsR buf).Contains (buf + BitVec.ofNat 64 d) (256 / 8) := by
    intro d hd
    simp only [Region.Contains]
    rw [Mem.sub_ofNat_toNat buf (by omega)]; omega
  exact (h.writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by omega))

theorem inReg_other (p : Bool) {k : Nat} (hk : k < 8 ∨ 12 ≤ k) : inReg p k = true := by
  simp only [inReg]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem vreg_other {k : Nat} (hk : k < 16) (hk' : k < 8 ∨ 12 ≤ k) :
    vreg k ≠ .xmm12 ∧ vreg k ≠ .xmm13 := by
  rcases hk' with h | h <;> interval_cases k <;> decide

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
  refine WP.seq (WP.mono (swap_step h₂ hrcx hb) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₃ hrcx hb h8) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₄ hrcx hb h8) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₅ hrcx hb h8) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₆ hrcx hb h8) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (swap_step h₇ hrcx hb) fun s₈ h₈ => ?_)
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
