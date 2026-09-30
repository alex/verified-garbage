import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttBfly
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-DSA on 32-bit ARM: the table, blocks and layers of `NTT` and `NTT⁻¹`

Untrusted: everything here is checked by Lean. `storeTab t 256` leaves the
`u32`s `t 0, …, t 255` at `r1` (`Tab`, `storeTab_ok`). The loops of
`nttBlk` and `nttLay`, for any butterfly code that does what a butterfly
`op` of the specification does (`BflyOk`): a block runs `len` butterflies
(`blockN`), and a layer its `128 / len` blocks (`layerN`), with the zetas
`Z (zi c)`, whose values `tab` the table at `zB` holds.
-/

namespace VG.Proof.MlDsa.Arm.Arith

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr inRegions_of)

/-! ## The table -/

/-- The `u32`s at `P` are the table `t`. -/
def Tab (t : Nat → Nat) (m : Mem) (P : Addr) : Prop := ∀ k < 256, coeffAt m P k = BitVec.ofNat 32 (t k)

/-- The table `tab` holds the values of the zetas `Z`. -/
def TabOf (tab : Nat → Nat) (Z : Nat → Zq) : Prop := ∀ k < 256, tab k = (Z k).val

theorem tab_word {t : Nat → Nat} (ht : ∀ k < 256, t k < q) (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 16 (t i / 65536) ++ ((BitVec.ofNat 16 (t i % 65536)).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 (t i) := by
  have := ht i hi
  rw [q_eq] at this
  generalize t i = v at *
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_zero, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  omega

theorem tabStep_ok (t : Nat → Nat) (ht : ∀ k < 256, t k < q) {i : Nat} (hi : i < 256) (s : State) {zB : BitVec 32}
    (h1 : s.gpr .r1 = zB) (hw : InRegions s.wr (State.addr (zB + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block (tabStep t i)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (zB + BitVec.ofNat 32 (4 * i))) (BitVec.ofNat 32 (t i)) ∧
        Keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' := by
  have ho : 4 * i < 4096 := by omega
  run_block [tabStep, h1, hw, ho, tab_word ht i hi]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl

/-- The table, stored in the 1024 bytes at `r1`. -/
theorem storeTab_ok (t : Nat → Nat) (ht : ∀ k < 256, t k < q) (s : State) {zB : BitVec 32}
    (h1 : s.gpr .r1 = zB) (hfit : zB.toNat + 1024 ≤ 2 ^ 32) (hw : polyRegion (State.addr zB) ∈ s.wr) :
    WP isa (.block (storeTab t 256)) s fun s' =>
      Tab t s'.mem (State.addr zB) ∧ Frame [polyRegion (State.addr zB)] s.mem s'.mem ∧
        Keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => Keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9,
      .r10, .r11, .lr] s s' ∧ Frame [polyRegion (State.addr zB)] s.mem s'.mem ∧
      ∀ j < k, coeffAt s'.mem (State.addr zB) j = BitVec.ofNat 32 (t j))
    (fun k s' hk ⟨hk', hf, ht'⟩ => ?_) 256 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s' ⟨hk, hf, ht'⟩ => ⟨ht', hf, hk⟩
  have e : State.addr (zB + BitVec.ofNat 32 (4 * k)) = coeffAddr (State.addr zB) k := by
    have := addr_ptr zB (4 * k) 0 (by omega)
    simp only [Nat.add_zero, BitVec.add_zero] at this
    exact this
  have hk256 : k < n := by rw [n_eq]; exact hk
  refine WP.mono (tabStep_ok t ht hk s' ((hk'.gpr .r1 (by decide)).trans h1)
      (by rw [e, hk'.wr]; exact inRegions_of hw (coeff_contains _ hk256)))
    fun s'' ⟨hm', hk''⟩ => ⟨hk'.trans hk'', ?_, fun j hj => ?_⟩
  · rw [hm', e]
    exact hf.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk256)
  · rw [hm', e, coeffAt_writeW _ _ (show j < n by rw [n_eq]; omega) hk256]
    by_cases e' : k = j
    · subst e'; rw [ite_eq_left rfl]
    · rw [ite_eq_right e']; exact ht' j (by omega)

/-- Writes elsewhere keep the table. -/
theorem Tab.frame {t : Nat → Nat} {m m' : Mem} {P : Addr} (h : Tab t m P) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (polyRegion P).Disjoint r) : Tab t m' P :=
  fun k hk => by rw [coeffAt_frame hf hd (show k < n by rw [n_eq]; exact hk)]; exact h k hk

/-! ## A block -/

section
variable {code : Nat → List Instr} {op : Poly → Nat → Nat → Zq → Poly} (hb : BflyOk code op)
include hb

/-- The `len` butterflies of a block. -/
theorem bflys_ok {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {len start : Nat} (hlen : 0 < len)
    (hl : len ≤ 128) (hs : start + 2 * len ≤ 256) (z : Zq) (G : Poly) (s : State)
    (h0 : s.gpr .r0 = p + BitVec.ofNat 32 (4 * start)) (hz : ZetaIn z s) (hG : PolyIs s.mem (State.addr p) G)
    (hw : polyRegion (State.addr p) ∈ s.wr) (h3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (len - 0))) :
    WP isa (.loop (.block (code len)) .ne) s fun s' =>
      PolyIs s'.mem (State.addr p) (blockN op G len z start len) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + len)) ∧ Keep bflyKeep s s' := by
  refine wp_loop_ne (fun t s' => PolyIs s'.mem (State.addr p) (blockN op G len z start t) ∧
      Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + t)) ∧
      s'.gpr .r3 = BitVec.ofNat 32 (1 * (len - t)) ∧ Keep bflyKeep s s') hlen
    (fun t ht s' ⟨hP, hf, h0', h3', hk⟩ => ?_) (fun _ ⟨hP, hf, h0', _, hk⟩ => ⟨hP, hf, h0', hk⟩)
    ⟨hG, Frame.refl _ _, by rw [h0, Nat.add_zero], h3, Keep.refl _ _⟩
  obtain ⟨z4, z5, z6, z7⟩ := hz
  have hz' : ZetaIn z s' := ⟨(hk.gpr .r4 (by decide)).trans z4, (hk.gpr .r5 (by decide)).trans z5,
    (hk.gpr .r6 (by decide)).trans z6, (hk.gpr .r7 (by decide)).trans z7⟩
  refine WP.mono (hb p len (start + t) hlen hl (by omega) hp z _ s' h0' hz' hP (by rw [hk.wr]; exact hw))
    fun s'' ⟨hP', hf', h0'', h3'', hz'', hk'⟩ => ⟨⟨?_, hf.trans hf', ?_, ?_, hk.trans hk'⟩, ?_⟩
  · rw [blockN_succ]; exact hP'
  · rw [h0'', Nat.add_assoc]
  · rw [h3'', h3']; exact count_sub (k := 1) ht
  · rw [hz'', h3']; exact count_z (k := 1) ht (by decide) (by omega)

omit hb in
theorem blkPre_ok (len : Nat) (hl : len ≤ 128) (op : DpOp) (hop : op = .add ∨ op = .sub) (s : State)
    {x : BitVec 32} (h1 : s.gpr .r1 = x) (hi : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block (([.ldr .r8 .r1 0] : List Instr) ++ zPieces .r8 ++
      ([.dp op .r1 .r1 (.imm 4), .mov .r3 (.imm (BitVec.ofNat 32 len))] : List Instr))) s fun s' =>
      s'.gpr .r5 = s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 >>> 14 ∧
      s'.gpr .r6 = s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 <<< 18 >>> 25 ∧
      s'.gpr .r7 = s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 <<< 25 >>> 25 ∧
      s'.gpr .r1 = (if op = .add then x + 4 else x - 4) ∧ s'.gpr .r3 = BitVec.ofNat 32 len ∧
      s'.mem = s.mem ∧ Keep [.r0, .r2, .r4, .r11, .lr] s s' := by
  have he : encodable (BitVec.ofNat 32 len) = true := by
    have : ∀ l < 129, encodable (BitVec.ofNat 32 l) = true := by decide
    exact this len (by omega)
  rcases hop with rfl | rfl <;>
  · run_block [zPieces, h1, hi, he]
    keep_simp

omit hb in
theorem blkPost_ok (len : Nat) (hl : len ≤ 128) (s : State) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4 * len))), .subs .r2 .r2 (.imm 1)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 (4 * len) ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧
        s'.z = (s.gpr .r2 - 1 == 0) ∧ s'.mem = s.mem ∧ Keep [.r1, .r4, .r5, .r6, .r7, .r11, .lr] s s' := by
  have he : encodable (BitVec.ofNat 32 (4 * len)) = true := by
    have : ∀ l < 129, encodable (BitVec.ofNat 32 (4 * l)) = true := by decide
    exact this len (by omega)
  run_block [he]
  keep_simp

/-- The pointer to the next zeta. -/
def nextZ (op : DpOp) (x : BitVec 32) : BitVec 32 := if op = .add then x + 4 else x - 4

/-- A block, with the zeta `Z k` at `r1`. -/
theorem blk_ok {tab : Nat → Nat} {Z : Nat → Zq} (hZ : TabOf tab Z) {p zB : BitVec 32}
    (hp : p.toNat + 1024 ≤ 2 ^ 32) (hzf : zB.toNat + 1024 ≤ 2 ^ 32) {len start k : Nat}
    (hlen : 0 < len) (hl : len ≤ 128) (hs : start + 2 * len ≤ 256) (hk : k < 256) (dop : DpOp)
    (hop : dop = .add ∨ dop = .sub) (G : Poly) (s : State) (h0 : s.gpr .r0 = p + BitVec.ofNat 32 (4 * start))
    (h1 : s.gpr .r1 = zB + BitVec.ofNat 32 (4 * k)) (h4 : s.gpr .r4 = Qw) (hG : PolyIs s.mem (State.addr p) G)
    (hw : polyRegion (State.addr p) ∈ s.wr) (hzw : polyRegion (State.addr zB) ∈ s.rd ++ s.wr)
    (ht : Tab tab s.mem (State.addr zB)) :
    WP isa (nttBlk (code len) len dop) s fun s' =>
      PolyIs s'.mem (State.addr p) (blockN op G len (Z k) start len) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + 2 * len)) ∧ s'.gpr .r1 = nextZ dop (s.gpr .r1) ∧
        s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧ Keep [.r4, .r11, .lr] s s' := by
  have eZ : State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0) = coeffAddr (State.addr zB) k :=
    addr_at0 hzf hk
  refine WP.seq (WP.mono (blkPre_ok len hl dop hop s h1 (by
    rw [eZ]; exact inRegions_of hzw (coeff_contains _ (show k < n by rw [n_eq]; exact hk))))
    fun s₁ ⟨e5, e6, e7, e1, e3, m₁, k₁⟩ => ?_)
  have hwv : s.mem.readW (State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 32 =
      BitVec.ofNat 32 (Z k).val := by
    rw [eZ, ← coeffAt_eq, ht k hk, hZ k hk]
  rw [hwv] at e5 e6 e7
  refine WP.seq (WP.mono (bflys_ok hb hp hlen hl hs (Z k) G s₁ ((k₁.gpr .r0 (by decide)).trans h0)
    ⟨(k₁.gpr .r4 (by decide)).trans h4, e5, e6, e7⟩ (by rw [m₁]; exact hG) (by rw [k₁.wr]; exact hw)
    (by rw [e3]; simp)) fun s₂ ⟨hP, hf, h0₂, k₂⟩ => ?_)
  refine WP.mono (blkPost_ok len hl s₂) fun s' ⟨h0', h2', hz', m', k₃⟩ => ⟨by rw [m']; exact hP,
    by rw [m', ← m₁]; exact hf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0', h0₂, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  · rw [k₃.gpr .r1 (by decide), k₂.gpr .r1 (by decide), e1, h1]; rfl
  · rw [h2', k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · rw [hz', k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · exact ((k₁.mono (rs' := [.r4, .r11, .lr]) (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))

omit hb in
theorem layPre_ok (c : Nat) (hc : c ≤ 128) (s : State) :
    WP isa (.block [.mov .r2 (.imm (BitVec.ofNat 32 c))]) s fun s' =>
      s'.gpr .r2 = BitVec.ofNat 32 c ∧ s'.mem = s.mem ∧ Keep [.r0, .r1, .r4, .r11, .lr] s s' := by
  have he : encodable (BitVec.ofNat 32 c) = true := by
    have : ∀ l < 129, encodable (BitVec.ofNat 32 l) = true := by decide
    exact this c (by omega)
  run_block [he]
  keep_simp

omit hb in
theorem layPost_ok (s : State) :
    WP isa (.block [.dp .sub .r0 .r0 (.imm 1024)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 - 1024 ∧ s'.mem = s.mem ∧ Keep [.r1, .r4, .r11, .lr] s s' := by
  run_block []
  keep_simp

omit hb in
/-- The facts about the lengths of the layers. -/
theorem lens_facts : ∀ len ∈ nttLens, 0 < len ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len ∧
    128 / len ≤ 128 := by
  decide

/-- A layer, from `r0` = `f` and the zeta of its first block at `r1`. -/
theorem lay_ok {tab : Nat → Nat} {Z : Nat → Zq} (hZ : TabOf tab Z) {p zB : BitVec 32}
    (hp : p.toNat + 1024 ≤ 2 ^ 32) (hzf : zB.toNat + 1024 ≤ 2 ^ 32) {len : Nat} (hlen : len ∈ nttLens)
    (dop : DpOp) (hop : dop = .add ∨ dop = .sub) (zi : Nat → Nat) (hzi : ∀ c < 128 / len, zi c < 256)
    (hstep : ∀ c < 128 / len, nextZ dop (zB + BitVec.ofNat 32 (4 * zi c)) = zB + BitVec.ofNat 32 (4 * zi (c + 1)))
    (F : Poly) (s : State) (h0 : s.gpr .r0 = p) (h1 : s.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi 0))
    (h4 : s.gpr .r4 = Qw) (hF : PolyIs s.mem (State.addr p) F) (hw : polyRegion (State.addr p) ∈ s.wr)
    (hzw : polyRegion (State.addr zB) ∈ s.rd ++ s.wr)
    (hd : (polyRegion (State.addr zB)).Disjoint (polyRegion (State.addr p))) (ht : Tab tab s.mem (State.addr zB)) :
    WP isa (nttLay (code len) len dop) s fun s' =>
      PolyIs s'.mem (State.addr p) (layerN op F len (fun c => Z (zi c)) (128 / len)) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ s'.gpr .r0 = p ∧
        s'.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi (128 / len)) ∧ Keep [.r4, .r11, .lr] s s' := by
  obtain ⟨hl0, hl1, hl2, hl3, hl4⟩ := lens_facts len hlen
  have hdd : ∀ r ∈ [polyRegion (State.addr p)], (polyRegion (State.addr zB)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hd
  refine WP.seq (WP.mono (layPre_ok (128 / len) hl4 s) fun s₁ ⟨e2, m₁, k₁⟩ => WP.seq ?_)
  refine WP.mono (Q := fun (s₂ : State) => PolyIs s₂.mem (State.addr p) (layerN op F len (fun c => Z (zi c)) (128 / len)) ∧
      Frame [polyRegion (State.addr p)] s.mem s₂.mem ∧ s₂.gpr .r0 = p + BitVec.ofNat 32 (4 * 256) ∧
      s₂.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi (128 / len)) ∧ Keep [.r4, .r11, .lr] s s₂) ?_
    fun s₂ ⟨hP, hf, h0₂, h1₂, k₂⟩ => ?_
  · refine wp_loop_ne (fun c s' => PolyIs s'.mem (State.addr p) (layerN op F len (fun c => Z (zi c)) c) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (2 * len * c)) ∧
        s'.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi c) ∧ s'.gpr .r2 = BitVec.ofNat 32 (1 * (128 / len - c)) ∧
        Keep [.r4, .r11, .lr] s s') hl3 (fun c hc s' ⟨hP, hf, h0', h1', h2', hk⟩ => ?_)
      (fun s' ⟨hP, hf, h0', h1', _, hk⟩ => ⟨hP, hf, by rw [h0', hl2], h1', hk⟩)
      ⟨by rw [m₁]; exact hF, by rw [m₁]; exact Frame.refl _ _, by rw [k₁.gpr .r0 (by decide), h0]; simp,
        by rw [k₁.gpr .r1 (by decide), h1], by rw [e2]; simp, k₁.mono (by decide)⟩
    have hcm : 2 * len * c + 2 * len ≤ 256 := by
      have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at this; omega
    refine WP.mono (blk_ok hb hZ hp hzf hl0 hl1 hcm (hzi c hc) dop hop _ s' h0' h1'
      ((hk.gpr .r4 (by decide)).trans h4) hP (by rw [hk.wr]; exact hw) (by rw [hk.rd, hk.wr]; exact hzw)
      (ht.frame hf hdd)) fun s'' ⟨hP', hf', h0'', h1'', h2'', hz'', hk'⟩ => ⟨⟨?_, hf.trans hf', ?_, ?_, ?_,
        hk.trans hk'⟩, ?_⟩
    · rw [layerN_succ]; exact hP'
    · rw [h0'', Nat.mul_succ]
    · rw [h1'', h1', hstep c hc]
    · rw [h2'', h2']; exact count_sub (k := 1) hc
    · rw [hz'', h2']; exact count_z (k := 1) hc (by decide) (by omega)
  · refine WP.mono (layPost_ok s₂) fun s' ⟨h0', m', k₃⟩ => ⟨by rw [m']; exact hP, by rw [m']; exact hf, ?_,
      by rw [k₃.gpr .r1 (by decide), h1₂], k₂.trans (k₃.mono (by decide))⟩
    rw [h0', h0₂]
    exact BitVec.add_sub_cancel _ _

end

end VG.Proof.MlDsa.Arm.Arith
