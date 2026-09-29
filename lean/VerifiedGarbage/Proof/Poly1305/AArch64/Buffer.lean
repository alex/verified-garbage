import VerifiedGarbage.Proof.Poly1305.AArch64.Blocks
import VerifiedGarbage.Proof.Poly1305.AArch64.Wp
import VerifiedGarbage.Proof.Poly1305.Stream

/-!
# Poly1305 on AArch64: the buffer

Untrusted: everything here is checked by Lean. Bytes stored into the buffer
(bytes 56–71 of the state), which leave the coefficients alone, and absorbing
the buffer as a block.
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P leNum bytesAt Repr Buffered)

/-! ## The buffer -/

theorem off_56 (p : Addr) : off p 56 = p + 56 := rfl

theorem and15 (x : BitVec 64) :
    x &&& (15 : BitVec 16).setWidth 64 = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show ((15 : BitVec 16).setWidth 64).toNat = 2 ^ 4 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega)]


/-- The buffer. -/
abbrev bfR (st : Addr) : Region := ⟨off st 56, 16⟩

/-- Byte `k` of the buffer. -/
abbrev bufB (st : Addr) (k : Nat) : Addr := st + BitVec.ofNat 64 (56 + k)

theorem bufB_eq (st : Addr) (k : Nat) : bufB st k = off st 56 + BitVec.ofNat 64 k := by
  rw [off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `[x + 56]` for `x = st + j`. -/
theorem bufB_of (st : Addr) (j : Nat) : st + BitVec.ofNat 64 j + BitVec.ofNat 64 56 = bufB st j := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

theorem bfR_contains (st : Addr) {d n : Nat} (h : d + n ≤ 16) :
    (bfR st).Contains (off st 56 + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains]
  rw [show off st 56 + BitVec.ofNat 64 d - off st 56 = BitVec.ofNat 64 d by bv_omega,
    toNat_ofNat_lt (by omega)]
  omega

theorem bufB_ne {st : Addr} {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    bufB st j ≠ bufB st k := by
  intro he
  have := congrArg BitVec.toNat (show BitVec.ofNat 64 (56 + j) = BitVec.ofNat 64 (56 + k) by
    simpa [bufB] using he)
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
  omega

/-- The buffer is writable when the state is. -/
theorem bufB_in {s : State} {st : Addr} (hw : sR st ∈ s.wr) {k : Nat} (hk : k < 16) :
    InRegions s.wr (bufB st k) 1 :=
  ⟨_, hw, contains_off (by omega) (by omega)⟩

theorem bfR_sub_wR (st : Addr) : Region.Sub (bfR st) (wR st) := by
  intro a ha
  simp only [Region.Contains, off] at *
  bv_omega

theorem bfR_disjoint_cR (st : Addr) : (bfR st).Disjoint (cR st) := by
  intro a h₁ h₂
  simp only [Region.Contains, off] at h₁ h₂
  bv_omega

/-- The first `n` bytes of the buffer are not where the coefficients are. -/
theorem buf_disjoint_cR (st : Addr) {n : Nat} (hn : n ≤ 16) :
    (⟨off st 56, n⟩ : Region).Disjoint (cR st) :=
  (bfR_disjoint_cR st).sub_left (Region.sub_prefix hn)

theorem coef_facts : ∀ k < 5, ∀ i < 5, 72 ≤ coef k i ∧ coef k i + 4 ≤ 108 := by decide

/-- The coefficients are unchanged by writes to the buffer. -/
theorem Coefs.frame {m m' : Mem} {st : Addr} {R : Nat} (h : Coefs m st R) (hf : Frame [bfR st] m m') :
    Coefs m' st R := by
  intro k hk i hi
  obtain ⟨c₁, c₂⟩ := coef_facts k hk i hi
  rw [← h k hk i hi]
  refine congrArg BitVec.toNat (hf.readW (r := ⟨off st (coef k i), 4⟩) (Region.contains_self _ _) ?_
    (by decide))
  simp only [List.mem_singleton, forall_eq]
  intro a h₁ h₂
  simp only [Region.Contains, off] at h₁ h₂
  bv_omega

/-- The coefficient words may be read when the state may be. -/
theorem coefIn_of {s : State} (hw : sR (s.gpr .x0) ∈ s.wr) : CoefIn s := fun off h₁ h₂ =>
  ⟨_, List.mem_append_right _ hw, contains_off (by omega) (by omega)⟩

/-- Absorbing the buffer: its 16 bytes, and `pad · 2¹²⁸`. -/
theorem absorbBuf_ok (s : State) (pad : Bool) {R : Nat} (hR : R < 2 ^ 128) (hm : s.gpr .x17 = M26)
    (hco : Coefs s.mem (s.gpr .x0) R) (hw : sR (s.gpr .x0) ∈ s.wr) :
    WP isa (.block ([.addImm .x .x1 .x0 56] ++ absorb pad)) s fun s' =>
      (Bounds s → hv s' % P = ((hv s + (leNum (bytesAt s.mem (off (s.gpr .x0) 56) 16) +
        2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps (.x1 :: absorbRegs) s s' := by
  refine WP.block_append (wp_addImm (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have x0₁ : s₁.gpr .x0 = s.gpr .x0 := u₁.other _ (by decide)
  have hin : ∀ d, d + 8 ≤ 16 → InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x1 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [u₁.rd, u₁.wr, u₁.gpr, ← off, off_off]
    exact ⟨_, List.mem_append_right _ hw, contains_off (by omega) (by omega)⟩
  refine WP.mono (absorb_ok s₁ pad hR (by rw [u₁.other _ (by decide)]; exact hm)
    (by rw [u₁.mem, x0₁]; exact hco) (coefIn_of (by rw [u₁.wr, x0₁]; exact hw)) (hin 0 (by omega))
    (hin (0 + 8) (by omega))) fun s' ⟨ha, k⟩ => ⟨fun hb => ?_, ?_⟩
  · have hv₁ : hv s₁ = hv s := by
      simp only [hv, v, u₁.other .x4 (by decide), u₁.other .x5 (by decide), u₁.other .x6 (by decide),
        u₁.other .x7 (by decide), u₁.other .x8 (by decide)]
    have hb₁ : Bounds s₁ := by
      simpa only [Bounds, v, u₁.other .x4 (by decide), u₁.other .x5 (by decide),
        u₁.other .x6 (by decide), u₁.other .x7 (by decide), u₁.other .x8 (by decide)] using hb
    obtain ⟨hv', hb'⟩ := ha hb₁
    refine ⟨?_, hb'⟩
    rw [hv', hv₁, leNum_key, u₁.mem, u₁.gpr]
  · refine ⟨fun r hr => ?_, by rw [k.2.1, u₁.mem], by rw [k.2.2.1, u₁.rd], by rw [k.2.2.2, u₁.wr]⟩
    simp only [List.mem_cons, not_or] at hr
    rw [k.1 r (by simpa using hr.2), u₁.other r hr.1]

/-! ## Copying bytes into the buffer -/

theorem copyIn_eq : copyIn = .loop (.block copyBody) (.nonzero .x .x10) := rfl

/-- While copying the `n` bytes at `src`, as in the memory `m₀`, to the buffer
from byte `j0` on, from the state `sI` (where `x11 = st + j0`): after `j` bytes. -/
structure CopyInv (sI : State) (m₀ : Mem) (src : Addr) (j0 n j : Nat) (s : State) : Prop where
  j_le : j ≤ n
  x1 : s.gpr .x1 = src + BitVec.ofNat 64 j
  x11 : s.gpr .x11 = sI.gpr .x0 + BitVec.ofNat 64 (j0 + j)
  x10 : s.gpr .x10 = BitVec.ofNat 64 (n - j)
  keep : ∀ r, r ≠ .x1 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  mem : s.mem = writeBytes sI.mem (bufB (sI.gpr .x0) j0) ((bytesAt m₀ src n).take j)

/-- What copying needs of the source: its bytes are readable, not in the
buffer, and as in `m₀`. -/
def SrcOk (sI : State) (m₀ : Mem) (src : Addr) (n : Nat) : Prop :=
  ∀ i < n, InRegions (sI.rd ++ sI.wr) (src + BitVec.ofNat 64 i) 1 ∧
    ¬ (bfR (sI.gpr .x0)).Contains (src + BitVec.ofNat 64 i) 1 ∧
    sI.mem (src + BitVec.ofNat 64 i) = m₀ (src + BitVec.ofNat 64 i)

theorem copy_step {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16)
    (hw : sR (sI.gpr .x0) ∈ sI.wr) (hs : SrcOk sI m₀ src n) {j : Nat} (hj : j < n) {s : State}
    (h : CopyInv sI m₀ src j0 n j s) :
    WP isa (.block copyBody) s fun s' =>
      CopyInv sI m₀ src j0 n (j + 1) s' ∧ s'.gpr .x10 = BitVec.ofNat 64 (n - (j + 1)) := by
  obtain ⟨hin, hnb, hm₀⟩ := hs j hj
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  have hq : (bfR (sI.gpr .x0)).Contains (bufB (sI.gpr .x0) j0) ((bytesAt m₀ src n).take j).length := by
    rw [bufB_eq, List.length_take]; exact bfR_contains _ (by omega)
  -- The byte read.
  have hbyte : s.mem (src + BitVec.ofNat 64 j) = m₀ (src + BitVec.ofNat 64 j) := by
    rw [h.mem, ← hm₀]
    exact writeBytes_frame _ _ _ hq _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hnb
  refine wp_ldrb (t := .x12) (a := src + BitVec.ofNat 64 j) (by decide)
    (by rw [h.x1, add_ofNat_zero]) (by rw [h.rd, h.wr]; exact hin) fun s₁ u₁ => ?_
  refine wp_strb (t := .x12) (a := bufB (sI.gpr .x0) (j0 + j)) (by decide)
    (by rw [u₁.other _ (by decide), h.x11, bufB_of]) (by rw [u₁.wr, h.wr]; exact bufB_in hw (by omega))
    fun s₂ m₂ => ?_
  refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ =>
    wp_subImm (by decide) fun s₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x1 → r ≠ .x12 → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, m₂.gpr, u₁.other r h4]
  have hx10 : s₅.gpr .x10 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [u₅.gpr, u₄.other .x10 (by decide), u₃.other .x10 (by decide), m₂.gpr, u₁.other .x10 (by decide),
      h.x10, show BitVec.ofNat 64 1 = 1 from rfl, ofNat_pred (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, hx10, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩, hx10⟩
  · rw [u₅.other .x1 (by decide), u₄.other .x1 (by decide), u₃.gpr, m₂.gpr, u₁.other .x1 (by decide), h.x1,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₅.other .x11 (by decide), u₄.gpr, u₃.other .x11 (by decide), m₂.gpr, u₁.other .x11 (by decide),
      h.x11, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g r h2 h3 h1 h4, h.keep r h1 h2 h3 h4]
  · rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, h.wr]
  · have hj' : j < (bytesAt m₀ src n).length := by omega
    have hl : ((bytesAt m₀ src n).take j).length = j := by rw [List.length_take, Nat.min_eq_left hj'.le]
    have ea : bufB (sI.gpr .x0) (j0 + j) =
        bufB (sI.gpr .x0) j0 + BitVec.ofNat 64 ((bytesAt m₀ src n).take j).length := by
      rw [hl, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
    have hv : (s₁.gpr .x12).setWidth 8 = (bytesAt m₀ src n)[j] := by
      rw [u₁.gpr, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, hbyte]; simp [bytesAt]
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, hv, u₁.mem, ea, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some, writeBytes_snoc _ _ _ _ (by omega)]

theorem copy_ok {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) (hn : 0 < n)
    (hw : sR (sI.gpr .x0) ∈ sI.wr) (hs : SrcOk sI m₀ src n) (hx1 : sI.gpr .x1 = src)
    (hx11 : sI.gpr .x11 = sI.gpr .x0 + BitVec.ofNat 64 j0) (hx10 : sI.gpr .x10 = BitVec.ofNat 64 n) :
    WP isa copyIn sI (CopyInv sI m₀ src j0 n n) := by
  have h₀ : CopyInv sI m₀ src j0 n 0 sI :=
    ⟨by omega, by rw [hx1, add_ofNat_zero], by rw [hx11, Nat.add_zero], by rw [hx10, Nat.sub_zero],
      fun _ _ _ _ _ => rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  rw [copyIn_eq]
  refine WP.loop (M := isa) (fun k s => ∃ j, k = n - j ∧ j < n ∧ CopyInv sI m₀ src j0 n j s)
    ?_ n sI ⟨0, rfl, hn, h₀⟩
  rintro k s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hj0 hw hs hj hc) fun s' ⟨hc', hx⟩ => ?_
  have hev : isa.eval (.nonzero .x .x10) s' = some (!(BitVec.ofNat 64 (n - (j + 1)) == 0)) := by
    rw [eval_nonzero, hx]; rfl
  rw [ofNat_beq_zero (by omega)] at hev
  by_cases hl : n - (j + 1) = 0
  · refine .inl ⟨by rw [hev]; simp [hl], ?_⟩
    rwa [show j + 1 = n by omega] at hc'
  · exact .inr ⟨by rw [hev]; simp [hl], _, by omega, j + 1, rfl, by omega, hc'⟩

/-- After copying: the buffer's first `j0` bytes and the `n` bytes copied. -/
theorem CopyInv.buf {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) {s : State}
    (h : CopyInv sI m₀ src j0 n n s) :
    bytesAt s.mem (off (sI.gpr .x0) 56) (j0 + n) =
      bytesAt sI.mem (off (sI.gpr .x0) 56) j0 ++ bytesAt m₀ src n := by
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  have e := bytesAt_writeBytes sI.mem (off (sI.gpr .x0) 56) j0 (bytesAt m₀ src n) (by omega)
  rw [hxs] at e
  rw [h.mem, List.take_of_length_le (by omega), bufB_eq]
  exact e

theorem CopyInv.frame {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) {s : State}
    (h : CopyInv sI m₀ src j0 n n s) : Frame [bfR (sI.gpr .x0)] sI.mem s.mem := by
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  rw [h.mem, List.take_of_length_le (by omega)]
  refine writeBytes_frame _ _ _ ?_
  rw [bufB_eq, hxs]; exact bfR_contains _ hj0

end VG.Proof.Poly1305.AArch64
