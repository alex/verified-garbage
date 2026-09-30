import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Poly1305.AArch64.Blocks
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

section

/-!
# Poly1305 on AArch64: one instruction at a time

Untrusted: everything here is checked by Lean. Weakest-precondition rules
for the instruction forms of the byte loops and the counts of `update` and
`finalize`, exposing only what changes.
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.write (s : State) (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    Upd s (s.write sz d v) d (v.setWidth 64) :=
  ⟨by simp only [State.write, ↓reduceIte], fun r h => by simp only [State.write, h, ↓reduceIte], rfl, rfl, rfl, rfl⟩

theorem Upd.write64 (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write .x d v) d v := by
  simpa using Upd.write s .x d v

theorem Upd.trans {s₁ s₂ s₃ : State} {d : Reg} {v w : BitVec 64} (h₁ : Upd s₁ s₂ d v)
    (h₂ : Upd s₂ s₃ d w) : Upd s₁ s₃ d w :=
  ⟨h₂.gpr, fun r h => (h₂.other r h).trans (h₁.other r h), h₂.mem.trans h₁.mem,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega_using [hi], dite_true]

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) (by simp only [exec, h, ↓reduceIte, State.read, BitVec.setWidth_eq])
    (k _ (Upd.write64 _ _ _))

theorem wp_subImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) (by simp only [exec, h, ↓reduceIte, State.read, BitVec.setWidth_eq])
    (k _ (Upd.write64 _ _ _))

theorem wp_movz {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 0 :: is)) s Q :=
  WP.cons (s' := s.write .x d (imm.setWidth 64)) (by simp only [exec, Nat.mul_zero, Nat.zero_lt_succ, ↓reduceIte, BitVec.shiftLeft_zero]) (k _ (Upd.write64 _ _ _))

theorem wp_add {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n + s.gpr m)) (by simp only [exec, State.read, BitVec.setWidth_eq]) (k _ (Upd.write64 _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - s.gpr m)) (by simp only [exec, State.read, BitVec.setWidth_eq]) (k _ (Upd.write64 _ _ _))

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n &&& s.gpr m)) (by simp only [exec, State.read, BitVec.setWidth_eq])
    (k _ (Upd.write64 _ _ _))

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (((s.mem a).setWidth 32))) ?_ (k _ ?_)
  · simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega_using [ho], ite_true, ha,
      Option.bind_some, State.load, hin, Option.map_some, read_one]
  · have := Upd.write s .w t ((s.mem a).setWidth 32)
    have e : ((s.mem a).setWidth 32).setWidth 64 = (s.mem a).setWidth 64 := by
      ext i hi; simp only [Nat.reduceLT, and_true, not_false_eq_true, BitVec.setWidth_setWidth, BitVec.getElem_setWidth]
    rwa [e] at this

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega_using [ho], ite_true, ha,
    Option.bind_some, State.store, hout, Mem.writeW, State.read]
  congr 3
  ext i hi; simp only [Size.bits, Nat.reduceLeDiff, BitVec.setWidth_setWidth_of_le, BitVec.getElem_setWidth, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]; try omega

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .x d n sh :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n >>> sh)) (by simp only [exec, h, ↓reduceIte, State.read, BitVec.setWidth_eq])
    (k _ (Upd.write64 _ _ _))

end

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .x r) s = some (s.gpr r == 0) := by
  simp only [eval, State.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat]

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .x r) s = some (s.gpr r != 0) := by
  simp only [eval, State.read, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat]

end VG.Proof.Poly1305.AArch64

end

/-!
# Poly1305 on AArch64: the buffer

Untrusted: everything here is checked by Lean. Bytes stored into the buffer
(bytes 56–71 of the state), which leave the coefficients alone, and absorbing
the buffer as a block.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P leNum bytesAt Repr Buffered)

/-! ## The buffer -/

theorem off_56 (p : Addr) : off p 56 = p + 56 := rfl

theorem and15 (x : BitVec 64) :
    x &&& (15 : BitVec 16).setWidth 64 = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show ((15 : BitVec 16).setWidth 64).toNat = 2 ^ 4 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega_using [])]


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
  exact Offset.contains_base _ h (by omega_using [h])

theorem bufB_ne {st : Addr} {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    bufB st j ≠ bufB st k := by
  intro he
  have := congrArg BitVec.toNat (show BitVec.ofNat 64 (56 + j) = BitVec.ofNat 64 (56 + k) by
    simpa [bufB] using he)
  rw [toNat_ofNat_lt (by omega_using [hj]), toNat_ofNat_lt (by omega_using [hk])] at this
  omega_using [h, this]

/-- The buffer is writable when the state is. -/
theorem bufB_in {s : State} {st : Addr} (hw : sR st ∈ s.wr) {k : Nat} (hk : k < 16) :
    InRegions s.wr (bufB st k) 1 :=
  ⟨_, hw, contains_off (by omega_using [hk]) (by omega_using [hk])⟩

theorem bfR_sub_wR (st : Addr) : Region.Sub (bfR st) (wR st) :=
  Offset.sub st (by decide) (by decide)

theorem bfR_disjoint_cR (st : Addr) : (bfR st).Disjoint (cR st) :=
  Offset.disjoint st (by decide) (by decide) (by decide)

/-- The first `n` bytes of the buffer are not where the coefficients are. -/
theorem buf_disjoint_cR (st : Addr) {n : Nat} (hn : n ≤ 16) :
    (⟨off st 56, n⟩ : Region).Disjoint (cR st) :=
  (bfR_disjoint_cR st).sub_left (Region.sub_prefix hn)

theorem coef_facts : ∀ k < 5, ∀ i < 5, 72 ≤ coef k i ∧ coef k i + 4 ≤ 108 := by decide +kernel

/-- The coefficients are unchanged by writes to the buffer. -/
theorem Coefs.frame {m m' : Mem} {st : Addr} {R : Nat} (h : Coefs m st R) (hf : Frame [bfR st] m m') :
    Coefs m' st R := by
  intro k hk i hi
  obtain ⟨c₁, c₂⟩ := coef_facts k hk i hi
  rw [← h k hk i hi]
  refine congrArg BitVec.toNat (hf.readW (r := ⟨off st (coef k i), 4⟩) (Region.contains_self _ _) ?_
    (by decide))
  simp only [List.mem_singleton, forall_eq]
  exact Offset.disjoint st (by omega_using [c₁, c₂]) (by omega_using [c₁, c₂]) (by decide)

/-- The coefficient words may be read when the state may be. -/
theorem coefIn_of {s : State} (hw : sR (s.gpr .x0) ∈ s.wr) : CoefIn s := fun off h₁ h₂ =>
  ⟨_, List.mem_append_right _ hw, contains_off (by omega_using [h₁, h₂]) (by omega_using [h₁, h₂])⟩

/-- Absorbing the buffer: its 16 bytes, and `pad · 2¹²⁸`. -/
theorem absorbBuf_ok (s : State) (pad : Bool) {R : Nat} (hR : R < 2 ^ 128) (hm : s.gpr .x17 = M26)
    (hco : Coefs s.mem (s.gpr .x0) R) (hw : sR (s.gpr .x0) ∈ s.wr) :
    WP isa (.block (([.addImm .x .x1 .x0 56] : List Instr) ++ absorb pad)) s fun s' =>
      (Bounds s → hv s' % P = ((hv s + (leNum (bytesAt s.mem (off (s.gpr .x0) 56) 16) +
        2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps (.x1 :: absorbRegs) s s' := by
  refine WP.block_append (wp_addImm (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have x0₁ : s₁.gpr .x0 = s.gpr .x0 := u₁.other _ (by decide)
  have hin : ∀ d, d + 8 ≤ 16 → InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x1 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [u₁.rd, u₁.wr, u₁.gpr, ← off, off_off]
    exact ⟨_, List.mem_append_right _ hw, contains_off (by omega_using [hd]) (by omega_using [hd])⟩
  refine WP.mono (absorb_ok s₁ pad hR (by rw [u₁.other _ (by decide)]; exact hm)
    (by rw [u₁.mem, x0₁]; exact hco) (coefIn_of (by rw [u₁.wr, x0₁]; exact hw)) (hin 0 (by decide))
    (hin (0 + 8) (by decide))) fun s' ⟨ha, k⟩ => ⟨fun hb => ?_, ?_⟩
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
    rw [bufB_eq, List.length_take]; exact bfR_contains _ (by omega_using [hj0, hj, hxs])
  -- The byte read.
  have hbyte : s.mem (src + BitVec.ofNat 64 j) = m₀ (src + BitVec.ofNat 64 j) := by
    rw [h.mem, ← hm₀]
    exact writeBytes_frame _ _ _ hq _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hnb
  refine wp_ldrb (t := .x12) (a := src + BitVec.ofNat 64 j) (by decide)
    (by rw [h.x1, add_ofNat_zero]) (by rw [h.rd, h.wr]; exact hin) fun s₁ u₁ => ?_
  refine wp_strb (t := .x12) (a := bufB (sI.gpr .x0) (j0 + j)) (by decide)
    (by rw [u₁.other _ (by decide), h.x11, bufB_of]) (by rw [u₁.wr, h.wr]; exact bufB_in hw (by omega_using [hj0, hj, hxs]))
    fun s₂ m₂ => ?_
  refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ =>
    wp_subImm (by decide) fun s₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x1 → r ≠ .x12 → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, m₂.gpr, u₁.other r h4]
  have hx10 : s₅.gpr .x10 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [u₅.gpr, u₄.other .x10 (by decide), u₃.other .x10 (by decide), m₂.gpr, u₁.other .x10 (by decide),
      h.x10, show BitVec.ofNat 64 1 = 1 from rfl, ofNat_pred (by omega_using [hj, hxs]), Nat.sub_sub]
  refine ⟨⟨by omega_using [hj, hxs], ?_, ?_, hx10, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩, hx10⟩
  · rw [u₅.other .x1 (by decide), u₄.other .x1 (by decide), u₃.gpr, m₂.gpr, u₁.other .x1 (by decide), h.x1,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₅.other .x11 (by decide), u₄.gpr, u₃.other .x11 (by decide), m₂.gpr, u₁.other .x11 (by decide),
      h.x11, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g r h2 h3 h1 h4, h.keep r h1 h2 h3 h4]
  · rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, h.wr]
  · have hj' : j < (bytesAt m₀ src n).length := by omega_using [hj, hxs]
    have hl : ((bytesAt m₀ src n).take j).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    have ea : bufB (sI.gpr .x0) (j0 + j) =
        bufB (sI.gpr .x0) j0 + BitVec.ofNat 64 ((bytesAt m₀ src n).take j).length := by
      rw [hl, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
    have hv : (s₁.gpr .x12).setWidth 8 = (bytesAt m₀ src n)[j] := by
      rw [u₁.gpr, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, hbyte]; simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, hv, u₁.mem, ea, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some, writeBytes_snoc _ _ _ _ (by omega_using [hj0, hj, hxs, hl])]

theorem copy_ok {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) (hn : 0 < n)
    (hw : sR (sI.gpr .x0) ∈ sI.wr) (hs : SrcOk sI m₀ src n) (hx1 : sI.gpr .x1 = src)
    (hx11 : sI.gpr .x11 = sI.gpr .x0 + BitVec.ofNat 64 j0) (hx10 : sI.gpr .x10 = BitVec.ofNat 64 n) :
    WP isa copyIn sI (CopyInv sI m₀ src j0 n n) := by
  have h₀ : CopyInv sI m₀ src j0 n 0 sI :=
    ⟨by omega_using [hn], by rw [hx1, add_ofNat_zero], by rw [hx11, Nat.add_zero], by rw [hx10, Nat.sub_zero],
      fun _ _ _ _ _ => rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  rw [copyIn_eq]
  refine WP.loop (M := isa) (fun k s => ∃ j, k = n - j ∧ j < n ∧ CopyInv sI m₀ src j0 n j s)
    ?_ n sI ⟨0, rfl, hn, h₀⟩
  rintro k s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hj0 hw hs hj hc) fun s' ⟨hc', hx⟩ => ?_
  have hev : isa.eval (.nonzero .x .x10) s' = some (!(BitVec.ofNat 64 (n - (j + 1)) == 0)) := by
    rw [eval_nonzero, hx]; rfl
  rw [ofNat_beq_zero (by omega_using [hj0, hn, hj])] at hev
  by_cases hl : n - (j + 1) = 0
  · refine .inl ⟨by rw [hev]; simp only [hl, decide_true, Bool.not_true], ?_⟩
    rwa [show j + 1 = n by omega_using [hj, hl]] at hc'
  · exact .inr ⟨by rw [hev]; simp only [hl, decide_false, Bool.not_false], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], hc'⟩

/-- After copying: the buffer's first `j0` bytes and the `n` bytes copied. -/
theorem CopyInv.buf {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) {s : State}
    (h : CopyInv sI m₀ src j0 n n s) :
    bytesAt s.mem (off (sI.gpr .x0) 56) (j0 + n) =
      bytesAt sI.mem (off (sI.gpr .x0) 56) j0 ++ bytesAt m₀ src n := by
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  have e := bytesAt_writeBytes sI.mem (off (sI.gpr .x0) 56) j0 (bytesAt m₀ src n) (by omega_using [hj0, hxs])
  rw [hxs] at e
  rw [h.mem, List.take_of_length_le (by omega_using [hxs]), bufB_eq]
  exact e

theorem CopyInv.frame {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) {s : State}
    (h : CopyInv sI m₀ src j0 n n s) : Frame [bfR (sI.gpr .x0)] sI.mem s.mem := by
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine writeBytes_frame _ _ _ ?_
  rw [bufB_eq, hxs]; exact bfR_contains _ hj0

/-- The proof contracts of `update` and `finalize` only need the length
of the message modulo 16. -/
theorem count_mod {count : BitVec 64} {n : Nat} (h : count = BitVec.ofNat 64 n) :
    count.toNat % 16 = n % 16 := by
  rw [h, BitVec.toNat_ofNat]; omega_using []

end VG.Proof.Poly1305.AArch64
