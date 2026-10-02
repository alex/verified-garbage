import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintBase
import VerifiedGarbage.Impl.MlDsa.X86.Pack.Hint

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_unpack`, the setup

The code follows the fold form of `HintBitUnpack` (`hintBitUnpack_eq`,
`Pack/Hint.lean`) step by step: after `i` polynomials the spec's state is `PS
s₀ i`, `eax` is its index, or 256 once a check has failed (`idxOf`), and while
no check has failed the words of `h` are its hint (`SR`).

Every register the code branches on or addresses memory with is a function
of the entry state `s₀` through the input `y`, which two runs with the same
public data and leak agree on (`Pub`).

This file: the contract's facts (`Pre`, `Pub`), what holds throughout the
body (`Base`: `h` and the argument slots of `len` and `hlen`, which the
code uses for the count of polynomials left and the address of the next
bound, are all it changes), zeroing `h`, and the setup of the loops.
-/

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Impl.MlKem.X86 (at_ saveRegs)
open VG.Proof.MlKem.X86
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (bytesAt_getD)
open VG.Proof.MlDsa.Pack

namespace Up

section
variable (s₀ : State)
/-- `len`, `hlen`, `k`. -/
abbrev yL : Nat := (arg s₀ 1).toNat
abbrev hL : Nat := (arg s₀ 4).toNat
abbrev K : Nat := yL s₀ - ω s₀
/-- `h`, and the argument slot `i`. -/
abbrev hR : Region := ⟨wA s₀, hL s₀ * 4⟩
abbrev slot (i : Nat) : Region := ⟨argAddr s₀ i, 4⟩
/-- What the body changes. -/
abbrev W : List Region := [hR s₀, slot s₀ 1, slot s₀ 4]
/-- The input. -/
abbrev Y : Array Byte := (bytesAt s₀.mem (rA s₀) (yL s₀)).toArray
abbrev yb (t : Nat) : Nat := ((Y s₀).getD t 0).toNat
/-- The spec's state after `i` polynomials. -/
abbrev PS (i : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huPoly (ω s₀) (Y s₀)) (List.range i) (Array.replicate (K s₀) noHint, 0)
/-- The bound of polynomial `i`. -/
abbrev bnd (i : Nat) : Nat := yb s₀ (ω s₀ + i)
end

/-- The index of a state of the spec, or 256 for a failed check. -/
def idxOf : Option (Array (Vector Bool n) × Nat) → Nat
  | none => 256
  | some st => st.2

/-- Unless a check failed, the words of `h` are the hint, and the index is at
most `ω`. -/
def SR (s₀ : State) (o : Option (Array (Vector Bool n) × Nat)) (m : Mem) : Prop :=
  ∀ st, o = some st → st.2 ≤ ω s₀ ∧ HArr m (wA s₀) (K s₀) st.1

theorem SR.none (s₀ : State) (m : Mem) : SR s₀ none m := fun _ h => nomatch h

theorem SR.congr {s₀ : State} {o : Option (Array (Vector Bool n) × Nat)} {m m' : Mem} (h : SR s₀ o m)
    (hm : ∀ t < 256 * K s₀, coeffAt m' (wA s₀) t = coeffAt m (wA s₀) t) : SR s₀ o m' :=
  fun st e => ⟨(h st e).1, harr_congr (h st e).2 hm⟩

structure Pre (s₀ : State) : Prop extends Lay s₀ (yL s₀) (hL s₀ * 4) where
  par : (ω s₀, K s₀) ∈ hintParams
  le : ω s₀ ≤ yL s₀
  hlen : hL s₀ = 256 * K s₀

theorem Pre.of {s₀ : State} (h : (hintBitUnpackContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18⟩

theorem Pre.facts {s₀ : State} (hp : Pre s₀) :
    4 ≤ K s₀ ∧ K s₀ ≤ 8 ∧ ω s₀ ≤ 80 ∧ ω s₀ + K s₀ = yL s₀ ∧ hL s₀ = 256 * K s₀ := by
  have := mem_hintParams hp.par
  have := hp.le
  have := hp.hlen
  have e : K s₀ = yL s₀ - ω s₀ := rfl
  omega

/-- The public data: `esp`, the arguments and the input. -/
structure Pub (s₀ s₀' : State) : Prop where
  e0 : E0 s₀ = E0 s₀'
  a0 : arg s₀ 0 = arg s₀' 0
  a1 : arg s₀ 1 = arg s₀' 1
  a2 : arg s₀ 2 = arg s₀' 2
  a3 : arg s₀ 3 = arg s₀' 3
  a4 : arg s₀ 4 = arg s₀' 4
  y : Y s₀ = Y s₀'

theorem Pub.of {s₀ s₀' : State} (h : (hintBitUnpackContract X86.abi 16).pub s₀ s₀') : Pub s₀ s₀' := by
  sig_pub [hintBitUnpackContract, hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e, hl, a0, a1, a2, a3, a4⟩ := h
  exact ⟨e, a0, a1, a2, a3, a4, congrArg List.toArray (map_toNat_inj hl)⟩

theorem Pub.eK {s₀ s₀' : State} (h : Pub s₀ s₀') : K s₀ = K s₀' := by
  show (arg s₀ 1).toNat - (arg s₀ 2).toNat = (arg s₀' 1).toNat - (arg s₀' 2).toNat; rw [h.a1, h.a2]
theorem Pub.eω {s₀ s₀' : State} (h : Pub s₀ s₀') : ω s₀ = ω s₀' := by
  show (arg s₀ 2).toNat = (arg s₀' 2).toNat; rw [h.a2]
theorem Pub.eyb {s₀ s₀' : State} (h : Pub s₀ s₀') (t : Nat) : yb s₀ t = yb s₀' t := by
  show ((Y s₀).getD t 0).toNat = ((Y s₀').getD t 0).toNat; rw [h.y]
theorem Pub.ePS {s₀ s₀' : State} (h : Pub s₀ s₀') (i : Nat) : PS s₀ i = PS s₀' i := by
  show optFold (huPoly (ω s₀) (Y s₀)) (List.range i) (Array.replicate (K s₀) noHint, 0) =
    optFold (huPoly (ω s₀') (Y s₀')) (List.range i) (Array.replicate (K s₀') noHint, 0)
  rw [h.y, h.eω, h.eK]
theorem Pub.ebnd {s₀ s₀' : State} (h : Pub s₀ s₀') (i : Nat) : bnd s₀ i = bnd s₀' i := by
  show yb s₀ (ω s₀ + i) = yb s₀' (ω s₀' + i); rw [h.eω, h.eyb]

/-! ## Regions -/

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem argAddr_eq {i : Nat} (hi : i < 5) : argAddr s₀ i = (E0 s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
  ea_off (by have := hp.sp'; unfold E0 at this; omega)

theorem slot_disj {i j : Nat} (hi : i < 5) (hj : j < 5) (hij : i ≠ j) : (slot s₀ i).Disjoint (slot s₀ j) := by
  rw [slot, slot, hp.argAddr_eq hi, hp.argAddr_eq hj]
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem slot_sub {i : Nat} (hi : i < 5) : Region.Sub (slot s₀ i) (gR s₀) :=
  sub_of_contains (arg_contains (n := 5) hi hp.sp')

theorem h_slot {i : Nat} (hi : i < 5) : (hR s₀).Disjoint (slot s₀ i) := hp.w_g.sub_right (hp.slot_sub hi)

/-- The slots of `y`, `ω` and `h` are apart from `W`. -/
theorem slotW {i : Nat} (hi : i < 5) (h1 : i ≠ 1) (h4 : i ≠ 4) : ∀ r ∈ W s₀, (slot s₀ i).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.h_slot hi).symm
  · exact hp.slot_disj hi (by omega) h1
  · exact hp.slot_disj hi (by omega) h4

theorem yW : ∀ r ∈ W s₀, (⟨rA s₀, yL s₀⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.r_w
  · exact hp.r_g.sub_right (hp.slot_sub (by omega))
  · exact hp.r_g.sub_right (hp.slot_sub (by omega))

theorem hW : ∀ r ∈ W s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have st := hp.stk_eq
  rcases hr with rfl | rfl | rfl
  · exact ⟨st ▸ hp.stk_w, hp.ret_w⟩
  · exact ⟨(st ▸ hp.stk_g).sub_right (hp.slot_sub (by omega)), hp.ret_g.sub_right (hp.slot_sub (by omega))⟩
  · exact ⟨(st ▸ hp.stk_g).sub_right (hp.slot_sub (by omega)), hp.ret_g.sub_right (hp.slot_sub (by omega))⟩

/-- A word of `h` is apart from the slots. -/
theorem coeff_slot {t j : Nat} (ht : t < 256 * K s₀) (hj : j < 5) :
    Mem.Sep (coeffAddr (wA s₀) t) 4 (argAddr s₀ j) (32 / 8) := by
  have := hp.facts
  have hc : (hR s₀).Contains (coeffAddr (wA s₀) t) 4 := Offset.contains_base _ (by omega) (by omega)
  exact (hp.h_slot hj).sep hc (Region.contains_self _ _)

theorem slot_coeff {t j : Nat} (ht : t < 256 * K s₀) (hj : j < 5) :
    Mem.Sep (argAddr s₀ j) 4 (coeffAddr (wA s₀) t) (32 / 8) := by
  have := hp.facts
  have hc : (hR s₀).Contains (coeffAddr (wA s₀) t) 4 := Offset.contains_base _ (by omega) (by omega)
  exact (hp.h_slot hj).symm.sep (Region.contains_self _ _) hc

theorem coeff_frame {m : Mem} {j : Nat} (hj : j < 5) (v : BitVec 32) :
    ∀ t < 256 * K s₀, coeffAt (m.writeW (argAddr s₀ j) v) (wA s₀) t = coeffAt m (wA s₀) t :=
  fun t ht => Mem.readW_writeW_sep (hp.coeff_slot ht hj) (by decide)

end Pre

/-! ## What holds throughout the body -/

structure Base (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame (W s₀) (P0 s₀).mem s.mem

theorem Base.keep {s₀ s s' : State} (h : Base s₀ s) {rs : List Reg} (k : Keep rs s s') (hsp : Reg.esp ∉ rs)
    (hm : Frame (W s₀) s.mem s'.mem) : Base s₀ s' :=
  ⟨(k.gpr hsp).trans h.esp, k.2.1.trans h.rd, k.2.2.trans h.wr, h.frame.trans hm⟩

namespace Base
variable {s₀ s : State} (hp : Pre s₀) (h : Base s₀ s)
include hp h

theorem argw {i : Nat} (hi : i < 5) (h1 : i ≠ 1) (h4 : i ≠ 4) : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  rw [h.frame.readW (Region.contains_self _ _) (hp.slotW hi h1 h4) (by decide)]
  exact hp.P0_argw hi

theorem argIn {i : Nat} (hi : i < 5) : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := hp.argIn h.rd h.wr hi

theorem argOut {i : Nat} (hi : i < 5) : InRegions s.wr (argAddr s₀ i) 4 := hp.argOut h.wr hi

/-- A byte of `y`. -/
theorem ybyte {t : Nat} (ht : t < yL s₀) : s.mem (rA s₀ + BitVec.ofNat 64 t) = (Y s₀).getD t 0 := by
  rw [hp.r_keep h.frame hp.yW ht, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    ← List.getD_eq_getElem?_getD, bytesAt_getD _ _ ht]

theorem inY {t : Nat} (ht : t < yL s₀) : InRegions (s.rd ++ s.wr) (rA s₀ + BitVec.ofNat 64 t) 1 := by
  have := hp.r_fit
  rw [h.rd, h.wr, pushed_rd, hp.rd]
  exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩

theorem inH {t : Nat} (ht : t < 256 * K s₀) : InRegions s.wr (coeffAddr (wA s₀) t) 4 := by
  have := hp.facts
  have := hp.w_fit
  rw [h.wr, P0_wr, hp.wr]
  exact ⟨hR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩

end Base

theorem frame_slot {s₀ : State} {m : Mem} {j : Nat} (hj : j = 1 ∨ j = 4) (v : BitVec 32) :
    Frame (W s₀) m (m.writeW (argAddr s₀ j) v) := by
  rcases hj with rfl | rfl
  · exact (Frame.refl _ _).writeW (r := slot s₀ 1) (by simp) _ (Region.contains_self _ _)
  · exact (Frame.refl _ _).writeW (r := slot s₀ 4) (by simp) _ (Region.contains_self _ _)

theorem frame_coeff {s₀ : State} (hp : Pre s₀) {m : Mem} {t : Nat} (ht : t < 256 * K s₀) (v : BitVec 32) :
    Frame (W s₀) m (m.writeW (coeffAddr (wA s₀) t) v) := by
  have := hp.facts
  exact (Frame.refl _ _).writeW (r := hR s₀) (by simp) _ (Offset.contains_base _ (by omega) (by omega))

/-- A word of `h`. -/
theorem hAddr {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < 256 * K s₀) :
    addr (arg s₀ 3 + BitVec.ofNat 32 (4 * t)) 0 = coeffAddr (wA s₀) t := by
  have := hp.facts; have := hp.w_fit; rw [addr_add (by omega), Nat.add_zero]

/-- A byte of `y`. -/
theorem yAddr {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < yL s₀) :
    addr (arg s₀ 0 + BitVec.ofNat 32 t) 0 = rA s₀ + BitVec.ofNat 64 t := by
  have := hp.r_fit; rw [addr_add (by omega), Nat.add_zero]

theorem yb_lt (s₀ : State) (t : Nat) : yb s₀ t < 256 := ((Y s₀).getD t 0).isLt

/-! ## Zeroing `h` -/

/-- After `t` words. -/
structure ZI (s₀ : State) (t : Nat) (s : State) : Prop extends Base s₀ s where
  ecx : s.gpr .ecx = arg s₀ 3 + BitVec.ofNat 32 (4 * t)
  edx : s.gpr .edx = BitVec.ofNat 32 (hL s₀ - t)
  eax : s.gpr .eax = 0
  zero : ∀ u < t, coeffAt s.mem (wA s₀) u = 0
  len : s.mem.readW (argAddr s₀ 1) 32 = arg s₀ 1

theorem zinit_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) (ZI · 0) (.block hbuZeroInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) (by taint_decide)
  · subst e
    have b₀ : Base s₀ (P0 s₀) := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
    have a3 : addr ((P0 s₀).gpr .esp) 32 = argAddr s₀ 3 := argEa rfl 3
    have a4 : addr ((P0 s₀).gpr .esp) 36 = argAddr s₀ 4 := argEa rfl 4
    have i3 := b₀.argIn hp (i := 3) (by omega)
    have i4 := b₀.argIn hp (i := 4) (by omega)
    have v3 := hp.P0_argw (i := 3) (by omega)
    have v4 := hp.P0_argw (i := 4) (by omega)
    have hb : WP isa (.block hbuZeroInit) (P0 s₀) fun s' => s'.gpr .ecx = arg s₀ 3 ∧ s'.gpr .edx = arg s₀ 4 ∧
        s'.gpr .eax = 0 ∧ s'.mem = (P0 s₀).mem := by
      hrun [hbuZeroInit, a3, a4, i3, i4, v3, v4]
    refine (WP.keep [.ecx, .edx, .eax] hb (by decide)).mono fun s' ⟨⟨e1, e2, e3, m⟩, k⟩ =>
      ⟨b₀.keep k (by decide) (by rw [m]; exact Frame.refl _ _), by rw [e1]; simp, by rw [e2]; simp, e3,
        fun u hu => absurd hu (Nat.not_lt_zero _), by rw [m]; exact hp.P0_argw (by omega)⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.e0]

theorem zstep {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < hL s₀) {s : State} (h : ZI s₀ t s) :
    WP isa (.block hbuZeroBody) s fun s' => ZI s₀ (t + 1) s' ∧ isa.eval .ne s' = some (decide (t + 1 < hL s₀)) := by
  have hf := hp.facts
  have ht' : t < 256 * K s₀ := by omega
  have ea : addr (s.gpr .ecx) 0 = coeffAddr (wA s₀) t := by rw [h.ecx]; exact hAddr hp ht'
  have hin := h.inH hp ht'
  have hb : WP isa (.block hbuZeroBody) s fun s' => s'.gpr .ecx = s.gpr .ecx + 4 ∧ s'.gpr .edx = s.gpr .edx - 1 ∧
      s'.zf = some (s.gpr .edx - 1 == 0) ∧ s'.mem = s.mem.writeW (coeffAddr (wA s₀) t) (s.gpr .eax) := by
    hrun [hbuZeroBody, ea, hin]
  refine (WP.keep [.ecx, .edx] hb (by decide)).mono fun s' ⟨⟨e1, e2, z, m⟩, k⟩ => ?_
  refine ⟨⟨h.keep k (by decide) (by rw [m]; exact frame_coeff hp ht' _), by rw [e1, h.ecx, add_four']; congr 2,
    by rw [e2, h.edx]; exact cnt_next ht, by rw [k.gpr (by decide), h.eax], fun u hu => ?_,
    by rw [m, Mem.readW_writeW_sep (hp.slot_coeff ht' (j := 1) (by omega)) (by decide), h.len]⟩,
    eval_ne_cnt ht (by omega) (by rw [z, h.edx])⟩
  rw [m, h.eax]
  by_cases e : u = t
  · subst e; rw [coeffAt_eq, Mem.readW_writeW_self32]
  · rw [coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      ← coeffAt_eq, h.zero u (by omega)]

theorem zloop_piece : Piece Pre Pub (ZI · 0) (fun s₀ s => ZI s₀ (hL s₀) s) (.loop (.block hbuZeroBody) .ne) :=
  countLoopN (fun t s₀ s => ZI s₀ t s) hL (fun s₀ hp => by have := hp.facts; omega)
    (fun _ _ _ _ hq => by simp only [hL, hq.a4]) [.ecx] (fun t s₀ s hp h ht => zstep hp ht h)
    (fun t s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.ecx, h'.ecx, hq.a3]) (by taint_decide)

/-! ## The state of the loops -/

/-- The registers and slots of polynomial `i`. -/
structure Ptr (s₀ : State) (i : Nat) (s : State) : Prop extends Base s₀ s where
  edi : s.gpr .edi = arg s₀ 0
  esi : s.gpr .esi = 1
  ecx : s.gpr .ecx = arg s₀ 3 + BitVec.ofNat 32 (1024 * i)
  cnt : s.mem.readW (argAddr s₀ 1) 32 = BitVec.ofNat 32 (K s₀ - i)
  ptr : s.mem.readW (argAddr s₀ 4) 32 = arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i)

/-- `Ptr`, after a block that writes only the registers `rs` (not those of
`Ptr`) and not memory. -/
theorem Ptr.keep {s₀ s s' : State} {i : Nat} (h : Ptr s₀ i s) {rs : List Reg} (k : Keep rs s s')
    (hrs : ∀ r ∈ rs, r = .eax ∨ r = .ebx ∨ r = .edx ∨ r = .ebp) (hm : s'.mem = s.mem) : Ptr s₀ i s' := by
  have g : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → r ≠ .ebp → s'.gpr r = s.gpr r := fun r a b c d =>
    k.gpr fun hr => by rcases hrs r hr with e | e | e | e <;> contradiction
  exact ⟨h.toBase.keep k (fun hr => by rcases hrs _ hr with e | e | e | e <;> cases e)
      (by rw [hm]; exact Frame.refl _ _),
    by rw [g _ (by decide) (by decide) (by decide) (by decide), h.edi],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), h.esi],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), h.ecx], by rw [hm, h.cnt], by rw [hm, h.ptr]⟩

/-- Before polynomial `i` (or after it, with the spec's state `o`). -/
structure OM (s₀ : State) (i : Nat) (o : Option (Array (Vector Bool n) × Nat)) (s : State) : Prop
    extends Ptr s₀ i s where
  eax : s.gpr .eax = BitVec.ofNat 32 (idxOf o)
  sr : SR s₀ o s.mem

theorem setup_piece : Piece Pre Pub (fun s₀ s => ZI s₀ (hL s₀) s) (fun s₀ s => OM s₀ 0 (PS s₀ 0) s)
    (.block hbuSetup) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have a0 : addr (s.gpr .esp) 20 = argAddr s₀ 0 := argEa h.esp 0
    have a1 : addr (s.gpr .esp) 24 = argAddr s₀ 1 := argEa h.esp 1
    have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa h.esp 2
    have a3 : addr (s.gpr .esp) 32 = argAddr s₀ 3 := argEa h.esp 3
    have a4 : addr (s.gpr .esp) 36 = argAddr s₀ 4 := argEa h.esp 4
    have i0 := h.argIn hp (i := 0) (by omega)
    have i1 := h.argIn hp (i := 1) (by omega)
    have i2 := h.argIn hp (i := 2) (by omega)
    have i3 := h.argIn hp (i := 3) (by omega)
    have o1 := h.argOut hp (i := 1) (by omega)
    have o4 := h.argOut hp (i := 4) (by omega)
    have v0 := h.argw hp (i := 0) (by omega) (by omega) (by omega)
    have v2 := h.argw hp (i := 2) (by omega) (by omega) (by omega)
    have v3 := h.argw hp (i := 3) (by omega) (by omega) (by omega)
    have v1 := h.len
    have hb : WP isa (.block hbuSetup) s fun s' => s'.gpr .ecx = arg s₀ 3 ∧ s'.gpr .edi = arg s₀ 0 ∧
        s'.gpr .esi = 1 ∧
        s'.mem = (s.mem.writeW (argAddr s₀ 1) (arg s₀ 1 - arg s₀ 2)).writeW (argAddr s₀ 4) (arg s₀ 0 + arg s₀ 2) := by
      hrun [hbuSetup, a0, a1, a2, a3, a4, i0, i1, i2, i3, o1, o4, v0, v1, v2, v3]
    have hf := hp.facts
    have l1 := (arg s₀ 1).isLt
    have l2 := (arg s₀ 2).isLt
    have s14 : Mem.Sep (argAddr s₀ 1) (32 / 8) (argAddr s₀ 4) (32 / 8) :=
      (hp.slot_disj (i := 1) (j := 4) (by omega) (by omega) (by omega)).sep (Region.contains_self _ _)
        (Region.contains_self _ _)
    refine (WP.keep [.ecx, .edi, .edx, .esi] hb (by decide)).mono fun s' ⟨⟨e1, e2, e3, m⟩, k⟩ =>
      ⟨⟨h.keep k (by decide) (by rw [m]; exact (frame_slot (.inl rfl) _).trans (frame_slot (.inr rfl) _)),
        e2, e3, by rw [e1]; simp, ?_, ?_⟩, by rw [k.gpr (by decide), h.eax]; rfl, ?_⟩
    · rw [m, Mem.readW_writeW_sep s14 (by decide), Mem.readW_writeW_self32]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
      simp only [K, yL, ω] at hf ⊢
      omega
    · rw [m, Mem.readW_writeW_self32]; simp
    · rintro st e
      simp only [PS, List.range_zero, optFold, Option.some.injEq] at e
      subst e
      refine ⟨Nat.zero_le _, harr_zero fun t ht => ?_⟩
      rw [m, hp.coeff_frame (by omega) _ t ht, hp.coeff_frame (by omega) _ t ht]
      exact h.zero t (by omega)
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

end Up

end VG.Proof.MlDsa.X86.Pack.Hint
