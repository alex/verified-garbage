import VerifiedGarbage.Proof.Blake2.Arm.CompressS.Block
import VerifiedGarbage.Proof.Blake2.Arm.Contract
import VerifiedGarbage.Proof.Blake2.Arm.LitS
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2.Contract

/-!
# BLAKE2s compression function on ARMv7: the whole function

The prologue, which keeps the arguments, the counter, the flag word and our
caller's registers in `scratch` (`setup_ok`); one block (`body_ok`: `init_ok`,
`rounds_ok`, `fin_ok` and `advance_ok`), whose loop invariant is all in
`scratch`; and the epilogue (`restore_ok`). The loop is proven against
`Proof.Blake2.compressArm Spec.Blake2.s` (`compress_verified'`), which the
streaming functions use for their calls; `compress_verified` moves it to the
shared contract of `Spec/Blake2/Contract.lean`. Constant time is the taint
analysis on the literal code (`LitS.lean`).
-/

namespace VG.Proof.Blake2.ArmS

open VG VG.Arm
open VG.Impl.Sha512.Arm (lo hi)
open VG.Impl.Blake2.Arm.S (wreg cOff xOff stOff blkOff nOff tOff fOff saved advance body save restore setup)
open VG.Proof.Sha512.Arm (A A_eq lo_add hi_add lo_toNat hi_toNat)
open VG.Proof.MdStream.Arm (eval_ne contains_offset sub_offset)
open VG.Spec.Blake2 (Work Block HashValue Params)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev stp : BitVec 32 := s₀.gpr .r0
abbrev bp : BitVec 32 := s₀.gpr .r1
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev scp : BitVec 32 := stackArg s₀ 3
abbrev t₀ : Nat := (tArm s₀).toNat
abbrev fl : Bool := stackArg s₀ 2 != 0
abbrev blR : Region := ⟨State.addr (bp s₀), 64 * nb s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 16⟩
abbrev stR : Region := ⟨State.addr (stp s₀), 32⟩
abbrev scrR : Region := ⟨State.addr (scp s₀), 512⟩
abbrev H₀ : HashValue 32 := Spec.Blake2.stateAt 32 s₀.mem (State.addr (stp s₀))

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (64 * i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀, argR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_scr : (argR s₀).Disjoint (scrR s₀)
  st_fits : (stp s₀).toNat + 32 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 64 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scp s₀).toNat + 512 ≤ 2 ^ 32
  sp_fits : s₀.sp.toNat + 16 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : (compressArm Spec.Blake2.s).pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem blk_toNat {i : Nat} (hi : i < nb s₀) : (blkAddr s₀ i).toNat = (bp s₀).toNat + 64 * i := by
  have := h.blk_fits
  simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 64 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blk_fit {i : Nat} (hi : i < nb s₀) : (blkAddr s₀ i).toNat + 64 ≤ 2 ^ 32 := by
  have := h.blk_fits; rw [h.blk_toNat hi]; omega

theorem blk_addr {i : Nat} (hi : i < nb s₀) :
    State.addr (blkAddr s₀ i) = State.addr (bp s₀) + BitVec.ofNat 64 (64 * i) :=
  addr_add (by have := h.blk_fits; omega)

theorem blk_sub {i : Nat} (hi : i < nb s₀) : Region.Sub ⟨State.addr (blkAddr s₀ i), 64⟩ (blR s₀) := by
  have := h.blk_fits
  rw [h.blk_addr hi]; exact sub_offset (by omega) (by omega)

theorem blk_rd {i : Nat} (hi : i < nb s₀) :
    ∀ o, o + 4 ≤ 64 → InRegions (s₀.rd ++ s₀.wr) (A (blkAddr s₀ i) o) 4 := fun o ho => by
  have := h.blk_fit hi
  have := h.blk_fits
  refine ⟨blR s₀, by simp [h.rd], ?_⟩
  rw [A_eq (by omega), h.blk_addr hi, Offset.add_ofNat_add_ofNat]
  exact contains_offset (by omega) (by omega)

/-- The address of a word of `scratch`. -/
theorem scr_addr {d : Nat} (hd : d < 512) :
    A (scp s₀) d = State.addr (scp s₀) + BitVec.ofNat 64 d := A_eq (by have := h.scr_fits; omega)

theorem out_scr {d : Nat} (hd : d + 4 ≤ 512) : InRegions s₀.wr (A (scp s₀) d) 4 := by
  rw [h.scr_addr (by omega)]
  exact ⟨scrR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem in_scr {d : Nat} (hd : d + 4 ≤ 512) : InRegions (s₀.rd ++ s₀.wr) (A (scp s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := h.out_scr hd; ⟨r, List.mem_append_right _ hr, hc⟩

theorem out_st {d : Nat} (hd : d + 4 ≤ 32) : InRegions s₀.wr (A (stp s₀) d) 4 := by
  rw [A_eq (by have := h.st_fits; omega)]
  exact ⟨stR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem in_st {d : Nat} (hd : d + 4 ≤ 32) : InRegions (s₀.rd ++ s₀.wr) (A (stp s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := h.out_st hd; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A word of `scratch` outside the regions a frame allows to change. -/
theorem scr_frame {d : Nat} (hd' : d + 4 ≤ 512) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨State.addr (scp s₀) + BitVec.ofNat 64 d, 4⟩ r) :
    m'.readW (A (scp s₀) d) 32 = m.readW (A (scp s₀) d) 32 := by
  rw [h.scr_addr (by omega)]
  exact hf.readW (Region.contains_self _ _) hd (by decide)

/-- A state word outside the scratch space. -/
theorem st_frame {m m' : Mem} (hf : Frame [scrR s₀] m m') {k : Nat} (hk : k < 8) :
    m'.readW (A (stp s₀) (4 * k)) 32 = m.readW (A (stp s₀) (4 * k)) 32 := by
  rw [A_eq (by have := h.st_fits; omega)]
  exact hf.readW (r := stR s₀) (Offset.contains_base _ (by omega) (by omega))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.st_scr) (by decide)

/-- A block word outside the state and the scratch space. -/
theorem blk_frame {m m' : Mem} (hf : Frame [stR s₀, scrR s₀] m m') {i : Nat} (hi : i < nb s₀) {o : Nat}
    (ho : o + 4 ≤ 64) : m'.readW (A (blkAddr s₀ i) o) 32 = m.readW (A (blkAddr s₀ i) o) 32 := by
  have := h.blk_fit hi
  rw [A_eq (by omega)]
  exact hf.readW (r := ⟨State.addr (blkAddr s₀ i), 64⟩) (Offset.contains_base _ (by omega) (by omega))
    (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.blk_st.sub_left (h.blk_sub hi)
    · exact h.blk_scr.sub_left (h.blk_sub hi)) (by decide)

end Pre

/-! ## The prologue -/

/-- The flag word of `last`. -/
def flag32 (l : BitVec 32) : BitVec 32 := 0 - ((0 - l ||| l) >>> 31)

/-- The flag word: all ones for the final block. -/
def flagW (f : Bool) : BitVec 32 := if f then BitVec.allOnes 32 else 0

theorem flag_eq (l : BitVec 32) : flag32 l = flagW (l != 0) := by
  by_cases h : l = 0
  · subst h; decide
  · have hm : (0 - l ||| l).msb = true := by
      rw [BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide, BitVec.toNat_sub]
      have := l.isLt
      have h0 : l.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
      simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, Bool.or_eq_true,
        decide_eq_true_eq]
      omega
    have e1 : (0 - l ||| l) >>> 31 = 1 := by
      rw [BitVec.msb_eq_decide] at hm
      simp only [decide_eq_true_eq] at hm
      apply BitVec.eq_of_toNat_eq
      have := (0 - l ||| l).isLt
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
      omega
    have ht : (l != 0) = true := by simpa using h
    simp only [flag32, e1, flagW, ht, ite_true]
    decide

/-- The words the prologue stores in `scratch`, in order. -/
def setupWrites (s₀ : State) : List (Nat × BitVec 32) :=
  [(92, stackArg s₀ 0), (96, stackArg s₀ 1), (108, s₀.gpr .r4), (112, s₀.gpr .r5), (116, s₀.gpr .r6),
   (120, s₀.gpr .r7), (124, s₀.gpr .r8), (128, s₀.gpr .r9), (132, s₀.gpr .r10), (136, s₀.gpr .r11),
   (140, s₀.gpr .lr), (80, s₀.gpr .r0), (84, s₀.gpr .r1), (88, s₀.gpr .r2), (100, flag32 (stackArg s₀ 2)),
   (104, 0)]

/-- The memory after the prologue. -/
def setupMem (s₀ : State) : Mem :=
  (setupWrites s₀).foldl (fun m p => m.writeW (A (scp s₀) p.1) p.2) s₀.mem

theorem readW_writeW_scr {s₀ : State} (hp : Pre s₀) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 512) (he : e + 4 ≤ 512) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (A (scp s₀) e) v).readW (A (scp s₀) d) 32 = m.readW (A (scp s₀) d) 32 := by
  refine Mem.readW_writeW_sep ?_ (by decide)
  rw [hp.scr_addr (by omega), hp.scr_addr (by omega)]
  exact Offset.sep _ h (by omega) (by omega)

/-- A stack argument is unchanged by a write to `scratch`. -/
theorem readW_writeW_arg {s₀ : State} (hp : Pre s₀) (m : Mem) (v : BitVec 32) {i e : Nat} (hi : i < 4)
    (he : e + 4 ≤ 512) :
    (m.writeW (A (scp s₀) e) v).readW (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 32 =
      m.readW (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 32 := by
  have := hp.sp_fits
  refine Mem.readW_writeW_sep (hp.a_scr.sep ?_ ?_) (by decide)
  · show (⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 16⟩ : Region).Contains _ 4
    rw [addr_add (by omega), addr_add (by omega)]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  · rw [hp.scr_addr (by omega)]; exact contains_offset he (by omega)

set_option simprocs false in
theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) s₀ fun s₁ =>
      s₁.mem = setupMem s₀ ∧ s₁.gpr .r12 = scp s₀ ∧ s₁.z = (s₀.gpr .r2 - 0 == 0) ∧ s₁.rd = s₀.rd ∧
      s₁.wr = s₀.wr ∧ s₁.sp = s₀.sp := by
  have hs := hp.sp_fits
  have ia : ∀ i, i < 4 → InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 4 :=
    fun i hi => ⟨argR s₀, by simp [hp.rd], by
      show (⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 16⟩ : Region).Contains _ 4
      rw [addr_add (by omega), addr_add (by omega)]
      exact Offset.contains _ (by omega) (by omega) (by omega)⟩
  have a0 := ia 0 (by decide); have a1 := ia 1 (by decide); have a2 := ia 2 (by decide)
  have a3 := ia 3 (by decide)
  simp only [show 4 * 0 = 0 from rfl, show 4 * 1 = 4 from rfl, show 4 * 2 = 8 from rfl,
    show 4 * 3 = 12 from rfl] at a0 a1 a2 a3
  have e3 : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 12)) 32 = stackArg s₀ 3 := rfl
  have e0 : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 0)) 32 = stackArg s₀ 0 := rfl
  have e1 : ∀ v, (s₀.mem.writeW (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 92)) v).readW
      (State.addr (s₀.sp + BitVec.ofNat 32 4)) 32 = stackArg s₀ 1 := fun v =>
    readW_writeW_arg hp _ v (i := 1) (by decide) (by decide)
  have e2 : ∀ v v', ((s₀.mem.writeW (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 92)) v).writeW
      (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 96)) v').readW
      (State.addr (s₀.sp + BitVec.ofNat 32 8)) 32 = stackArg s₀ 2 := fun v v' => by
    rw [readW_writeW_arg hp _ v' (i := 2) (by decide) (by decide),
      readW_writeW_arg hp _ v (i := 2) (by decide) (by decide)]; rfl
  have w : ∀ d, d + 4 ≤ 512 → InRegions s₀.wr (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 d)) 4 :=
    fun d hd => hp.out_scr hd
  have w92 := w 92 (by decide); have w96 := w 96 (by decide); have w108 := w 108 (by decide)
  have w112 := w 112 (by decide); have w116 := w 116 (by decide); have w120 := w 120 (by decide)
  have w124 := w 124 (by decide); have w128 := w 128 (by decide); have w132 := w 132 (by decide)
  have w136 := w 136 (by decide); have w140 := w 140 (by decide); have w80 := w 80 (by decide)
  have w84 := w 84 (by decide); have w88 := w 88 (by decide); have w100 := w 100 (by decide)
  have w104 := w 104 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [setup, save, saved, Impl.Blake2.Arm.S.S, Impl.Blake2.Arm.S.T,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, tOff, stOff, blkOff, nOff, fOff,
    show 92 + 4 = 96 from rfl, show 100 + 4 = 104 from rfl, runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, Op2.eval, State.load32, State.store32, subFlags,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.sp_setReg, a0, a1, a2, a3, e3, e0, e1, e2, w92, w96, w108, w112, w116, w120, w124, w128,
    w132, w136, w140, w80, w84, w88, w100, w104,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial⟩

/-! ## Advancing the counter -/

/-- `scratch` after `advance`: the counter's two words advanced by 64, the
pointers `P8` and `P9` stored again and the count `n` decremented. -/
def ctrMem (m : Mem) (scr : BitVec 32) (N : Nat) (P8 P9 n : BitVec 32) : Mem :=
  ((((m.writeW (A scr tOff) (lo (BitVec.ofNat 64 (N + 64)))).writeW (A scr (tOff + 4))
    (hi (BitVec.ofNat 64 (N + 64)))).writeW (A scr stOff) P8).writeW (A scr blkOff) P9).writeW (A scr nOff) (n - 1)

theorem carry_lo (N : Nat) : lo (BitVec.ofNat 64 N) + 64 = lo (BitVec.ofNat 64 (N + 64)) := by
  rw [← BitVec.ofNat_add_ofNat, lo_add]; rfl

theorem carry_hi (N : Nat) :
    hi (BitVec.ofNat 64 N) + 0 + (if 2 ^ 32 ≤ (lo (BitVec.ofNat 64 N)).toNat + 64 then 1 else 0) =
      hi (BitVec.ofNat 64 (N + 64)) := by
  rw [← BitVec.ofNat_add_ofNat, hi_add]
  simp only [show lo (BitVec.ofNat 64 64) = 64 from rfl, show hi (BitVec.ofNat 64 64) = 0 from rfl,
    show (64 : BitVec 32).toNat = 64 from rfl]

set_option simprocs false in
theorem advance_ok {s : State} {scr : BitVec 32} {N : Nat} {P8 P9 n : BitVec 32}
    (h12 : s.gpr .r12 = scr) (h8 : s.gpr .r8 = P8) (h9 : s.gpr .r9 = P9) (h10 : s.gpr .r10 = n)
    (hw : ∀ d, d + 4 ≤ 512 → InRegions s.wr (A scr d) 4)
    (hlo : s.mem.readW (A scr tOff) 32 = lo (BitVec.ofNat 64 N))
    (hhi : s.mem.readW (A scr (tOff + 4)) 32 = hi (BitVec.ofNat 64 N)) :
    WP isa (.block advance) s fun s' =>
      s'.z = (n - 1 == 0) ∧ s'.gpr .r12 = scr ∧ (∀ r, r ∉ [Reg.r0, .r1, .r10] → s'.gpr r = s.gpr r) ∧
      s'.mem = ctrMem s.mem scr N P8 P9 n ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have ir : ∀ d, d + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (A scr d) 4 := fun d hd =>
    let ⟨r, hr, hc⟩ := hw d hd; ⟨r, List.mem_append_right _ hr, hc⟩
  have o92 := hw 92 (by decide); have o96 := hw 96 (by decide); have o80 := hw 80 (by decide)
  have o84 := hw 84 (by decide); have o88 := hw 88 (by decide)
  have i92 := ir 92 (by decide); have i96 := ir 96 (by decide)
  simp only [A, tOff, show 92 + 4 = 96 from rfl] at o92 o96 o80 o84 o88 i92 i96 hlo hhi
  apply WP.of_runBlock
  simp (config := {decide := true}) only [advance, Impl.Blake2.Arm.S.S, tOff, nOff, stOff, blkOff,
    show 92 + 4 = 96 from rfl, runBlock_cons, runStep_some, runBlock_nil, exec, isa, Op2.eval, State.load32,
    State.store32, addFlags, subFlags, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.c_setReg, RegUpd.z_setReg, RegUpd.sp_setReg, h12, h8, h9, h10, o92, o96, o80, o84, o88, i92, i96, hlo,
    hhi, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, ?_, trivial⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h2⟩ := hr
    simp only [h0, h1, h2, ite_false]
  · simp only [decide_eq_true_eq, show (64 : BitVec 32).toNat = 64 from rfl, carry_lo, carry_hi]
    rfl

/-! ## The work vector of `F` -/

/-- The work vector at the start of the rounds of `F` (RFC 7693 §3.2). -/
def initV (h : Spec.Blake2.HashValue 32) (t : Nat) (f : Bool) : Spec.Blake2.Work 32 :=
  let v : Spec.Blake2.Work 32 := h ++ Spec.Blake2.s.IV
  let v := v.set 12 (v[12] ^^^ BitVec.ofNat 32 t)
  let v := v.set 13 (v[13] ^^^ BitVec.ofNat 32 (t / 2 ^ 32))
  if f then v.set 14 (v[14] ^^^ BitVec.allOnes 32) else v

theorem initW_eq (h : Spec.Blake2.HashValue 32) (N : Nat) (f : Bool) {H X : Nat → BitVec 32}
    (hH : ∀ k (hk : k < 8), H k = h[k]) (h12 : X 12 = BitVec.ofNat 32 N)
    (h13 : X 13 = BitVec.ofNat 32 (N / 2 ^ 32)) (h14 : X 14 = flagW f) (h15 : X 15 = 0) (k : Nat)
    (hk : k < 16) : initW H X k = (initV h N f)[k] := by
  have ha : ∀ j (hj : j < 16), (h ++ Spec.Blake2.s.IV)[j] =
      if h8 : j < 8 then h[j] else Spec.Blake2.s.IV[j - 8] := fun j hj => Vector.getElem_append hj
  have hg : ∀ j (hj : j < 8), Spec.Blake2.s.IV.toList.getD j 0 = Spec.Blake2.s.IV[j] := fun j hj => by
    simp [List.getD_eq_getElem?_getD, hj]
  unfold initW initV
  rcases (by omega : k < 8 ∨ (8 ≤ k ∧ k < 12) ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15) with
    h8 | h8 | rfl | rfl | rfl | rfl
  · have : 12 ≠ k ∧ 13 ≠ k ∧ 14 ≠ k := by omega
    cases f <;> simp [h8, this, ha k hk, hH k h8]
  · have : 12 ≠ k ∧ 13 ≠ k ∧ 14 ≠ k := by omega
    simp only [show ¬ k < 8 by omega, h8.2, ↓reduceIte]
    rw [hg (k - 8) (by omega)]
    cases f <;> simp [show ¬ k < 8 by omega, this, ha k hk]
  · cases f <;> simp [ha, h12]
  · cases f <;> simp [ha, h13]
  · cases f <;> simp [ha, h14, flagW]
  · cases f <;> simp [ha, h15]

theorem F_eq (h : HashValue 32) (m : Block 32) (t : Nat) (f : Bool) :
    Spec.Blake2.F Spec.Blake2.s h m t f =
      Vector.ofFn fun i => h[i] ^^^ ((List.range 10).foldl (Spec.Blake2.round Spec.Blake2.s m) (initV h t f))[i] ^^^
        ((List.range 10).foldl (Spec.Blake2.round Spec.Blake2.s m) (initV h t f))[i.val + 8] := rfl

theorem stateAt_get {st : BitVec 32} (hfit : st.toNat + 32 ≤ 2 ^ 32) (m : Mem) {k : Nat} (hk : k < 8) :
    (Spec.Blake2.stateAt 32 m (State.addr st))[k] = m.readW (A st (4 * k)) 32 := by
  simp only [Spec.Blake2.stateAt, Vector.getElem_ofFn]
  rw [A_eq (by omega)]

theorem blockAt_get {bk : BitVec 32} (hfit : bk.toNat + 64 ≤ 2 ^ 32) (m : Mem) {j : Nat} (hj : j < 16) :
    Spec.Blake2.blockAt 32 m (State.addr bk) ⟨j, hj⟩ = m.readW (A bk (4 * j)) 32 := by
  rw [Proof.Blake2.blockAt_word, A_eq (by omega)]

theorem lo_ofNat (N : Nat) : lo (BitVec.ofNat 64 N) = BitVec.ofNat 32 N := by
  apply BitVec.eq_of_toNat_eq
  rw [lo_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem hi_ofNat (N : Nat) : hi (BitVec.ofNat 64 N) = BitVec.ofNat 32 (N / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [hi_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch space. -/
def Saved (s₀ : State) (m : Mem) : Prop := ∀ p ∈ saved, m.readW (A (scp s₀) p.2) 32 = s₀.gpr p.1

theorem saved_off : ∀ p ∈ saved, 108 ≤ p.2 ∧ p.2 + 4 ≤ 144 := by decide

/-- What holds between blocks, after `i` of them: everything is in `scratch`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = scp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : Spec.Blake2.stateAt 32 s.mem (State.addr (stp s₀)) =
    Spec.Blake2.compressBlocks Spec.Blake2.s (H₀ s₀) s₀.mem (State.addr (bp s₀)) i (t₀ s₀) (fl s₀)
  saved : Saved s₀ s.mem
  st : s.mem.readW (A (scp s₀) stOff) 32 = stp s₀
  blk : s.mem.readW (A (scp s₀) blkOff) 32 = blkAddr s₀ i
  n : s.mem.readW (A (scp s₀) nOff) 32 = BitVec.ofNat 32 (nb s₀ - i)
  tlo : s.mem.readW (A (scp s₀) tOff) 32 = lo (BitVec.ofNat 64 (t₀ s₀ + i * 64))
  thi : s.mem.readW (A (scp s₀) (tOff + 4)) 32 = hi (BitVec.ofNat 64 (t₀ s₀ + i * 64))
  f : s.mem.readW (A (scp s₀) fOff) 32 = flagW (fl s₀)
  z : s.mem.readW (A (scp s₀) (fOff + 4)) 32 = 0

theorem compressBlocks_succ' (H : HashValue 32) (m : Mem) (p : Addr) (i t : Nat) (f : Bool) :
    Spec.Blake2.compressBlocks Spec.Blake2.s H m p (i + 1) t f =
      Spec.Blake2.F Spec.Blake2.s (Spec.Blake2.compressBlocks Spec.Blake2.s H m p i t f)
        (Spec.Blake2.blockAt 32 m (p + BitVec.ofNat 64 (64 * i))) (t + i * 64) f :=
  Proof.Blake2.compressBlocks_succ _ _ _ _ _ _ _

/-! ## One block -/

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ LInv s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have fitS := hp.st_fits
  have fitV := hp.scr_fits
  have fitB := hp.blk_fit hi
  set N := t₀ s₀ + i * 64 with hN
  set H := Spec.Blake2.compressBlocks Spec.Blake2.s (H₀ s₀) s₀.mem (State.addr (bp s₀)) i (t₀ s₀) (fl s₀)
    with hH
  set M := Spec.Blake2.blockAt 32 s₀.mem (State.addr (blkAddr s₀ i)) with hM
  have hHk : ∀ k (hk : k < 8), s.mem.readW (A (stp s₀) (4 * k)) 32 = H[k] := fun k hk => by
    rw [← stateAt_get fitS _ hk, hL.state]
  have wV : ∀ o, o + 4 ≤ 512 → InRegions s.wr (A (scp s₀) o) 4 := by rw [hL.wr]; exact fun o ho => hp.out_scr ho
  have dScr : ∀ d, d + 4 ≤ 512 → Region.Disjoint ⟨State.addr (scp s₀) + BitVec.ofNat 64 d, 4⟩ (stR s₀) :=
    fun d hd => (hp.st_scr.sub_right (Offset.sub_base _ (by omega))).symm
  -- Initialize the work vector.
  refine WP.seq (WP.mono (init_ok (V := scp s₀) (st := stp s₀) (B := blkAddr s₀ i) hL.r12 fitV fitS fitB wV
    (by rw [hL.rd, hL.wr]; exact fun o ho => hp.in_st ho) (by rw [hL.rd, hL.wr]; exact hp.blk_rd hi)
    hL.st hL.blk ((hp.blk_scr.sub_left (hp.blk_sub hi)).sub_right (Region.sub_prefix (by omega)))
    hp.st_scr) fun s₁ h₁ => ?_)
  have hv : ∀ k (hk : k < 16), Holds (scp s₀) s₁ k (initV H N (fl s₀))[k] := fun k hk => by
    rw [← initW_eq H N (fl s₀) hHk ?_ ?_ ?_ ?_ k hk]
    · exact h₁.vars k hk
    · show s.mem.readW (A (scp s₀) tOff) 32 = _; rw [hL.tlo, lo_ofNat]
    · show s.mem.readW (A (scp s₀) (tOff + 4)) 32 = _; rw [hL.thi, hi_ofNat]
    · exact hL.f
    · exact hL.z
  -- The rounds.
  have rc : RCtx (scp s₀) M s₁ :=
    ⟨h₁.r12, fitV, by rw [h₁.wr]; exact wV, fun j hj => by
      rw [h₁.msg j hj, hp.blk_frame hL.frame hi (by omega), hM, blockAt_get fitB _ hj]⟩
  refine WP.seq (WP.mono (rounds_ok rc hv 10) fun s₂ h₂ => ?_)
  -- XOR into the state.
  set v := (List.range 10).foldl (Spec.Blake2.round Spec.Blake2.s M) (initV H N (fl s₀)) with hv'
  have hst₁ : ∀ d, (d = 80 ∨ 88 ≤ d) → d + 4 ≤ 512 →
      s₁.mem.readW (A (scp s₀) d) 32 = s.mem.readW (A (scp s₀) d) 32 := fun d h1 h2 =>
    hp.scr_frame h2 h₁.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact Offset.disjoint _ (by simp only [blkOff]; omega) (by omega) (by simp only [blkOff]; omega)
  have hst₂ : ∀ d, 80 ≤ d → d + 4 ≤ 512 →
      s₂.mem.readW (A (scp s₀) d) 32 = s₁.mem.readW (A (scp s₀) d) 32 := fun d h1 h2 =>
    hp.scr_frame h2 h₂.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have fc : FCtx (scp s₀) (stp s₀) v s₂ :=
    ⟨fitS, fitV, by rw [h₂.wr, h₁.wr, hL.wr]; exact fun o ho => hp.out_st ho,
      by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hL.rd, hL.wr]; exact fun o ho => hp.in_scr ho,
      fun k hk => (holds_c (by omega) (by omega)).mp (h₂.vars (k + 8) (by omega)), hp.st_scr⟩
  refine WP.seq (WP.mono (fin_ok fc h₂.vars (by rw [h₂.r12, h₁.r12])
    (by rw [hst₂ stOff (by decide) (by decide), hst₁ stOff (.inl rfl) (by decide)]; exact hL.st))
    fun s₃ ⟨r12₃, r8₃, r9₃, r10₃, rd₃, wr₃, sp₃, f₃, w₃⟩ => ?_)
  have hst₃ : ∀ d, d + 4 ≤ 512 → s₃.mem.readW (A (scp s₀) d) 32 = s₂.mem.readW (A (scp s₀) d) 32 :=
    fun d h2 => hp.scr_frame h2 f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dScr d h2
  have hs : ∀ d, (d = 80 ∨ 88 ≤ d) → d + 4 ≤ 512 →
      s₃.mem.readW (A (scp s₀) d) 32 = s.mem.readW (A (scp s₀) d) 32 := fun d h1 h2 => by
    rw [hst₃ d h2, hst₂ d (by omega) h2, hst₁ d h1 h2]
  -- Advance the counter.
  have wV₃ : ∀ d, d + 4 ≤ 512 → InRegions s₃.wr (A (scp s₀) d) 4 := by
    rw [wr₃, h₂.wr, h₁.wr]; exact wV
  refine WP.mono (advance_ok (N := N) r12₃ r8₃ r9₃ r10₃ wV₃
    (by rw [hs tOff (by decide) (by decide)]; exact hL.tlo)
    (by rw [hs (tOff + 4) (by decide) (by decide)]; exact hL.thi))
    fun s₄ ⟨z₄, r12₄, g₄, m₄, rd₄, wr₄, sp₄⟩ => ?_
  have hs₄ : ∀ d, d + 4 ≤ 512 → (d + 4 ≤ 80 ∨ 100 ≤ d) →
      s₄.mem.readW (A (scp s₀) d) 32 = s₃.mem.readW (A (scp s₀) d) 32 := fun d h2 h3 => by
    rw [m₄, ctrMem, readW_writeW_scr hp _ _ h2 (by decide) (by simp only [nOff]; omega),
      readW_writeW_scr hp _ _ h2 (by decide) (by simp only [blkOff]; omega),
      readW_writeW_scr hp _ _ h2 (by decide) (by simp only [stOff]; omega),
      readW_writeW_scr hp _ _ h2 (by decide) (by simp only [tOff]; omega),
      readW_writeW_scr hp _ _ h2 (by decide) (by simp only [tOff]; omega)]
  have hc : Frame [scrR s₀] s₃.mem s₄.mem := by
    have c : ∀ d, d + 4 ≤ 512 → (scrR s₀).Contains (A (scp s₀) d) (32 / 8) := fun d hd => by
      rw [hp.scr_addr (by omega)]; exact contains_offset hd (by omega)
    have m := List.mem_singleton_self (scrR s₀)
    rw [m₄]
    exact ((((((Frame.refl _ _).writeW m _ (c _ (by decide))).writeW m _ (c _ (by decide))).writeW m _
      (c _ (by decide))).writeW m _ (c _ (by decide))).writeW m _ (c _ (by decide)))
  -- The state.
  have hstate : Spec.Blake2.stateAt 32 s₄.mem (State.addr (stp s₀)) = Spec.Blake2.F Spec.Blake2.s H M N (fl s₀) := by
    refine Vector.ext fun k hk => ?_
    have hk8 : k < 8 := hk
    have hw : Frame [scrR s₀] s.mem s₂.mem :=
      (h₁.frame.sub fun r hr => ⟨scrR s₀, List.mem_singleton_self _, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Region.sub_prefix (by omega)
        · exact Offset.sub_base _ (by simp only [blkOff]; omega)⟩).trans
      (h₂.frame.sub fun r hr => ⟨scrR s₀, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega)⟩)
    rw [stateAt_get fitS _ hk8, hp.st_frame hc hk8, w₃ k hk8, hp.st_frame hw hk8, hHk k hk8, F_eq,
      Vector.getElem_ofFn, BitVec.xor_assoc]
    rfl
  have hsub : ∀ r ∈ initR (scp s₀), ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨scrR s₀, by simp, ?_⟩
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by omega)
    · exact Offset.sub_base _ (by simp only [blkOff]; omega)
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₄.mem :=
    (((hL.frame.trans (h₁.frame.sub hsub)).trans (h₂.frame.sub fun r hr => ⟨scrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega)⟩)).trans
      (f₃.mono (by simp))).trans (hc.mono (by simp))
  have hnb : nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  have hn : s₃.gpr .r10 = BitVec.ofNat 32 (nb s₀ - i) := by
    rw [r10₃, hst₂ nOff (by decide) (by decide), hst₁ nOff (by decide) (by decide)]; exact hL.n
  have hn1 : BitVec.ofNat 32 (nb s₀ - i) - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hN1 : N + 64 = t₀ s₀ + (i + 1) * 64 := by rw [hN, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  have hL' : LInv s₀ (i + 1) s₄ := by
    refine ⟨r12₄, by rw [rd₄, rd₃, h₂.rd, h₁.rd, hL.rd],
      by rw [wr₄, wr₃, h₂.wr, h₁.wr, hL.wr], by rw [sp₄, sp₃, h₂.sp, h₁.sp, hL.sp], hframe, ?_,
      fun p hp' => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hstate, compressBlocks_succ', ← hH, hM, hp.blk_addr hi]
    · have := saved_off p hp'
      rw [hs₄ p.2 (by omega) (by omega), hs p.2 (by omega) (by omega)]; exact hL.saved p hp'
    · rw [m₄, ctrMem, readW_writeW_scr hp _ _ (by decide) (by decide) (by decide),
        readW_writeW_scr hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    · rw [m₄, ctrMem, readW_writeW_scr hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
        hst₂ blkOff (by decide) (by decide), h₁.blk]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [m₄, ctrMem]
      show (_ : Mem).readW (A (scp s₀) nOff) 32 = _
      rw [Mem.readW_writeW_self32, ← r10₃, hn, hn1]
    · rw [m₄, ctrMem, readW_writeW_scr hp _ _ (by decide) (by decide) (by decide),
        readW_writeW_scr hp _ _ (by decide) (by decide) (by decide),
        readW_writeW_scr hp _ _ (by decide) (by decide) (by decide),
        readW_writeW_scr hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, hN1]
    · rw [m₄, ctrMem, readW_writeW_scr hp _ _ (by decide) (by decide) (by decide),
        readW_writeW_scr hp _ _ (by decide) (by decide) (by decide),
        readW_writeW_scr hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, hN1]
    · rw [hs₄ fOff (by decide) (by decide), hs fOff (by decide) (by decide)]; exact hL.f
    · rw [hs₄ (fOff + 4) (by decide) (by decide), hs (fOff + 4) (by decide) (by decide)]; exact hL.z
  have hev : eval .ne s₄ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    rw [eval_ne, z₄, ← r10₃, hn, hn1]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hL'⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    exact ⟨by rw [hev]; simpa using h0, by omega, hL'⟩

/-! ## The prologue's memory -/

theorem setupMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scrR s₀] s₀.mem (setupMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 512 → (scrR s₀).Contains (A (scp s₀) d) (32 / 8) :=
    fun d hd => by rw [hp.scr_addr (by omega)]; exact contains_offset hd (by have := hp.scr_fits; omega)
  have m := List.mem_singleton_self (scrR s₀)
  have key : ∀ (l : List (Nat × BitVec 32)), (∀ p ∈ l, p.1 + 4 ≤ 512) → ∀ m₀ : Mem,
      Frame [scrR s₀] s₀.mem m₀ →
      Frame [scrR s₀] s₀.mem (l.foldl (fun m p => m.writeW (A (scp s₀) p.1) p.2) m₀) := by
    intro l
    induction l with
    | nil => intro _ m₀ h; exact h
    | cons p ps ih =>
      intro hl m₀ h
      exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _
        (h.writeW m _ (c p.1 (hl p List.mem_cons_self)))
  have hl : ∀ p ∈ setupWrites s₀, p.1 + 4 ≤ 512 := by
    intro p hp
    simp only [setupWrites, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> exact Nat.le_of_ble_eq_true rfl
  exact key _ hl _ (Frame.refl _ _)

theorem linv_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hm : s₁.mem = setupMem s₀)
    (h12 : s₁.gpr .r12 = scp s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) :
    LInv s₀ 0 s₁ := by
  have hf := setupMem_frame hp
  refine ⟨h12, hrd, hwr, hsp, by rw [hm]; exact hf.mono (by simp), ?_, fun p hp' => ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · refine Vector.ext fun k hk => ?_
    rw [hm, stateAt_get hp.st_fits _ hk, hp.st_frame hf hk, ← stateAt_get hp.st_fits _ hk]
    rfl
  all_goals simp only [hm, A, stOff, blkOff, nOff, tOff, fOff]
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      readW_writeW_scr hp]
  · simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      readW_writeW_scr hp]
  · simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      readW_writeW_scr hp]
    simp [blkAddr]
  · simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      readW_writeW_scr hp]
    simp [nb]
  · simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      readW_writeW_scr hp]
    rw [Nat.zero_mul, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact (Proof.Sha512.Arm.lo_append _ _).symm
  · simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      readW_writeW_scr hp]
    rw [Nat.zero_mul, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact (Proof.Sha512.Arm.hi_append _ _).symm
  · simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      readW_writeW_scr hp]
    exact flag_eq _
  · simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, A, Mem.readW_writeW_self32]

/-! ## The epilogue -/

set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : LInv s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ (compressArm Spec.Blake2.s).post s₀ s' := by
  have i : ∀ d, d + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 d)) 4 :=
    fun d hd => by rw [hc.rd, hc.wr]; exact hp.in_scr hd
  have i0 := i 108 (by decide); have i1 := i 112 (by decide); have i2 := i 116 (by decide)
  have i3 := i 120 (by decide); have i4 := i 124 (by decide); have i5 := i 128 (by decide)
  have i6 := i 132 (by decide); have i7 := i 136 (by decide); have i8 := i 140 (by decide)
  have g : ∀ p ∈ saved, s.mem.readW (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 p.2)) 32 = s₀.gpr p.1 :=
    hc.saved
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := g
  have hstate := hc.state
  have hr12 := hc.r12
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restore, saved, Impl.Blake2.Arm.S.S, List.map_cons, List.map_nil,
    runBlock_cons, runStep_some, runBlock_nil, exec, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32, hr12, i0, i1, i2, i3, i4, i5, i6, i7, i8, ite_true,
    ite_false, g0, g1, g2, g3, g4, g5, g6, g7, g8, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, hstate⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Blake2.Arm.S.compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ (compressArm Spec.Blake2.s).post s₀ s' := by
  unfold Impl.Blake2.Arm.S.compress
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨m₁, r12₁, z₁, rd₁, wr₁, sp₁⟩ => ?_)
  have hL₀ := linv_zero hp m₁ r12₁ rd₁ wr₁ sp₁
  refine WP.seq (WP.mono (Q := LInv s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  refine WP.ite (s₀.gpr .r2 - 0 == 0) (by rw [← z₁]; rfl) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hL₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ LInv s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-! ## Verified -/

/-- The initial taint: `r0`–`r2` are public, and so are the 16 bytes of stack
arguments. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [32, 512], argLen := 16, argBases := [(12, 1)] }

theorem argByte_eq {s : State} (hsp : s.sp.toNat + 16 ≤ 2 ^ 32) {k : Nat} (hk : k < 16) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

theorem wf₀ {s : State} (hp : Pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hst := hp.st_fits; have hsc := hp.scr_fits
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hp.sp_fits, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · have e : (⟨State.addr s.sp, 16⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.a_st
    · exact hp.a_scr
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : (compressArm Spec.Blake2.s).pre s₁)
    (h₂ : (compressArm Spec.Blake2.s).pre s₂) (hpub : (compressArm Spec.Blake2.s).pub s₁ s₂) :
    VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, a0, a1, a2, a3⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scrR, stp, scp, p0, a3]
  · simp only [τ₀] at hk
    rw [argByte_eq hp₁.sp_fits hk, argByte_eq hp₂.sp_fits hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 ∨ k / 4 = 2 ∨ k / 4 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

/-- A state satisfying the precondition (with no blocks, and the scratch space at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩, ⟨0x4000, 16⟩]
  wr := [⟨0x1000, 32⟩, ⟨0, 512⟩]

/-- The proof, against the ARMv7 contract the streaming functions use. -/
theorem compress_verified' :
    Verified Arm.target Impl.Blake2.Arm.S.compress (compressArm Spec.Blake2.s) := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub)
      (by taint_decide)
  · refine ⟨sat, rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
    exact Region.disjoint_of_sep (by decide)

theorem compress_noCalls : Impl.Blake2.Arm.S.compress.noCalls = true := by
  lit_decide

theorem compress_implies :
    (compressArm Spec.Blake2.s).Implies (Spec.Blake2.compressSContract Arm.abi) := by
  sig_implies [Spec.Blake2.compressSContract, Spec.Blake2.compressSSig, compressArm, tArm, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Blake2.blockBytes]
    [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat

/-- The proof, against the shared contract of `Spec/Blake2/Contract.lean`. -/
theorem compress_verified :
    Verified Arm.target Impl.Blake2.Arm.S.compress (Spec.Blake2.compressSContract Arm.abi) :=
  compress_verified'.of_implies compress_implies

end VG.Proof.Blake2.ArmS
