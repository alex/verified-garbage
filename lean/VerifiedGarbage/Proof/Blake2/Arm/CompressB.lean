import VerifiedGarbage.Proof.Blake2.Arm.BlockB
import VerifiedGarbage.Proof.Blake2.Arm.Contract
import VerifiedGarbage.Proof.Blake2.Arm.LitB
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2.Contract

/-!
# BLAKE2b compression function on ARMv7: the whole function

The loop is proven against `Proof.Blake2.compressArm Spec.Blake2.b`
(`compress_verified'`), which the streaming functions use for their calls;
`compress_verified` moves it to the shared contract of
`Spec/Blake2/Contract.lean`. Constant time is the taint analysis on the
literal code (`LitB.lean`).
-/

namespace VG.Proof.Blake2.ArmB

open VG VG.Arm
open VG.Impl.Sha512.Arm (lo hi)
open VG.Impl.Blake2.Arm.B (advance body save restore setup saved tweak ctrLo ctrHi flagOff zeroOff)
open VG.Proof.Sha512.Arm (Only Pair rd64 write64 A A_eq Reg64 lo_append hi_append hi_append_lo
  eq_of_lo_hi lo_add hi_add lo_toNat hi_toNat readW64 rd64_frame lo_rd64 hi_rd64)
open VG.Proof.MdStream.Arm (eval_ne contains_offset sub_offset)
open VG.Spec.Blake2 (Work Block HashValue Params)

/-! ## Memory -/

theorem stateAt_get {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) (m : Mem) {k : Nat} (hk : k < 8) :
    (Spec.Blake2.stateAt 64 m (State.addr st))[k] = rd64 m st (8 * k) := by
  simp only [Spec.Blake2.stateAt, Vector.getElem_ofFn, rd64]
  rw [readW64, A_eq (by omega), A_eq (by omega),
    show State.addr st + BitVec.ofNat 64 (8 * k) + 4 = State.addr st + BitVec.ofNat 64 (8 * k + 4) from
      Offset.add_ofNat_add_ofNat _ _ 4]

theorem stateAt_ext {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) {m : Mem} {H : HashValue 64}
    (h : ∀ k (hk : k < 8), rd64 m st (8 * k) = H[k]) : Spec.Blake2.stateAt 64 m (State.addr st) = H := by
  ext k hk
  rw [stateAt_get hfit m hk, h k hk]

theorem blockAt_get {bk : BitVec 32} (hfit : bk.toNat + 128 ≤ 2 ^ 32) (m : Mem) {j : Nat} (hj : j < 16) :
    Spec.Blake2.blockAt 64 m (State.addr bk) ⟨j, hj⟩ = rd64 m bk (8 * j) := by
  rw [Proof.Blake2.blockAt_word, readW64, rd64, A_eq (by omega), A_eq (by omega),
    show State.addr bk + BitVec.ofNat 64 (64 / 8 * j) + 4 = State.addr bk + BitVec.ofNat 64 (8 * j + 4) from
      Offset.add_ofNat_add_ofNat _ _ 4]

/-- A 32-bit word outside the regions a frame allows to change. -/
theorem readW_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 4⟩ r) : m'.readW a 32 = m.readW a 32 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev stp : BitVec 32 := s₀.gpr .r0
abbrev bp : BitVec 32 := s₀.gpr .r1
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev scp : BitVec 32 := stackArg s₀ 3
abbrev t₀ : Nat := (tArm s₀).toNat
abbrev fl : Bool := stackArg s₀ 2 != 0
abbrev blR : Region := ⟨State.addr (bp s₀), 128 * nb s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 16⟩
abbrev H₀ : HashValue 64 := Spec.Blake2.stateAt 64 s₀.mem (State.addr (stp s₀))

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (128 * i)

/-- The counter's region in `scratch`. -/
abbrev ctrR : Region := ⟨State.addr (scp s₀) + BitVec.ofNat 64 ctrLo, 12⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀, argR s₀]
  wr : s₀.wr = [stR (stp s₀), scrR (scp s₀)]
  st_scr : (stR (stp s₀)).Disjoint (scrR (scp s₀))
  blk_st : (blR s₀).Disjoint (stR (stp s₀))
  blk_scr : (blR s₀).Disjoint (scrR (scp s₀))
  a_st : (argR s₀).Disjoint (stR (stp s₀))
  a_scr : (argR s₀).Disjoint (scrR (scp s₀))
  st_fits : (stp s₀).toNat + 64 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 128 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scp s₀).toNat + 512 ≤ 2 ^ 32
  sp_fits : s₀.sp.toNat + 16 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : (compressArm Spec.Blake2.b).pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem ctx {s : State} (h0 : s.gpr .r0 = stp s₀) (h3 : s.gpr .r3 = scp s₀) (hw : s.wr = s₀.wr) :
    Ctx (stp s₀) (scp s₀) s :=
  ⟨h0, h3, h.st_fits, h.scr_fits, h.st_scr,
    Reg64.of_mem (by rw [hw, h.wr]; simp) h.st_fits, Reg64.of_mem (by rw [hw, h.wr]; simp) h.scr_fits⟩

theorem blk_toNat {i : Nat} (hi : i < nb s₀) : (blkAddr s₀ i).toNat = (bp s₀).toNat + 128 * i := by
  have := h.blk_fits
  simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 128 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blk_fit {i : Nat} (hi : i < nb s₀) : (blkAddr s₀ i).toNat + 128 ≤ 2 ^ 32 := by
  have := h.blk_fits; rw [h.blk_toNat hi]; omega

theorem blk_addr {i : Nat} (hi : i < nb s₀) :
    State.addr (blkAddr s₀ i) = State.addr (bp s₀) + BitVec.ofNat 64 (128 * i) :=
  addr_add (by have := h.blk_fits; omega)

theorem blk_sub {i : Nat} (hi : i < nb s₀) : Region.Sub ⟨State.addr (blkAddr s₀ i), 128⟩ (blR s₀) := by
  have := h.blk_fits
  rw [h.blk_addr hi]; exact sub_offset (by omega) (by omega)

theorem blk_rd {i : Nat} (hi : i < nb s₀) : Rd64 (s₀.rd ++ s₀.wr) (blkAddr s₀ i) 128 := by
  have := h.blk_fit hi
  have := h.blk_fits
  have hc : ∀ o, o + 4 ≤ 128 → InRegions (s₀.rd ++ s₀.wr) (A (blkAddr s₀ i) o) 4 := fun o ho => by
    refine ⟨blR s₀, by simp [h.rd], ?_⟩
    rw [A_eq (by omega), h.blk_addr hi, Offset.add_ofNat_add_ofNat]
    exact contains_offset (by omega) (by omega)
  exact fun o ho => ⟨hc o (by omega), hc (o + 4) (by omega)⟩

/-- The address of a word of `scratch`. -/
theorem scr_addr {d : Nat} (hd : d < 512) :
    A (scp s₀) d = State.addr (scp s₀) + BitVec.ofNat 64 d := A_eq (by have := h.scr_fits; omega)

theorem in_scr {d : Nat} (hd : d + 4 ≤ 512) : InRegions (s₀.rd ++ s₀.wr) (A (scp s₀) d) 4 := by
  rw [h.scr_addr (by omega)]
  exact ⟨scrR (scp s₀), by simp [h.wr], contains_offset hd (by omega)⟩

theorem out_scr {d : Nat} (hd : d + 4 ≤ 512) : InRegions s₀.wr (A (scp s₀) d) 4 := by
  rw [h.scr_addr (by omega)]
  exact ⟨scrR (scp s₀), by simp [h.wr], contains_offset hd (by omega)⟩

/-- A scratch word apart from the work vector, the state and the counter. -/
theorem scr_frame {d : Nat} (hd : 128 ≤ d) (hd' : d + 4 ≤ 512) (hc : d + 4 ≤ ctrLo ∨ ctrLo + 12 ≤ d)
    {m m' : Mem}
    (hf : Frame [workR (scp s₀)] m m' ∨ Frame [stR (stp s₀)] m m' ∨ Frame [ctrR s₀] m m') :
    m'.readW (A (scp s₀) d) 32 = m.readW (A (scp s₀) d) 32 := by
  have := h.scr_fits
  rw [h.scr_addr (by omega)]
  rcases hf with hf | hf | hf <;> refine readW_frame hf ?_ <;>
    simp only [List.mem_singleton, forall_eq]
  · exact Offset.disjoint_base _ hd (by omega)
  · exact Region.Disjoint.sub_left h.st_scr.symm (Offset.sub_base _ (by omega))
  · exact Offset.disjoint _ hc (by omega) (by simp only [ctrLo]; omega)

theorem scr_frame64 {d : Nat} (hd : 128 ≤ d) (hd' : d + 8 ≤ 512) (hc : d + 8 ≤ ctrLo ∨ ctrLo + 12 ≤ d)
    {m m' : Mem}
    (hf : Frame [workR (scp s₀)] m m' ∨ Frame [stR (stp s₀)] m m' ∨ Frame [ctrR s₀] m m') :
    rd64 m' (scp s₀) d = rd64 m (scp s₀) d := by
  simp only [rd64]
  rw [h.scr_frame (by omega) (by omega) (by omega) hf, h.scr_frame (by omega) (by omega) (by omega) hf]

/-- A state word apart from the scratch space. -/
theorem st_frame {m m' : Mem} (hf : Frame [scrR (scp s₀)] m m') {k : Nat} (hk : k < 8) :
    rd64 m' (stp s₀) (8 * k) = rd64 m (stp s₀) (8 * k) :=
  rd64_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.st_scr)
    h.st_fits (by omega)

/-- A block word apart from the state and the scratch space. -/
theorem blk_frame {m m' : Mem} (hf : Frame [stR (stp s₀), scrR (scp s₀)] m m') {i : Nat}
    (hi : i < nb s₀) {o : Nat} (ho : o + 8 ≤ 128) :
    rd64 m' (blkAddr s₀ i) o = rd64 m (blkAddr s₀ i) o :=
  rd64_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.blk_st.sub_left (h.blk_sub hi)
    · exact h.blk_scr.sub_left (h.blk_sub hi)) (h.blk_fit hi) ho

end Pre

/-! ## Advancing the counter -/

/-- The counter's three words after advancing by 128. -/
def ctrMem (m : Mem) (scr : BitVec 32) (N : Nat) : Mem :=
  ((m.writeW (A scr ctrLo) (lo (BitVec.ofNat 64 (N + 128)))).writeW (A scr (ctrLo + 4))
    (hi (BitVec.ofNat 64 (N + 128)))).writeW (A scr ctrHi) (BitVec.ofNat 32 ((N + 128) / 2 ^ 64))

theorem carry_lo (N : Nat) : lo (BitVec.ofNat 64 N) + 128 = lo (BitVec.ofNat 64 (N + 128)) := by
  rw [← BitVec.ofNat_add_ofNat, lo_add]; rfl

theorem carry_hi (N : Nat) :
    hi (BitVec.ofNat 64 N) + (0 + 0 + if 2 ^ 32 ≤ (lo (BitVec.ofNat 64 N)).toNat + 128 then 1 else 0) =
      hi (BitVec.ofNat 64 (N + 128)) := by
  rw [← BitVec.ofNat_add_ofNat, hi_add]
  simp only [show lo (BitVec.ofNat 64 128) = 128 from rfl, show hi (BitVec.ofNat 64 128) = 0 from rfl,
    show (128 : BitVec 32).toNat = 128 from rfl]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add]

theorem carry_top (N : Nat) :
    BitVec.ofNat 32 (N / 2 ^ 64) + 0 +
      (if 2 ^ 32 ≤ (hi (BitVec.ofNat 64 N)).toNat +
        (0 + 0 + if 2 ^ 32 ≤ (lo (BitVec.ofNat 64 N)).toNat + 128 then (1 : BitVec 32) else 0).toNat
        then 1 else 0) = BitVec.ofNat 32 ((N + 128) / 2 ^ 64) := by
  have hl := lo_toNat (BitVec.ofNat 64 N)
  have hh := hi_toNat (BitVec.ofNat 64 N)
  rw [BitVec.toNat_ofNat] at hl hh
  generalize (lo (BitVec.ofNat 64 N)).toNat = L at hl
  generalize (hi (BitVec.ofNat 64 N)).toNat = H at hh
  apply BitVec.eq_of_toNat_eq
  by_cases c0 : 2 ^ 32 ≤ L + 128
  · simp only [c0, ite_true, show ((0 : BitVec 32) + 0 + 1).toNat = 1 from rfl]
    by_cases c1 : 2 ^ 32 ≤ H + 1
    · simp only [c1, ite_true, BitVec.toNat_add, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl,
        show (1 : BitVec 32).toNat = 1 from rfl]
      omega
    · simp only [c1, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl]
      omega
  · simp only [c0, ite_false, show ((0 : BitVec 32) + 0 + 0).toNat = 0 from rfl, Nat.add_zero]
    have c1 : ¬ 2 ^ 32 ≤ H := by omega
    simp only [c1, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl]
    omega

set_option simprocs false in
theorem advance_ok {s : State} {scr : BitVec 32} {N : Nat} (h3 : s.gpr .r3 = scr) (hw : Reg64 s.wr scr 512)
    (hlo : rd64 s.mem scr ctrLo = BitVec.ofNat 64 N)
    (hhi : s.mem.readW (A scr ctrHi) 32 = BitVec.ofNat 32 (N / 2 ^ 64)) :
    WP isa (.block advance) s fun s' =>
      s'.gpr .r1 = s.gpr .r1 + 128 ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧
      (∀ r, r ∉ [Reg.r1, .r2, .r4, .r5, .r6, .r7] → s'.gpr r = s.gpr r) ∧
      s'.mem = ctrMem s.mem scr N ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have o168 := hw ctrLo (by decide)
  have o176 := hw ctrHi (by decide)
  have i168 := Reg64.rd s.rd hw ctrLo (by decide)
  have i176 := Reg64.rd s.rd hw ctrHi (by decide)
  have hl := lo_rd64 s.mem scr ctrLo
  have hh := hi_rd64 s.mem scr ctrLo
  rw [hlo] at hl hh
  simp only [A, ctrLo, ctrHi, show 168 + 4 = 172 from rfl] at o168 o176 i168 i176 hhi hl hh
  apply WP.of_runBlock
  simp (config := {decide := true}) only [advance, ctrLo, ctrHi, show 168 + 4 = 172 from rfl,
    runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, Op2.eval, State.load32, State.store32, addFlags, subFlags,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.c_setReg,
    RegUpd.z_setReg, RegUpd.sp_setReg, h3, i168.1, i168.2, i176.1, o168.1, o168.2, o176.1,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  rw [← hl, ← hh, hhi]
  simp only [decide_eq_true_eq, show (128 : BitVec 32).toNat = 128 from rfl]
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h4, h5, h6, h7⟩ := hr
    simp only [h1, h2, h4, h5, h6, h7, ite_false]
  · refine ⟨?_, trivial⟩
    rw [carry_lo, carry_hi, carry_top N]
    rfl

/-! ## The prologue -/

/-- The address of word `d` of `scratch`. -/
abbrev SA (s₀ : State) (d : Nat) : Addr := State.addr (scp s₀ + BitVec.ofNat 32 d)

/-- The flag word of `last`. -/
def flag32 (l : BitVec 32) : BitVec 32 := 0 - ((0 - l ||| l) >>> 31)

/-- The words the prologue stores in `scratch`, in order. -/
def setupWrites (s₀ : State) : List (Nat × BitVec 32) :=
  [(168, stackArg s₀ 0), (172, stackArg s₀ 1), (128, s₀.gpr .r4), (132, s₀.gpr .r5),
   (136, s₀.gpr .r6), (140, s₀.gpr .r7), (144, s₀.gpr .r8), (148, s₀.gpr .r9), (152, s₀.gpr .r10),
   (156, s₀.gpr .r11), (160, s₀.gpr .lr), (176, 0), (180, 0), (192, 0), (196, 0),
   (184, flag32 (stackArg s₀ 2)), (188, flag32 (stackArg s₀ 2))]

/-- The memory after the prologue. -/
def setupMem (s₀ : State) : Mem :=
  (setupWrites s₀).foldl (fun m p => m.writeW (SA s₀ p.1) p.2) s₀.mem

theorem SA_eq {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d < 512) :
    SA s₀ d = State.addr (scp s₀) + BitVec.ofNat 64 d := hp.scr_addr hd

theorem SA_sep {s₀ : State} (hp : Pre s₀) {d e : Nat} (hd : d + 4 ≤ 512) (he : e + 4 ≤ 512)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (SA s₀ d) 4 (SA s₀ e) 4 := by
  rw [SA_eq hp (by omega), SA_eq hp (by omega)]
  exact Offset.sep _ h (by omega) (by omega)

theorem readW_writeW_SA {s₀ : State} (hp : Pre s₀) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 512) (he : e + 4 ≤ 512) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (SA s₀ e) v).readW (SA s₀ d) 32 = m.readW (SA s₀ d) 32 :=
  Mem.readW_writeW_sep (SA_sep hp hd he h) (by decide)

/-- A stack argument is unchanged by a write to `scratch`. -/
theorem readW_writeW_arg {s₀ : State} (hp : Pre s₀) (m : Mem) (v : BitVec 32) {i e : Nat} (hi : i < 4)
    (he : e + 4 ≤ 512) :
    (m.writeW (SA s₀ e) v).readW (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 32 =
      m.readW (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 32 := by
  have := hp.sp_fits
  refine Mem.readW_writeW_sep (hp.a_scr.sep ?_ ?_) (by decide)
  · show (⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 16⟩ : Region).Contains _ 4
    rw [addr_add (by omega), addr_add (by omega)]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  · rw [SA_eq hp (by omega)]; exact contains_offset he (by omega)

set_option simprocs false in
theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) s₀ fun s₁ =>
      s₁.mem = setupMem s₀ ∧ (∀ r ∈ [Reg.r0, .r1, .r2], s₁.gpr r = s₀.gpr r) ∧
      s₁.gpr .r3 = scp s₀ ∧ s₁.z = (s₀.gpr .r2 - 0 == 0) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.sp = s₀.sp := by
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
  have e1 : ∀ v, (s₀.mem.writeW (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 168)) v).readW
      (State.addr (s₀.sp + BitVec.ofNat 32 4)) 32 = stackArg s₀ 1 := fun v =>
    readW_writeW_arg hp _ v (i := 1) (by decide) (by decide)
  have e2 : ∀ v v', ((s₀.mem.writeW (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 168)) v).writeW
      (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 172)) v').readW
      (State.addr (s₀.sp + BitVec.ofNat 32 8)) 32 = stackArg s₀ 2 := fun v v' => by
    rw [readW_writeW_arg hp _ v' (i := 2) (by decide) (by decide),
      readW_writeW_arg hp _ v (i := 2) (by decide) (by decide)]; rfl
  have w : ∀ d, d + 4 ≤ 512 → InRegions s₀.wr (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 d)) 4 :=
    fun d hd => hp.out_scr hd
  have w168 := w 168 (by decide); have w172 := w 172 (by decide); have w128 := w 128 (by decide)
  have w132 := w 132 (by decide); have w136 := w 136 (by decide); have w140 := w 140 (by decide)
  have w144 := w 144 (by decide); have w148 := w 148 (by decide); have w152 := w 152 (by decide)
  have w156 := w 156 (by decide); have w160 := w 160 (by decide); have w176 := w 176 (by decide)
  have w180 := w 180 (by decide); have w192 := w 192 (by decide); have w196 := w 196 (by decide)
  have w184 := w 184 (by decide); have w188 := w 188 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [setup, save, saved, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, ctrLo, ctrHi, zeroOff, flagOff,
    show 168 + 4 = 172 from rfl, show 176 + 4 = 180 from rfl, show 192 + 4 = 196 from rfl,
    show 184 + 4 = 188 from rfl, runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, Op2.eval, State.load32, State.store32, subFlags,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.sp_setReg, a0, a1, a2, a3, e3, e0, e1, e2, w168, w172, w128, w132, w136, w140, w144, w148,
    w152, w156, w160, w176, w180, w192, w196, w184, w188,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rfl

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch space. -/
def Saved (s₀ : State) (m : Mem) : Prop := ∀ p ∈ saved, m.readW (A (scp s₀) p.2) 32 = s₀.gpr p.1

theorem saved_off : ∀ p ∈ saved, 128 ≤ p.2 ∧ p.2 + 4 ≤ 164 := by decide

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = stp s₀
  r3 : s.gpr .r3 = scp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [stR (stp s₀), scrR (scp s₀)] s₀.mem s.mem
  state : Spec.Blake2.stateAt 64 s.mem (State.addr (stp s₀)) =
    Spec.Blake2.compressBlocks Spec.Blake2.b (H₀ s₀) s₀.mem (State.addr (bp s₀)) i (t₀ s₀) (fl s₀)
  saved : Saved s₀ s.mem
  lo : rd64 s.mem (scp s₀) ctrLo = BitVec.ofNat 64 (t₀ s₀ + i * 128)
  hi : s.mem.readW (A (scp s₀) ctrHi) 32 = BitVec.ofNat 32 ((t₀ s₀ + i * 128) / 2 ^ 64)
  hi' : s.mem.readW (A (scp s₀) (ctrHi + 4)) 32 = 0
  f : rd64 s.mem (scp s₀) flagOff = flagW 64 (fl s₀)
  z : rd64 s.mem (scp s₀) zeroOff = 0

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  r1 : s.gpr .r1 = blkAddr s₀ i
  r2 : s.gpr .r2 = BitVec.ofNat 32 (nb s₀ - i)

/-- The high 64 bits of the counter, from its two words. -/
theorem hi64 {H : Nat} (h : H < 2 ^ 32) : ((0 : BitVec 32) ++ BitVec.ofNat 32 H : BitVec 64) = BitVec.ofNat 64 H := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_shiftLeft,
    Nat.zero_or]
  omega

theorem ctr_bound {s₀ : State} {i : Nat} (hi : i ≤ nb s₀) : (t₀ s₀ + i * 128) / 2 ^ 64 < 2 ^ 32 := by
  have h1 : t₀ s₀ < 2 ^ 64 := (tArm s₀).isLt
  have h2 : nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  omega

theorem compressBlocks_succ' (H : HashValue 64) (m : Mem) (p : Addr) (i t : Nat) (f : Bool) :
    Spec.Blake2.compressBlocks Spec.Blake2.b H m p (i + 1) t f =
      Spec.Blake2.F Spec.Blake2.b (Spec.Blake2.compressBlocks Spec.Blake2.b H m p i t f)
        (Spec.Blake2.blockAt 64 m (p + BitVec.ofNat 64 (128 * i))) (t + i * 128) f :=
  Proof.Blake2.compressBlocks_succ _ _ _ _ _ _ _

theorem ctrMem_frame {s₀ : State} (hp : Pre s₀) (m : Mem) (N : Nat) :
    Frame [ctrR s₀] m (ctrMem m (scp s₀) N) := by
  have := hp.scr_fits
  have c : ∀ d, ctrLo ≤ d → d + 4 ≤ ctrLo + 12 → (ctrR s₀).Contains (A (scp s₀) d) (32 / 8) :=
    fun d h1 h2 => by
      rw [hp.scr_addr (by simp only [ctrLo] at h2; omega)]
      exact Offset.contains _ h1 (by omega) (by simp only [ctrLo]; omega)
  have m' := List.mem_singleton_self (ctrR s₀)
  exact (((Frame.refl _ _).writeW m' _ (c _ (by decide) (by decide))).writeW m' _
    (c _ (by decide) (by decide))).writeW m' _ (c _ (by decide) (by decide))

theorem ctrMem_lo {s₀ : State} (hp : Pre s₀) (m : Mem) (N : Nat) :
    rd64 (ctrMem m (scp s₀) N) (scp s₀) ctrLo = BitVec.ofNat 64 (N + 128) := by
  simp only [rd64, ctrMem, ctrLo, ctrHi, A]
  rw [readW_writeW_SA hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
    readW_writeW_SA hp _ _ (by decide) (by decide) (by decide),
    readW_writeW_SA hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, hi_append_lo]

theorem ctrMem_hi {s₀ : State} (m : Mem) (N : Nat) :
    (ctrMem m (scp s₀) N).readW (A (scp s₀) ctrHi) 32 = BitVec.ofNat 32 ((N + 128) / 2 ^ 64) := by
  simp only [ctrMem, Mem.readW_writeW_self32]

/-! ## One block -/

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have c := hp.ctx hL.r0 hL.r3 hL.wr
  have fitS := hp.st_fits
  have fitV := hp.scr_fits
  have fitB := hp.blk_fit hi
  set N := t₀ s₀ + i * 128 with hN
  set H := Spec.Blake2.compressBlocks Spec.Blake2.b (H₀ s₀) s₀.mem (State.addr (bp s₀)) i (t₀ s₀) (fl s₀)
    with hH
  set M := Spec.Blake2.blockAt 64 s₀.mem (State.addr (blkAddr s₀ i)) with hM
  have hb := ctr_bound (s₀ := s₀) (Nat.le_of_lt hi)
  have hHk : ∀ k (hk : k < 8), rd64 s.mem (stp s₀) (8 * k) = H[k] := fun k hk => by
    rw [← stateAt_get fitS _ hk, hL.state]
  -- Initialize the work vector.
  have hT : ∀ k < 8, rd64 s.mem (scp s₀) (tweak k) = tweakV N (fl s₀) k := fun k hk => by
    unfold tweak tweakV
    by_cases h4 : k = 4
    · simp only [h4, ite_true]; exact hL.lo
    by_cases h5 : k = 5
    · simp only [h5, ite_true, show (5 : Nat) ≠ 4 by decide, ite_false]
      have e1 := hL.hi
      have e2 := hL.hi'
      simp only [rd64, ctrHi, A] at e1 e2 ⊢
      rw [e1, e2, hi64 hb]
    by_cases h6 : k = 6
    · simp only [h6, ite_true, show (6 : Nat) ≠ 4 by decide, show (6 : Nat) ≠ 5 by decide, ite_false]
      exact hL.f
    simp only [h4, h5, h6, ite_false]; exact hL.z
  refine WP.seq (WP.mono (init_ok c _ hT) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, v₁⟩ => ?_)
  have hv : ∀ k (hk : k < 16), rd64 s₁.mem (scp s₀) (8 * k) = (initV Spec.Blake2.b H N (fl s₀))[k] :=
    fun k hk => by
      rw [v₁ k hk, initV_get]
      by_cases h8 : k < 8
      · simp only [h8, ↓reduceIte, ↓reduceDIte]; exact hHk k h8
      · simp only [h8, ↓reduceIte, ↓reduceDIte]
  -- The rounds.
  have fr₁ : Frame [stR (stp s₀), scrR (scp s₀)] s₀.mem s₁.mem :=
    hL.frame.trans (f₁.sub fun r hr => ⟨scrR (scp s₀), by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩)
  have rc : RCtx (scp s₀) (blkAddr s₀ i) M s₁ :=
    ⟨by rw [g₁ _ (by decide), hL.r3], by rw [g₁ _ (by decide), hL.r1], by omega, fitB,
      fun o ho => by rw [wr₁]; exact c.wV o (by omega),
      by rw [rd₁, wr₁, hL.rd, hL.wr]; exact hp.blk_rd hi,
      (hp.blk_scr.sub_left (hp.blk_sub hi)).sub_right (Region.sub_prefix (by omega)),
      fun j hj => by rw [hp.blk_frame fr₁ hi (by omega), hM, blockAt_get fitB _ hj]⟩
  refine WP.seq (WP.mono (rounds_ok rc hv 12) fun s₂ h₂ => ?_)
  -- XOR into the state.
  have c₂ : Ctx (stp s₀) (scp s₀) s₂ :=
    c.of_eq ((h₂.gpr _ (by decide)).trans (g₁ _ (by decide)))
      ((h₂.gpr _ (by decide)).trans (g₁ _ (by decide))) (h₂.wr.trans wr₁)
  rw [WP.block_append_iff]
  refine WP.mono (fin_ok c₂ 8 (Nat.le_refl _)) fun s₃ h₃ => ?_
  have f₁₂ : Frame [workR (scp s₀)] s.mem s₂.mem := f₁.trans h₂.frame
  have hctr : ∀ {m m' : Mem}, Frame [workR (scp s₀)] m m' ∨ Frame [stR (stp s₀)] m m' ∨
      Frame [ctrR s₀] m m' → ∀ d, 128 ≤ d → d + 4 ≤ 512 → (d + 4 ≤ ctrLo ∨ ctrLo + 12 ≤ d) →
      m'.readW (A (scp s₀) d) 32 = m.readW (A (scp s₀) d) 32 :=
    fun hf d h1 h2 h3 => hp.scr_frame h1 h2 h3 hf
  have hctr3 : ∀ d, 128 ≤ d → d + 4 ≤ 512 →
      s₃.mem.readW (A (scp s₀) d) 32 = s.mem.readW (A (scp s₀) d) 32 := fun d h1 h2 => by
    have e₁ : s₂.mem.readW (A (scp s₀) d) 32 = s.mem.readW (A (scp s₀) d) 32 := by
      rw [hp.scr_addr (by omega)]
      exact readW_frame f₁₂ (by
        simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint_base _ h1 (by omega))
    rw [← e₁, hp.scr_addr (by omega)]
    exact readW_frame h₃.frame (by
      simp only [List.mem_singleton, forall_eq]
      exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by omega)))
  have hlo₃ : rd64 s₃.mem (scp s₀) ctrLo = BitVec.ofNat 64 N := by
    simp only [rd64]; rw [hctr3 _ (by decide) (by decide), hctr3 _ (by decide) (by decide)]
    exact hL.lo
  have hhi₃ : s₃.mem.readW (A (scp s₀) ctrHi) 32 = BitVec.ofNat 32 (N / 2 ^ 64) := by
    rw [hctr3 _ (by decide) (by decide)]; exact hL.hi
  have c₃ : Ctx (stp s₀) (scp s₀) s₃ := c₂.of_eq (h₃.gpr _ (by decide)) (h₃.gpr _ (by decide)) h₃.wr
  refine advance_ok c₃.r3 c₃.wV hlo₃ hhi₃ |>.mono fun s₄ ⟨r1₄, r2₄, z₄, g₄, m₄, rd₄, wr₄, sp₄⟩ => ?_
  -- Registers
  have g₃ : ∀ r, r ∉ [Reg.r1, .r2, .r4, .r5, .r6, .r7] → r ∉ gRegs → s₄.gpr r = s.gpr r :=
    fun r ha hb => by
      have e₃ : r ∉ [Reg.r4, .r5, .r6, .r7, .r8, .r9] := fun h => hb
        ((by decide : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9], r ∈ gRegs) r h)
      have e₁ : r ∉ [Reg.r4, .r5, .r6, .r7] := fun h => hb
        ((by decide : ∀ r ∈ [Reg.r4, .r5, .r6, .r7], r ∈ gRegs) r h)
      rw [g₄ r ha, h₃.gpr r e₃, h₂.gpr r hb, g₁ r e₁]
  have hrd : s₄.rd = s₀.rd := by rw [rd₄, h₃.rd, h₂.rd, rd₁, hL.rd]
  have hwr : s₄.wr = s₀.wr := by rw [wr₄, h₃.wr, h₂.wr, wr₁, hL.wr]
  have hsp : s₄.sp = s₀.sp := by rw [sp₄, h₃.sp, h₂.sp, sp₁, hL.sp]
  -- Memory
  have hsub : ∀ r ∈ [workR (scp s₀)], ∃ r' ∈ [stR (stp s₀), scrR (scp s₀)], Region.Sub r r' :=
    fun r hr => ⟨scrR (scp s₀), by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  have hsubC : ∀ r ∈ [ctrR s₀], ∃ r' ∈ [stR (stp s₀), scrR (scp s₀)], Region.Sub r r' :=
    fun r hr => ⟨scrR (scp s₀), by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by simp only [ctrLo]; omega)⟩
  have hframe : Frame [stR (stp s₀), scrR (scp s₀)] s₀.mem s₄.mem := by
    rw [m₄]
    exact ((fr₁.trans (h₂.frame.sub hsub)).trans (h₃.frame.mono (by simp))).trans
      ((ctrMem_frame hp _ N).sub hsubC)
  have hc4 : ∀ d, 128 ≤ d → d + 4 ≤ 512 → (d + 4 ≤ ctrLo ∨ ctrLo + 12 ≤ d) →
      s₄.mem.readW (A (scp s₀) d) 32 = s.mem.readW (A (scp s₀) d) 32 := fun d h1 h2 h3 => by
    rw [m₄, hp.scr_frame h1 h2 h3 (.inr (.inr (ctrMem_frame hp _ N))), hctr3 d h1 h2]
  have hstate : Spec.Blake2.stateAt 64 s₄.mem (State.addr (stp s₀)) =
      Spec.Blake2.F Spec.Blake2.b H M N (fl s₀) := by
    rw [m₄]
    refine stateAt_ext fitS fun k hk => ?_
    have hcs : Frame [scrR (scp s₀)] s₃.mem (ctrMem s₃.mem (scp s₀) N) :=
      (ctrMem_frame hp _ N).sub fun r hr => ⟨scrR (scp s₀), by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by simp only [ctrLo]; omega)⟩
    have hws : Frame [scrR (scp s₀)] s.mem s₂.mem := f₁₂.sub fun r hr => ⟨scrR (scp s₀), by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
    rw [hp.st_frame hcs hk, h₃.done k hk, hp.st_frame hws hk, hHk k hk, h₂.vars k (by omega),
      show 64 + 8 * k = 8 * (k + 8) by omega, h₂.vars (k + 8) (by omega), F_eq, Vector.getElem_ofFn]
    rfl
  have hcommon : Common s₀ (i + 1) s₄ := by
    refine ⟨by rw [g₃ _ (by decide) (by decide), hL.r0], by rw [g₃ _ (by decide) (by decide), hL.r3],
      hrd, hwr, hsp, hframe, ?_, fun p hp' => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hstate, compressBlocks_succ', ← hH, hM, hp.blk_addr hi]
    · have := saved_off p hp'
      rw [hc4 _ this.1 (by omega) (by simp only [ctrLo]; omega)]; exact hL.saved p hp'
    · rw [m₄, ctrMem_lo hp, show N + 128 = t₀ s₀ + (i + 1) * 128 by rw [hN, Nat.add_mul, Nat.one_mul, Nat.add_assoc]]
    · rw [m₄, ctrMem_hi, show N + 128 = t₀ s₀ + (i + 1) * 128 by rw [hN, Nat.add_mul, Nat.one_mul, Nat.add_assoc]]
    · rw [hc4 _ (by decide) (by decide) (by decide)]; exact hL.hi'
    · simp only [rd64]; rw [hc4 _ (by decide) (by decide) (by decide), hc4 _ (by decide) (by decide) (by decide)]
      exact hL.f
    · simp only [rd64]; rw [hc4 _ (by decide) (by decide) (by decide), hc4 _ (by decide) (by decide) (by decide)]
      exact hL.z
  have hnb : nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  have hr2 : s₃.gpr .r2 - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [h₃.gpr _ (by decide), h₂.gpr _ (by decide), g₁ _ (by decide), hL.r2,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hev : eval .ne s₄ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    rw [eval_ne, z₄, hr2]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon with r1 := ?_, r2 := ?_ }⟩
    · rw [r1₄, h₃.gpr _ (by decide), h₂.gpr _ (by decide), g₁ _ (by decide), hL.r1]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (128 : BitVec _) = BitVec.ofNat _ 128 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [r2₄, hr2]

/-! ## The prologue's memory -/

theorem flag_eq (l : BitVec 32) : (flag32 l ++ flag32 l : BitVec 64) = flagW 64 (l != 0) := by
  by_cases h : l = 0
  · subst h; decide
  · have h0 : l.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have hm : (0 - l ||| l).msb = true := by
      rw [BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide, BitVec.toNat_sub]
      have := l.isLt
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

theorem setupMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scrR (scp s₀)] s₀.mem (setupMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 512 → (scrR (scp s₀)).Contains (SA s₀ d) (32 / 8) :=
    fun d hd => by rw [SA_eq hp (by omega)]; exact contains_offset hd (by have := hp.scr_fits; omega)
  have m := List.mem_singleton_self (scrR (scp s₀))
  have key : ∀ (l : List (Nat × BitVec 32)), (∀ p ∈ l, p.1 + 4 ≤ 512) → ∀ m₀ : Mem,
      Frame [scrR (scp s₀)] s₀.mem m₀ →
      Frame [scrR (scp s₀)] s₀.mem (l.foldl (fun m p => m.writeW (SA s₀ p.1) p.2) m₀) := by
    intro l
    induction l with
    | nil => intro _ m₀ h; exact h
    | cons p ps ih =>
      intro hl m₀ h
      exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _
        (h.writeW m _ (c p.1 (hl p (List.mem_cons_self))))
  have hl : ∀ p ∈ setupWrites s₀, p.1 + 4 ≤ 512 := by
    intro p hp
    simp only [setupWrites, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> exact Nat.le_of_ble_eq_true rfl
  exact key _ hl _ (Frame.refl _ _)

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hm : s₁.mem = setupMem s₀)
    (h0 : s₁.gpr .r0 = s₀.gpr .r0) (h3 : s₁.gpr .r3 = scp s₀) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) : Common s₀ 0 s₁ := by
  have hf := setupMem_frame hp
  have ht := (tArm s₀).isLt
  refine ⟨h0, h3, hrd, hwr, hsp, by rw [hm]; exact hf.mono (by simp), ?_, fun p hp' => ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · refine stateAt_ext hp.st_fits fun k hk => ?_
    rw [hm, hp.st_frame hf hk, ← stateAt_get hp.st_fits _ hk]
    rfl
  all_goals simp only [hm, rd64, A, ctrLo, ctrHi, flagOff, zeroOff]
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, Mem.readW_writeW_self32,
      readW_writeW_SA hp]
  · simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, Mem.readW_writeW_self32,
      readW_writeW_SA hp]
    show tArm s₀ = _
    rw [Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, Mem.readW_writeW_self32,
      readW_writeW_SA hp]
    rw [Nat.zero_mul, Nat.add_zero, Nat.div_eq_of_lt ht]; rfl
  · simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, Mem.readW_writeW_self32,
      readW_writeW_SA hp]
  · simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, Mem.readW_writeW_self32,
      readW_writeW_SA hp]
    exact flag_eq _
  · simp (config := {decide := true}) only [setupMem, setupWrites, List.foldl, Mem.readW_writeW_self32,
      readW_writeW_SA hp]

/-! ## The epilogue -/

set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ (compressArm Spec.Blake2.b).post s₀ s' := by
  have i : ∀ d, d + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 d)) 4 :=
    fun d hd => by rw [hc.rd, hc.wr]; exact hp.in_scr hd
  have i0 := i 128 (by decide); have i1 := i 132 (by decide); have i2 := i 136 (by decide)
  have i3 := i 140 (by decide); have i4 := i 144 (by decide); have i5 := i 148 (by decide)
  have i6 := i 152 (by decide); have i7 := i 156 (by decide); have i8 := i 160 (by decide)
  have g : ∀ p ∈ saved, s.mem.readW (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 p.2)) 32 = s₀.gpr p.1 :=
    hc.saved
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := g
  have hstate := hc.state
  have hr3 := hc.r3
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restore, saved, List.map_cons, List.map_nil, runBlock_cons,
    runStep_some, runBlock_nil, exec, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, State.load32, hr3, i0, i1, i2, i3, i4, i5, i6, i7, i8, ite_true, ite_false,
    g0, g1, g2, g3, g4, g5, g6, g7, g8, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, hstate⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Blake2.Arm.B.compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ (compressArm Spec.Blake2.b).post s₀ s' := by
  unfold Impl.Blake2.Arm.B.compress
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨m₁, g₁, r3₁, z₁, rd₁, wr₁, sp₁⟩ => ?_)
  have hc₀ := common_zero hp m₁ (g₁ _ (by decide)) r3₁ rd₁ wr₁ sp₁
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  refine WP.ite (s₀.gpr .r2 - 0 == 0) (by rw [← z₁]; rfl) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        r1 := by rw [g₁ _ (by decide)]; simp [blkAddr]
        r2 := by rw [g₁ _ (by decide)]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-! ## Verified -/

/-- The initial taint: `r0`–`r2` are public, and so are the 16 bytes of stack
arguments. -/
def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2], flags := false, argLen := 16 }

theorem argByte_eq {s : State} (hsp : s.sp.toNat + 16 ≤ 2 ^ 32) {k : Nat} (hk : k < 16) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

theorem agree₀ {s₁ s₂ : State} (h₁ : (compressArm Spec.Blake2.b).pre s₁)
    (h₂ : (compressArm Spec.Blake2.b).pre s₂) (hpub : (compressArm Spec.Blake2.b).pub s₁ s₂) :
    VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, a0, a1, a2, a3⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => (h rfl).elim, ⟨fun h => (h rfl).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hp₁.sp_fits, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩,
    ⟨fun h => (h rfl).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hp₂.sp_fits, ?_⟩,
      fun _ h => (List.not_mem_nil h).elim⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · have e : (⟨State.addr s₁.sp, 16⟩ : Region) = argR s₁ := by simp [stackArgAddr]
    simp only [τ₀, e, hp₁.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp₁.a_st
    · exact hp₁.a_scr
  · have e : (⟨State.addr s₂.sp, 16⟩ : Region) = argR s₂ := by simp [stackArgAddr]
    simp only [τ₀, e, hp₂.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp₂.a_st
    · exact hp₂.a_scr
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
  wr := [⟨0x1000, 64⟩, ⟨0, 512⟩]

/-- The proof, against the ARMv7 contract the streaming functions use. -/
theorem compress_verified' :
    Verified Arm.target Impl.Blake2.Arm.B.compress (compressArm Spec.Blake2.b) := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub)
      (by taint_decide)
  · refine ⟨sat, rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
    exact Region.disjoint_of_sep (by decide)

theorem compress_implies :
    (compressArm Spec.Blake2.b).Implies (Spec.Blake2.compressBContract Arm.abi) := by
  sig_implies [Spec.Blake2.compressBContract, Spec.Blake2.compressBSig, compressArm, tArm, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Blake2.blockBytes]
    [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat

/-- The proof, against the shared contract of `Spec/Blake2/Contract.lean`. -/
theorem compress_verified :
    Verified Arm.target Impl.Blake2.Arm.B.compress (Spec.Blake2.compressBContract Arm.abi) :=
  compress_verified'.of_implies compress_implies

end VG.Proof.Blake2.ArmB
