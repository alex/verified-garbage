import VerifiedGarbage.Proof.Blake2.X86.CompressS.Rounds
import VerifiedGarbage.Proof.Blake2.X86.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# BLAKE2s on x86 (32-bit): the compression function's precondition

Untrusted: everything here is checked by Lean. `Pre` unpacks the
precondition of `compressX86 Spec.Blake2.s`; its lemmas locate the words the
code reads and writes. Also `V0` and `F_eq`: `F` in the order of the code.
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86 VG.X86.Wp
open VG.Spec.Blake2 (Work Block HashValue blockBytes stateAt blockAt compressBlocks)
open VG.Impl.Blake2.X86.CompressS
open VG.Proof.MdStream.X86 (contains_addr readW_writeW_addr)

/-! ## The compression function, in the order of the code -/

/-- The work vector before the rounds (RFC 7693 §3.2). -/
def V0 (h : HashValue 32) (t : Nat) (f : Bool) : Work 32 :=
  let v : Work 32 := h ++ Spec.Blake2.s.IV
  let v := v.set 12 (v[12] ^^^ BitVec.ofNat 32 t)
  let v := v.set 13 (v[13] ^^^ BitVec.ofNat 32 (t / 2 ^ 32))
  if f then v.set 14 (v[14] ^^^ BitVec.allOnes 32) else v

theorem F_eq (h : HashValue 32) (m : Block 32) (t : Nat) (f : Bool) :
    Spec.Blake2.F Spec.Blake2.s h m t f = Vector.ofFn fun i : Fin 8 =>
      h[i] ^^^ ((List.range 10).foldl (Spec.Blake2.round Spec.Blake2.s m) (V0 h t f))[i] ^^^
        ((List.range 10).foldl (Spec.Blake2.round Spec.Blake2.s m) (V0 h t f))[i.val + 8] := rfl

/-- The final block flag as a word. -/
def flagW (f : Bool) : BitVec 32 := if f then BitVec.allOnes 32 else 0

theorem V0_get (h : HashValue 32) (t : Nat) (f : Bool) (k : Nat) (hk : k < 16) : (V0 h t f)[k] =
    if hk8 : k < 8 then h[k] else if k = 12 then Spec.Blake2.s.IV[4] ^^^ BitVec.ofNat 32 t
    else if k = 13 then Spec.Blake2.s.IV[5] ^^^ BitVec.ofNat 32 (t / 2 ^ 32)
    else if k = 14 then Spec.Blake2.s.IV[6] ^^^ flagW f else Spec.Blake2.s.IV[k - 8]'(by omega) := by
  have base : ((h ++ Spec.Blake2.s.IV : Work 32))[k] =
      if hk8 : k < 8 then h[k] else Spec.Blake2.s.IV[k - 8]'(by omega) := by
    simp only [Vector.getElem_append]
  have e12 : (h ++ Spec.Blake2.s.IV : Work 32)[12] = Spec.Blake2.s.IV[4] := by
    simp only [Vector.getElem_append]; rfl
  have e13 : (h ++ Spec.Blake2.s.IV : Work 32)[13] = Spec.Blake2.s.IV[5] := by
    simp only [Vector.getElem_append]; rfl
  have e14 : (h ++ Spec.Blake2.s.IV : Work 32)[14] = Spec.Blake2.s.IV[6] := by
    simp only [Vector.getElem_append]; rfl
  by_cases k14 : k = 14
  · subst k14; cases f <;> simp [V0, flagW, e14]
  by_cases k13 : k = 13
  · subst k13; cases f <;> simp [V0, e13]
  by_cases k12 : k = 12
  · subst k12; cases f <;> simp [V0, e12]
  have n14 : ¬14 = k := Ne.symm k14
  have n13 : ¬13 = k := Ne.symm k13
  have n12 : ¬12 = k := Ne.symm k12
  cases f <;> simp only [V0, Vector.getElem_set, n14, n13, n12, k14, k13, k12, ite_false, base,
    Bool.false_eq_true, ite_true]

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
abbrev t₀ : Nat := (arg s₀ 4 ++ arg s₀ 3).toNat
abbrev fl : Bool := arg s₀ 5 != 0
abbrev scr : BitVec 32 := arg s₀ 6
abbrev stR : Region := ⟨(st s₀).setWidth 64, 32⟩
abbrev blR : Region := ⟨(bp s₀).setWidth 64, 64 * nb s₀⟩
abbrev scrR : Region := ⟨(scr s₀).setWidth 64, 512⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 28⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : HashValue 32 := stateAt 32 s₀.mem ((st s₀).setWidth 64)

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (64 * i)

/-- Block `i`, as `compressBlocks` reads it. -/
abbrev blk (i : Nat) : Block 32 :=
  blockAt 32 s₀.mem ((bp s₀).setWidth 64 + BitVec.ofNat 64 (blockBytes 32 * i))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀, argR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  arg_st : (argR s₀).Disjoint (stR s₀)
  arg_scr : (argR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  st_fits : (st s₀).toNat + 32 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 64 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 512 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 32 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : (Proof.Blake2.compressX86 Spec.Blake2.s).pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The callee-saved registers are saved in `scratch`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (addr (scr s₀) 80) 32 = s₀.gpr .ebx ∧ m.readW (addr (scr s₀) 84) 32 = s₀.gpr .esi ∧
  m.readW (addr (scr s₀) 88) 32 = s₀.gpr .edi

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem in_st {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 32) :
    InRegions s.wr (addr (st s₀) d) 4 :=
  ⟨stR s₀, by simp [hw, h.wr], contains_addr hd (by omega) h.st_fits⟩

theorem in_scr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 512) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scrR s₀, by simp [hw, h.wr], contains_addr hd (by omega) h.scr_fits⟩

theorem argAddr_eq {d : Nat} (hd : d < 32) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.esp_fits; omega)

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 32) :
    (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  show (⟨addr (esp₀ s₀) 4, 28⟩ : Region).Contains _ _
  rw [h.argAddr_eq (by omega), h.argAddr_eq (by omega)]
  exact Offset.contains _ hd (by omega) (by omega)

theorem in_arg {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 32) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [hrd, h.rd], h.arg_contains hd hd'⟩

theorem arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  show Region.Sub ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩ ⟨addr (esp₀ s₀) 4, 28⟩
  rw [h.argAddr_eq (by omega), h.argAddr_eq (by omega)]
  exact Offset.sub _ (by omega) (by omega)

/-- The arguments are unchanged while only the state and `scratch` are written. -/
theorem arg_frame {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) {i : Nat} (hi : i < 7) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.arg_st.sub_left (h.arg_sub hi), h.arg_scr.sub_left (h.arg_sub hi)⟩

theorem blk_toNat {i : Nat} (hi : i < nb s₀) : (blkAddr s₀ i).toNat = (bp s₀).toNat + 64 * i := by
  have := h.blk_fits
  simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 64 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blk_word {i : Nat} (hi : i < nb s₀) {o : Nat} (ho : o + 4 ≤ 64) :
    addr (blkAddr s₀ i) o = (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i + o) := by
  rw [show addr (blkAddr s₀ i) o = addr (bp s₀) (64 * i + o) by
    simp only [addr, blkAddr, BitVec.add_assoc, BitVec.ofNat_add]]
  exact addr_eq (by have := h.blk_fits; have : i + 1 ≤ nb s₀ := hi; omega)

theorem blk_contains {i : Nat} (hi : i < nb s₀) {o : Nat} (ho : o + 4 ≤ 64) :
    (blR s₀).Contains (addr (blkAddr s₀ i) o) 4 := by
  rw [h.blk_word hi ho]
  have := h.blk_fits
  exact Offset.contains_base _ (by have : i + 1 ≤ nb s₀ := hi; omega) (by omega)

theorem scr_contains {d : Nat} (hd : d + 4 ≤ 512) : (scrR s₀).Contains (addr (scr s₀) d) 4 :=
  contains_addr hd (by omega) h.scr_fits

theorem st_contains {d : Nat} (hd : d + 4 ≤ 32) : (stR s₀).Contains (addr (st s₀) d) 4 :=
  contains_addr hd (by omega) h.st_fits

/-- What the rounds of block `i` need. -/
theorem ctx {i : Nat} (hi : i < nb s₀) : Ctx (scr s₀) (blkAddr s₀ i) s₀.rd s₀.wr where
  fit := by have := h.scr_fits; omega
  wr k hk := h.in_scr rfl (by simp only [vOff]; omega)
  rd j hj := ⟨blR s₀, by simp [h.rd], h.blk_contains hi (by omega)⟩
  sep k hk j hj := h.blk_scr.sep (h.blk_contains hi (by omega)) (h.scr_contains (by simp only [vOff]; omega))

/-- Block `i`, while only the state and `scratch` are written. -/
theorem msg {i : Nat} (hi : i < nb s₀) {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) :
    Msg (blkAddr s₀ i) (blk s₀ i) m := by
  intro j
  have hj := j.isLt
  rw [hf.readW (r := blR s₀) (h.blk_contains hi (by omega)) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨h.blk_st, h.blk_scr⟩) (by decide),
    h.blk_word hi (by omega)]
  have e := Proof.Blake2.blockAt_word (w := 32) s₀.mem
    ((bp s₀).setWidth 64 + BitVec.ofNat 64 (blockBytes 32 * i)) j.1 hj
  rw [show blk s₀ i j = blk s₀ i ⟨j.1, hj⟩ from rfl, blk, e, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rfl

/-- Word `k` of the state. -/
theorem stateAt_get (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt 32 m ((st s₀).setWidth 64))[k] = m.readW (addr (st s₀) (4 * k)) 32 := by
  simp only [stateAt, Vector.getElem_ofFn]
  rw [addr_eq (by have := h.st_fits; omega)]

theorem stateAt_ext {m : Mem} {H : HashValue 32}
    (hH : ∀ k (hk : k < 8), m.readW (addr (st s₀) (4 * k)) 32 = H[k]) :
    stateAt 32 m ((st s₀).setWidth 64) = H := by
  ext k hk
  rw [h.stateAt_get m hk, hH k hk]

/-- `scratch` beyond the work vector is unchanged while only the work vector,
or the state, is written. -/
theorem high_frame {m m' : Mem} (hf : Frame [workR (scr s₀)] m m' ∨ Frame [stR s₀] m m') {d : Nat}
    (hd : 64 ≤ d) (hd' : d + 4 ≤ 512) :
    m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  have hc : (⟨addr (scr s₀) d, 4⟩ : Region).Contains (addr (scr s₀) d) (32 / 8) :=
    Region.contains_self _ _
  have := h.scr_fits
  rcases hf with hf | hf
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    rw [addr_eq (by omega)]
    exact Offset.disjoint_base _ hd (by omega)
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    refine Region.Disjoint.sub_left h.st_scr.symm ?_
    rw [addr_eq (by omega)]
    exact Offset.sub_base _ (by omega)

/-- The state is unchanged while only the work vector is written. -/
theorem st_frame {m m' : Mem} (hf : Frame [workR (scr s₀)] m m') {d : Nat} (hd : d + 4 ≤ 32) :
    m'.readW (addr (st s₀) d) 32 = m.readW (addr (st s₀) d) 32 := by
  refine hf.readW (r := stR s₀) (h.st_contains hd) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  exact h.st_scr.sub_right (Region.sub_prefix (by omega))

/-- The work vector is unchanged while only the state is written. -/
theorem work_frame {m m' : Mem} (hf : Frame [stR s₀] m m') {d : Nat} (hd : d + 4 ≤ 512) :
    m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  refine hf.readW (r := scrR s₀) (h.scr_contains hd) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  exact h.st_scr.symm

theorem saved_frame {m m' : Mem} (hs : Saved s₀ m)
    (hf : Frame [workR (scr s₀)] m m' ∨ Frame [stR s₀] m m') : Saved s₀ m' := by
  obtain ⟨h1, h2, h3⟩ := hs
  exact ⟨(h.high_frame hf (by omega) (by omega)).trans h1, (h.high_frame hf (by omega) (by omega)).trans h2,
    (h.high_frame hf (by omega) (by omega)).trans h3⟩

end Pre

end VG.Proof.Blake2.X86.CompressS
