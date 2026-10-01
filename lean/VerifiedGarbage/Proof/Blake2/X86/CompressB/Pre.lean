import VerifiedGarbage.Proof.Blake2.X86.CompressB.Rounds
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# BLAKE2b compression function on x86 (32-bit): the precondition

Untrusted: everything here is checked by Lean. The facts `compressX86.pre`
gives (`Pre`), and the addresses and regions the code uses.
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86 VG.Impl.Blake2.X86.CompressB
open VG.Spec.Blake2 (HashValue Block stateAt blockAt)
open VG.Proof.Sha512.X86 (Acc rd64 mem_rd)
open VG.Proof.Sha256.X86.Stream (contains_addr sub_offset)

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
/-- The offset counter of the first block. -/
abbrev t₀ : Nat := (arg s₀ 4 ++ arg s₀ 3).toNat
/-- The final block flag. -/
abbrev fl : Bool := arg s₀ 5 != 0
abbrev scr : BitVec 32 := arg s₀ 6
abbrev stR : Region := ⟨(st s₀).setWidth 64, 64⟩
abbrev blR : Region := ⟨(bp s₀).setWidth 64, 128 * nb s₀⟩
abbrev scrR : Region := ⟨(scr s₀).setWidth 64, 512⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 28⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : HashValue 64 := stateAt 64 s₀.mem ((st s₀).setWidth 64)

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (128 * i)

/-- Block `i`, as `compressBlocks` reads it. -/
abbrev blk (i : Nat) : Block 64 :=
  blockAt 64 s₀.mem ((bp s₀).setWidth 64 + BitVec.ofNat 64 (Spec.Blake2.blockBytes 64 * i))

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
  st_fits : (st s₀).toNat + 64 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 128 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 512 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 32 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : compressX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem addr_ofNat {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    addr x d = x.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem acc {s : State} (hw : s.wr = s₀.wr) : Acc s.wr (scr s₀) 512 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [hw, hp.wr]; simp) hp.scr_fits

theorem accS {s : State} (hw : s.wr = s₀.wr) : Acc s.wr (st s₀) 64 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [hw, hp.wr]; simp) hp.st_fits

theorem in_scr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 512) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  mem_rd (hp.acc hw d hd)

theorem in_st {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 64) :
    InRegions (s.rd ++ s.wr) (addr (st s₀) d) 4 :=
  mem_rd (hp.accS hw d hd)

theorem argAddr_eq {d : Nat} (hd : d < 32) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.esp_fits; omega)

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 32) :
    (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  show (⟨addr (esp₀ s₀) 4, 28⟩ : Region).Contains _ _
  rw [hp.argAddr_eq (by omega), hp.argAddr_eq (by omega)]
  exact Offset.contains _ hd (by omega) (by omega)

theorem in_arg {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : 4 ≤ d)
    (hd' : d + 4 ≤ 32) : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [hrd, hp.rd], hp.arg_contains hd hd'⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  show Region.Sub ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩ ⟨addr (esp₀ s₀) 4, 28⟩
  rw [hp.argAddr_eq (by omega), hp.argAddr_eq (by omega)]
  exact Offset.sub _ (by omega) (by omega)

/-- The arguments are unchanged while only the state and the scratch buffer are written. -/
theorem arg_frame {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) {i : Nat} (hi : i < 7) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.arg_st.sub_left (hp.arg_sub hi), hp.arg_scr.sub_left (hp.arg_sub hi)⟩

theorem blk_toNat {i : Nat} (hi : i < nb s₀) :
    (blkAddr s₀ i).toNat = (bp s₀).toNat + 128 * i := by
  have := hp.blk_fits
  simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 128 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blk_fit {i : Nat} (hi : i < nb s₀) : (blkAddr s₀ i).toNat + 128 ≤ 2 ^ 32 := by
  have := hp.blk_fits; rw [hp.blk_toNat hi]; omega

theorem blk_addr {i : Nat} (hi : i < nb s₀) :
    (blkAddr s₀ i).setWidth 64 = (bp s₀).setWidth 64 + BitVec.ofNat 64 (128 * i) :=
  addr_eq (x := bp s₀) (k := 128 * i) (by have := hp.blk_fits; omega)

theorem blk_sub {i : Nat} (hi : i < nb s₀) :
    Region.Sub ⟨(blkAddr s₀ i).setWidth 64, 128⟩ (blR s₀) := by
  have := hp.blk_fits
  rw [hp.blk_addr hi]; exact sub_offset (by omega) (by omega)

theorem blk_rd {i : Nat} (hi : i < nb s₀) {o : Nat} (ho : o + 4 ≤ 128) :
    InRegions (s₀.rd ++ s₀.wr) (addr (blkAddr s₀ i) o) 4 := by
  refine ⟨blR s₀, by simp [hp.rd], ?_⟩
  rw [show addr (blkAddr s₀ i) o = addr (bp s₀) (128 * i + o) by
    simp only [addr, blkAddr, BitVec.add_assoc, BitVec.ofNat_add]]
  exact contains_addr (by have : i + 1 ≤ nb s₀ := hi; omega) (by omega) hp.blk_fits

theorem blk_disj {i : Nat} (hi : i < nb s₀) :
    ∀ r ∈ [stR s₀, scrR s₀], Region.Disjoint ⟨(blkAddr s₀ i).setWidth 64, 128⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.blk_st.sub_left (hp.blk_sub hi), hp.blk_scr.sub_left (hp.blk_sub hi)⟩

/-- The words of `scratch` from offset 256 on (the parameters and the saved
registers) are unchanged while only `scratch[0, 256)` or the state is written. -/
theorem high_frame {m m' : Mem}
    (hf : Frame [⟨(scr s₀).setWidth 64, 256⟩] m m' ∨ Frame [stR s₀] m m') {d : Nat}
    (hd : 256 ≤ d) (hd' : d + 4 ≤ 512) :
    m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  have hc : (⟨addr (scr s₀) d, 4⟩ : Region).Contains (addr (scr s₀) d) (32 / 8) :=
    Region.contains_self _ _
  have := hp.scr_fits
  rcases hf with hf | hf
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    rw [addr_eq (by omega)]
    exact Offset.disjoint_base _ hd (by omega)
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    refine Region.Disjoint.sub_left hp.st_scr.symm ?_
    rw [addr_eq (by omega)]
    exact Offset.sub_base _ (by omega)

theorem high_frame64 {m m' : Mem}
    (hf : Frame [⟨(scr s₀).setWidth 64, 256⟩] m m' ∨ Frame [stR s₀] m m') {d : Nat}
    (hd : 256 ≤ d) (hd' : d + 8 ≤ 512) :
    rd64 m' (scr s₀) d = rd64 m (scr s₀) d := by
  simp only [rd64]
  rw [hp.high_frame hf hd (by omega), hp.high_frame hf (by omega) hd']

/-- The state's words are unchanged while only `scratch` is written. -/
theorem st_frame {m m' : Mem} (hf : Frame [scrR s₀] m m') {d : Nat} (hd : d + 4 ≤ 64) :
    m'.readW (addr (st s₀) d) 32 = m.readW (addr (st s₀) d) 32 := by
  refine hf.readW (contains_addr (len := 64) hd (by omega) hp.st_fits) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  exact hp.st_scr

end Pre

end VG.Proof.Blake2.X86.CompressB
