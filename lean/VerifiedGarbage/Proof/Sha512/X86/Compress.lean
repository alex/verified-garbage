import VerifiedGarbage.Proof.Sha512.X86.Rounds
import VerifiedGarbage.Proof.Sha512.X86.Contract

/-!
# SHA-512 compression function on x86 (32-bit): the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha512.X86

open VG VG.X86 VG.Impl.Sha512.X86
open VG.Spec.Sha512 (HashValue Word Block W stateAt blockAt compress compressBlocks parseBlock)
open VG.Proof.Sha256.X86.Stream (contains_addr sub_offset Upd Mupd wp_store wp_addi wp_subi)
open VG.Proof.Sha512.Arm (readW64 lo_append hi_append)

/-! ## Memory -/

theorem cat44 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((b0 ++ b1 ++ b2 ++ b3 : BitVec 32) ++ (b4 ++ b5 ++ b6 ++ b7 : BitVec 32) : BitVec 64) =
      (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) := by
  simp only [BitVec.append_assoc, BitVec.cast_eq]

theorem add_one' (p : Addr) (a : Nat) : p + BitVec.ofNat 64 a + 1 = p + BitVec.ofNat 64 (a + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- A store, which leaves the registers and the flags alone. -/
theorem wp_storeF {s : State} {is : List Instr} {Q : State → Prop} {m : MemOp} {r : Reg} {a : Addr}
    (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : WP isa (.block is) { s with mem := s.mem.writeW a (s.gpr r) } Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine Proof.Sha256.X86.Stream.WP.cons ?_ k
  simp [exec, State.store32, ha, hout]

theorem stateAt_get {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt m (st.setWidth 64))[k] = rd64 m st (8 * k) := by
  simp only [stateAt, Vector.getElem_ofFn, rd64]
  rw [readW64, show st.setWidth 64 + BitVec.ofNat 64 (8 * k) + 4 =
      st.setWidth 64 + BitVec.ofNat 64 (8 * k + 4) by bv_omega,
    ← addr_eq (by omega), ← addr_eq (by omega)]

theorem stateAt_ext {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) {m : Mem} {H : HashValue}
    (h : ∀ k (hk : k < 8), rd64 m st (8 * k) = H[k]) : stateAt m (st.setWidth 64) = H := by
  ext k hk
  rw [stateAt_get hfit m hk, h k hk]

/-- `loadW` makes the block's words from its bytes. -/
theorem raw_block {bk : BitVec 32} (hfit : bk.toNat + 128 ≤ 2 ^ 32) (m : Mem) :
    Raw bk (blockAt m (bk.setWidth 64)) m := by
  intro j hj
  rw [W_lt _ hj]
  simp only [blockAt, parseBlock]
  rw [addr_eq (by omega), addr_eq (by omega), bswap_readW, bswap_readW]
  simp only [add_one', Nat.add_assoc]
  exact cat44 _ _ _ _ _ _ _ _

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (128 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

namespace Compress

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
abbrev scr : BitVec 32 := arg s₀ 3
abbrev stR : Region := ⟨(st s₀).setWidth 64, 64⟩
abbrev blR : Region := ⟨(bp s₀).setWidth 64, 128 * nb s₀⟩
abbrev scrR : Region := ⟨(scr s₀).setWidth 64, 224⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : HashValue := stateAt s₀.mem ((st s₀).setWidth 64)

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (128 * i)

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
  scr_fits : (scr s₀).toNat + 224 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 20 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha512.compressX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem ctx {s : State} (hesi : s.gpr .esi = scr s₀) (hw : s.wr = s₀.wr) : Ctx (scr s₀) s :=
  ⟨hesi, h.scr_fits, Acc.of_mem (by rw [hw, h.wr]; simp) h.scr_fits⟩

theorem accS {s : State} (hw : s.wr = s₀.wr) : Acc s.wr (st s₀) 64 :=
  Acc.of_mem (by rw [hw, h.wr]; simp) h.st_fits

theorem accV {s : State} (hw : s.wr = s₀.wr) : Acc s.wr (scr s₀) 224 :=
  Acc.of_mem (by rw [hw, h.wr]; simp) h.scr_fits

theorem in_st {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 64) :
    InRegions (s.rd ++ s.wr) (addr (st s₀) d) 4 :=
  mem_rd (h.accS hw d hd)

theorem in_scr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 224) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  mem_rd (h.accV hw d hd)

theorem argAddr_eq {d : Nat} (hd : d < 20) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.esp_fits; omega)

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  simp only [Region.Contains, argAddr]
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    h.argAddr_eq (by omega), h.argAddr_eq (by omega)]
  have := h.esp_fits
  generalize (esp₀ s₀).setWidth 64 = a
  rw [show a + BitVec.ofNat 64 d - (a + BitVec.ofNat 64 4) = BitVec.ofNat 64 (d - 4) by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem in_arg {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : 4 ≤ d)
    (hd' : d + 4 ≤ 20) : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [hrd, h.rd], h.arg_contains hd hd'⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 4) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  intro a ha
  simp only [Region.Contains, argAddr] at ha ⊢
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    h.argAddr_eq (by omega)]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (esp₀ s₀) (4 + 4 * i)
    from rfl, h.argAddr_eq (by omega)] at ha
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

/-- The arguments are unchanged while only the state and the scratch buffer are written. -/
theorem arg_frame {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.arg_st.sub_left (h.arg_sub hi), h.arg_scr.sub_left (h.arg_sub hi)⟩

theorem blk_toNat {i : Nat} (hi : i < nb s₀) : (blkAddr s₀ i).toNat = (bp s₀).toNat + 128 * i := by
  have := h.blk_fits
  simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 128 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blk_fit {i : Nat} (hi : i < nb s₀) : (blkAddr s₀ i).toNat + 128 ≤ 2 ^ 32 := by
  have := h.blk_fits; rw [h.blk_toNat hi]; omega

theorem blk_addr {i : Nat} (hi : i < nb s₀) :
    (blkAddr s₀ i).setWidth 64 = (bp s₀).setWidth 64 + BitVec.ofNat 64 (128 * i) :=
  addr_eq (x := bp s₀) (k := 128 * i) (by have := h.blk_fits; omega)

theorem blk_sub {i : Nat} (hi : i < nb s₀) : Region.Sub ⟨(blkAddr s₀ i).setWidth 64, 128⟩ (blR s₀) := by
  have := h.blk_fits
  rw [h.blk_addr hi]; exact sub_offset (by omega) (by omega)

theorem blk_rd {i : Nat} (hi : i < nb s₀) {o : Nat} (ho : o + 4 ≤ 128) :
    InRegions (s₀.rd ++ s₀.wr) (addr (blkAddr s₀ i) o) 4 := by
  refine ⟨blR s₀, by simp [h.rd], ?_⟩
  rw [show addr (blkAddr s₀ i) o = addr (bp s₀) (128 * i + o) by
    simp only [addr, blkAddr, BitVec.add_assoc, BitVec.ofNat_add]]
  exact contains_addr (by have : i + 1 ≤ nb s₀ := hi; omega) (by omega) h.blk_fits

theorem blk_disj {i : Nat} (hi : i < nb s₀) :
    ∀ r ∈ [stR s₀, scrR s₀], Region.Disjoint ⟨(blkAddr s₀ i).setWidth 64, 128⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.blk_st.sub_left (h.blk_sub hi), h.blk_scr.sub_left (h.blk_sub hi)⟩

theorem st_work : (stR s₀).Disjoint (workR (scr s₀)) :=
  h.st_scr.sub_right (Region.sub_prefix (by omega))

/-- The saved registers and the block count (at offsets `192 … 212` of the
scratch buffer) are unchanged while only the working variables and the
message schedule, or the hash value, are written. -/
theorem high_frame {m m' : Mem} (hf : Frame [workR (scr s₀)] m m' ∨ Frame [stR s₀] m m') {d : Nat}
    (hd : 192 ≤ d) (hd' : d + 4 ≤ 224) : m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  have hc : (⟨addr (scr s₀) d, 4⟩ : Region).Contains (addr (scr s₀) d) (32 / 8) :=
    Region.contains_self _ _
  have := h.scr_fits
  rcases hf with hf | hf
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    rw [addr_eq (by omega)] at h₁
    generalize (scr s₀).setWidth 64 = b at *
    bv_omega
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    refine Region.Disjoint.sub_left h.st_scr.symm fun a ha => ?_
    simp only [Region.Contains] at ha ⊢
    rw [addr_eq (by omega)] at ha
    generalize (scr s₀).setWidth 64 = b at *
    bv_omega
end Pre

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (addr (scr s₀) 192) 32 = s₀.gpr .ebx ∧ m.readW (addr (scr s₀) 196) 32 = s₀.gpr .esi ∧
  m.readW (addr (scr s₀) 200) 32 = s₀.gpr .edi ∧ m.readW (addr (scr s₀) 204) 32 = s₀.gpr .ebp

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem ((st s₀).setWidth 64) =
    compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  edi : s.gpr .edi = blkAddr s₀ i
  cnt : s.mem.readW (addr (scr s₀) cntOff) 32 = BitVec.ofNat 32 (nb s₀ - i)

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [workR (scr s₀)] m m' ∨ Frame [stR s₀] m m') : Saved s₀ m' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨(hp.high_frame hf (by omega) (by omega)).trans h1, (hp.high_frame hf (by omega) (by omega)).trans h2,
    (hp.high_frame hf (by omega) (by omega)).trans h3, (hp.high_frame hf (by omega) (by omega)).trans h4⟩

/-! ## Loading the working variables -/

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem loadH_ok (k : Nat) (hk : k < 8) {s : State} (hecx : s.gpr .ecx = st s₀)
    (hesi : s.gpr .esi = scr s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block (loadH k)) s fun s' =>
      Wrote [T] s s' (write64 s.mem (scr s₀) (8 * k) (rd64 s.mem (st s₀) (8 * k))) := by
  have fS := hp.st_fits
  have fV := hp.scr_fits
  have hA := (hp.ctx hesi hwr).wV
  simp only [loadH]
  refine wp_movS (readSrc_mem hecx (hp.in_st hwr (by omega))) fun s₁ u₁ => ?_
  refine wp_store (ea_of (by rw [u₁.other _ (by decide), hesi]) _) (by rw [u₁.wr]; exact hA _ (by omega))
    fun s₂ u₂ => ?_
  refine wp_movS (readSrc_mem (by rw [u₂.gpr, u₁.other _ (by decide), hecx])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hp.in_st hwr (by omega))) fun s₃ u₃ => ?_
  refine wp_store (ea_of (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hesi]) _)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hA _ (by omega)) fun s₄ u₄ => WP.block_nil ?_
  refine ⟨fun r hr => ?_, ?_, by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  · have hr' : r ≠ T := by simpa using hr
    rw [u₄.gpr, u₃.other _ hr', u₂.gpr, u₁.other _ hr']
  · have sep : Mem.Sep (addr (st s₀) (8 * k + 4)) (32 / 8) (addr (scr s₀) (8 * k)) (32 / 8) :=
      hp.st_scr.sep (contains_addr (by omega) (by omega) fS) (contains_addr (by omega) (by omega) fV)
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.mem, Mem.readW_writeW_sep sep (by decide), u₁.gpr, write64,
      lo_rd64, hi_rd64]

/-- After copying words `0 … n-1` of the hash value to the working variables. -/
structure LdInv (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ T → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  vars : ∀ k < n, rd64 s'.mem (scr s₀) (8 * k) = rd64 s.mem (st s₀) (8 * k)
  frame : Frame [workR (scr s₀)] s.mem s'.mem

theorem loadHs_ok {s : State} (hecx : s.gpr .ecx = st s₀) (hesi : s.gpr .esi = scr s₀)
    (hwr : s.wr = s₀.wr) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap loadH)) s (LdInv (s₀ := s₀) s n) := by
  intro n hn
  have fS := hp.st_fits
  have fV := hp.scr_fits
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (loadH_ok hp n (by omega) (by rw [h₁.gpr _ (by decide), hecx])
      (by rw [h₁.gpr _ (by decide), hesi]) (by rw [h₁.wr, hwr])) fun s₂ w₂ =>
      ⟨fun r hr => by rw [w₂.gpr r (by simpa using hr), h₁.gpr r hr], by rw [w₂.rd, h₁.rd],
        by rw [w₂.wr, h₁.wr], fun k hk => ?_, ?_⟩
    · have eS : rd64 s₁.mem (st s₀) (8 * n) = rd64 s.mem (st s₀) (8 * n) :=
        rd64_frame h₁.frame (fun r hr => by simp at hr; subst hr; exact hp.st_work) fS (by omega)
      rw [w₂.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [rd64_write64_self _ _ (by omega), eS]
      · rw [rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
        exact h₁.vars k (by omega)
    · rw [w₂.mem]
      exact frame_write64 (N := 192) h₁.frame (by simp) (by omega) (by omega) _

/-! ## Adding them into the hash value -/

theorem addH_ok (k : Nat) (hk : k < 8) {s : State} (hecx : s.gpr .ecx = st s₀)
    (hesi : s.gpr .esi = scr s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block (addH k)) s fun s' =>
      Wrote [T, Z1] s s' (write64 s.mem (st s₀) (8 * k)
        (rd64 s.mem (scr s₀) (8 * k) + rd64 s.mem (st s₀) (8 * k))) := by
  have hA := hp.accS hwr
  simp only [addH, sc]
  refine wp_movS (readSrc_mem hesi (hp.in_scr hwr (by omega))) fun s₁ u₁ => ?_
  refine wp_movS (readSrc_mem (by rw [u₁.other _ (by decide), hesi])
    (by rw [u₁.rd, u₁.wr]; exact hp.in_scr hwr (by omega))) fun s₂ u₂ => ?_
  have O₂ := (Only.of_upd u₁).trans (Only.of_upd u₂)
  have p₂ : Pair s₂ T Z1 (rd64 s.mem (scr s₀) (8 * k)) :=
    ⟨by rw [u₂.other _ (by decide), u₁.gpr, lo_rd64], by rw [u₂.gpr, u₁.mem, hi_rd64]⟩
  refine wp_addS (readSrc_mem (by rw [O₂.gpr _ (by decide), hecx])
    (by rw [O₂.rd, O₂.wr]; exact hp.in_st hwr (by omega))) fun s₃ u₃ hc => ?_
  refine wp_adcS (readSrc_mem (by rw [u₃.other _ (by decide), O₂.gpr _ (by decide), hecx])
    (by rw [u₃.rd, u₃.wr, O₂.rd, O₂.wr]; exact hp.in_st hwr (by omega))) hc fun s₄ u₄ => ?_
  have O₄ := (O₂.trans (Only.of_upd u₃)).trans (Only.of_upd u₄)
  have p₄ : Pair s₄ T Z1 (rd64 s.mem (scr s₀) (8 * k) + rd64 s.mem (st s₀) (8 * k)) := by
    refine ⟨?_, ?_⟩
    · rw [u₄.other _ (by decide), u₃.gpr, p₂.1, O₂.mem, VG.Proof.Sha512.Arm.lo_add]
      simp only [lo_rd64]
    · rw [u₄.gpr, carry_eq, u₃.other _ (by decide), u₃.mem, O₂.mem, p₂.1, p₂.2,
        VG.Proof.Sha512.Arm.hi_add]
      simp only [lo_rd64, hi_rd64]
  refine wp_store (ea_of (by rw [O₄.gpr _ (by decide), hecx]) _) (by rw [O₄.wr]; exact hA _ (by omega))
    fun s₅ u₅ => ?_
  refine wp_store (ea_of (by rw [u₅.gpr, O₄.gpr _ (by decide), hecx]) _)
    (by rw [u₅.wr, O₄.wr]; exact hA _ (by omega)) fun s₆ u₆ => WP.block_nil ?_
  refine ⟨fun r hr => ?_, ?_, by rw [u₆.rd, u₅.rd, O₄.rd], by rw [u₆.wr, u₅.wr, O₄.wr]⟩
  · rw [u₆.gpr, u₅.gpr]; exact (O₄.mono (by decide)).gpr r hr
  · rw [u₆.mem, u₅.gpr, u₅.mem, O₄.mem, p₄.1, p₄.2]; rfl

structure UInv (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ∉ [T, Z1] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  done : ∀ k < n, rd64 s'.mem (st s₀) (8 * k) = rd64 s.mem (scr s₀) (8 * k) + rd64 s.mem (st s₀) (8 * k)
  todo : ∀ k, n ≤ k → k < 8 → rd64 s'.mem (st s₀) (8 * k) = rd64 s.mem (st s₀) (8 * k)
  frame : Frame [stR s₀] s.mem s'.mem

theorem addHs_ok {s : State} (hecx : s.gpr .ecx = st s₀) (hesi : s.gpr .esi = scr s₀)
    (hwr : s.wr = s₀.wr) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap addH)) s (UInv (s₀ := s₀) s n) := by
  intro n hn
  have fS := hp.st_fits
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, fun _ h => absurd h (by omega),
      fun _ _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (addH_ok hp n (by omega) (by rw [h₁.gpr _ (by decide), hecx])
      (by rw [h₁.gpr _ (by decide), hesi]) (by rw [h₁.wr, hwr])) fun s₂ w₂ =>
      ⟨fun r hr => by rw [w₂.gpr r hr, h₁.gpr r hr], by rw [w₂.rd, h₁.rd],
        by rw [w₂.wr, h₁.wr], fun k hk => ?_, fun k hk hk' => ?_, ?_⟩
    · rw [w₂.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [rd64_write64_self _ _ (by omega), h₁.todo k (by omega) (by omega),
          rd64_frame h₁.frame (fun r hr => by simp at hr; subst hr; exact hp.st_scr.symm) hp.scr_fits
            (by omega)]
      · rw [rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
        exact h₁.done k (by omega)
    · rw [w₂.mem, rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
      exact h₁.todo k (by omega) hk'
    · rw [w₂.mem]
      exact frame_write64 (N := 64) h₁.frame (by simp) fS (by omega) _

end

/-! ## One block -/

theorem load_eq : load = .mov .ecx (.mem ⟨.esp, 4⟩) :: (List.range 8).flatMap loadH := rfl

theorem update_eq : update ++ advance =
    .mov .ecx (.mem ⟨.esp, 4⟩) :: ((List.range 8).flatMap addH ++ advance) := rfl

theorem harg_of {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) :
    m.readW (addr (esp₀ s₀) 4) 32 = st s₀ :=
  hp.arg_frame hf (i := 0) (by decide)

theorem movArg_ok {s₀ : State} (hp : Pre s₀) {s : State} {d : Reg} (hesp : s.gpr .esp = esp₀ s₀)
    (hrd : s.rd = s₀.rd) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (s.mem.readW (addr (esp₀ s₀) 4) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem ⟨.esp, 4⟩) :: is)) s Q :=
  wp_movS (readSrc_mem (b := .esp) (d := 4) hesp (hp.in_arg hrd (by omega) (by omega))) k

theorem advance_ok {s : State} {Q : State → Prop} {B : BitVec 32} (hesi : s.gpr .esi = B)
    (hA : Acc s.wr B 224)
    (k : ∀ s', s'.gpr .edi = s.gpr .edi + 128 →
      s'.zf = some (s.mem.readW (addr B cntOff) 32 - 1 == 0) →
      (∀ r, r ≠ .edi → r ≠ T → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW (addr B cntOff) (s.mem.readW (addr B cntOff) 32 - 1) → s'.rd = s.rd →
      s'.wr = s.wr → Q s') :
    WP isa (.block advance) s Q := by
  unfold advance
  refine wp_addi fun s₁ u₁ => ?_
  refine wp_movS (readSrc_mem (b := .esi) (d := cntOff) (by rw [u₁.other _ (by decide), hesi])
    (by rw [u₁.rd, u₁.wr]; exact mem_rd (hA _ (by decide)))) fun s₂ u₂ => wp_subi fun s₃ u₃ hz => ?_
  refine wp_storeF (ea_of (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
    hesi]) _) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hA _ (by decide)) (WP.block_nil ?_)
  refine k _ ?_ ?_ (fun r h1 h2 => ?_) ?_ ?_ ?_
  · show s₃.gpr .edi = _
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · show s₃.zf = _
    rw [hz, u₂.gpr, u₁.mem]
  · show s₃.gpr r = _
    rw [u₃.other _ h2, u₂.other _ h2, u₁.other _ h1]
  · show s₃.mem.writeW _ (s₃.gpr T) = _
    rw [u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, u₁.mem]
  · show s₃.rd = _
    rw [u₃.rd, u₂.rd, u₁.rd]
  · show s₃.wr = _
    rw [u₃.wr, u₂.wr, u₁.wr]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have fitS := hp.st_fits
  have fitV := hp.scr_fits
  have fitB := hp.blk_fit hi
  set H := stateAt s.mem ((st s₀).setWidth 64) with hH
  set M := blockAt s₀.mem ((blkAddr s₀ i).setWidth 64) with hMdef
  -- Load the working variables.
  refine WP.seq ?_
  rw [load_eq]
  refine movArg_ok hp hL.esp hL.rd fun s₀' u₀ => ?_
  rw [harg_of hp hL.frame] at u₀
  refine WP.mono (loadHs_ok hp u₀.gpr (by rw [u₀.other _ (by decide), hL.esi])
    (by rw [u₀.wr, hL.wr]) 8 (Nat.le_refl _)) fun s₁ h₁ => ?_
  have g₁ : ∀ r, r ≠ T → r ≠ .ecx → s₁.gpr r = s.gpr r := fun r h1 h2 => by
    rw [h₁.gpr r h1, u₀.other r h2]
  have m₁ : Frame [workR (scr s₀)] s.mem s₁.mem := by rw [← u₀.mem]; exact h₁.frame
  have c₁ := hp.ctx (s := s₁) (by rw [g₁ _ (by decide) (by decide), hL.esi])
    (by rw [h₁.wr, u₀.wr, hL.wr])
  have hB : BlkCtx (scr s₀) (blkAddr s₀ i) s₁ :=
    ⟨by rw [g₁ _ (by decide) (by decide), hL.edi], fitB,
      (hp.blk_scr.sub_left (hp.blk_sub hi)).sub_right (Region.sub_prefix (by omega)),
      fun o ho => by rw [h₁.rd, h₁.wr, u₀.rd, u₀.wr, hL.rd, hL.wr]; exact hp.blk_rd hi ho⟩
  have hM : Raw (blkAddr s₀ i) M s₁.mem := fun j hj => by
    have e : ∀ o, o + 4 ≤ 128 → s₁.mem.readW (addr (blkAddr s₀ i) o) 32 =
        s₀.mem.readW (addr (blkAddr s₀ i) o) 32 := fun o ho => by
      rw [m₁.readW (contains_addr ho (by omega) fitB)
          (fun r hr => by simp at hr; subst hr; exact hB.disj) (by decide),
        hL.frame.readW (contains_addr ho (by omega) fitB) (hp.blk_disj hi) (by decide)]
    rw [e _ (by omega), e _ (by omega)]
    exact raw_block fitB s₀.mem j hj
  have h0 : ∀ k (hk : k < 8), rd64 s₁.mem (scr s₀) (8 * k) = H[k] := fun k hk => by
    rw [h₁.vars k hk, u₀.mem, stateAt_get fitS _ hk]
  refine WP.seq (WP.mono (rounds_ok c₁ hB hM h0 80 (Nat.le_refl _)) fun s₂ h₂ => ?_)
  have g₂ : ∀ r, r ∉ temps → r ≠ .ecx → s₂.gpr r = s.gpr r := fun r hr h2 => by
    rw [h₂.gpr r hr, g₁ r (fun h => hr (by subst h; decide)) h2]
  have hrd₂ : s₂.rd = s₀.rd := by rw [h₂.rd, h₁.rd, u₀.rd, hL.rd]
  have hwr₂ : s₂.wr = s₀.wr := by rw [h₂.wr, h₁.wr, u₀.wr, hL.wr]
  have m₂ : Frame [workR (scr s₀)] s.mem s₂.mem := m₁.trans h₂.frame
  have sw : ∀ r ∈ [workR (scr s₀)], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  have hframe₂ : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem := hL.frame.trans (m₂.sub sw)
  -- Update the hash value, and advance.
  rw [update_eq]
  refine movArg_ok hp (by rw [g₂ _ (by decide) (by decide), hL.esp]) hrd₂ fun s₃ u₃ => ?_
  rw [harg_of hp hframe₂] at u₃
  rw [WP.block_append_iff]
  refine WP.mono (addHs_ok hp u₃.gpr (by rw [u₃.other _ (by decide), g₂ _ (by decide) (by decide), hL.esi])
    (by rw [u₃.wr, hwr₂]) 8 (Nat.le_refl _)) fun s₄ h₄ => ?_
  have hesi₄ : s₄.gpr .esi = scr s₀ := by
    rw [h₄.gpr _ (by decide), u₃.other _ (by decide), g₂ _ (by decide) (by decide), hL.esi]
  refine advance_ok hesi₄ (hp.ctx hesi₄ (by rw [h₄.wr, u₃.wr, hwr₂])).wV
    fun s₅ edi₅ z₅ g₅ m₅ rd₅ wr₅ => ?_
  -- Registers
  have eT : ∀ x ∈ [T, Z1], x ∈ temps := by decide
  have g : ∀ r, r ∉ temps → r ≠ .ecx → r ≠ .edi → s₅.gpr r = s.gpr r := fun r hr h2 h3 => by
    have hT : r ≠ T := fun h => hr (eT r (by simp [h]))
    rw [g₅ r h3 hT, h₄.gpr r (fun h => hr (eT r h)), u₃.other r h2, g₂ r hr h2]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, u₃.rd, hrd₂]
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, u₃.wr, hwr₂]
  -- Memory
  have hcnt₄ : s₄.mem.readW (addr (scr s₀) cntOff) 32 = BitVec.ofNat 32 (nb s₀ - i) := by
    rw [hp.high_frame (.inr h₄.frame) (by decide) (by decide), u₃.mem,
      hp.high_frame (.inl m₂) (by decide) (by decide), hL.cnt]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₅.mem := by
    rw [m₅]
    refine ((hframe₂.trans ?_).trans (h₄.frame.mono (by simp))).writeW (r := scrR s₀) (by simp) _
      (contains_addr (by decide) (by omega) fitV)
    rw [u₃.mem]; exact Frame.refl _ _
  have hstate : stateAt s₅.mem ((st s₀).setWidth 64) = compress H M := by
    have e5 : ∀ k < 8, rd64 s₅.mem (st s₀) (8 * k) = rd64 s₄.mem (st s₀) (8 * k) := fun k hk => by
      rw [m₅]
      simp only [rd64]
      rw [Mem.readW_writeW_sep (hp.st_scr.sep (contains_addr (by omega) (by omega) fitS)
          (contains_addr (by decide) (by omega) fitV)) (by decide),
        Mem.readW_writeW_sep (hp.st_scr.sep (contains_addr (by omega) (by omega) fitS)
          (contains_addr (by decide) (by omega) fitV)) (by decide)]
    refine stateAt_ext fitS fun k hk => ?_
    rw [e5 k hk, h₄.done k hk, u₃.mem, show 8 * k = vOff 80 k by simp only [vOff]; omega, h₂.vars k hk,
      show vOff 80 k = 8 * k by simp only [vOff]; omega,
      rd64_frame m₂ (fun r hr => by simp at hr; subst hr; exact hp.st_work) fitS (by omega),
      ← stateAt_get fitS _ hk]
    simp only [Spec.Sha512.compress, Vector.getElem_zipWith]
    rfl
  have hsaved : Saved s₀ s₅.mem := by
    have s₄' : Saved s₀ s₄.mem := by
      refine saved_frame hp ?_ (.inr h₄.frame)
      rw [u₃.mem]
      exact saved_frame hp hL.saved (.inl m₂)
    obtain ⟨a1, a2, a3, a4⟩ := s₄'
    have e : ∀ d, 192 ≤ d → d + 4 ≤ 208 →
        s₅.mem.readW (addr (scr s₀) d) 32 = s₄.mem.readW (addr (scr s₀) d) 32 := fun d h1 h2 => by
      rw [m₅]
      exact Mem.readW_writeW_sep (Proof.Sha256.X86.Stream.addr_sep (by omega) (by simp [cntOff]; omega)
        (by simp [cntOff]; omega)) (by decide)
    exact ⟨(e 192 (by omega) (by omega)).trans a1, (e 196 (by omega) (by omega)).trans a2,
      (e 200 (by omega) (by omega)).trans a3, (e 204 (by omega) (by omega)).trans a4⟩
  have hnb : nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  have hc1 : s₄.mem.readW (addr (scr s₀) cntOff) 32 - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [hcnt₄]
    bv_omega
  have hcommon : Common s₀ (i + 1) s₅ := by
    refine ⟨by rw [g _ (by decide) (by decide) (by decide), hL.esi],
      by rw [g _ (by decide) (by decide) (by decide), hL.esp], hrd, hwr, hframe, ?_, hsaved⟩
    rw [hstate, compressBlocks_succ, ← hL.state, hMdef, hp.blk_addr hi]
  have hev : eval .ne s₅ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    rw [Proof.Sha256.X86.Stream.eval_ne, z₅, hc1]; rfl
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
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon with edi := ?_, cnt := ?_ }⟩
    · rw [edi₅, h₄.gpr _ (by decide), u₃.other _ (by decide), g₂ _ (by decide) (by decide), hL.edi]
      simp only [blkAddr]
      bv_omega
    · rw [m₅, Mem.readW_writeW_self32, hc1]

/-! ## Prologue and epilogue -/

theorem prologue_eq : prologue = [.mov .eax (.mem ⟨.esp, 16⟩), .store ⟨.eax, 192⟩ .ebx,
    .store ⟨.eax, 196⟩ .esi, .store ⟨.eax, 200⟩ .edi, .store ⟨.eax, 204⟩ .ebp,
    .mov .esi (.reg .eax), .mov .edi (.mem ⟨.esp, 8⟩), .mov .eax (.mem ⟨.esp, 12⟩),
    .store ⟨.esi, 208⟩ .eax, .alu .test .eax (.reg .eax)] := rfl

theorem epilogue_eq : epilogue = [.mov .ebx (.mem ⟨.esi, 192⟩), .mov .edi (.mem ⟨.esi, 200⟩),
    .mov .ebp (.mem ⟨.esi, 204⟩), .mov .esi (.mem ⟨.esi, 196⟩)] := rfl

/-- Reading an argument after writing the scratch buffer. -/
theorem readW_writeW_scr_arg {s₀ : State} (hp : Pre s₀) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 224) (he : 4 ≤ e) (he' : e + 4 ≤ 20) :
    (m.writeW (addr (scr s₀) d) v).readW (addr (esp₀ s₀) e) 32 = m.readW (addr (esp₀ s₀) e) 32 :=
  Mem.readW_writeW_sep (hp.arg_scr.sep (hp.arg_contains he he')
    (contains_addr hd (by omega) hp.scr_fits)) (by decide)

theorem readW_writeW_scr {s₀ : State} (hp : Pre s₀) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 224) (he : e + 4 ≤ 224) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr (scr s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
  Proof.Sha256.X86.Stream.readW_writeW_addr m v (by have := hp.scr_fits; omega)
    (by have := hp.scr_fits; omega) h

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem :=
  ((((s₀.mem.writeW (addr (scr s₀) 192) (s₀.gpr .ebx)).writeW (addr (scr s₀) 196) (s₀.gpr .esi)).writeW
    (addr (scr s₀) 200) (s₀.gpr .edi)).writeW (addr (scr s₀) 204) (s₀.gpr .ebp)).writeW
    (addr (scr s₀) 208) (arg s₀ 2)

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ fun s₁ =>
      s₁.gpr .esi = scr s₀ ∧ s₁.gpr .edi = bp s₀ ∧ s₁.gpr .esp = esp₀ s₀ ∧ s₁.rd = s₀.rd ∧
      s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧ s₁.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  have hsa := readW_writeW_scr_arg hp
  have i8 := hp.in_arg (s := s₀) rfl (d := 8) (by omega) (by omega)
  have i12 := hp.in_arg (s := s₀) rfl (d := 12) (by omega) (by omega)
  have i16 := hp.in_arg (s := s₀) rfl (d := 16) (by omega) (by omega)
  have a8 : s₀.mem.readW (addr (esp₀ s₀) 8) 32 = bp s₀ := rfl
  have a12 : s₀.mem.readW (addr (esp₀ s₀) 12) 32 = arg s₀ 2 := rfl
  have a16 : s₀.mem.readW (addr (esp₀ s₀) 16) 32 = scr s₀ := rfl
  have hout : ∀ d, d + 4 ≤ 224 → InRegions s₀.wr (addr (scr s₀) d) 4 := hp.accV (s := s₀) rfl
  apply WP.of_runBlock
  rw [prologue_eq]
  simp (config := {decide := true}) (disch := decide) only [runBlock_cons,
    runBlock_nil, runStep_some, exec, execAlu, readSrc, ea_mk, State.setReg, arithFlags,
    State.setFlags, State.load32, State.store32, i8, i12, i16, a8, a12, a16, hout, hsa, ite_true,
    ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

theorem saveMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (saveMem s₀) := by
  have hrw := readW_writeW_scr hp
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) (disch := decide) only [Mem.readW_writeW_self32, hrw]

theorem saveMem_cnt {s₀ : State} :
    (saveMem s₀).readW (addr (scr s₀) cntOff) 32 = arg s₀ 2 := by
  simp only [saveMem, cntOff, Mem.readW_writeW_self32]

theorem saveMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scrR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 224 → (scrR s₀).Contains (addr (scr s₀) d) (32 / 8) :=
    fun d hd => contains_addr hd (by omega) hp.scr_fits
  simp only [saveMem]
  have m := List.mem_singleton_self (scrR s₀)
  exact (((((Frame.refl _ _).writeW m _ (c 192 (by omega))).writeW m _ (c 196 (by omega))).writeW
    m _ (c 200 (by omega))).writeW m _ (c 204 (by omega))).writeW m _ (c 208 (by omega))

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hesi : s₁.gpr .esi = scr s₀)
    (hesp : s₁.gpr .esp = esp₀ s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (hm : s₁.mem = saveMem s₀) : Common s₀ 0 s₁ := by
  refine ⟨hesi, hesp, hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved hp⟩
  · rw [hm]; exact (saveMem_frame hp).mono (by simp)
  · rw [hm]
    have hd : ∀ r ∈ [scrR s₀], Region.Disjoint (stR s₀) r := fun r hr => by
      simp at hr; subst hr; exact hp.st_scr
    refine stateAt_ext hp.st_fits fun k hk => ?_
    rw [rd64_frame (saveMem_frame hp) hd hp.st_fits (by omega), ← stateAt_get hp.st_fits _ hk]
    simp [compressBlocks]

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  have hin : ∀ d, d + 4 ≤ 224 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
    fun d hd => hp.in_scr hc.wr hd
  obtain ⟨g0, g1, g2, g3⟩ := hc.saved
  have hesi := hc.esi
  have hesp := hc.esp
  apply WP.of_runBlock
  rw [epilogue_eq]
  simp (config := {decide := true}) (disch := decide) only [runBlock_cons,
    runBlock_nil, runStep_some, exec, readSrc, ea_mk, State.setReg, State.load32, hesi, hin,
    g0, g1, g2, g3, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hesp]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Sha512.X86.compress s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha512.compressX86.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hesi, hedi, hesp, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc =>
    WP.mono (restore_ok hp hc) fun s' ⟨hr, hm'⟩ => ⟨⟨hr, ?_⟩, ?_⟩)
  rotate_left
  · rw [hm']
    refine hc.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simpa using ⟨hp.ret_st, hp.ret_scr⟩
  · show stateAt s'.mem _ = _
    rw [hm']; exact hc.state
  have hc₀ := common_zero hp hesi hesp hrd hwr hm
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp only [BitVec.and_self, beq_iff_eq] at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
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
        edi := by rw [hedi]; simp [blkAddr]
        cnt := by rw [hm, saveMem_cnt]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x4011 then 0x30 else 0

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x3000, 224⟩]

theorem sat_pre : Proof.Sha512.compressX86.pre satState := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x2000 := by decide
  have a2 : arg satState 2 = 0 := by decide
  have a3 : arg satState 3 = 0x3000 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  simp only [Proof.Sha512.compressX86, a0, a1, a2, a3, e]
  refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, satState] at h₁ h₂
    bv_omega

/-- The taint analysis starts with the stack arguments public, and the words
holding `state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [64, 224], argLen := 20, argBases := [(4, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hst := hp.st_fits; have hsc := hp.scr_fits; have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha512.compressX86.pre s₁)
    (h₂ : Proof.Sha512.compressX86.pre s₂) (hpub : Proof.Sha512.compressX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scrR, st, scr, a0, a3]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.esp_fits h4 hk, VG.X86.Taint.argByte_eq hp₂.esp_fits h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem compress_verified :
    Verified X86.target Impl.Sha512.X86.compress Proof.Sha512.compressX86 :=
  ⟨fun s hs => correct (pre_of s hs),
    VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨satState, sat_pre⟩⟩

end Compress

end VG.Proof.Sha512.X86
