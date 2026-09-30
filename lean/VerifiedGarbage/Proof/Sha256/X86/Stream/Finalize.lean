import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
import VerifiedGarbage.Proof.Sha256.X86.Contract

/-!
# Streaming SHA-256 on x86 (32-bit): the loop of `finalize`

Untrusted: everything here is checked by Lean. `finalize` itself is verified
by the generic proof (`Proof/Sha256/X86/Shared.lean`); HMAC-SHA256 on x86
(`Proof/Hmac/X86/`), whose `finalize` reuses its code, and SHA-512 on x86
use the pieces here: its prologue and loop body (`prologue_ok`, `body_ok`),
with `state` in `ebx`, `scratch` in `ebp`, the buffered bytes in `edi`,
whether the block being padded is not the last in `esi`, and `count` and
`out` in `scratch[128..140)`. Each compression calls the compression
function (`compressAt_ok`), which uses the 20 bytes below `esp`.
-/

namespace VG.Proof.Sha256.X86.Stream.Finalize

open VG VG.X86 VG.Impl.Sha256.X86.Stream
open VG.Impl.Sha256.X86 (at_)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream
open VG.Proof.Sha256.Stream
open VG.Spec.Sha256 (HashValue stateAt blockAt compress parseBlock bytesAt wordBytes)
open VG.Proof.Sha256 (countX86)

theorem lit32 (n : Nat) : (OfNat.ofNat n : BitVec 32) = BitVec.ofNat 32 n := rfl

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev cnt : Nat := (countX86 s₀).toNat
abbrev out : BitVec 32 := arg s₀ 3
abbrev scr : BitVec 32 := arg s₀ 4
abbrev stA : Addr := (st s₀).setWidth 64
abbrev outA : Addr := (out s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev stR : Region := ⟨stA s₀, 96⟩
abbrev outR : Region := ⟨outA s₀, 32⟩
abbrev scR : Region := ⟨scA s₀, 160⟩
abbrev argR : Region := ⟨addr (esp₀ s₀) 4, 20⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (esp₀ s₀) 20

/-- The messages the initial state represents. -/
def R₀ (m : List Byte) : Prop :=
  Spec.Sha256.Repr s₀.mem (stA s₀) m ∧ countX86 s₀ = BitVec.ofNat 64 m.length

/-- Our caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop := ∀ p ∈ saved, m.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1

/-- The digest, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (compress (stateAt mem (stA s₀))
    (parseBlock fun t => (bytesAt mem (stA s₀ + 32) n ++ List.replicate (64 - n) 0).getD t 0))
    (parseBlock fun t => (List.replicate 56 0 ++ lenBytes m).getD t 0)

/-- The digest, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (stateAt mem (stA s₀))
    (parseBlock fun t => (bytesAt mem (stA s₀ + 32) n ++ List.replicate (56 - n) 0 ++ lenBytes m).getD t 0)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, outR s₀, scR s₀, argR s₀]
  st_out : (stR s₀).Disjoint (outR s₀)
  st_scr : (stR s₀).Disjoint (scR s₀)
  out_scr : (outR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_out : (argR s₀).Disjoint (outR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_out : (retR s₀).Disjoint (outR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_out : (stkR s₀).Disjoint (outR s₀)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + 96 ≤ 2 ^ 32
  out_fit : (out s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 160 ≤ 2 ^ 32
  sp_lo : 20 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 24 ≤ 2 ^ 32

theorem cnt_mod (s₀ : State) : cnt s₀ % 64 = (arg s₀ 1).toNat % 64 := by
  simp only [cnt, countX86]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (arg s₀ 1).isLt, Nat.shiftLeft_eq]
  omega

theorem R₀.length {s₀ : State} {m : List Byte} (h : R₀ s₀ m) : cnt s₀ % 64 = m.length % 64 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ 160) : (scR s₀).Contains (addr (scr s₀) d) 4 :=
  contains_addr hd (by omega) hp.scr_fit

theorem scr_sub {d : Nat} (hd : d + 4 ≤ 160) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR s₀) := by
  rw [addr_eq (by have := hp.scr_fit; omega)]
  exact sub_offset hd (by omega)

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (esp₀ s₀) 4, 20⟩ : Region).Contains _ _
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ hd₁ (by omega) (by omega)

theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  show Region.Sub _ ⟨addr (esp₀ s₀) 4, 20⟩
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sub _ hd₁ (by omega)

end Pre

/-- The return address is below the arguments. -/
theorem ret_a {s₀ : State} (hp : Pre s₀) : (retR s₀).Disjoint (argR s₀) := by
  have := hp.sp_fit
  show Region.Disjoint ⟨(esp₀ s₀).setWidth 64, 4⟩ ⟨addr (esp₀ s₀) 4, 20⟩
  rw [addr_eq (by omega)]
  exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)

theorem ret_stk {s₀ : State} (hp : Pre s₀) : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨(esp₀ s₀).setWidth 64, 4⟩ ⟨(esp₀ s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩
  rw [Taint.sub_setWidth (by omega)]
  exact Offset.base_disjoint_below _ (by omega)

/-! ## Invariants -/

structure Common (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  frame : Frame [stR s₀, scR s₀, argR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  lo : s.mem.readW (addr (scr s₀) 128) 32 = arg s₀ 1
  hi : s.mem.readW (addr (scr s₀) 132) 32 = arg s₀ 2
  outp : s.mem.readW (addr (scr s₀) 136) 32 = out s₀

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv (s₀ : State) (k n : Nat) (s : State) : Prop extends Common s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ 56 + 8 * k
  edi : s.gpr .edi = BitVec.ofNat 32 n
  esi : s.gpr .esi = BitVec.ofNat 32 k
  hash : ∀ m, R₀ s₀ m → Spec.Sha256.hash m =
    (if k = 1 then Fin1 s₀ s.mem n m else Fin0 s₀ s.mem n m).toList.flatMap wordBytes

/-- All blocks are compressed. -/
def Done (s₀ : State) (s : State) : Prop :=
  Common s₀ s ∧ ∀ m, R₀ s₀ m → Spec.Sha256.hash m = (stateAt s.mem (stA s₀)).toList.flatMap wordBytes

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common s₀ s)
    (hg : ∀ r ∈ [Reg.ebx, .ebp, .esp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by simp)]; exact h.ebx
  ebp := by rw [hg _ (by simp)]; exact h.ebp
  esp := by rw [hg _ (by simp)]; exact h.esp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  lo := by rw [hm]; exact h.lo
  hi := by rw [hm]; exact h.hi
  outp := by rw [hm]; exact h.outp

/-- A write within `stR` or the arguments keeps what `Common` says about memory. -/
theorem Common.frame_keep {s₀ : State} (hp : Pre s₀) {s : State} (h : Common s₀ s) {m : Mem}
    (hf : Frame [stR s₀, argR s₀] s.mem m) :
    Frame [stR s₀, scR s₀, argR s₀, stkR s₀] s₀.mem m ∧ Saved s₀ m ∧
      m.readW (addr (scr s₀) 128) 32 = arg s₀ 1 ∧ m.readW (addr (scr s₀) 132) 32 = arg s₀ 2 ∧
      m.readW (addr (scr s₀) 136) 32 = out s₀ := by
  have word : ∀ d, 112 ≤ d → d + 4 ≤ 160 → m.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := by
    intro d h₁ h₂
    refine hf.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_scr.symm.sub_left (hp.scr_sub h₂)
    · exact hp.a_scr.symm.sub_left (hp.scr_sub h₂)
  refine ⟨h.frame.trans (hf.mono (by simp)), fun p hp' => ?_, by rw [word 128 (by omega) (by omega)]; exact h.lo,
    by rw [word 132 (by omega) (by omega)]; exact h.hi, by rw [word 136 (by omega) (by omega)]; exact h.outp⟩
  have hd : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
    simp only [VG.Impl.Sha256.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp
  rw [word p.2 hd.1 (by omega)]
  exact h.saved p hp'

theorem st_add (s₀ : State) (n : Nat) : stA s₀ + 32 + BitVec.ofNat 64 n = stA s₀ + BitVec.ofNat 64 (32 + n) := by
  simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl

/-- Writing buffer bytes `[n, n + |xs|)`. -/
theorem buf_frame {s₀ : State} (m : Mem) {n : Nat} {xs : List Byte} (hn : n + xs.length ≤ 64) :
    Frame [stR s₀] m (writeBytes m (stA s₀ + 32 + BitVec.ofNat 64 n) xs) := by
  refine writeBytes_frame _ _ _ ?_
  rw [st_add]
  exact contains_offset (by omega) (by omega)

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ [Reg.ebx, .ebp, .esp, .esi, .ecx], s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  edi : s.gpr .edi = BitVec.ofNat 32 (n + j)
  eax : s.gpr .eax = BitVec.ofNat 32 (lim - n - j)
  mem : s.mem = writeBytes sI.mem (stA s₀ + 32 + BitVec.ofNat 64 n) (List.replicate j 0)

theorem zero_step {s₀ : State} (hp : Pre s₀) {sI : State} (hC : Common s₀ sI) (hecx : sI.gpr .ecx = 0)
    {n lim j : Nat} (hlim : lim ≤ 64) (hj : j < lim - n) {s : State} (h : Zero s₀ sI n lim j s) :
    WP isa (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .store8 (at_ .edx 32) .cl,
      .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) s fun s' =>
      Zero s₀ sI n lim (j + 1) s' ∧ s'.zf = some (decide (lim - n - (j + 1) = 0)) := by
  have hst := hp.st_fit
  have hebx : s.gpr .ebx = st s₀ := by rw [h.keep _ (by simp), hC.ebx]
  have ha : stA s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j = stA s₀ + BitVec.ofNat 64 (32 + n + j) := by
    simp only [BitVec.ofNat_add]; ac_rfl
  have hout : InRegions s.wr (stA s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [ha]
    exact contains_offset (by omega) (by omega)
  refine wp_mov fun s₁ u₁ => wp_add fun s₂ u₂ => ?_
  refine wp_store8 (r := .cl) (a := stA s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ u₃ => ?_
  · rw [ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), hebx, h.edi, ha, addr_add_ofNat (by omega)]
    congr 2; omega
  refine wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => WP.block_nil ⟨⟨by omega, fun r hr => ?_,
    by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .eax ∧ r ≠ .edi ∧ r ≠ .edx := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₅.other r this.1, u₄.other r this.2.1, u₃.gpr, u₂.other r this.2.2, u₁.other r this.2.2, h.keep r hr]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.edi,
      ← ofNat_succ, Nat.add_assoc]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.eax,
      ofNat_pred (by omega), Nat.sub_sub]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, show Reg8.cl.reg = Reg.ecx from rfl, u₂.other _ (by decide),
      u₁.other _ (by decide), h.keep _ (by simp), hecx, h.mem, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [hz₅, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.eax,
      ofNat_pred (by omega), ofNat_beq_zero (by omega), Nat.sub_sub, Nat.sub_sub]

theorem zero_ok {s₀ : State} (hp : Pre s₀) {sI : State} (hC : Common s₀ sI) (hecx : sI.gpr .ecx = 0)
    {n lim : Nat} (hlim : lim ≤ 64) (hn : n ≤ lim) {s : State} (h : Zero s₀ sI n lim 0 s)
    (hz : s.zf = some (decide (lim - n = 0))) :
    WP isa (.ite .e (.block []) (.loop (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edi),
      .store8 (at_ .edx 32) .cl, .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) .ne)) s
      (Zero s₀ sI n lim (lim - n)) := by
  refine WP.ite (decide (lim - n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ Zero s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (zero_step hp hC hecx hlim hj hZ) fun s' ⟨hZ', hz'⟩ => ?_
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by show s'.zf.map (!·) = _; rw [hz']; simp [hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by show s'.zf.map (!·) = _; rw [hz']; simp [hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The compression of the buffer. -/
theorem compress_buf {s₀ : State} (hp : Pre s₀) {s : State} (hC : Common s₀ s)
    (heax : s.gpr .eax = st s₀ + BitVec.ofNat 32 32) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      stateAt s'.mem (stA s₀) = compress (stateAt s.mem (stA s₀)) (blockAt s.mem (stA s₀ + 32)) → Q s') :
    WP isa (compressAt .ebx .ebp) s Q := by
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hsp := hp.sp_fit
  have e32 : Region.Sub ⟨stA s₀, 32⟩ (stR s₀) := Region.sub_prefix (by omega)
  have e112 : Region.Sub ⟨scA s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega)
  have hb : (st s₀ + BitVec.ofNat 32 32).setWidth 64 = stA s₀ + BitVec.ofNat 64 32 := addr_eq (by omega)
  have eb : Region.Sub ⟨(st s₀ + BitVec.ofNat 32 32).setWidth 64, 64⟩ (stR s₀) := by
    rw [hb]; exact sub_offset (by omega) (by omega)
  refine compressAt_ok (st := st s₀) (scr := scr s₀) (blk := st s₀ + BitVec.ofNat 32 32) (E := esp₀ s₀)
    (by decide) (by decide) (by decide) (by decide) hC.esp hC.ebx hC.ebp heax hp.sp_lo (by omega)
    (by rw [BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (by omega)
    ((hp.st_scr.sub_left e32).sub_right e112) ?_ ((hp.st_scr.sub_left eb).sub_right e112)
    (hp.stk_st.sub_right e32) (hp.stk_scr.sub_right e112) (hp.stk_st.sub_right eb) ?_ ?_ ?_
  · rw [hb]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  · rw [hC.rd, hC.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨stR s₀, by simp, 32, hb, by simp⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · intro s' hrd hwr hcs hf hstate
    have cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := hcs
    have word : ∀ d, 112 ≤ d → d + 4 ≤ 160 →
        s'.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := by
      intro d h₁ h₂
      refine hf.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.st_scr.symm.sub_left (hp.scr_sub h₂)).sub_right e32
      · rw [addr_eq (by omega)]; exact Offset.disjoint_base _ (by omega) (by omega)
      · exact hp.stk_scr.symm.sub_left (hp.scr_sub h₂)
    refine hQ s' ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide)]; exact hC.ebx,
      by rw [cs _ (by decide)]; exact hC.ebp, by rw [cs _ (by decide)]; exact hC.esp,
      hC.frame.trans (hf.sub ?_), fun p hp' => ?_, by rw [word 128 (by omega) (by omega)]; exact hC.lo,
      by rw [word 132 (by omega) (by omega)]; exact hC.hi, by rw [word 136 (by omega) (by omega)]; exact hC.outp⟩
      hcs (by rw [hstate, show (st s₀ + BitVec.ofNat 32 32).setWidth 64 = stA s₀ + 32 from hb])
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, e32⟩
      · exact ⟨scR s₀, by simp, e112⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · have hd : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
        simp only [VG.Impl.Sha256.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl | rfl <;> simp
      rw [word p.2 hd.1 (by omega)]
      exact hC.saved p hp'

theorem times8 (x : BitVec 32) : x + x + (x + x) + (x + x + (x + x)) = x <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem writeW_bswap (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a (bswap w) = writeBytes m a (wordBytes w) := by
  rw [Mem.writeW, write_eq_writeBytes, ← bswap_bytes]; rfl

/-- The two words of the message length in bits, in order of their bytes. -/
abbrev lenL (s₀ : State) : List Byte :=
  wordBytes ((arg s₀ 2 <<< 3) ||| (arg s₀ 1 >>> 29)) ++ wordBytes (arg s₀ 1 <<< 3)

/-- Storing the message length in bits, big-endian, at `state[88..96)`. -/
theorem len_ok {s₀ : State} (hp : Pre s₀) {s : State} (hC : Common s₀ s) :
    WP isa (.block lengthStore) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = writeBytes s.mem (stA s₀ + 32 + BitVec.ofNat 64 56) (lenL s₀) := by
  have hst := hp.st_fit; have hsc := hp.scr_fit
  have rin : ∀ d, d + 4 ≤ 160 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
    fun d hd => ⟨scR s₀, by simp [hC.rd, hC.wr, hp.wr], hp.scr_in hd⟩
  have hout : ∀ o, o + 4 ≤ 96 → InRegions s.wr (addr (st s₀) o) 4 :=
    fun o ho => ⟨stR s₀, by simp [hC.wr, hp.wr], contains_addr ho (by omega) hst⟩
  unfold lengthStore
  refine wp_movm (a := addr (scr s₀) 128) (by rw [ea_at, hC.ebp]) (rin 128 (by omega)) fun s₁ u₁ => ?_
  refine wp_movm (a := addr (scr s₀) 132) (by rw [ea_at, u₁.other _ (by decide), hC.ebp])
    (by rw [u₁.rd, u₁.wr]; exact rin 132 (by omega)) fun s₂ u₂ => ?_
  refine wp_add fun s₃ u₃ => wp_add fun s₄ u₄ => wp_add fun s₅ u₅ => wp_mov fun s₆ u₆ =>
    wp_shr (by decide) fun s₇ u₇ => wp_or fun s₈ u₈ => wp_add fun s₉ u₉ => wp_add fun s₁₀ u₁₀ =>
    wp_add fun s₁₁ u₁₁ => wp_bswap fun s₁₂ u₁₂ => ?_
  have g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₁₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₁₂.other r h2, u₁₁.other r h1, u₁₀.other r h1, u₉.other r h1, u₈.other r h2, u₇.other r h3,
      u₆.other r h3, u₅.other r h2, u₄.other r h2, u₃.other r h2, u₂.other r h2, u₁.other r h1]
  have m₁₂ : s₁₂.mem = s.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have c2 : s₂.gpr .ecx = arg s₀ 2 := by rw [u₂.gpr, u₁.mem, hC.hi]
  have a2 : s₂.gpr .eax = arg s₀ 1 := by rw [u₂.other _ (by decide), u₁.gpr, hC.lo]
  have c5 : s₅.gpr .ecx = arg s₀ 2 <<< 3 := by rw [u₅.gpr, u₄.gpr, u₃.gpr, c2, times8]
  have a5 : s₅.gpr .eax = arg s₀ 1 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), a2]
  have d7 : s₇.gpr .edx = arg s₀ 1 >>> 29 := by rw [u₇.gpr, u₆.gpr, a5]
  have c8 : s₈.gpr .ecx = (arg s₀ 2 <<< 3) ||| (arg s₀ 1 >>> 29) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), c5, d7]
  have a11 : s₁₁.gpr .eax = arg s₀ 1 <<< 3 := by
    rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), a5,
      times8]
  have c12 : s₁₂.gpr .ecx = bswap ((arg s₀ 2 <<< 3) ||| (arg s₀ 1 >>> 29)) := by
    rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), c8]
  have wr₁₂ : s₁₂.wr = s.wr := by
    rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have rd₁₂ : s₁₂.rd = s.rd := by
    rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have ebx₁₂ : s₁₂.gpr .ebx = st s₀ := by rw [g _ (by decide) (by decide) (by decide), hC.ebx]
  refine wp_store (a := addr (st s₀) 88) (by rw [ea_at, ebx₁₂]) (by rw [wr₁₂]; exact hout 88 (by omega))
    fun s₁₃ u₁₃ => wp_bswap fun s₁₄ u₁₄ => wp_store (a := addr (st s₀) 92)
      (by rw [ea_at, u₁₄.other _ (by decide), u₁₃.gpr, ebx₁₂])
      (by rw [u₁₄.wr, u₁₃.wr, wr₁₂]; exact hout 92 (by omega)) fun s₁₅ u₁₅ => WP.block_nil ?_
  refine ⟨fun r h1 h2 h3 => by rw [u₁₅.gpr, u₁₄.other r h1, u₁₃.gpr, g r h1 h2 h3],
    by rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, rd₁₂], by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, wr₁₂], ?_⟩
  have a14 : s₁₄.gpr .eax = bswap (arg s₀ 1 <<< 3) := by
    rw [u₁₄.gpr, u₁₃.gpr, u₁₂.other _ (by decide), a11]
  rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, a14, c12, m₁₂, writeW_bswap, writeW_bswap,
    addr_eq (show (st s₀).toNat + 88 < 2 ^ 32 by omega), addr_eq (show (st s₀).toNat + 92 < 2 ^ 32 by omega),
    show stA s₀ + BitVec.ofNat 64 92 = stA s₀ + BitVec.ofNat 64 88 +
      BitVec.ofNat 64 (wordBytes ((arg s₀ 2 <<< 3) ||| (arg s₀ 1 >>> 29))).length by
      rw [BitVec.add_assoc]; rfl, writeBytes_append _ _ _ _ (by simp [wordBytes]),
    show stA s₀ + 32 + BitVec.ofNat 64 56 = stA s₀ + BitVec.ofNat 64 88 by rw [BitVec.add_assoc]; rfl]

/-- Point `eax` at the buffer. -/
theorem args_ok {s₀ : State} {s : State} (hC : Common s₀ s) :
    WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 32)]) s fun s' =>
      Common s₀ s' ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.gpr .eax = st s₀ + BitVec.ofNat 32 32 ∧
        Frame [argR s₀] s.mem s'.mem := by
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r h => by rw [u₂.other r h, u₁.other r h]
  have hm : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨hC.of_gpr (fun r hr => g₂ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) hm
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]), g₂, by rw [u₂.gpr, u₁.gpr, hC.ebx]; rfl,
    by rw [hm]; exact Frame.refl _ _⟩

/-- The loop's postcondition for one iteration. -/
def Step (s₀ : State) (k : Nat) (s : State) : Prop :=
  (eval .e s = some false ∧ Done s₀ s) ∨ (eval .e s = some true ∧ k = 1 ∧ LInv s₀ 0 0 s)

theorem regs3 {r : Reg} (hr : r ∈ [Reg.ebx, .ebp, .esp]) : r ≠ .eax ∧ r ≠ .ecx ∧ r ≠ .edx ∧ r ≠ .edi ∧ r ≠ .esi := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> decide

theorem body_ok {s₀ : State} (hp : Pre s₀) {k n : Nat} {s : State} (h : LInv s₀ k n s) :
    WP isa finalizeBody s (Step s₀ k) := by
  have hk := h.k_le; have hn := h.n_le; have hst := hp.st_fit
  have hC := h.toCommon
  unfold finalizeBody
  -- `eax := 64` or `56`: the end of the zeros.
  refine WP.seq (wp_movi fun s₁ u₁ => wp_test fun s₂ f₂ z₂ => WP.block_nil ?_)
  have hz₂ : s₂.zf = some (decide (k = 0)) := by
    rw [z₂, u₁.other _ (by decide), h.esi, BitVec.and_self, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .eax = BitVec.ofNat 32 (56 + 8 * k) ∧
      (∀ r, r ≠ .eax → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr) ?_
    fun s₃ ⟨heax₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show s₂.zf = _; rw [hz₂]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine wp_movi fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr]; rfl, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [u₃.other r hr, f₂.gpr, u₁.other r hr]
      · rw [u₃.mem, f₂.mem, u₁.mem]
      · rw [u₃.rd, f₂.rd, u₁.rd]
      · rw [u₃.wr, f₂.wr, u₁.wr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨by rw [f₂.gpr, u₁.gpr, show k = 1 by omega]; rfl, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [f₂.gpr, u₁.other r hr]
      · rw [f₂.mem, u₁.mem]
      · rw [f₂.rd, u₁.rd]
      · rw [f₂.wr, u₁.wr]
  -- `ecx := 0; eax -= edi`: zero the rest of the buffer, up to `lim`.
  have hC₃ : Common s₀ s₃ := hC.of_gpr (fun r hr => g₃ r (regs3 hr).1) m₃ rd₃ wr₃
  refine WP.seq (wp_movi fun s₄ u₄ => wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  have hC₄ : Common s₀ s₄ := hC₃.of_gpr (fun r hr => u₄.other r (regs3 hr).2.1) u₄.mem u₄.rd u₄.wr
  have hecx₄ : s₄.gpr .ecx = 0 := u₄.gpr
  have hedi₄ : s₄.gpr .edi = BitVec.ofNat 32 n := by rw [u₄.other _ (by decide), g₃ _ (by decide), h.edi]
  have heax₅ : s₅.gpr .eax = BitVec.ofNat 32 (56 + 8 * k - n) := by
    rw [u₅.gpr, u₄.other _ (by decide), heax₃, hedi₄, sub_ofNat (a := 56 + 8 * k) (b := n) (by omega)]
  have hZ : Zero s₀ s₄ n (56 + 8 * k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => u₅.other r ?_, u₅.rd, u₅.wr,
      by rw [u₅.other _ (by decide), hedi₄, Nat.add_zero], by rw [heax₅, Nat.sub_zero],
      by rw [u₅.mem, List.replicate_zero, writeBytes_nil]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  have hz₅ : s₅.zf = some (decide (56 + 8 * k - n = 0)) := by
    rw [z₅, ← u₅.gpr, heax₅, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (zero_ok hp hC₄ hecx₄ (by omega) hn hZ hz₅) fun s₆ hZ₆ => ?_)
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃]
  have hf₆ : Frame [stR s₀] s₄.mem s₆.mem := by
    rw [hZ₆.mem]; exact buf_frame _ (by simp only [List.length_replicate]; omega)
  obtain ⟨hfr₆, hsv₆, hlo₆, hhi₆, hout₆⟩ := hC₄.frame_keep hp (hf₆.mono (by simp))
  have hC₆ : Common s₀ s₆ := ⟨hZ₆.rd.trans hC₄.rd, hZ₆.wr.trans hC₄.wr, by rw [hZ₆.keep _ (by simp), hC₄.ebx],
    by rw [hZ₆.keep _ (by simp), hC₄.ebp], by rw [hZ₆.keep _ (by simp), hC₄.esp], hfr₆, hsv₆, hlo₆, hhi₆, hout₆⟩
  have hst₆ : stateAt s₆.mem (stA s₀) = stateAt s.mem (stA s₀) := by
    rw [hZ₆.mem, hm₄]
    apply stateAt_congr
    intro i hi
    rw [st_add]
    exact writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (stA s₀ + 32) (56 + 8 * k) =
      bytesAt s.mem (stA s₀ + 32) n ++ List.replicate (56 + 8 * k - n) 0 := by
    rw [hZ₆.mem, hm₄, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega
  have hesi₆ : s₆.gpr .esi = BitVec.ofNat 32 k := by
    rw [hZ₆.keep _ (by simp), u₄.other _ (by decide), g₃ _ (by decide), h.esi]
  -- In the last block, the length.
  refine WP.seq (wp_test fun s₇ f₇ z₇ => WP.block_nil ?_)
  have hC₇ : Common s₀ s₇ := hC₆.of_gpr (fun r _ => by rw [f₇.gpr]) f₇.mem f₇.rd f₇.wr
  have hz₇ : s₇.zf = some (decide (k = 0)) := by
    rw [z₇, hesi₆, BitVec.and_self, ofNat_beq_zero (by omega)]
  have hesi₇ : s₇.gpr .esi = BitVec.ofNat 32 k := by rw [f₇.gpr, hesi₆]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Common s₀ s₈ ∧ s₈.gpr .esi = BitVec.ofNat 32 k ∧
      stateAt s₈.mem (stA s₀) = stateAt s.mem (stA s₀) ∧
      ∀ m, R₀ s₀ m → bytesAt s₈.mem (stA s₀ + 32) 64 = bytesAt s.mem (stA s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)) ?_
    fun s₈ ⟨hC₈, hesi₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show s₇.zf = _; rw [hz₇]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine WP.mono (len_ok hp hC₇) fun s₈ ⟨g₈, rd₈, wr₈, m₈⟩ => ?_
      have hfL : Frame [stR s₀] s₇.mem s₈.mem := by
        rw [m₈]; exact buf_frame _ (by simp [lenL, wordBytes])
      obtain ⟨hfr, hsv, hlo, hhi, hout⟩ := hC₇.frame_keep hp (hfL.mono (by simp))
      refine ⟨⟨rd₈.trans hC₇.rd, wr₈.trans hC₇.wr, by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.ebx],
        by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.ebp],
        by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.esp], hfr, hsv, hlo, hhi, hout⟩,
        by rw [g₈ _ (by decide) (by decide) (by decide), hesi₇], ?_, fun m hm => ?_⟩
      · rw [m₈, ← hst₆, ← f₇.mem]
        apply stateAt_congr
        intro i hi
        rw [st_add]
        exact writeBytes_before _ _ _ (by omega) (by simp [lenL, wordBytes])
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        have e := bytesAt_writeBytes s₇.mem (stA s₀ + 32) 56 (lenL s₀) (by simp [lenL, wordBytes])
        simp only [lenL, List.length_append, show ∀ w, (wordBytes w).length = 4 from fun _ => rfl] at e
        rw [m₈, e, f₇.mem, hby₆, ← lenBytes_halves _ _ m hm.2]
        simp [List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₇, hesi₇, by rw [f₇.mem, hst₆], fun m _ => ?_⟩
      rw [f₇.mem, hby₆]; simp
  -- Compress the block.
  refine WP.seq (WP.mono (args_ok hC₈) fun s₉ ⟨hC₉, g₉, heax₉, hf₉⟩ => ?_)
  refine WP.seq (compress_buf hp hC₉ heax₉ fun s₁₀ hC₁₀ cs₁₀ hst₁₀ => ?_)
  have hesi₁₀ : s₁₀.gpr .esi = BitVec.ofNat 32 k := by
    rw [cs₁₀ _ (by decide), g₉ _ (by decide), hesi₈]
  have hbyte : ∀ i, i < 96 → s₉.mem (stA s₀ + BitVec.ofNat 64 i) = s₈.mem (stA s₀ + BitVec.ofNat 64 i) :=
    fun i hi => frame_bytes hf₉ (R := stR s₀) (by simpa using hp.a_st.symm) (by simp) hi
  have hblk : ∀ m, R₀ s₀ m → blockAt s₉.mem (stA s₀ + 32) = parseBlock fun t =>
      (bytesAt s.mem (stA s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)).getD t 0 := by
    intro m hm
    apply parseBlock_congr
    intro t ht
    rw [show stA s₀ + 32 + BitVec.ofNat 64 t = stA s₀ + BitVec.ofNat 64 (32 + t) by
      simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl, hbyte _ (by omega),
      ← show stA s₀ + 32 + BitVec.ofNat 64 t = stA s₀ + BitVec.ofNat 64 (32 + t) by
      simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl]
    exact bytesAt_getD (hby₈ m hm) ht
  have hst₉ : stateAt s₉.mem (stA s₀) = stateAt s₈.mem (stA s₀) :=
    stateAt_congr fun i hi => hbyte i (by omega)
  -- Next block, if any.
  refine wp_movi fun s₁₁ u₁₁ => wp_subi fun s₁₂ u₁₂ z₁₂ => WP.block_nil ?_
  have hC₁₂ : Common s₀ s₁₂ := hC₁₀.of_gpr (fun r hr => by
      rw [u₁₂.other r (regs3 hr).2.2.2.2, u₁₁.other r (regs3 hr).2.2.2.1]) (by rw [u₁₂.mem, u₁₁.mem])
    (by rw [u₁₂.rd, u₁₁.rd]) (by rw [u₁₂.wr, u₁₁.wr])
  have hz : s₁₂.zf = some (decide (k = 1)) := by
    rw [z₁₂, u₁₁.other _ (by decide), hesi₁₀, lit32 1, sub_beq (a := k) (b := 1) (by omega) (by omega)]
  have hst : ∀ m, R₀ s₀ m → stateAt s₁₂.mem (stA s₀) = compress (stateAt s.mem (stA s₀)) (parseBlock fun t =>
      (bytesAt s.mem (stA s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)).getD t 0) := by
    intro m hm
    rw [u₁₂.mem, u₁₁.mem, hst₁₀, hst₉, hst₈, hblk m hm]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨by show s₁₂.zf = _; rw [hz]; rfl, rfl, ⟨hC₁₂, by omega, by omega, ?_, ?_, fun m hm => ?_⟩⟩
    · rw [u₁₂.other _ (by decide), u₁₁.gpr]; rfl
    · rw [u₁₂.gpr, u₁₁.other _ (by decide), hesi₁₀]; rfl
    · rw [h.hash m hm]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, Fin1, Fin0, hst m hm]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨by show s₁₂.zf = _; rw [hz]; rfl, hC₁₂, fun m hm => ?_⟩
    rw [h.hash m hm, hst m hm]
    simp only [show ¬ (0 = 1) by decide, ite_false, Fin0, List.append_assoc]

/-! ## Prologue -/

/-- The memory after saving our caller's registers and copying `count` and `out` to scratch. -/
def proMem (s₀ : State) : Mem :=
  ((((((s₀.mem.writeW (addr (scr s₀) 112) (s₀.gpr .ebx)).writeW (addr (scr s₀) 116) (s₀.gpr .esi)).writeW
    (addr (scr s₀) 120) (s₀.gpr .edi)).writeW (addr (scr s₀) 124) (s₀.gpr .ebp)).writeW
    (addr (scr s₀) 128) (arg s₀ 1)).writeW (addr (scr s₀) 132) (arg s₀ 2)).writeW (addr (scr s₀) 136) (out s₀)

theorem proMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scR s₀] s₀.mem (proMem s₀) := by
  have c : ∀ d, d + 4 ≤ 160 → (scR s₀).Contains (addr (scr s₀) d) (32 / 8) := fun d hd => hp.scr_in hd
  simp only [proMem]
  exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 112 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 116 (by omega))).writeW (List.mem_singleton_self _) _
    (c 120 (by omega))).writeW (List.mem_singleton_self _) _ (c 124 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 128 (by omega))).writeW (List.mem_singleton_self _) _
    (c 132 (by omega))).writeW (List.mem_singleton_self _) _ (c 136 (by omega))

theorem proMem_words {s₀ : State} (hp : Pre s₀) :
    Saved s₀ (proMem s₀) ∧ (proMem s₀).readW (addr (scr s₀) 128) 32 = arg s₀ 1 ∧
      (proMem s₀).readW (addr (scr s₀) 132) 32 = arg s₀ 2 ∧ (proMem s₀).readW (addr (scr s₀) 136) 32 = out s₀ := by
  have hs := hp.scr_fit
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 160 → e + 4 ≤ 160 → d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (scr s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
    fun m v d e h₁ h₂ h => readW_writeW_addr m v (by omega) (by omega) h
  refine ⟨fun p hp' => ?_, ?_, ?_, ?_⟩
  · simp only [VG.Impl.Sha256.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp only [proMem] <;>
      rw [w _ _ _ 136 (by omega) (by omega) (by omega), w _ _ _ 132 (by omega) (by omega) (by omega),
        w _ _ _ 128 (by omega) (by omega) (by omega)]
    · rw [w _ _ 112 124 (by omega) (by omega) (by omega), w _ _ 112 120 (by omega) (by omega) (by omega),
        w _ _ 112 116 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
    · rw [w _ _ 116 124 (by omega) (by omega) (by omega), w _ _ 116 120 (by omega) (by omega) (by omega),
        Mem.readW_writeW_self32]
    · rw [w _ _ 120 124 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
    · rw [Mem.readW_writeW_self32]
  · simp only [proMem]
    rw [w _ _ 128 136 (by omega) (by omega) (by omega), w _ _ 128 132 (by omega) (by omega) (by omega),
      Mem.readW_writeW_self32]
  · simp only [proMem]
    rw [w _ _ 132 136 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · simp only [proMem]; rw [Mem.readW_writeW_self32]

/-- The arguments, in memory that differs only in the scratch space. -/
theorem arg_read {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [scR s₀] s₀.mem m) {e : Nat}
    (h₁ : 4 ≤ e) (h₂ : e + 4 ≤ 24) : m.readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 :=
  hf.readW (Region.contains_self _ _) (by simpa using hp.a_scr.sub_left (hp.arg_sub h₁ h₂)) (by decide)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.seq (.block (([.mov .eax (.mem (at_ .esp 20))] : List Instr) ++ save .eax ++
      ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
       .mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp 128) .ecx,
       .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp 132) .ecx,
       .mov .ecx (.mem (at_ .esp 16)), .store (at_ .ebp 136) .ecx,
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 63),
       .mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .mov .ecx (.imm 0x80),
       .store8 (at_ .edx 32) .cl, .alu .add .edi (.imm 1),
       .mov .esi (.imm 0), .alu .cmp .edi (.imm 57)] : List Instr)))
      (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))) s₀
      fun s => ∃ k, LInv s₀ k (cnt s₀ % 64 + 1) s := by
  have hst := hp.st_fit
  have hr : cnt s₀ % 64 < 64 := Nat.mod_lt _ (by omega)
  have ain : ∀ e, 4 ≤ e → e + 4 ≤ 24 → ∀ t : State, t.rd = s₀.rd → t.wr = s₀.wr →
      InRegions (t.rd ++ t.wr) (addr (esp₀ s₀) e) 4 :=
    fun e h₁ h₂ t hrd hwr => ⟨argR s₀, by simp [hrd, hwr, hp.wr], hp.arg_in h₁ h₂⟩
  have sout : ∀ d, d + 4 ≤ 160 → ∀ t : State, t.wr = s₀.wr → InRegions t.wr (addr (scr s₀) d) 4 :=
    fun d hd t hwr => ⟨scR s₀, by simp [hwr, hp.wr], hp.scr_in hd⟩
  have fw : ∀ {m : Mem}, Frame [scR s₀] s₀.mem m → ∀ d, d + 4 ≤ 160 → ∀ v : BitVec 32,
      Frame [scR s₀] s₀.mem (m.writeW (addr (scr s₀) d) v) :=
    fun hf d hd v => hf.writeW (List.mem_singleton_self _) _ (hp.scr_in hd)
  simp only [List.cons_append, save, saved, List.map_cons, List.map_nil,
    List.nil_append]
  refine WP.seq ?_
  refine wp_movm (a := addr (esp₀ s₀) 20) (ea_at _ _ _) (ain 20 (by omega) (by omega) s₀ rfl rfl) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (a := addr (scr s₀) 112) (by rw [ea_at, e₁]) (sout 112 (by omega) _ u₁.wr) fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) 116) (by rw [ea_at, u₂.gpr, e₁])
    (sout 116 (by omega) _ (by rw [u₂.wr, u₁.wr])) fun s₃ u₃ => ?_
  refine wp_store (a := addr (scr s₀) 120) (by rw [ea_at, u₃.gpr, u₂.gpr, e₁])
    (sout 120 (by omega) _ (by rw [u₃.wr, u₂.wr, u₁.wr])) fun s₄ u₄ => ?_
  refine wp_store (a := addr (scr s₀) 124) (by rw [ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (sout 124 (by omega) _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₅ : s₅.gpr .esp = esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  have m₅ : s₅.mem = (((s₀.mem.writeW (addr (scr s₀) 112) (s₀.gpr .ebx)).writeW (addr (scr s₀) 116)
      (s₀.gpr .esi)).writeW (addr (scr s₀) 120) (s₀.gpr .edi)).writeW (addr (scr s₀) 124) (s₀.gpr .ebp) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
  have f₅ : Frame [scR s₀] s₀.mem s₅.mem := by
    rw [m₅]; exact fw (fw (fw (fw (Frame.refl _ _) 112 (by omega) _) 116 (by omega) _) 120 (by omega) _)
      124 (by omega) _
  refine wp_mov fun s₆ u₆ => wp_movm (a := addr (esp₀ s₀) 4) (by rw [ea_at, u₆.other _ (by decide), sp₅])
    (ain 4 (by omega) (by omega) s₆ (by rw [u₆.rd, rd₅]) (by rw [u₆.wr, wr₅])) fun s₇ u₇ => ?_
  have ebp₇ : s₇.gpr .ebp = scr s₀ := by rw [u₇.other _ (by decide), u₆.gpr, g₅, e₁]
  have sp₇ : s₇.gpr .esp = esp₀ s₀ := by rw [u₇.other _ (by decide), u₆.other _ (by decide), sp₅]
  have ebx₇ : s₇.gpr .ebx = st s₀ := by
    rw [u₇.gpr, u₆.mem, arg_read hp f₅ (by omega) (by omega)]; rfl
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, rd₅]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, wr₅]
  have m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  -- `count` and `out` into scratch.
  refine wp_movm (a := addr (esp₀ s₀) 8) (by rw [ea_at, sp₇]) (ain 8 (by omega) (by omega) s₇ rd₇ wr₇)
    fun s₈ u₈ => ?_
  refine wp_store (a := addr (scr s₀) 128) (by rw [ea_at, u₈.other _ (by decide), ebp₇])
    (sout 128 (by omega) _ (by rw [u₈.wr, wr₇])) fun s₉ u₉ => ?_
  have v₉ : s₉.mem = s₅.mem.writeW (addr (scr s₀) 128) (arg s₀ 1) := by
    rw [u₉.mem, u₈.gpr, u₈.mem, m₇, arg_read hp f₅ (by omega) (by omega)]; rfl
  have f₉ : Frame [scR s₀] s₀.mem s₉.mem := by rw [v₉]; exact fw f₅ 128 (by omega) _
  refine wp_movm (a := addr (esp₀ s₀) 12) (by rw [ea_at, u₉.gpr, u₈.other _ (by decide), sp₇])
    (ain 12 (by omega) (by omega) _ (by rw [u₉.rd, u₈.rd, rd₇]) (by rw [u₉.wr, u₈.wr, wr₇])) fun s₁₀ u₁₀ => ?_
  refine wp_store (a := addr (scr s₀) 132) (by rw [ea_at, u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide),
    ebp₇]) (sout 132 (by omega) _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, wr₇])) fun s₁₁ u₁₁ => ?_
  have v₁₁ : s₁₁.mem = s₉.mem.writeW (addr (scr s₀) 132) (arg s₀ 2) := by
    rw [u₁₁.mem, u₁₀.gpr, u₁₀.mem, arg_read hp f₉ (by omega) (by omega)]; rfl
  have f₁₁ : Frame [scR s₀] s₀.mem s₁₁.mem := by rw [v₁₁]; exact fw f₉ 132 (by omega) _
  have g₁₁ : ∀ r, r ≠ .ecx → s₁₁.gpr r = s₇.gpr r := fun r h => by
    rw [u₁₁.gpr, u₁₀.other r h, u₉.gpr, u₈.other r h]
  refine wp_movm (a := addr (esp₀ s₀) 16) (by rw [ea_at, g₁₁ _ (by decide), sp₇])
    (ain 16 (by omega) (by omega) _ (by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇])
      (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇])) fun s₁₂ u₁₂ => ?_
  refine wp_store (a := addr (scr s₀) 136) (by rw [ea_at, u₁₂.other _ (by decide), g₁₁ _ (by decide), ebp₇])
    (sout 136 (by omega) _ (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇])) fun s₁₃ u₁₃ => ?_
  have m₁₃ : s₁₃.mem = proMem s₀ := by
    rw [u₁₃.mem, u₁₂.gpr, u₁₂.mem, arg_read hp f₁₁ (by omega) (by omega), v₁₁, v₉, m₅]; rfl
  have g₁₃ : ∀ r, r ≠ .ecx → s₁₃.gpr r = s₇.gpr r := fun r h => by rw [u₁₃.gpr, u₁₂.other r h, g₁₁ r h]
  have rd₁₃ : s₁₃.rd = s₀.rd := by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇]
  -- The `0x80` byte.
  refine wp_movm (a := addr (esp₀ s₀) 8) (by rw [ea_at, g₁₃ _ (by decide), sp₇])
    (ain 8 (by omega) (by omega) _ rd₁₃ wr₁₃) fun s₁₄ u₁₄ => wp_andi fun s₁₅ u₁₅ => ?_
  have edi₁₅ : s₁₅.gpr .edi = BitVec.ofNat 32 (cnt s₀ % 64) := by
    rw [u₁₅.gpr, u₁₄.gpr, m₁₃, arg_read hp (proMem_frame hp) (by omega) (by omega), and63, cnt_mod]
    rfl
  refine wp_mov fun s₁₆ u₁₆ => wp_add fun s₁₇ u₁₇ => wp_movi fun s₁₈ u₁₈ => ?_
  have edx₁₈ : s₁₈.gpr .edx = st s₀ + BitVec.ofNat 32 (cnt s₀ % 64) := by
    rw [u₁₈.other _ (by decide), u₁₇.gpr, u₁₆.gpr, u₁₆.other _ (by decide), edi₁₅, u₁₅.other _ (by decide),
      u₁₄.other _ (by decide), g₁₃ _ (by decide), ebx₇]
  have hq : addr (s₁₈.gpr .edx) 32 = stA s₀ + 32 + BitVec.ofNat 64 (cnt s₀ % 64) := by
    rw [edx₁₈, addr_add_ofNat (by omega), st_add, Nat.add_comm]
  have hout : InRegions s₁₈.wr (stA s₀ + 32 + BitVec.ofNat 64 (cnt s₀ % 64)) 1 :=
    ⟨stR s₀, by simp [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, wr₁₃, hp.wr], by
      rw [st_add]; exact contains_offset (by omega) (by omega)⟩
  refine wp_store8 (r := .cl) (a := stA s₀ + 32 + BitVec.ofNat 64 (cnt s₀ % 64)) (by rw [ea_at, hq]) hout
    fun s₁₉ u₁₉ => wp_addi fun s₂₀ u₂₀ => wp_movi fun s₂₁ u₂₁ => wp_cmpi fun s₂₂ f₂₂ cf₂₂ _ => WP.block_nil ?_
  have hm₁₉ : s₁₉.mem = writeBytes (proMem s₀) (stA s₀ + 32 + BitVec.ofNat 64 (cnt s₀ % 64)) [0x80] := by
    rw [u₁₉.mem, show Reg8.cl.reg = Reg.ecx from rfl, u₁₈.gpr, u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem, m₁₃,
      ← List.nil_append [(0x80 : Byte)], writeBytes_snoc _ _ _ _ (by simp), writeBytes_nil]
    simp
  have hm₂₂ : s₂₂.mem = s₁₉.mem := by rw [f₂₂.mem, u₂₁.mem, u₂₀.mem]
  have hfb : Frame [stR s₀] (proMem s₀) s₁₉.mem := by rw [hm₁₉]; exact buf_frame _ (by simp; omega)
  have keep : ∀ r, r ≠ .ecx → r ≠ .edi → r ≠ .edx → r ≠ .esi → s₂₂.gpr r = s₇.gpr r := fun r h1 h2 h3 h4 => by
    rw [f₂₂.gpr, u₂₁.other r h4, u₂₀.other r h2, u₁₉.gpr, u₁₈.other r h1, u₁₇.other r h3, u₁₆.other r h3,
      u₁₅.other r h2, u₁₄.other r h2, g₁₃ r h1]
  obtain ⟨hsv, hlo, hhi, hou⟩ := proMem_words hp
  have word : ∀ d, d + 4 ≤ 160 → s₂₂.mem.readW (addr (scr s₀) d) 32 = (proMem s₀).readW (addr (scr s₀) d) 32 :=
    fun d hd => by
      rw [hm₂₂]
      exact hfb.readW (Region.contains_self _ _) (by simpa using hp.st_scr.symm.sub_left (hp.scr_sub hd))
        (by decide)
  have hC : Common s₀ s₂₂ :=
    ⟨by rw [f₂₂.rd, u₂₁.rd, u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, rd₁₃],
      by rw [f₂₂.wr, u₂₁.wr, u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, wr₁₃],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), ebx₇],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), ebp₇],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), sp₇],
      by rw [hm₂₂]; exact ((proMem_frame hp).mono (by simp)).trans (hfb.mono (by simp)),
      fun p hp' => by
        have hd : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
          simp only [VG.Impl.Sha256.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl | rfl | rfl <;> simp
        rw [word _ (by omega)]; exact hsv p hp',
      by rw [word 128 (by omega)]; exact hlo, by rw [word 132 (by omega)]; exact hhi,
      by rw [word 136 (by omega)]; exact hou⟩
  have edi₂₂ : s₂₂.gpr .edi = BitVec.ofNat 32 (cnt s₀ % 64 + 1) := by
    rw [f₂₂.gpr, u₂₁.other _ (by decide), u₂₀.gpr, u₁₉.gpr, u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), edi₁₅, ofNat_succ]
  have hcf : s₂₂.cf = some (decide (cnt s₀ % 64 + 1 < 57)) := by
    rw [cf₂₂, ← f₂₂.gpr, edi₂₂, toNat_ofNat_lt (by omega)]; rfl
  -- The facts about the buffer.
  have hst : stateAt s₂₂.mem (stA s₀) = stateAt s₀.mem (stA s₀) := by
    apply stateAt_congr
    intro i hi
    rw [hm₂₂, hm₁₉, st_add, writeBytes_before _ _ _ (by omega) (by simp; omega)]
    exact frame_bytes (proMem_frame hp) (R := stR s₀) (by simpa using hp.st_scr) (by simp) (by show i < 96; omega)
  have hbytes : ∀ m, R₀ s₀ m → bytesAt s₂₂.mem (stA s₀ + 32) (cnt s₀ % 64 + 1) = rest m ++ [0x80] := by
    intro m hm
    have e := bytesAt_writeBytes (proMem s₀) (stA s₀ + 32) (cnt s₀ % 64) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₂₂, hm₁₉, e]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    rw [st_add]
    exact frame_bytes (proMem_frame hp) (R := stR s₀) (by simpa using hp.st_scr) (by simp)
      (by show 32 + i < 96; have := hm.length; omega)
  have hesi : s₂₂.gpr .esi = 0 := by rw [f₂₂.gpr, u₂₁.gpr]
  refine WP.ite (!decide (cnt s₀ % 64 + 1 < 57)) (by show s₂₂.cf.map (!·) = _; rw [hcf]; rfl)
    (fun hb => ?_) (fun hb => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb
    refine wp_movi fun s₂₃ u₂₃ => WP.block_nil ⟨1, hC.of_gpr (fun r hr => u₂₃.other r (regs3 hr).2.2.2.2)
      u₂₃.mem u₂₃.rd u₂₃.wr, (Nat.le_refl _), by omega, by rw [u₂₃.other _ (by decide), edi₂₂], by rw [u₂₃.gpr]; rfl,
      fun m hm => ?_⟩
    simp only [↓reduceIte]
    rw [hash_two (by rw [← hm.length]; omega), Fin1, u₂₃.mem, hbytes m hm, hst, hm.1.1,
      ← hm.length, show 64 - (cnt s₀ % 64 + 1) = 63 - cnt s₀ % 64 by omega]
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    refine WP.block_nil ⟨0, hC, by omega, by omega, edi₂₂, by rw [hesi]; rfl, fun m hm => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [hash_one (by rw [← hm.length]; omega), Fin0, hbytes m hm, hst, hm.1.1,
      ← hm.length, show 56 - (cnt s₀ % 64 + 1) = 55 - cnt s₀ % 64 by omega]

theorem seq_assoc {M : ISA} {a b c : Prog M} {s : M.State} {Q : M.State → Prop} :
    WP M (.seq (.seq a b) c) s Q ↔ WP M (.seq a (.seq b c)) s Q := by
  simp only [WP.seq_iff]

theorem argWord_eq {s : State} (hsp : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) {k : Nat} (hk : k < 20) :
    addr (s.gpr .esp) 4 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (k / 4))).setWidth 64 = addr (s.gpr .esp) (4 + 4 * (k / 4))
    from rfl, addr_eq (by omega), addr_eq (by omega), BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2; omega

end VG.Proof.Sha256.X86.Stream.Finalize
