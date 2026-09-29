import VerifiedGarbage.Proof.Sha512.X86.Stream.Common
import VerifiedGarbage.Proof.Sha256.X86.Stream.Finalize

/-!
# Streaming SHA-512 on x86 (32-bit): `finalize`

Untrusted: everything here is checked by Lean. The structure of the SHA-256
proof (`VG.Proof.Sha256.X86.Stream.Finalize`), with `state` in `ebx`, the
buffered bytes in `edi` and whether the block being padded is not the last
in `esi`; `count`, `out` and `scratch` stay in their argument words, and the
compression function is called (`compressAt_ok`), with the 20 bytes below
`esp` for its frame.
-/

namespace VG.Proof.Sha512.X86.Stream.Finalize

open VG VG.X86 VG.Impl.Sha512.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_store8 wp_add wp_addi
  wp_sub wp_subi wp_andi wp_or wp_cmpi wp_test wp_shr wp_bswap contains_addr sub_offset frame_bytes
  addr_add_ofNat readW_writeW_addr ofNat_beq_zero sub_ofNat sub_beq ofNat_succ ofNat_pred toNat_ofNat_lt
  bytesAt_getD addr_toNat)
open VG.Proof.Sha256.X86.Stream.Finalize (times8)
open VG.Proof.Sha512.Word64 (lo hi wordBytes_split lo_shr61 hi_shr61 lo_shl3 hi_shl3)
open VG.Proof.Sha512.Stream
open VG.Spec.Sha512 (HashValue stateAt blockAt compress parseBlock bytesAt wordBytes)
open VG.Proof.Sha512 (countX86)

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
abbrev stR : Region := ⟨stA s₀, 192⟩
abbrev outR : Region := ⟨outA s₀, 64⟩
abbrev scR : Region := ⟨scA s₀, 272⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (esp₀ s₀) 20

/-- The messages the initial state represents, from the initial hash value
`iv`, of fewer than 2⁶⁴ bytes. -/
def R₀ (iv : HashValue) (m : List Byte) : Prop :=
  Spec.Sha512.Repr iv s₀.mem (stA s₀) m ∧ m.length < 2 ^ 64 ∧ countX86 s₀ = BitVec.ofNat 64 m.length

/-- Our caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop := ∀ p ∈ saved, m.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1

/-- The digest, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (compress (stateAt mem (stA s₀))
    (parseBlock fun t => (bytesAt mem (stA s₀ + 64) n ++ List.replicate (128 - n) 0).getD t 0))
    (parseBlock fun t => (List.replicate 112 0 ++ lenBytes m).getD t 0)

/-- The digest, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (stateAt mem (stA s₀))
    (parseBlock fun t => (bytesAt mem (stA s₀ + 64) n ++ List.replicate (112 - n) 0 ++ lenBytes m).getD t 0)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR s₀, outR s₀, scR s₀]
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
  st_fit : (st s₀).toNat + 192 ≤ 2 ^ 32
  out_fit : (out s₀).toNat + 64 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 272 ≤ 2 ^ 32
  sp_lo : 20 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 24 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Proof.Sha512.finalizeX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  have e := stk_eq h18
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by show (below _ _).Disjoint _; rw [e]; exact h12,
    by show (below _ _).Disjoint _; rw [e]; exact h13, by show (below _ _).Disjoint _; rw [e]; exact h14,
    h15, h16, h17, h18, h19⟩

theorem cnt_mod (s₀ : State) : cnt s₀ % 128 = (arg s₀ 1).toNat % 128 := by
  simp only [cnt, countX86]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (arg s₀ 1).isLt, Nat.shiftLeft_eq]
  omega

theorem R₀.length {s₀ : State} {iv : HashValue} {m : List Byte} (h : R₀ s₀ iv m) :
    cnt s₀ % 128 = m.length % 128 := by
  rw [cnt, h.2.2, BitVec.toNat_ofNat]
  omega

theorem st_add (s₀ : State) (n : Nat) :
    stA s₀ + 64 + BitVec.ofNat 64 n = stA s₀ + BitVec.ofNat 64 (64 + n) := by
  simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ 272) : (scR s₀).Contains (addr (scr s₀) d) 4 :=
  contains_addr hd (by omega) hp.scr_fit

theorem scr_sub {d : Nat} (hd : d + 4 ≤ 272) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR s₀) := by
  rw [addr_eq (by have := hp.scr_fit; omega)]
  exact sub_offset hd (by omega)

theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [show argAddr s₀ 0 = addr (esp₀ s₀) 4 from rfl, addr_eq (by omega)]
  rw [addr_eq (by omega)] at ha
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.arg_sub hd₁ hd (addr (esp₀ s₀) d) (by simp [Region.Contains])
  have h2 := hp.arg_sub hd₁ hd (addr (esp₀ s₀) d + 3) (by simp only [Region.Contains]; bv_omega)
  simp only [Region.Contains] at this h2 ⊢
  bv_omega

/-- The arguments are above the stack region. -/
theorem a_stk : (argR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [show argAddr s₀ 0 = addr (esp₀ s₀) 4 from rfl, addr_eq (by omega)] at h₁
  rw [Taint.sub_setWidth (by omega)] at h₂
  have hE : ((esp₀ s₀).setWidth 64).toNat = (esp₀ s₀).toNat := addr_toNat _
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth (by omega)] at h₂
  have hE : ((esp₀ s₀).setWidth 64).toNat = (esp₀ s₀).toNat := addr_toNat _
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

/-- The words of the scratch space from 224 on (the saved registers) are
outside the regions the compression function writes. -/
theorem saved_sep {d : Nat} (hd₁ : 224 ≤ d) (hd : d + 4 ≤ 272) :
    ∀ r ∈ [(⟨stA s₀, 64⟩ : Region), ⟨scA s₀, 224⟩, stkR s₀], Region.Disjoint ⟨addr (scr s₀) d, 4⟩ r := by
  have := hp.scr_fit
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.st_scr.symm.sub_left (hp.scr_sub hd)).sub_right (Region.sub_prefix (by omega))
  · intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    rw [addr_eq (by omega)] at h₁
    have hE : (scA s₀).toNat = (scr s₀).toNat := addr_toNat _
    generalize scA s₀ = b at *
    bv_omega
  · exact (hp.stk_scr.symm.sub_left (hp.scr_sub hd))

end Pre

/-! ## Invariants -/

structure Common (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  esp : s.gpr .esp = esp₀ s₀
  frame : Frame [stR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv (s₀ : State) (k n : Nat) (s : State) : Prop extends Common s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ 112 + 16 * k
  edi : s.gpr .edi = BitVec.ofNat 32 n
  esi : s.gpr .esi = BitVec.ofNat 32 k
  hash : ∀ iv m, R₀ s₀ iv m → Spec.Sha512.finalHash iv m =
    (if k = 1 then Fin1 s₀ s.mem n m else Fin0 s₀ s.mem n m).toList.flatMap wordBytes

/-- All blocks are compressed. -/
def Done (s₀ : State) (s : State) : Prop :=
  Common s₀ s ∧ ∀ iv m, R₀ s₀ iv m → Spec.Sha512.finalHash iv m = (stateAt s.mem (stA s₀)).toList.flatMap wordBytes

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common s₀ s)
    (hg : ∀ r ∈ [Reg.ebx, .esp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by simp)]; exact h.ebx
  esp := by rw [hg _ (by simp)]; exact h.esp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- The argument words are never written. -/
theorem Common.arg {s₀ : State} (hp : Pre s₀) {s : State} (h : Common s₀ s) {d : Nat} (h₁ : 4 ≤ d)
    (h₂ : d + 4 ≤ 24) : s.mem.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 := by
  refine h.frame.readW (r := ⟨addr (esp₀ s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_st.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_scr.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_stk.sub_left (hp.arg_sub h₁ h₂)

/-- The argument words, read with `esp`. -/
theorem Common.argIn {s₀ : State} (hp : Pre s₀) {s : State} (h : Common s₀ s) {d : Nat} (h₁ : 4 ≤ d)
    (h₂ : d + 4 ≤ 24) : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [h.rd, hp.rd], hp.arg_in h₁ h₂⟩

/-- A write within the state keeps what `Common` says about memory. -/
theorem Common.writeSt {s₀ : State} (hp : Pre s₀) {s : State} (h : Common s₀ s) {m : Mem}
    (hf : Frame [stR s₀] s.mem m) : Frame [stR s₀, scR s₀, stkR s₀] s₀.mem m ∧ Saved s₀ m := by
  refine ⟨h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  have hd : 224 ≤ p.2 ∧ p.2 + 4 ≤ 240 := by
    simp only [VG.Impl.Sha512.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp
  rw [← h.saved p hp']
  refine hf.readW (r := ⟨addr (scr s₀) p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact hp.st_scr.symm.sub_left (hp.scr_sub (by omega))

/-- Writing buffer bytes `[n, n + |xs|)`. -/
theorem buf_frame {s₀ : State} (m : Mem) {n : Nat} {xs : List Byte} (hn : n + xs.length ≤ 128) :
    Frame [stR s₀] m (writeBytes m (stA s₀ + 64 + BitVec.ofNat 64 n) xs) := by
  refine writeBytes_frame _ _ _ ?_
  rw [st_add]
  exact contains_offset (by omega) (by omega)

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ [Reg.ebx, .esp, .esi, .ecx], s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  edi : s.gpr .edi = BitVec.ofNat 32 (n + j)
  eax : s.gpr .eax = BitVec.ofNat 32 (lim - n - j)
  mem : s.mem = writeBytes sI.mem (stA s₀ + 64 + BitVec.ofNat 64 n) (List.replicate j 0)

theorem zero_step {s₀ : State} (hp : Pre s₀) {sI : State} (hC : Common s₀ sI) (hecx : sI.gpr .ecx = 0)
    {n lim j : Nat} (hlim : lim ≤ 128) (hj : j < lim - n) {s : State} (h : Zero s₀ sI n lim j s) :
    WP isa (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .store8 (at_ .edx 64) .cl,
      .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) s fun s' =>
      Zero s₀ sI n lim (j + 1) s' ∧ s'.zf = some (decide (lim - n - (j + 1) = 0)) := by
  have hst := hp.st_fit
  have hebx : s.gpr .ebx = st s₀ := by rw [h.keep _ (by simp), hC.ebx]
  have ha : stA s₀ + 64 + BitVec.ofNat 64 n + BitVec.ofNat 64 j = stA s₀ + BitVec.ofNat 64 (64 + n + j) := by
    simp only [BitVec.ofNat_add]; ac_rfl
  have hout : InRegions s.wr (stA s₀ + 64 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [ha]
    exact contains_offset (by omega) (by omega)
  refine wp_mov fun s₁ u₁ => wp_add fun s₂ u₂ => ?_
  refine wp_store8 (r := .cl) (a := stA s₀ + 64 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ u₃ => ?_
  · rw [ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), hebx, h.edi, ha, addr_add_ofNat (by omega)]
    congr 2; omega
  refine wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => WP.block_nil ⟨⟨by omega, fun r hr => ?_,
    by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .eax ∧ r ≠ .edi ∧ r ≠ .edx := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
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
    {n lim : Nat} (hlim : lim ≤ 128) (hn : n ≤ lim) {s : State} (h : Zero s₀ sI n lim 0 s)
    (hz : s.zf = some (decide (lim - n = 0))) :
    WP isa (.ite .e (.block []) (.loop (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edi),
      .store8 (at_ .edx 64) .cl, .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) .ne)) s
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

/-- The call of the compression function on the buffer. -/
theorem compress_buf {s₀ : State} (hp : Pre s₀) {s : State} (hC : Common s₀ s) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' → (∀ r ∈ [Reg.ebx, .esi, .edi, .ebp, .esp], s'.gpr r = s.gpr r) →
      stateAt s'.mem (stA s₀) = compress (stateAt s.mem (stA s₀)) (blockAt s.mem (stA s₀ + 64)) → Q s') :
    WP isa (compressAt 20) s Q := by
  refine compressAt_ok (st := st s₀) (scr := scr s₀) (E := esp₀ s₀) hC.esp hC.ebx
    (hC.argIn hp (by omega) (by omega)) (by rw [hC.arg hp (by omega) (by omega)]; rfl) hp.st_fit hp.scr_fit
    hp.sp_lo hp.st_scr hp.stk_st hp.stk_scr (by simp [hC.wr, hp.wr]) (by simp [hC.wr, hp.wr])
    fun s' hrd hwr hg hf hst => hQ s' ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [hg _ (by simp)]; exact hC.ebx,
      by rw [hg _ (by simp)]; exact hC.esp, hC.frame.trans (hf.sub fun r hr => ?_), fun p hp' => ?_⟩ hg hst
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · have hd : 224 ≤ p.2 ∧ p.2 + 4 ≤ 240 := by
      simp only [VG.Impl.Sha512.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> simp
    rw [← hC.saved p hp']
    exact hf.readW (r := ⟨addr (scr s₀) p.2, 4⟩) (Region.contains_self _ _)
      (hp.saved_sep hd.1 (by omega)) (by decide)

/-! ## The message length -/

theorem writeW_bswap (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a (bswap w) = writeBytes m a (Spec.Sha256.wordBytes w) := by
  rw [Mem.writeW, write_eq_writeBytes, ← VG.Proof.Sha256.X86.Stream.bswap_bytes]; rfl

/-- The bytes `lenW` writes, from `count` in the argument words 1 and 2. -/
def lenL (s₀ : State) : List Byte :=
  Spec.Sha256.wordBytes 0 ++ Spec.Sha256.wordBytes (arg s₀ 2 >>> 29) ++
    Spec.Sha256.wordBytes ((arg s₀ 2 <<< 3) ||| (arg s₀ 1 >>> 29)) ++ Spec.Sha256.wordBytes (arg s₀ 1 <<< 3)

theorem lenL_eq {s₀ : State} {iv : HashValue} {m : List Byte} (hm : R₀ s₀ iv m) : lenL s₀ = lenBytes m := by
  have hc := hm.2.2
  have h8 : BitVec.ofNat 64 (8 * m.length) = countX86 s₀ <<< 3 := by
    rw [hc]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  rw [lenBytes_split m hm.2.1, ← hc, h8, wordBytes_split, wordBytes_split, hi_shr61, lo_shr61, hi_shl3,
    lo_shl3]
  simp only [countX86, Word64.hi_append, Word64.lo_append, lenL, List.append_assoc]

theorem lenL_length (s₀ : State) : (lenL s₀).length = 16 := rfl

/-- Writing the message length. -/
theorem len_ok {s₀ : State} (hp : Pre s₀) {s : State} (hC : Common s₀ s) :
    WP isa (.block lenW) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = writeBytes s.mem (stA s₀ + 64 + BitVec.ofNat 64 112) (lenL s₀) := by
  have hst := hp.st_fit
  have hout : ∀ o, o + 4 ≤ 192 → InRegions s.wr (addr (st s₀) o) 4 :=
    fun o ho => ⟨stR s₀, by simp [hC.wr, hp.wr], contains_addr ho (by omega) hst⟩
  unfold lenW
  refine wp_movm (a := addr (esp₀ s₀) 8) (by rw [ea_at, hC.esp]) (hC.argIn hp (by omega) (by omega))
    fun s₁ u₁ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 12) (by rw [ea_at, u₁.other _ (by decide), hC.esp])
    (by rw [u₁.rd, u₁.wr]; exact hC.argIn hp (by omega) (by omega)) fun s₂ u₂ => ?_
  have a2 : s₂.gpr .eax = arg s₀ 1 := by
    rw [u₂.other _ (by decide), u₁.gpr, hC.arg hp (by omega) (by omega)]; rfl
  have c2 : s₂.gpr .ecx = arg s₀ 2 := by
    rw [u₂.gpr, u₁.mem, hC.arg hp (by omega) (by omega)]; rfl
  have b2 : s₂.gpr .ebx = st s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hC.ebx]
  refine wp_movi fun s₃ u₃ => wp_store (a := addr (st s₀) 176) (by rw [ea_at, u₃.other _ (by decide), b2])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hout 176 (by omega)) fun s₄ u₄ => ?_
  refine wp_mov fun s₅ u₅ => wp_shr (by decide) fun s₆ u₆ => wp_bswap fun s₇ u₇ => ?_
  have g₇ : ∀ r, r ≠ .edx → s₇.gpr r = s₂.gpr r := fun r h => by
    rw [u₇.other r h, u₆.other r h, u₅.other r h, u₄.gpr, u₃.other r h]
  refine wp_store (a := addr (st s₀) 180) (by rw [ea_at, g₇ _ (by decide), b2])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hout 180 (by omega)) fun s₈ u₈ => ?_
  refine wp_add fun s₉ u₉ => wp_add fun s₁₀ u₁₀ => wp_add fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ =>
    wp_shr (by decide) fun s₁₃ u₁₃ => wp_or fun s₁₄ u₁₄ => wp_bswap fun s₁₅ u₁₅ => ?_
  have g₁₅ : ∀ r, r ≠ .edx → r ≠ .ecx → s₁₅.gpr r = s₂.gpr r := fun r h h' => by
    rw [u₁₅.other r h', u₁₄.other r h', u₁₃.other r h, u₁₂.other r h, u₁₁.other r h', u₁₀.other r h',
      u₉.other r h', u₈.gpr, g₇ r h]
  refine wp_store (a := addr (st s₀) 184) (by rw [ea_at, g₁₅ _ (by decide) (by decide), b2])
    (by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr,
      u₂.wr, u₁.wr]; exact hout 184 (by omega)) fun s₁₆ u₁₆ => ?_
  refine wp_add fun s₁₇ u₁₇ => wp_add fun s₁₈ u₁₈ => wp_add fun s₁₉ u₁₉ => wp_bswap fun s₂₀ u₂₀ => ?_
  have g₂₀ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ecx → s₂₀.gpr r = s₂.gpr r := fun r h h' h'' => by
    rw [u₂₀.other r h, u₁₉.other r h, u₁₈.other r h, u₁₇.other r h, u₁₆.gpr, g₁₅ r h' h'']
  refine wp_store (a := addr (st s₀) 188) (by rw [ea_at, g₂₀ _ (by decide) (by decide) (by decide), b2])
    (by rw [u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr,
      u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hout 188 (by omega)) fun s₂₁ u₂₁ => WP.block_nil ?_
  refine ⟨fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
  · rw [u₂₁.gpr, g₂₀ r h1 h3 h2, u₂.other r h2, u₁.other r h1]
  · rw [u₂₁.rd, u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd,
      u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₂₁.wr, u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr,
      u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  -- The values stored.
  have v0 : s₃.gpr .edx = bswap 0 := by rw [u₃.gpr]; decide
  have v1 : s₇.gpr .edx = bswap (arg s₀ 2 >>> 29) := by
    rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.other _ (by decide), c2]
  have c11 : s₁₁.gpr .ecx = arg s₀ 2 <<< 3 := by
    rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.gpr, g₇ _ (by decide), c2, times8]
  have v2 : s₁₅.gpr .ecx = bswap ((arg s₀ 2 <<< 3) ||| (arg s₀ 1 >>> 29)) := by
    rw [u₁₅.gpr, u₁₄.gpr, u₁₃.gpr, u₁₃.other _ (by decide), u₁₂.gpr, u₁₂.other _ (by decide), c11,
      u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, g₇ _ (by decide), a2]
  have v3 : s₂₀.gpr .eax = bswap (arg s₀ 1 <<< 3) := by
    rw [u₂₀.gpr, u₁₉.gpr, u₁₈.gpr, u₁₇.gpr, u₁₆.gpr, g₁₅ _ (by decide) (by decide), a2, times8]
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have a0 : addr (st s₀) 176 = stA s₀ + 64 + BitVec.ofNat 64 112 := by
    rw [addr_eq (by omega), BitVec.add_assoc]; rfl
  have a1 : addr (st s₀) 180 = stA s₀ + 64 + BitVec.ofNat 64 112 + BitVec.ofNat 64 4 := by
    rw [addr_eq (by omega), BitVec.add_assoc, BitVec.add_assoc]; rfl
  have a2' : addr (st s₀) 184 = stA s₀ + 64 + BitVec.ofNat 64 112 + BitVec.ofNat 64 8 := by
    rw [addr_eq (by omega), BitVec.add_assoc, BitVec.add_assoc]; rfl
  have a3 : addr (st s₀) 188 = stA s₀ + 64 + BitVec.ofNat 64 112 + BitVec.ofNat 64 12 := by
    rw [addr_eq (by omega), BitVec.add_assoc, BitVec.add_assoc]; rfl
  rw [u₂₁.mem, v3, u₂₀.mem, u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, v2, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem,
    u₁₀.mem, u₉.mem, u₈.mem, v1, u₇.mem, u₆.mem, u₅.mem, u₄.mem, v0, u₃.mem, m₂, writeW_bswap, writeW_bswap,
    writeW_bswap, writeW_bswap, a0, a1, a2', a3,
    show (4 : Nat) = (Spec.Sha256.wordBytes 0).length from rfl,
    writeBytes_append _ _ _ _ (by simp [Spec.Sha256.wordBytes]),
    show (8 : Nat) = (Spec.Sha256.wordBytes 0 ++ Spec.Sha256.wordBytes (arg s₀ 2 >>> 29)).length from rfl,
    writeBytes_append _ _ _ _ (by simp [Spec.Sha256.wordBytes]),
    show (12 : Nat) = (Spec.Sha256.wordBytes 0 ++ Spec.Sha256.wordBytes (arg s₀ 2 >>> 29) ++
      Spec.Sha256.wordBytes ((arg s₀ 2 <<< 3) ||| (arg s₀ 1 >>> 29))).length from rfl,
    writeBytes_append _ _ _ _ (by simp [Spec.Sha256.wordBytes])]
  rfl

/-! ## One block -/

/-- The loop's postcondition for one iteration. -/
def Step (s₀ : State) (k : Nat) (s : State) : Prop :=
  (eval .e s = some false ∧ Done s₀ s) ∨ (eval .e s = some true ∧ k = 1 ∧ LInv s₀ 0 0 s)

theorem regs2 {r : Reg} (hr : r ∈ [Reg.ebx, .esp]) :
    r ≠ .eax ∧ r ≠ .ecx ∧ r ≠ .edx ∧ r ≠ .edi ∧ r ≠ .esi := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> decide

theorem body_ok {s₀ : State} (hp : Pre s₀) {k n : Nat} {s : State} (h : LInv s₀ k n s) :
    WP isa finalizeBody s (Step s₀ k) := by
  have hk := h.k_le; have hn := h.n_le; have hst := hp.st_fit
  have hC := h.toCommon
  unfold finalizeBody
  -- `eax := 128` or `112`: the end of the zeros.
  refine WP.seq (wp_movi fun s₁ u₁ => wp_test fun s₂ f₂ z₂ => WP.block_nil ?_)
  have hz₂ : s₂.zf = some (decide (k = 0)) := by
    rw [z₂, u₁.other _ (by decide), h.esi, BitVec.and_self, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .eax = BitVec.ofNat 32 (112 + 16 * k) ∧
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
  have hC₃ : Common s₀ s₃ := hC.of_gpr (fun r hr => g₃ r (regs2 hr).1) m₃ rd₃ wr₃
  refine WP.seq (wp_movi fun s₄ u₄ => wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  have hC₄ : Common s₀ s₄ := hC₃.of_gpr (fun r hr => u₄.other r (regs2 hr).2.1) u₄.mem u₄.rd u₄.wr
  have hecx₄ : s₄.gpr .ecx = 0 := u₄.gpr
  have hedi₄ : s₄.gpr .edi = BitVec.ofNat 32 n := by rw [u₄.other _ (by decide), g₃ _ (by decide), h.edi]
  have heax₅ : s₅.gpr .eax = BitVec.ofNat 32 (112 + 16 * k - n) := by
    rw [u₅.gpr, u₄.other _ (by decide), heax₃, hedi₄, sub_ofNat (a := 112 + 16 * k) (b := n) (by omega)]
  have hZ : Zero s₀ s₄ n (112 + 16 * k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => u₅.other r ?_, u₅.rd, u₅.wr,
      by rw [u₅.other _ (by decide), hedi₄, Nat.add_zero], by rw [heax₅, Nat.sub_zero],
      by rw [u₅.mem, List.replicate_zero, writeBytes_nil]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  have hz₅ : s₅.zf = some (decide (112 + 16 * k - n = 0)) := by
    rw [z₅, ← u₅.gpr, heax₅, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (zero_ok hp hC₄ hecx₄ (by omega) hn hZ hz₅) fun s₆ hZ₆ => ?_)
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃]
  have hf₆ : Frame [stR s₀] s₄.mem s₆.mem := by
    rw [hZ₆.mem]; exact buf_frame _ (by simp only [List.length_replicate]; omega)
  obtain ⟨hfr₆, hsv₆⟩ := hC₄.writeSt hp hf₆
  have hC₆ : Common s₀ s₆ := ⟨hZ₆.rd.trans hC₄.rd, hZ₆.wr.trans hC₄.wr, by rw [hZ₆.keep _ (by simp), hC₄.ebx],
    by rw [hZ₆.keep _ (by simp), hC₄.esp], hfr₆, hsv₆⟩
  have hst₆ : stateAt s₆.mem (stA s₀) = stateAt s.mem (stA s₀) := by
    rw [hZ₆.mem, hm₄]
    apply stateAt_congr
    intro i hi
    rw [st_add]
    exact writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (stA s₀ + 64) (112 + 16 * k) =
      bytesAt s.mem (stA s₀ + 64) n ++ List.replicate (112 + 16 * k - n) 0 := by
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
      ∀ iv m, R₀ s₀ iv m → bytesAt s₈.mem (stA s₀ + 64) 128 = bytesAt s.mem (stA s₀ + 64) n ++
        (if k = 1 then List.replicate (128 - n) 0 else List.replicate (112 - n) 0 ++ lenBytes m)) ?_
    fun s₈ ⟨hC₈, hesi₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show s₇.zf = _; rw [hz₇]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine WP.mono (len_ok hp hC₇) fun s₈ ⟨g₈, rd₈, wr₈, m₈⟩ => ?_
      have hfL : Frame [stR s₀] s₇.mem s₈.mem := by
        rw [m₈]; exact buf_frame _ (by rw [lenL_length])
      obtain ⟨hfr, hsv⟩ := hC₇.writeSt hp hfL
      refine ⟨⟨rd₈.trans hC₇.rd, wr₈.trans hC₇.wr, by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.ebx],
        by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.esp], hfr, hsv⟩,
        by rw [g₈ _ (by decide) (by decide) (by decide), hesi₇], ?_, fun iv m hm => ?_⟩
      · rw [m₈, ← hst₆, ← f₇.mem]
        apply stateAt_congr
        intro i hi
        rw [st_add]
        exact writeBytes_before _ _ _ (by omega) (by rw [lenL_length]; omega)
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        have e := bytesAt_writeBytes s₇.mem (stA s₀ + 64) 112 (lenL s₀) (by rw [lenL_length]; omega)
        rw [lenL_length] at e
        rw [show 112 + 16 * 0 = 112 from rfl] at hby₆
        rw [m₈, e, f₇.mem, hby₆, lenL_eq hm]
        simp [List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₇, hesi₇, by rw [f₇.mem, hst₆], fun iv m _ => ?_⟩
      rw [f₇.mem, show (128 : Nat) = 112 + 16 * 1 from rfl, hby₆]; simp
  -- Compress the block.
  refine WP.seq (compress_buf hp hC₈ fun s₁₀ hC₁₀ cs₁₀ hst₁₀ => ?_)
  have hesi₁₀ : s₁₀.gpr .esi = BitVec.ofNat 32 k := by rw [cs₁₀ _ (by simp), hesi₈]
  have hblk : ∀ iv m, R₀ s₀ iv m → blockAt s₈.mem (stA s₀ + 64) = parseBlock fun t =>
      (bytesAt s.mem (stA s₀ + 64) n ++
        (if k = 1 then List.replicate (128 - n) 0 else List.replicate (112 - n) 0 ++ lenBytes m)).getD t 0 :=
    fun iv m hm => parseBlock_congr fun t ht => bytesAt_getD (hby₈ iv m hm) ht
  -- Next block, if any.
  refine wp_movi fun s₁₁ u₁₁ => wp_subi fun s₁₂ u₁₂ z₁₂ => WP.block_nil ?_
  have hC₁₂ : Common s₀ s₁₂ := hC₁₀.of_gpr (fun r hr => by
      rw [u₁₂.other r (regs2 hr).2.2.2.2, u₁₁.other r (regs2 hr).2.2.2.1]) (by rw [u₁₂.mem, u₁₁.mem])
    (by rw [u₁₂.rd, u₁₁.rd]) (by rw [u₁₂.wr, u₁₁.wr])
  have hz : s₁₂.zf = some (decide (k = 1)) := by
    rw [z₁₂, u₁₁.other _ (by decide), hesi₁₀, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (a := k) (b := 1) (by omega) (by omega)]
  have hst : ∀ iv m, R₀ s₀ iv m → stateAt s₁₂.mem (stA s₀) = compress (stateAt s.mem (stA s₀)) (parseBlock fun t =>
      (bytesAt s.mem (stA s₀ + 64) n ++
        (if k = 1 then List.replicate (128 - n) 0 else List.replicate (112 - n) 0 ++ lenBytes m)).getD t 0) := by
    intro iv m hm
    rw [u₁₂.mem, u₁₁.mem, hst₁₀, hst₈, hblk iv m hm]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨by show s₁₂.zf = _; rw [hz]; rfl, rfl, ⟨hC₁₂, by omega, by omega, ?_, ?_, fun iv m hm => ?_⟩⟩
    · rw [u₁₂.other _ (by decide), u₁₁.gpr]; rfl
    · rw [u₁₂.gpr, u₁₁.other _ (by decide), hesi₁₀]; rfl
    · rw [h.hash iv m hm]
      simp only [ite_true, show ¬ ((0 : Nat) = 1) by decide, ite_false, Fin1, Fin0, hst iv m hm]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨by show s₁₂.zf = _; rw [hz]; rfl, hC₁₂, fun iv m hm => ?_⟩
    rw [h.hash iv m hm, hst iv m hm]
    simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false, Fin0, List.append_assoc]

/-! ## Prologue -/

/-- The memory after saving our caller's registers. -/
def saveMem (s₀ : State) : Mem :=
  (((s₀.mem.writeW (addr (scr s₀) 224) (s₀.gpr .ebx)).writeW (addr (scr s₀) 228) (s₀.gpr .esi)).writeW
    (addr (scr s₀) 232) (s₀.gpr .edi)).writeW (addr (scr s₀) 236) (s₀.gpr .ebp)

theorem saveMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d, d + 4 ≤ 272 → (scR s₀).Contains (addr (scr s₀) d) (32 / 8) := fun d hd => hp.scr_in hd
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 224 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 228 (by omega))).writeW (List.mem_singleton_self _) _
    (c 232 (by omega))).writeW (List.mem_singleton_self _) _ (c 236 (by omega))

theorem saveMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (saveMem s₀) := by
  have hs := hp.scr_fit
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 272 → e + 4 ≤ 272 → d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (scr s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
    fun m v d e h₁ h₂ h => readW_writeW_addr m v (by omega) (by omega) h
  intro p hp'
  simp only [VG.Impl.Sha512.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl <;> simp only [saveMem]
  · rw [w _ _ 224 236 (by omega) (by omega) (by omega), w _ _ 224 232 (by omega) (by omega) (by omega),
      w _ _ 224 228 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [w _ _ 228 236 (by omega) (by omega) (by omega), w _ _ 228 232 (by omega) (by omega) (by omega),
      Mem.readW_writeW_self32]
  · rw [w _ _ 232 236 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

/-- The prologue's straight-line code. -/
def proBlock : List Instr :=
  [.mov .eax (.mem (at_ .esp 20)), .store (at_ .eax 224) .ebx, .store (at_ .eax 228) .esi,
   .store (at_ .eax 232) .edi, .store (at_ .eax 236) .ebp,
   .mov .ebx (.mem (at_ .esp 4)), .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 127),
   .mov .eax (.reg .ebx), .alu .add .eax (.reg .edi), .mov .ecx (.imm 0x80),
   .store8 (at_ .eax 64) .cl, .alu .add .edi (.imm 1),
   .mov .esi (.imm 0), .alu .cmp .edi (.imm 113)]

theorem finalize_eq : finalize =
    .seq (.block proBlock)
    (.seq (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))
    (.seq (.loop finalizeBody .e)
      (.block (.mov .eax (.mem (at_ .esp 16)) :: (List.range 8).flatMap outW ++
        .mov .eax (.mem (at_ .esp 20)) :: restore)))) := rfl

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.seq (.block proBlock) (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))) s₀
      fun s => ∃ k, LInv s₀ k (cnt s₀ % 128 + 1) s := by
  have hsp := hp.sp_fit; have hsc := hp.scr_fit; have hst := hp.st_fit
  have hr : cnt s₀ % 128 < 128 := Nat.mod_lt _ (by omega)
  have ain : ∀ e, 4 ≤ e → e + 4 ≤ 24 → ∀ t : State, t.rd = s₀.rd → t.wr = s₀.wr →
      InRegions (t.rd ++ t.wr) (addr (esp₀ s₀) e) 4 :=
    fun e h₁ h₂ t hrd hwr => ⟨argR s₀, by simp [hrd, hp.rd], hp.arg_in h₁ h₂⟩
  have sout : ∀ d, d + 4 ≤ 272 → ∀ t : State, t.wr = s₀.wr → InRegions t.wr (addr (scr s₀) d) 4 :=
    fun d hd t hwr => ⟨scR s₀, by simp [hwr, hp.wr], hp.scr_in hd⟩
  have ard : ∀ e, 4 ≤ e → e + 4 ≤ 24 →
      (saveMem s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 :=
    fun e h₁ h₂ => (saveMem_frame hp).readW (Region.contains_self _ _)
      (by simpa using hp.a_scr.sub_left (hp.arg_sub h₁ h₂)) (by decide)
  refine WP.seq ?_
  unfold proBlock
  refine wp_movm (a := addr (esp₀ s₀) 20) (ea_at _ _ _) (ain 20 (by omega) (by omega) s₀ rfl rfl)
    fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (a := addr (scr s₀) 224) (by rw [ea_at, e₁]) (sout 224 (by omega) _ u₁.wr) fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) 228) (by rw [ea_at, u₂.gpr, e₁])
    (sout 228 (by omega) _ (by rw [u₂.wr, u₁.wr])) fun s₃ u₃ => ?_
  refine wp_store (a := addr (scr s₀) 232) (by rw [ea_at, u₃.gpr, u₂.gpr, e₁])
    (sout 232 (by omega) _ (by rw [u₃.wr, u₂.wr, u₁.wr])) fun s₄ u₄ => ?_
  refine wp_store (a := addr (scr s₀) 236) (by rw [ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (sout 236 (by omega) _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₅ : s₅.gpr .esp = esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  have m₅ : s₅.mem = saveMem s₀ := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
    rfl
  refine wp_movm (a := addr (esp₀ s₀) 4) (by rw [ea_at, sp₅]) (ain 4 (by omega) (by omega) s₅ rd₅ wr₅)
    fun s₆ u₆ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 8) (by rw [ea_at, u₆.other _ (by decide), sp₅])
    (ain 8 (by omega) (by omega) s₆ (by rw [u₆.rd, rd₅]) (by rw [u₆.wr, wr₅])) fun s₇ u₇ =>
    wp_andi fun s₈ u₈ => ?_
  have ebx₈ : s₈.gpr .ebx = st s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, m₅, ard 4 (by omega) (by omega)]; rfl
  have edi₈ : s₈.gpr .edi = BitVec.ofNat 32 (cnt s₀ % 128) := by
    rw [u₈.gpr, u₇.gpr, u₆.mem, m₅, ard 8 (by omega) (by omega), and127, cnt_mod]; rfl
  have m₈ : s₈.mem = saveMem s₀ := by rw [u₈.mem, u₇.mem, u₆.mem, m₅]
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, wr₅]
  have sp₈ : s₈.gpr .esp = esp₀ s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), sp₅]
  -- The `0x80` byte.
  refine wp_mov fun s₉ u₉ => wp_add fun s₁₀ u₁₀ => wp_movi fun s₁₁ u₁₁ => ?_
  have eax₁₁ : s₁₁.gpr .eax = st s₀ + BitVec.ofNat 32 (cnt s₀ % 128) := by
    rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), ebx₈, edi₈]
  have hq : addr (s₁₁.gpr .eax) 64 = stA s₀ + 64 + BitVec.ofNat 64 (cnt s₀ % 128) := by
    rw [eax₁₁, addr_add_ofNat (by omega), st_add, Nat.add_comm]
  have hout : InRegions s₁₁.wr (stA s₀ + 64 + BitVec.ofNat 64 (cnt s₀ % 128)) 1 :=
    ⟨stR s₀, by simp [u₁₁.wr, u₁₀.wr, u₉.wr, wr₈, hp.wr], by
      rw [st_add]; exact contains_offset (by omega) (by omega)⟩
  refine wp_store8 (r := .cl) (a := stA s₀ + 64 + BitVec.ofNat 64 (cnt s₀ % 128)) (by rw [ea_at, hq]) hout
    fun s₁₂ u₁₂ => wp_addi fun s₁₃ u₁₃ => wp_movi fun s₁₄ u₁₄ => wp_cmpi fun s₁₅ f₁₅ cf₁₅ _ =>
    WP.block_nil ?_
  have hm₁₂ : s₁₂.mem = writeBytes (saveMem s₀) (stA s₀ + 64 + BitVec.ofNat 64 (cnt s₀ % 128)) [0x80] := by
    rw [u₁₂.mem, show Reg8.cl.reg = Reg.ecx from rfl, u₁₁.gpr, u₁₁.mem, u₁₀.mem, u₉.mem, m₈,
      ← List.nil_append [(0x80 : Byte)], writeBytes_snoc _ _ _ _ (by simp), writeBytes_nil]
    simp
  have hm₁₅ : s₁₅.mem = s₁₂.mem := by rw [f₁₅.mem, u₁₄.mem, u₁₃.mem]
  have hfb : Frame [stR s₀] (saveMem s₀) s₁₂.mem := by rw [hm₁₂]; exact buf_frame _ (by simp; omega)
  have keep : ∀ r, r ≠ .ecx → r ≠ .edi → r ≠ .eax → r ≠ .esi → s₁₅.gpr r = s₈.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [f₁₅.gpr, u₁₄.other r h4, u₁₃.other r h2, u₁₂.gpr, u₁₁.other r h1, u₁₀.other r h3, u₉.other r h3]
  have hC₈ : Common s₀ s₈ := ⟨rd₈, wr₈, ebx₈, sp₈, by rw [m₈]; exact (saveMem_frame hp).mono (by simp),
    by rw [m₈]; exact saveMem_saved hp⟩
  obtain ⟨hfr, hsv⟩ := hC₈.writeSt hp (m := s₁₂.mem) (by rw [m₈]; exact hfb)
  have hC : Common s₀ s₁₅ :=
    ⟨by rw [f₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, rd₈],
      by rw [f₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, wr₈],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), ebx₈],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), sp₈],
      by rw [hm₁₅]; exact hfr, by rw [hm₁₅]; exact hsv⟩
  have edi₁₅ : s₁₅.gpr .edi = BitVec.ofNat 32 (cnt s₀ % 128 + 1) := by
    rw [f₁₅.gpr, u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), edi₈, ofNat_succ]
  have hcf : s₁₅.cf = some (decide (cnt s₀ % 128 + 1 < 113)) := by
    rw [cf₁₅, ← f₁₅.gpr, edi₁₅, toNat_ofNat_lt (by omega)]; rfl
  -- The facts about the buffer.
  have hst' : stateAt s₁₅.mem (stA s₀) = stateAt s₀.mem (stA s₀) := by
    apply stateAt_congr
    intro i hi
    rw [hm₁₅, hm₁₂, st_add, writeBytes_before _ _ _ (by omega) (by simp; omega)]
    exact frame_bytes (saveMem_frame hp) (R := stR s₀) (by simpa using hp.st_scr) (by simp)
      (by show i < 192; omega)
  have hbytes : ∀ iv m, R₀ s₀ iv m →
      bytesAt s₁₅.mem (stA s₀ + 64) (cnt s₀ % 128 + 1) = rest m ++ [0x80] := by
    intro iv m hm
    have e := bytesAt_writeBytes (saveMem s₀) (stA s₀ + 64) (cnt s₀ % 128) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₅, hm₁₂, e]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    rw [st_add]
    exact frame_bytes (saveMem_frame hp) (R := stR s₀) (by simpa using hp.st_scr) (by simp)
      (by show 64 + i < 192; have := hm.length; omega)
  have hesi : s₁₅.gpr .esi = 0 := by rw [f₁₅.gpr, u₁₄.gpr]
  refine WP.ite (!decide (cnt s₀ % 128 + 1 < 113)) (by show s₁₅.cf.map (!·) = _; rw [hcf]; rfl)
    (fun hb => ?_) (fun hb => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb
    refine wp_movi fun s₁₆ u₁₆ => WP.block_nil ⟨1, hC.of_gpr (fun r hr => u₁₆.other r (regs2 hr).2.2.2.2)
      u₁₆.mem u₁₆.rd u₁₆.wr, (Nat.le_refl _), by omega, by rw [u₁₆.other _ (by decide), edi₁₅], by rw [u₁₆.gpr]; rfl,
      fun iv m hm => ?_⟩
    simp only [↓reduceIte]
    rw [hash_two (by rw [← hm.length]; omega), Fin1, u₁₆.mem, hbytes iv m hm, hst', hm.1.1,
      ← hm.length, show 128 - (cnt s₀ % 128 + 1) = 127 - cnt s₀ % 128 by omega]
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    refine WP.block_nil ⟨0, hC, by omega, by omega, edi₁₅, by rw [hesi]; rfl, fun iv m hm => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [hash_one (by rw [← hm.length]; omega), Fin0, hbytes iv m hm, hst', hm.1.1,
      ← hm.length, show 112 - (cnt s₀ % 128 + 1) = 111 - cnt s₀ % 128 by omega]

/-! ## Output and epilogue -/

/-- `k` words of the digest are written. -/
structure Out (s₀ sD : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r ∈ [Reg.ebx, .esp], s.gpr r = sD.gpr r
  eax : s.gpr .eax = out s₀
  mem : s.mem = writeBytes sD.mem (outA s₀) (((stateAt sD.mem (stA s₀)).toList.take k).flatMap wordBytes)

theorem flat_length (H : HashValue) (k : Nat) (hk : k ≤ 8) :
    ((H.toList.take k).flatMap wordBytes).length = 8 * k := by
  rw [List.length_flatMap]
  have : ∀ w ∈ H.toList.take k, (wordBytes w).length = 8 := fun w _ => by simp [wordBytes]
  rw [List.map_congr_left this, List.map_const', List.sum_replicate_nat, List.length_take]
  simp; omega

theorem out_frame (s₀ : State) (m : Mem) (xs : List Byte) (hx : xs.length ≤ 64) :
    Frame [outR s₀] m (writeBytes m (outA s₀) xs) :=
  writeBytes_frame _ _ _ (by
    rw [show outA s₀ = outA s₀ + BitVec.ofNat 64 0 by simp]
    exact contains_offset (by omega) (by omega))

theorem out_step {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) {k : Nat} (hk : k < 8)
    {s : State} (h : Out s₀ sD k s) {rest : List Instr} {Q : State → Prop}
    (hnext : ∀ s', Out s₀ sD (k + 1) s' → WP isa (.block rest) s' Q) :
    WP isa (.block (outW k ++ rest)) s Q := by
  have hC := hD.1
  have hst := hp.st_fit; have ho := hp.out_fit
  have hebx : s.gpr .ebx = st s₀ := by rw [h.keep _ (by simp), hC.ebx]
  have hP := flat_length (stateAt sD.mem (stA s₀)) k (Nat.le_of_lt hk)
  have hin : ∀ o, o + 4 ≤ 8 → InRegions (s.rd ++ s.wr) (addr (st s₀) (8 * k + o)) 4 := fun o ho' =>
    ⟨stR s₀, by simp [h.rd, h.wr, hp.wr], contains_addr (by omega) (by omega) hst⟩
  -- The word's halves, unchanged since `Done`.
  have hread : ∀ o, o + 4 ≤ 8 → s.mem.readW (addr (st s₀) (8 * k + o)) 32 =
      sD.mem.readW (addr (st s₀) (8 * k + o)) 32 := by
    intro o ho'
    rw [h.mem]
    refine (out_frame s₀ sD.mem _ (by omega)).readW (r := ⟨addr (st s₀) (8 * k + o), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    rw [addr_eq (by omega)]
    exact hp.st_out.sub_left (sub_offset (by omega) (by omega))
  have hw := stateAt_get (st := st s₀) (by omega) sD.mem hk
  have wlo : sD.mem.readW (addr (st s₀) (8 * k + 0)) 32 = lo (stateAt sD.mem (stA s₀))[k] := by
    rw [hw, lo_rd64, Nat.add_zero]
  have whi : sD.mem.readW (addr (st s₀) (8 * k + 4)) 32 = hi (stateAt sD.mem (stA s₀))[k] := by
    rw [hw, hi_rd64]
  simp only [outW, List.cons_append, List.nil_append]
  refine wp_movm (a := addr (st s₀) (8 * k + 0)) (by rw [ea_at, hebx, Nat.add_zero]) (hin 0 (by omega))
    fun s₁ u₁ => ?_
  refine wp_movm (a := addr (st s₀) (8 * k + 4)) (by rw [ea_at, u₁.other _ (by decide), hebx])
    (by rw [u₁.rd, u₁.wr]; exact hin 4 (by omega)) fun s₂ u₂ => wp_bswap fun s₃ u₃ => wp_bswap fun s₄ u₄ => ?_
  have heax : s₄.gpr .eax = out s₀ := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.eax]
  have hwo : ∀ o, o + 4 ≤ 8 → ∀ t : State, t.wr = s₀.wr → InRegions t.wr (addr (out s₀) (8 * k + o)) 4 :=
    fun o ho' t ht => ⟨outR s₀, by simp [ht, hp.wr], contains_addr (by omega) (by omega) ho⟩
  refine wp_store (a := addr (out s₀) (8 * k + 0)) (by rw [ea_at, heax, Nat.add_zero])
    (hwo 0 (by omega) _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr])) fun s₅ u₅ => ?_
  refine wp_store (a := addr (out s₀) (8 * k + 4)) (by rw [ea_at, u₅.gpr, heax])
    (hwo 4 (by omega) _ (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr])) fun s₆ u₆ =>
    hnext s₆ ⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
      by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], fun r hr => ?_,
      by rw [u₆.gpr, u₅.gpr, heax], ?_⟩
  · have : r ≠ .ecx ∧ r ≠ .edx := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    rw [u₆.gpr, u₅.gpr, u₄.other r this.1, u₃.other r this.2, u₂.other r this.2, u₁.other r this.1,
      h.keep r hr]
  · have v2 : s₄.gpr .edx = bswap (hi (stateAt sD.mem (stA s₀))[k]) := by
      rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.mem, hread 4 (by omega), whi]
    have v1 : s₅.gpr .ecx = bswap (lo (stateAt sD.mem (stA s₀))[k]) := by
      rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hread 0 (by omega), wlo]
    have a0 : addr (out s₀) (8 * k + 0) = outA s₀ +
        BitVec.ofNat 64 (((stateAt sD.mem (stA s₀)).toList.take k).flatMap wordBytes).length := by
      rw [hP, addr_eq (by omega), Nat.add_zero]
    have a4 : addr (out s₀) (8 * k + 4) = outA s₀ +
        BitVec.ofNat 64 (((stateAt sD.mem (stA s₀)).toList.take k).flatMap wordBytes).length +
        BitVec.ofNat 64 (Spec.Sha256.wordBytes (hi (stateAt sD.mem (stA s₀))[k])).length := by
      rw [hP, addr_eq (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
    rw [u₆.mem, v1, u₅.mem, v2, u₄.mem, u₃.mem, u₂.mem, u₁.mem, writeW_bswap, writeW_bswap, a0, a4,
      writeBytes_append _ _ _ _ (by simp [Spec.Sha256.wordBytes]), ← wordBytes_split, h.mem,
      writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop := abiPreserved s₀ s' ∧ Proof.Sha512.finalizeX86.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) {s : State}
    (h : Out s₀ sD 8 s) : WP isa (.block (.mov .eax (.mem (at_ .esp 20)) :: restore)) s (Post s₀) := by
  have hC := hD.1
  have hsc := hp.scr_fit
  have hfo := out_frame s₀ sD.mem (((stateAt sD.mem (stA s₀)).toList.take 8).flatMap wordBytes)
    (by rw [flat_length _ _ (Nat.le_refl _)])
  have hesp : s.gpr .esp = esp₀ s₀ := by rw [h.keep _ (by simp), hC.esp]
  have rin : ∀ d, d + 4 ≤ 272 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
    fun d hd => ⟨scR s₀, by simp [h.rd, h.wr, hp.wr], hp.scr_in hd⟩
  have sv : ∀ p ∈ saved, s.mem.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1 := by
    intro p hp'
    have hd : 224 ≤ p.2 ∧ p.2 + 4 ≤ 240 := by
      simp only [VG.Impl.Sha512.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> simp
    rw [h.mem, hfo.readW (r := ⟨addr (scr s₀) p.2, 4⟩) (Region.contains_self _ _)
      (by simpa using hp.out_scr.symm.sub_left (hp.scr_sub (by omega))) (by decide)]
    exact hC.saved p hp'
  refine wp_movm (a := addr (esp₀ s₀) 20) (by rw [ea_at, hesp])
    ⟨argR s₀, by simp [h.rd, hp.rd], hp.arg_in (by omega) (by omega)⟩ fun s₀' u₀ => ?_
  have e₀ : s₀'.gpr .eax = scr s₀ := by
    rw [u₀.gpr, h.mem, hfo.readW (r := ⟨addr (esp₀ s₀) 20, 4⟩) (Region.contains_self _ _)
      (by simpa using hp.a_out.sub_left (hp.arg_sub (by omega) (by omega))) (by decide),
      hC.arg hp (by omega) (by omega)]
    rfl
  unfold restore
  simp only [saved, List.map_cons, List.map_nil]
  refine wp_movm (a := addr (scr s₀) 224) (by rw [ea_at, e₀])
    (by rw [u₀.rd, u₀.wr]; exact rin 224 (by omega)) fun s₁ u₁ => ?_
  refine wp_movm (a := addr (scr s₀) 228) (by rw [ea_at, u₁.other _ (by decide), e₀])
    (by rw [u₁.rd, u₁.wr, u₀.rd, u₀.wr]; exact rin 228 (by omega)) fun s₂ u₂ => ?_
  refine wp_movm (a := addr (scr s₀) 232) (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), e₀])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, u₀.rd, u₀.wr]; exact rin 232 (by omega)) fun s₃ u₃ => ?_
  refine wp_movm (a := addr (scr s₀) 236)
    (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), e₀])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, u₀.rd, u₀.wr]; exact rin 236 (by omega))
    fun s₄ u₄ => WP.block_nil ?_
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₀.mem]
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun iv m hm hl hc => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₀.mem]
      exact sv (.ebx, 224) (by simp [saved])
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, u₀.mem]
      exact sv (.esi, 228) (by simp [saved])
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, u₀.mem]
      exact sv (.edi, 232) (by simp [saved])
    · rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem, u₀.mem]
      exact sv (.ebp, 236) (by simp [saved])
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
        u₀.other _ (by decide), hesp]
  · rw [hm₄, h.mem, hfo.readW (r := retR s₀) (Region.contains_self _ _) (by simpa using hp.ret_out) (by decide)]
    refine hC.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.ret_st, hp.ret_scr, hp.ret_stk]
  · have e := bytesAt_writeBytes sD.mem (outA s₀) 0 (((stateAt sD.mem (stA s₀)).toList.take 8).flatMap wordBytes)
      (by rw [flat_length _ _ (Nat.le_refl _)]; omega)
    have e' : bytesAt (writeBytes sD.mem (outA s₀) (((stateAt sD.mem (stA s₀)).toList.take 8).flatMap wordBytes))
        (outA s₀) 64 = ((stateAt sD.mem (stA s₀)).toList.take 8).flatMap wordBytes := by
      rw [flat_length _ _ (Nat.le_refl _), show outA s₀ + BitVec.ofNat 64 0 = outA s₀ by simp,
        show bytesAt sD.mem (outA s₀) 0 = [] from rfl, List.nil_append] at e
      exact e
    rw [← h.mem, ← hm₄] at e'
    show bytesAt s₄.mem (outA s₀) 64 = _
    rw [e', hD.2 iv m ⟨hm, hl, hc⟩, List.take_of_length_le (by simp)]

theorem out_all {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) :
    ∀ j ≤ 8, ∀ s, Out s₀ sD (8 - j) s →
      WP isa (.block (((List.range 8).drop (8 - j)).flatMap outW ++
        .mov .eax (.mem (at_ .esp 20)) :: restore)) s (Post s₀) := by
  intro j
  induction j with
  | zero =>
    intro _ s h
    rw [show (List.range 8).drop (8 - 0) = [] from rfl, List.flatMap_nil, List.nil_append]
    exact epilogue_ok hp hD h
  | succ j ih =>
    intro hj s h
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.append_assoc,
      List.getElem_range]
    refine out_step hp hD (by omega) h fun s' h' => ?_
    rw [show 8 - (j + 1) + 1 = 8 - j by omega]
    exact ih (by omega) s' (by rwa [show 8 - (j + 1) + 1 = 8 - j by omega] at h')

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa finalize s₀ (Post s₀) := by
  rw [finalize_eq, ← Proof.Sha256.X86.Stream.Finalize.seq_assoc]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨k, hL⟩ => ?_)
  refine WP.seq (WP.mono (Q := Done s₀) ?_ fun sD hD => ?_)
  · refine WP.loop (M := isa) (fun i s => ∃ n, LInv s₀ i n s) ?_ k s₁ ⟨_, hL⟩
    rintro i s ⟨n, hL⟩
    refine WP.mono (body_ok hp hL) fun s' h => ?_
    rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
    · exact .inl ⟨he, hD⟩
    · exact .inr ⟨he, 0, by omega, 0, hL'⟩
  · have hC := hD.1
    refine wp_movm (a := addr (esp₀ s₀) 16) (by rw [ea_at, hC.esp]) (hC.argIn hp (by omega) (by omega))
      fun s₁ u₁ => ?_
    have := out_all hp hD 8 (Nat.le_refl _) s₁ ⟨by rw [u₁.rd, hC.rd], by rw [u₁.wr, hC.wr],
      fun r hr => u₁.other r (regs2 hr).1, by rw [u₁.gpr, hC.arg hp (by omega) (by omega)]; rfl,
      by simp [u₁.mem, writeBytes_nil]⟩
    rw [show 8 - 8 = 0 from rfl, List.drop_zero] at this
    exact this

/-! ## Constant time -/

/-- The initial taint: the stack arguments are public, the words holding
`state`, `out` and `scratch` are the base addresses of the writable regions,
and the 20 bytes below `esp` are outside them. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [192, 64, 272], argLen := 24,
    argBases := [(4, 0), (16, 1), (20, 2)], room := 20 }

theorem wf₀ {s : State} (h : Proof.Sha512.finalizeX86.pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have hst := hp.st_fit; have ho := hp.out_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, k1, k2, k3, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_out, hp.st_scr⟩, hp.out_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_st hp.a_st
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_out hp.a_out
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_scr hp.a_scr
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [k1, k2, k3]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha512.finalizeX86.pre s₁) (h₂ : Proof.Sha512.finalizeX86.pre s₂)
    (hpub : Proof.Sha512.finalizeX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [stR, outR, scR, stA, outA, scA, st, out, scr, ha 0 (by omega), ha 3 (by omega), ha 4 (by omega)]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    have f₁ : (s₁.gpr .esp).toNat + 24 ≤ 2 ^ 32 := hp₁.sp_fit
    have f₂ : (s₂.gpr .esp).toNat + 24 ≤ 2 ^ 32 := hp₂.sp_fit
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-- Memory holding the arguments `0x1000, 0, 0, 0x2000, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4011 then 0x20 else if a = 0x4015 then 0x30 else 0

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x4004, 20⟩]
  wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 272⟩]

theorem sat_pre : Proof.Sha512.finalizeX86.pre sat := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a3 : arg sat 3 = 0x2000 := by decide
  have a4 : arg sat 4 = 0x3000 := by decide
  have e : argAddr sat 0 = 0x4004 := by decide
  simp only [Proof.Sha512.finalizeX86, a0, a3, a4, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
    by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, sat] at h₁ h₂
    bv_omega

theorem finalize_verified : Verified X86.target finalize Proof.Sha512.finalizeX86 := by
  refine ⟨fun s hs => ?_, ?_, ⟨sat, sat_pre⟩⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.Sha512.X86.Stream.Finalize
