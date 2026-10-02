import VerifiedGarbage.Proof.Pbkdf2.MdHmac
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common
import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Impl.Pbkdf2.Md.X86

/-!
# HMAC and PBKDF2-HMAC over a Merkle–Damgård hash function on x86 (32-bit): the block

What HMAC's `finalize` and PBKDF2's iteration (`Impl/Pbkdf2/Md/X86.lean`)
share: a hash value at `ebx` with a block right after it, which they pad
(`pad_ok`), compress into the hash value with any verified compression
function (`cmp_ok`, against the compression contract of the hash function's
`Md`, `cmpK`; `cmp_rel` relates two runs of the call) and write the digest
into (`digest_ok`, from the hash function's own `out`, `OutOk`); and the
copies of words (`copyW_ok`) and stores of constant words (`storeW_ok`) they
are made of.
-/

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash cpW copyW wordOf storeW tail)
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Proof.MdStream (Md)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movi wp_movm wp_store wp_addi sub_offset)
open VG.Proof.Pbkdf2.Stream.X86 (ea_at stk After after_of stk_sub stk_sub' setWidth_add toNat_add_ofNat
  rel_agree)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open Spec.Sha256 (bytesAt)

/-! ## Words -/

/-- Word `k` of `n` words at `[x + o]`, within the 32-bit address space. -/
theorem addr_word {x : BitVec 32} {o n k : Nat} (h : x.toNat + o + 4 * n ≤ 2 ^ 32) (hk : k < n) :
    addr x (o + 4 * k) = x.setWidth 64 + BitVec.ofNat 64 o + BitVec.ofNat 64 (4 * k) := by
  rw [addr_eq (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Copying `n` words from `[x + o₁]` to `[y + o₂]`. -/
theorem copyW_ok {src dst : Reg} (hs : src ≠ .ecx) (hd : dst ≠ .ecx) {x y : BitVec 32} {o₁ o₂ : Nat}
    (n : Nat) : ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr src = x → s.gpr dst = y → x.toNat + o₁ + 4 * n ≤ 2 ^ 32 → y.toNat + o₂ + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr) (addr x (o₁ + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (addr y (o₂ + 4 * k)) 4) →
    Mem.Sep (x.setWidth 64 + BitVec.ofNat 64 o₁) (4 * n) (y.setWidth 64 + BitVec.ofNat 64 o₂) (4 * n) →
    (∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (y.setWidth 64 + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 o₁) (4 * n)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block (copyW src o₁ dst o₂ n ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hx hy fx fy hin hout hsep k
    rw [copyW, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q hx hy (by omega) (by omega) (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun a ha hb => hsep a (by omega) (by omega)) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [cpW, List.cons_append, List.nil_append]
    refine wp_movm (a := addr x (o₁ + 4 * n)) (by rw [ea_at, g₁ _ hs, hx])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_store (a := addr y (o₂ + 4 * n)) (by rw [ea_at, u₂.other _ hd, g₁ _ hd, hy])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega)) fun s₃ u₃ => ?_
    refine k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
      (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) ?_
    rw [u₃.mem, u₂.gpr, u₂.mem, addr_word fx (by omega : n < n + 1), addr_word fy (by omega : n < n + 1), m₁]
    have := VG.Proof.Hmac.Common.copy_mem s.mem (x.setWidth 64 + BitVec.ofNat 64 o₁)
      (y.setWidth 64 + BitVec.ofNat 64 o₂) n 4 (by rw [show 4 * n + 4 = 4 * (n + 1) by omega]; exact hsep)
      (by omega)
    simp only [Nat.reduceMul] at this
    rw [this, show 4 * (n + 1) = 4 * n + 4 by omega]

/-- The bytes of a little-endian word made of four bytes. -/
theorem word_bytes (a b c d : Byte) :
    (List.range (32 / 8)).map (fun j => ((a ++ b ++ c ++ d : BitVec 32).setWidth (8 * (32 / 8))).extractLsb' (8 * j) 8) =
      [d, c, b, a] := by
  simp only [show 32 / 8 = 4 from rfl, BitVec.setWidth_eq, List.range_succ,
    List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append, List.cons.injEq,
    and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext i hi
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
    repeat' split
    all_goals first | omega | (rw [← BitVec.getLsbD_eq_getElem]; congr 1; omega)

/-- A word of `xs` is its four bytes. -/
theorem wordOf_bytes {xs : List Byte} {k : Nat} (hk : 4 * k + 4 ≤ xs.length) :
    (List.range (32 / 8)).map (fun j => ((wordOf xs k).setWidth (8 * (32 / 8))).extractLsb' (8 * j) 8) =
      (xs.drop (4 * k)).take 4 := by
  rw [wordOf, word_bytes]
  apply List.ext_getElem (by simp; omega)
  intro j h₁ h₂
  simp only [List.length_cons, List.length_nil] at h₁
  simp only [List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show 4 * k + 3 < xs.length by omega), List.getElem?_eq_getElem (show 4 * k + 2 < xs.length by omega),
    List.getElem?_eq_getElem (show 4 * k + 1 < xs.length by omega), List.getElem?_eq_getElem (show 4 * k < xs.length by omega),
    Option.getD_some]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- Storing the first `4 n` bytes of `xs` at `[y + o]`, a word at a time. -/
theorem storeW_ok {dst : Reg} (hd : dst ≠ .ecx) {y : BitVec 32} {o : Nat} {xs : List Byte} (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), 4 * n ≤ xs.length →
    s.gpr dst = y → y.toNat + o + 4 * n ≤ 2 ^ 32 → (∀ k < n, InRegions s.wr (addr y (o + 4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (y.setWidth 64 + BitVec.ofNat 64 o) (xs.take (4 * n)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block (storeW dst o xs n ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro rest s Q hl hy fy hout k
    rw [storeW, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (by omega) hy (by omega) (fun j hj => hout j (by omega)) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_movi fun s₂ u₂ => ?_
    refine wp_store (a := addr y (o + 4 * n)) (by rw [ea_at, u₂.other _ hd, g₁ _ hd, hy])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega)) fun s₃ u₃ => ?_
    refine k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
      (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) ?_
    have ht : (xs.take (4 * n)).length = 4 * n := by simp; omega
    rw [u₃.mem, u₂.gpr, u₂.mem, m₁, addr_word fy (by omega : n < n + 1),
      Memory.writeW_bytes _ _ (wordOf xs n) ((xs.drop (4 * n)).take 4) (wordOf_bytes (by omega)),
      Memory.writeBytes_append' _ _ _ (by rw [ht]) (by simp; omega), show 4 * (n + 1) = 4 * n + 4 by omega,
      List.take_add]

/-! ## The compression function -/

/-- The contract of a compression function `compress(state, blocks, n, scratch)`
of `H`, with `so` bytes of scratch space: updates the hash value at `state`
with the `n` blocks at `blocks` (as `Proof.Md5.compressX86` and the others). -/
def cmpK {B N L : Nat} (H : Md B N L) (so : Nat) : Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, N⟩
    let blocks : Region := ⟨(arg s 1).setWidth 64, B * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, so⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + N ≤ 2 ^ 32 ∧ (arg s 1).toNat + B * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + so ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    H.stateAt s'.mem ((arg s 0).setWidth 64) =
      H.compressBlocks (H.stateAt s.mem ((arg s 0).setWidth 64)) s.mem ((arg s 1).setWidth 64) (arg s 2).toNat
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧
    arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

/-- A verified compression function, as the code calls it: correct and
constant time, never writing `esp`, and calling nothing that uses the
stack. -/
structure CompOk {B N L : Nat} (H : Md B N L) (so : Nat) (code : Prog isa) : Prop where
  verified : Verified X86.target code (cmpK H so)
  nosp : NoSp code
  stack : stackUse code = 0

/-- The four words a call of the compression function pushes, last to first. -/
abbrev cmp4 : List Reg := [.ebp, .ecx, .eax, .ebx]

theorem cmp4_nesp : Reg.esp ∉ cmp4 := by decide

/-- A part of a region that `rs` covers. -/
theorem covers_off {rs : List Region} {b : Addr} {L o n : Nat} (h : Covers [⟨b, L⟩] rs) (hl : o + n ≤ L) :
    Covers [⟨b + BitVec.ofNat 64 o, n⟩] rs := fun a k hi =>
  h a k (Covers.of_sub (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, o, rfl, hl⟩) a k hi)

theorem covers_cons {rs : List Region} {r : Region} {l : List Region} (h : Covers [r] rs) (h' : Covers l rs) :
    Covers (r :: l) rs := fun a k ⟨q, hq, hc⟩ => by
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h a k ⟨_, List.mem_singleton_self _, hc⟩
  · exact h' a k ⟨q, hq, hc⟩

/-- What the frame of a call of the compression function needs of the state
before its push: the hash value at `st` in `ebx` and the block after it in
`eax`, the scratch space at `sc` in `ebp`, `ecx = 1`, the regions the callee
may write, disjoint, and from the 48 bytes below `esp`, and none wrapping
around. -/
structure CmpArgs (N B so : Nat) (s : State) (st sc : BitVec 32) : Prop where
  ebx : s.gpr .ebx = st
  eax : s.gpr .eax = st + BitVec.ofNat 32 N
  ebp : s.gpr .ebp = sc
  sp48 : 48 ≤ (s.gpr .esp).toNat
  cst : Covers [⟨st.setWidth 64, N + B⟩] s.wr
  csc : Covers [⟨sc.setWidth 64, so⟩] s.wr
  st_sc : Region.Disjoint ⟨st.setWidth 64, N + B⟩ ⟨sc.setWidth 64, so⟩
  b_st : (stk s).Disjoint ⟨st.setWidth 64, N + B⟩
  b_sc : (stk s).Disjoint ⟨sc.setWidth 64, so⟩
  nst : st.toNat + (N + B) ≤ 2 ^ 32
  nsc : sc.toNat + so ≤ 2 ^ 32

/-- The regions the compression function is given: the block and its
arguments, the hash value and its scratch space. -/
abbrev CmpArgs.rd (N B : Nat) (st sp : BitVec 32) : List Region :=
  [⟨(st + BitVec.ofNat 32 N).setWidth 64, B * 1⟩, below sp 16]
abbrev CmpArgs.wr (N so : Nat) (st sc : BitVec 32) : List Region := [⟨st.setWidth 64, N⟩, ⟨sc.setWidth 64, so⟩]

namespace CmpArgs
variable {N B so : Nat} {s : State} {st sc : BitVec 32} (h : CmpArgs N B so s st sc) (hcx : s.gpr .ecx = 1)
include h

theorem fit : 4 * cmp4.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.sp48; simp only [List.length_cons, List.length_nil]; omega


theorem a0 : arg (pushed cmp4 s).callEntry 0 = st := by
  rw [callEntry_arg h.fit cmp4_nesp (by simp)]; simpa using h.ebx
theorem a1 : arg (pushed cmp4 s).callEntry 1 = st + BitVec.ofNat 32 N := by
  rw [callEntry_arg h.fit cmp4_nesp (by simp)]; simpa using h.eax
theorem a3 : arg (pushed cmp4 s).callEntry 3 = sc := by
  rw [callEntry_arg h.fit cmp4_nesp (by simp)]; simpa using h.ebp

include hcx in
theorem a2 : arg (pushed cmp4 s).callEntry 2 = 1 := by
  rw [callEntry_arg h.fit cmp4_nesp (by simp)]; simpa using hcx

theorem blk (hB : 0 < B) : (st + BitVec.ofNat 32 N).setWidth 64 = st.setWidth 64 + BitVec.ofNat 64 N :=
  setWidth_add (by have := h.nst; omega)

include hcx in
theorem callPre {L : Nat} (H : Md B N L) (hB : 0 < B) :
    CallPre (cmpK H so) cmp4 (CmpArgs.rd N B st (s.gpr .esp)) (CmpArgs.wr N so st sc) s := by
  have e := h.sp48
  have fit := h.fit
  have nst := h.nst
  have a2' : (arg (pushed cmp4 s).callEntry 2).toNat = 1 := by rw [h.a2 hcx]; rfl
  have hb : (st + BitVec.ofNat 32 N).toNat = st.toNat + N := toNat_add_ofNat (by omega)
  have sS : Region.Sub ⟨st.setWidth 64, N⟩ ⟨st.setWidth 64, N + B⟩ := Region.sub_prefix (by omega)
  have sB : Region.Sub ⟨(st + BitVec.ofNat 32 N).setWidth 64, B * 1⟩ ⟨st.setWidth 64, N + B⟩ := by
    rw [h.blk hB]; exact sub_offset (by omega) (by omega)
  have dBS : Region.Disjoint ⟨(st + BitVec.ofNat 32 N).setWidth 64, B * 1⟩ ⟨st.setWidth 64, N⟩ := by
    rw [h.blk hB]; exact Offset.disjoint_base _ (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [cmpK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
      argAddr_withRegions, h.a0, h.a1, h.a3, a2', callEntry_argAddr0, callEntry_esp', cmp4,
      List.length_cons, List.length_nil]
    have sA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 4)).setWidth 64, 16⟩ (stk s) :=
      stk_sub e (by omega) (by omega)
    have sR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 4 + 4)).setWidth 64, 4⟩ (stk s) :=
      stk_sub e (by omega) (by omega)
    refine ⟨trivial, trivial, h.st_sc.sub_left sS, dBS, h.st_sc.sub_left sB, (h.b_st.sub_left sA).sub_right sS,
      h.b_sc.sub_left sA, (h.b_st.sub_left sR).sub_right sS, h.b_sc.sub_left sR, by omega, by rw [hb]; omega,
      h.nsc, ?_⟩
    rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · have cB : Covers [⟨(st + BitVec.ofNat 32 N).setWidth 64, B * 1⟩] s.wr := by
      rw [h.blk hB]; exact covers_off h.cst (by omega)
    have cS : Covers [⟨st.setWidth 64, N⟩] s.wr := by
      have := covers_off (o := 0) (n := N) h.cst (by omega); simpa using this
    intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cB a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · refine InRegions_append_cons.mpr (.inl ?_)
      simpa using hc
    · obtain ⟨q', hq', hc'⟩ := cS a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · obtain ⟨q', hq', hc'⟩ := h.csc a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
  · have cS : Covers [⟨st.setWidth 64, N⟩] s.wr := by
      have := covers_off (o := 0) (n := N) h.cst (by omega); simpa using this
    intro a n hi
    obtain ⟨q', hq', hc'⟩ := covers_cons cS h.csc a n hi
    exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

theorem entry_frame : Frame [stk s] s.mem (pushed cmp4 s).callEntry.mem :=
  (callEntry_frame h.fit cmp4_nesp).sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_singleton_self _, below_sub (by simp only [List.length_cons, List.length_nil]; omega) h.sp48⟩

end CmpArgs

section
variable {B N L : Nat} {H : Md B N L} {so : Nat} {name : String} {code : Prog isa} (hc : CompOk H so code)
include hc

/-- A call of the compression function on the block after the hash value at
`st`, in a frame of its arguments: it compresses the block into the hash
value, writing only the hash value, its scratch space and the stack below
`esp`. -/
theorem cmp_frame (hB : 0 < B) {s : State} {st sc : BitVec 32} (h : CmpArgs N B so s st sc) (hcx : s.gpr .ecx = 1)
    {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st.setWidth 64, N⟩, ⟨sc.setWidth 64, so⟩] s' →
      H.stateAt s'.mem (st.setWidth 64) =
        H.compress (H.stateAt s.mem (st.setWidth 64)) (H.blockAt s.mem (st.setWidth 64 + BitVec.ofNat 64 N)) →
      Q s') :
    WP isa (.frame (.push cmp4) (.call name code) (.pop .eax cmp4.length)) s Q := by
  have e := h.sp48
  refine WP.callWith hc.verified.1 hc.nosp (by simp) cmp4_nesp
    (by rw [hc.stack]; simp only [List.length_cons, List.length_nil]; omega) (h.callPre hcx H hB)
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [hc.stack] at f'
  refine hQ s' (after_of e (by simp only [List.length_cons, List.length_nil]; omega) rd' wr' cs' f') ?_
  simp only [cmpK, arg_withRegions, State.withRegions_mem, h.a0, h.a1, h.a2 hcx] at post
  have fE := h.entry_frame
  have dS : ∀ q ∈ [stk s], (⟨st.setWidth 64, N + B⟩ : Region).Disjoint q := by
    simp only [List.mem_singleton]; rintro q rfl; exact h.b_st.symm
  have e₁ : H.stateAt (pushed cmp4 s).callEntry.mem (st.setWidth 64) = H.stateAt s.mem (st.setWidth 64) :=
    H.stateAt_congr fun i hi => fE.bytes (R := ⟨st.setWidth 64, N + B⟩) dS (by
      show N + B ≤ 2 ^ 64; have := h.nst; omega) (by show i < N + B; omega)
  have e₂ : H.blockAt (pushed cmp4 s).callEntry.mem (st.setWidth 64 + BitVec.ofNat 64 N) =
      H.blockAt s.mem (st.setWidth 64 + BitVec.ofNat 64 N) := by
    simp only [Md.blockAt]
    refine H.parse_congr fun k hk => ?_
    rw [Memory.add_ofNat]
    exact fE.bytes (R := ⟨st.setWidth 64, N + B⟩) dS (by show N + B ≤ 2 ^ 64; have := h.nst; omega)
      (by show N + k < N + B; omega)
  rw [← m₂, post, show (1 : BitVec 32).toNat = 1 from rfl, Md.compressBlocks_one, e₁, h.blk hB, e₂]

/-- The compression of the block after the hash value at `ebx`, with `eax`
at the block. -/
theorem cmp_ok (hB : 0 < B) {s : State} {st sc : BitVec 32} (h : CmpArgs N B so s st sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st.setWidth 64, N⟩, ⟨sc.setWidth 64, so⟩] s' →
      H.stateAt s'.mem (st.setWidth 64) =
        H.compress (H.stateAt s.mem (st.setWidth 64)) (H.blockAt s.mem (st.setWidth 64 + BitVec.ofNat 64 N)) →
      Q s') :
    WP isa (Impl.MdStream.X86.compressAt name code .ebx .ebp) s Q := by
  refine WP.seq (wp_movi fun s₁ u₁ => WP.block_nil ?_)
  have h₁ : CmpArgs N B so s₁ st sc :=
    { ebx := by rw [u₁.other _ (by decide), h.ebx], eax := by rw [u₁.other _ (by decide), h.eax],
      ebp := by rw [u₁.other _ (by decide), h.ebp], sp48 := by rw [u₁.other _ (by decide)]; exact h.sp48,
      cst := by rw [u₁.wr]; exact h.cst, csc := by rw [u₁.wr]; exact h.csc, st_sc := h.st_sc, b_st := by rw [stk, u₁.other _ (by decide)]; exact h.b_st,
      b_sc := by rw [stk, u₁.other _ (by decide)]; exact h.b_sc, nst := h.nst, nsc := h.nsc }
  refine cmp_frame hc hB h₁ u₁.gpr fun s' ha e => hQ s' ?_ (by rw [e, u₁.mem])
  exact ⟨ha.rd.trans u₁.rd, ha.wr.trans u₁.wr, fun r hr => (ha.cs r hr).trans (u₁.other r (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)),
    by have f := ha.frame; rw [stk, u₁.other _ (by decide), u₁.mem] at f; rw [stk]; exact f⟩

omit hc in
theorem mov1_check : ∃ hc, (VG.Taint.check taint (τr []) (.block [.mov .ecx (.imm 1)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- Two runs of the compression of the block, from the same hash value and
scratch space, and the same `esp`, leak the same: the call by the compression
function's contract. -/
theorem cmp_rel (hB : 0 < B) {P : State → State → Prop} {sp st sc : BitVec 32}
    (h : ∀ s s', P s s' → CmpArgs N B so s st sc ∧ CmpArgs N B so s' st sc ∧ s.gpr .esp = sp ∧ s'.gpr .esp = sp) :
    RelCT isa P (Impl.MdStream.X86.compressAt name code .ebx .ebp) fun _ _ => True := by
  have wp1 : ∀ s, CmpArgs N B so s st sc ∧ s.gpr .esp = sp → WP isa (.block [.mov .ecx (.imm 1)]) s
      fun t => (CmpArgs N B so t st sc ∧ t.gpr .ecx = 1) ∧ t.gpr .esp = sp := fun s ⟨a, e⟩ =>
    wp_movi fun s₁ u₁ => WP.block_nil
      ⟨⟨{ ebx := by rw [u₁.other _ (by decide), a.ebx], eax := by rw [u₁.other _ (by decide), a.eax],
          ebp := by rw [u₁.other _ (by decide), a.ebp], sp48 := by rw [u₁.other _ (by decide)]; exact a.sp48,
          cst := by rw [u₁.wr]; exact a.cst, csc := by rw [u₁.wr]; exact a.csc, st_sc := a.st_sc,
          b_st := by rw [stk, u₁.other _ (by decide)]; exact a.b_st,
          b_sc := by rw [stk, u₁.other _ (by decide)]; exact a.b_sc, nst := a.nst, nsc := a.nsc }, u₁.gpr⟩,
        by rw [u₁.other _ (by decide), e]⟩
  have r1 := rel_agree (F := fun s => CmpArgs N B so s st sc ∧ s.gpr .esp = sp)
    (F' := fun s => CmpArgs N B so s st sc ∧ s.gpr .esp = sp) (τr []) (fun _ _ _ _ => agree_regs (by simp))
    mov1_check (wp1) (wp1)
  refine (r1.mono (fun s s' hp => by
      obtain ⟨a, a', e, e'⟩ := h s s' hp; exact ⟨⟨a, e⟩, ⟨a', e'⟩⟩) fun _ _ h => h).seq ?_
  refine RelCT.callWith (rs := cmp4) hc.verified.1 hc.verified.2.1 (CmpArgs.rd N B st sp)
    (CmpArgs.wr N so st sc) fun s s' ⟨⟨⟨a, x⟩, e⟩, ⟨⟨a', x'⟩, e'⟩⟩ => ?_
  have c := a.callPre x H hB
  have c' := a'.callPre x' H hB
  rw [e] at c; rw [e'] at c'
  refine ⟨c, c', e.trans e'.symm, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e, e']
  · simp only [arg_withRegions, a.a0, a'.a0]
  · simp only [arg_withRegions, a.a1, a'.a1]
  · simp only [arg_withRegions, a.a2 x, a'.a2 x']
  · simp only [arg_withRegions, a.a3, a'.a3]

end

/-! ## The digest -/

/-- `out` writes the digest of the `N`-byte hash value at `ebx` to `eax`,
writing only `ecx` and `edx`. -/
def OutOk {B N L : Nat} (H : Md B N L) (out : List Instr) : Prop :=
  ∀ s : State, (s.gpr .ebx).toNat + N ≤ 2 ^ 32 → (s.gpr .eax).toNat + N ≤ 2 ^ 32 →
    InRegions (s.rd ++ s.wr) ((s.gpr .ebx).setWidth 64) N → InRegions s.wr ((s.gpr .eax).setWidth 64) N →
    Region.Disjoint ⟨(s.gpr .ebx).setWidth 64, N⟩ ⟨(s.gpr .eax).setWidth 64, N⟩ →
    WP isa (.block out) s fun s' =>
      (∀ r, r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem ((s.gpr .eax).setWidth 64) (H.digest (H.stateAt s.mem ((s.gpr .ebx).setWidth 64)))

/-! ## The block after the hash value at `ebx` -/

/-- The sizes the proofs support, checked for each hash function by `decide`:
blocks of 64 or 128 bytes, a hash value of words, a digest of words of at
most the hash value, room in the block for the digest, the `0x80` word and
the length field, a streaming state of a hash value and a block, and the
compression function's scratch space within that of the streaming
functions. -/
structure Sizes (H : Hash) : Prop where
  B : H.B = 64 ∨ H.B = 128
  N : 0 < H.N ∧ H.N ≤ 64 ∧ H.N % 4 = 0
  D : 0 < H.D ∧ H.D ≤ H.N ∧ H.D % 4 = 0
  DL : H.D + H.L + 4 ≤ H.B
  S : H.S = H.N + H.B
  so : H.so ≤ 8 * H.st.W
  W : H.st.W ≤ 64
  F : H.D ≤ H.st.F ∧ H.st.F ≤ 64

/-- A range within a region that `rs` covers. -/
theorem inReg {rs : List Region} {b : Addr} {L o n : Nat} (h : Covers [⟨b, L⟩] rs) (hl : o + n ≤ L)
    (hL : L < 2 ^ 64) : InRegions rs (b + BitVec.ofNat 64 o) n :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hl (by omega)⟩

section
variable {H : Hash} (hz : Sizes H)
include hz

theorem Sizes.B4 : H.B % 4 = 0 ∧ 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> rw [h] <;> decide

theorem Sizes.tail_length : H.tailB.length = H.B - H.D := by
  have := hz.DL
  simp only [Hash.tailB, tail, List.length_append, List.length_singleton, List.length_replicate,
    List.length_map, List.length_range]
  omega

omit hz in
/-- `eax` at the block. -/
theorem atBlk_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .eax = s.gpr .ebx + BitVec.ofNat 32 H.N → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' Q) :
    WP isa (.block (H.atBlk ++ rest)) s Q := by
  simp only [Hash.atBlk, List.cons_append, List.nil_append]
  exact wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => k s₂ (by rw [u₂.gpr, u₁.gpr])
    (fun r hr => by rw [u₂.other r hr, u₁.other r hr]) (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd])
    (by rw [u₂.wr, u₁.wr])

/-- The padding after the block's first `D` bytes. -/
theorem pad_ok {s : State} {x : BitVec 32} (hx : s.gpr .ebx = x) (hf : x.toNat + (H.N + H.B) ≤ 2 ^ 32)
    (hw : Covers [⟨x.setWidth 64, H.N + H.B⟩] s.wr) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (x.setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) H.tailB →
      WP isa (.block rest) s' Q) :
    WP isa (.block (H.pad ++ rest)) s Q := by
  have := hz.D; have := hz.B4; have := hz.tail_length; have := hz.DL
  have h4 : 4 * ((H.B - H.D) / 4) = H.B - H.D := by omega
  refine storeW_ok (by decide) _ rest s Q (by omega) hx (by omega) (fun j hj => ?_) fun s' g rd wr m =>
    k s' g rd wr ?_
  · rw [addr_eq (by omega)]; exact inReg hw (by omega) (by omega)
  · rw [m, h4, List.take_of_length_le (by omega)]

end

/-- The digest of the hash value into the block, from `OutOk`, the padding
after its first `D` bytes as it was. -/
theorem digest_ok {H : Hash} (hz : Sizes H) {md : Md H.B H.N H.L} (hout : OutOk md H.out) {s : State}
    {x : BitVec 32} (hx : s.gpr .ebx = x) (hf : x.toNat + (H.N + H.B) ≤ 2 ^ 32)
    (hw : Covers [⟨x.setWidth 64, H.N + H.B⟩] s.wr)
    (hpad : bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [⟨x.setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem s'.mem →
      bytesAt s'.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) H.D = (md.digest (md.stateAt s.mem (x.setWidth 64))).take H.D →
      bytesAt s'.mem (x.setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB →
      WP isa (.block rest) s' Q) :
    WP isa (.block (H.digest ++ rest)) s Q := by
  have := hz.D; have := hz.B4; have := hz.tail_length; have := hz.N; have := hz.DL
  have h4 : 4 * ((H.N - H.D) / 4) = H.N - H.D := by omega
  let X := x.setWidth 64
  have aN : (x + BitVec.ofNat 32 H.N).setWidth 64 = X + BitVec.ofNat 64 H.N := setWidth_add (by omega)
  have tN : (x + BitVec.ofNat 32 H.N).toNat = x.toNat + H.N := toNat_add_ofNat (by omega)
  unfold Hash.digest
  simp only [List.append_assoc]
  refine atBlk_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ => ?_
  rw [WP.block_append_iff]
  have bx₁ : s₁.gpr .ebx = x := by rw [g₁ _ (by decide), hx]
  refine WP.mono (hout s₁ (by rw [bx₁]; omega) (by rw [e₁, hx, tN]; omega) ?_ ?_ ?_) fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
  · rw [bx₁, rd₁, wr₁]
    have := inReg (o := 0) (n := H.N) hw (by omega) (by omega)
    rw [BitVec.add_zero] at this
    exact Proof.Hmac.Generic.Common.InRegions.right' this
  · rw [e₁, hx, aN, wr₁]; exact inReg hw (by omega) (by omega)
  · rw [bx₁, e₁, hx, aN]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)
  rw [e₁, hx, aN, bx₁, m₁] at m₂
  have hdl := md.digest_length (md.stateAt s.mem X)
  have bx₂ : s₂.gpr .ebx = x := by rw [g₂ _ (by decide) (by decide), bx₁]
  refine storeW_ok (by decide) _ rest s₂ Q (by omega) bx₂ (by omega) (fun j hj => ?_)
    fun s₃ g₃ rd₃ wr₃ m₃ => k s₃ (fun r h1 h2 h3 => by rw [g₃ r h2, g₂ r h2 h3, g₁ r h1]) (by rw [rd₃, rd₂, rd₁])
      (by rw [wr₃, wr₂, wr₁]) ?_ ?_ ?_
  · rw [addr_eq (by omega), wr₂, wr₁]; exact inReg hw (by omega) (by omega)
  · rw [m₃, m₂, h4]
    refine (writeBytes_frame _ _ _ ?_).trans (writeBytes_frame _ _ _ ?_)
    · rw [hdl]; have := Offset.contains_base (X + BitVec.ofNat 64 H.N) (d := 0) (n := H.N) (k := H.B) (by omega)
        (by omega); rwa [BitVec.add_zero] at this
    · rw [List.length_take, Nat.min_eq_left (by omega), ← Memory.add_ofNat]
      exact Offset.contains_base _ (by omega) (by omega)
  · rw [m₃, h4, bytesAt_writeBytes_sep _ _ ?_ (by omega), m₂,
      Proof.Hmac.Generic.Common.bytesAt_take _ _ hz.D.2.1,
      Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' hdl (by omega)]
    rw [List.length_take, Nat.min_eq_left (by omega), ← Memory.add_ofNat]
    have := Offset.sep (X + BitVec.ofNat 64 H.N) (d := 0) (n := H.D) (e := H.D) (k := H.N - H.D) (.inl (by omega))
      (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  · -- The padding: its first `N - D` bytes written back, the rest as it was.
    have hsplit : ∀ m : Mem, bytesAt m (X + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) =
        bytesAt m (X + BitVec.ofNat 64 (H.N + H.D)) (H.N - H.D) ++
          bytesAt m (X + BitVec.ofNat 64 (H.N + H.N)) (H.B - H.N) := by
      intro m
      rw [show H.B - H.D = (H.N - H.D) + (H.B - H.N) by omega, bytesAt_add, Memory.add_ofNat,
        show H.N + H.D + (H.N - H.D) = H.N + H.N by omega]
    have hY : bytesAt s.mem (X + BitVec.ofNat 64 (H.N + H.N)) (H.B - H.N) = H.tailB.drop (H.N - H.D) := by
      rw [← hpad, hsplit, List.drop_left' (bytesAt_length _ _ _)]
    have r₂ : bytesAt s₂.mem (X + BitVec.ofNat 64 (H.N + H.N)) (H.B - H.N) =
        bytesAt s.mem (X + BitVec.ofNat 64 (H.N + H.N)) (H.B - H.N) := by
      rw [m₂, ← Memory.add_ofNat]
      refine bytesAt_writeBytes_sep _ _ ?_ (by omega)
      rw [hdl]
      have := Offset.sep (X + BitVec.ofNat 64 H.N) (d := H.N) (n := H.B - H.N) (e := 0) (k := H.N) (.inr (by omega))
        (by omega) (by omega)
      rwa [BitVec.add_zero] at this
    have htl : (H.tailB.take (H.N - H.D)).length = H.N - H.D := by rw [List.length_take]; omega
    rw [hsplit, m₃, h4, Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' htl (by omega),
      bytesAt_writeBytes_sep _ _ ?_ (by omega), r₂, hY, List.take_append_drop]
    rw [htl, ← Memory.add_ofNat, ← Memory.add_ofNat]
    exact Offset.sep _ (.inr (by omega)) (by omega) (by omega)

/-! ## What the proofs know of a hash function -/

/-- A hash function's x86 functions, verified: its streaming functions, as
HMAC's `init` and `finalize` call them (`HashOK`), and its `Md`, from the
initial hash value `iv`, which is the hash function of the specification
(`link`, and `back`: a state represents a message as the specification has
it if it does as `md` has it), whose stored hash value depends only on its
bytes (`reloc`), whose
padding of a `B + D`-byte message is the code's (`tail`), whose digest the
code's `out` writes, and whose compression function is verified (`comp`). -/
structure MdOk (H : Hash) where
  hH : VG.Proof.Pbkdf2.Stream.X86.HashOK H.st
  md : Md H.B H.N H.L
  iv : md.HV
  link : md.Link hH.SH iv H.D
  back : ∀ m p x, md.Repr iv m p x → hH.SH.Repr m p x
  reloc : md.Reloc
  tail : md.tailPad H.D = H.tailB
  out : OutOk md H.out
  comp : CompOk md H.so H.compC
  sizes : Sizes H

end VG.Proof.Pbkdf2.Md.X86
