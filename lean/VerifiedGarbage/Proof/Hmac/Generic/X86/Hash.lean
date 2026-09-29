import VerifiedGarbage.Proof.Hmac.Generic.X86.Contract
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
import VerifiedGarbage.Impl.Pbkdf2.Generic.X86

/-!
# HMAC over any streaming hash function on x86 (32-bit): the functions we call

Untrusted: everything here is checked by Lean. As on the other targets
(`Proof/Hmac/Generic/Arm/Hash.lean`): `HashOK H` is what the proofs know of
the hash function `H`: its streaming functions are verified against
`initK`, `updK` and `finK`, never write `esp` and use at most 20 bytes of
stack, the representation of its streaming state is determined by the
state's bytes, and its sizes are small.

Each call is in a frame of its arguments (`WP.callWith`): `init_frame`,
`upd_frame` and `fin_frame` run one, from the state before its push, given
the registers pushed (`InitArgs`, `UpdArgs`, `FinArgs`, which give the
callee's precondition, `CallPre`). A call writes the 48 bytes below `esp`
(`stk`), which `After` lets change. `init_rel`, `upd_rel` and `fin_rel`
relate two runs of them (`RelCT.callWith`).
-/

namespace VG.Proof.Hmac.Generic.X86

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash)
open VG.Proof.Sha256.X86.Stream (Upd WP.cons)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-- A streaming hash function's x86 functions, verified. `Wb` is the scratch
space their contracts use, at most the `8 W` bytes we give them. -/
structure HashOK (H : Hash) where
  SH : StreamingHash
  Wb : Nat
  hS : SH.stateBytes = H.S
  hD : SH.digestBytes = H.D
  hB : SH.H.blockSize = H.B
  hDF : H.D ≤ H.F
  hF : H.F ≤ 64
  hD0 : 0 < H.D
  hS0 : 0 < H.S
  hSB : H.S ≤ 256
  hB0 : 0 < H.B
  hBB : H.B ≤ 128
  hWb : Wb ≤ 8 * H.W
  hW : H.W ≤ 64
  /-- The representation depends only on the state's bytes. -/
  repr : ∀ (m m' : Mem) (p q : Addr) (msg : List Byte),
    (∀ i < H.S, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) →
    SH.Repr m p msg → SH.Repr m' q msg
  init : Verified X86.target H.initC (initK H.S SH.Repr)
  upd : Verified X86.target H.updC (updK H.S Wb SH.Repr)
  fin : Verified X86.target H.finC (finK H.S Wb H.F H.D SH.Repr SH.H.hash)
  initSp : NoSp H.initC
  updSp : NoSp H.updC
  finSp : NoSp H.finC
  initSU : stackUse H.initC ≤ 20
  updSU : stackUse H.updC ≤ 20
  finSU : stackUse H.finC ≤ 20

variable {H : Hash} (hH : HashOK H)

/-- The 48 bytes below `esp`, where our frames and calls go. -/
abbrev stk (s : State) : Region := below (s.gpr .esp) 48

/-- What a call leaves: the regions, the callee-saved registers (`esp`
among them), and memory outside what it may write and `stk`. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame (ws ++ [stk s]) s.mem s'.mem

theorem After.esp {s s' : State} {ws : List Region} (h : After s ws s') : s'.gpr .esp = s.gpr .esp :=
  h.cs .esp (by simp [calleeSaved])

theorem frame_app {ws ws' : List Region} {m m' : Mem} (h : Frame ws m m') : Frame (ws ++ ws') m m' :=
  h.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩

/-! ## The stack below `esp` -/

section Stack
variable {E : BitVec 32} (hE : 48 ≤ E.toNat)
include hE

/-- `n` bytes at `k ≥ n` below `E` are in `below E 48`. -/
theorem stk_sub {k n : Nat} (hn : n ≤ k) (hk : k ≤ 48) :
    Region.Sub ⟨(E - BitVec.ofNat 32 k).setWidth 64, n⟩ (below E 48) := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [Taint.sub_setWidth (by omega)] at ha
  rw [Taint.sub_setWidth (by omega)]
  have := E.isLt
  have hE' : (E.setWidth 64).toNat = E.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  generalize E.setWidth 64 = B at *
  bv_omega

/-- The `n` bytes below `E - k`, as a contract writes them, are in `below E 48`. -/
theorem stk_sub' {k n : Nat} (h : k + n ≤ 48) :
    Region.Sub ⟨(E - BitVec.ofNat 32 k).setWidth 64 - BitVec.ofNat 64 n, n⟩ (below E 48) := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [Taint.sub_setWidth (by omega)] at ha
  rw [Taint.sub_setWidth (by omega)]
  have := E.isLt
  have hE' : (E.setWidth 64).toNat = E.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  generalize E.setWidth 64 = B at *
  bv_omega

end Stack

@[simp] theorem count_withRegions (s : State) (rd wr : List Region) :
    count (s.withRegions rd wr) = count s := rfl

theorem toNat_sub_ofNat {E : BitVec 32} {k : Nat} (h : k ≤ E.toNat) :
    (E - BitVec.ofNat 32 k).toNat = E.toNat - k := sub_toNat h

theorem zero_append_ofNat {n : Nat} (h : n < 2 ^ 32) :
    (0 : BitVec 32) ++ BitVec.ofNat 32 n = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have z : (0 : BitVec 32).toNat = 0 := rfl
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, z, Nat.zero_shiftLeft, Nat.zero_or]
  omega

/-- After a framed call, from what `WP.callWith` gives. -/
theorem after_of {s s' : State} {ws : List Region} {n : Nat} (h48 : 48 ≤ (s.gpr .esp).toNat) (hn : n ≤ 48)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame (ws ++ [below (s.gpr .esp) n]) s.mem s'.mem) : After s ws s' :=
  ⟨hrd, hwr, hcs, Frame.below_mono hf hn h48⟩

theorem covers_one {rs : List Region} {r : Region} (h : r ∈ rs) : Covers [r] rs :=
  Covers.of_sub fun r' hr' => by
    simp only [List.mem_singleton] at hr'
    exact ⟨r, h, 0, by rw [hr']; simp, by rw [hr']; simp⟩

/-! ## `init`, in a frame of its argument -/

/-- What a framed call of `init` on the state at `st` (in `r`) needs. -/
structure InitArgs (s : State) (r : Reg) (st : BitVec 32) : Prop where
  hst : s.gpr r = st
  hr : r ≠ .esp
  sp48 : 48 ≤ (s.gpr .esp).toNat
  cw : Covers [⟨st.setWidth 64, H.S⟩] s.wr
  b_st : (stk s).Disjoint ⟨st.setWidth 64, H.S⟩
  nst : st.toNat + H.S ≤ 2 ^ 32

/-- The regions `init` is given: its argument and the state. -/
abbrev InitArgs.rd (sp : BitVec 32) : List Region := [below sp 4]
abbrev InitArgs.wr (st : BitVec 32) : List Region := [⟨st.setWidth 64, H.S⟩]

namespace InitArgs
variable {s : State} {r : Reg} {st : BitVec 32} (h : InitArgs (H := H) s r st)
include h

theorem fit : 4 * [r].length + 4 ≤ (s.gpr .esp).toNat := by have := h.sp48; simp only [List.length_cons, List.length_nil]; omega
theorem nesp : Reg.esp ∉ [r] := by simp [Ne.symm h.hr]

theorem a0 : arg (pushed [r] s).callEntry 0 = st := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.hst

theorem callPre : CallPre (initK H.S hH.SH.Repr) [r] (InitArgs.rd (s.gpr .esp)) (InitArgs.wr (H := H) st) s := by
  have e := h.sp48
  have fit := h.fit
  refine ⟨?_, ?_, ?_⟩
  · simp only [initK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
      argAddr_withRegions, h.a0, callEntry_argAddr0, callEntry_esp', List.length_cons, List.length_nil]
    refine ⟨trivial, trivial, h.b_st.sub_left (below_sub (by omega) e), ?_, h.nst, ?_⟩
    · exact h.b_st.sub_left (stk_sub e (by omega) (by omega))
    · rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact InRegions_append_cons.mpr (.inl hc)
    · obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
  · intro a n hi
    obtain ⟨q', hq', hc'⟩ := h.cw a n hi
    exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

end InitArgs

theorem init_frame {s : State} {r : Reg} {st : BitVec 32} (h : InitArgs (H := H) s r st) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st.setWidth 64, H.S⟩] s' → hH.SH.Repr s'.mem (st.setWidth 64) [] → Q s') :
    WP isa (H.callInit r) s Q := by
  have e := h.sp48
  have su := hH.initSU
  refine WP.callWith hH.init.1 hH.initSp (by simp) h.nesp
    (by simp only [List.length_cons, List.length_nil]; omega) (h.callPre hH) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  refine hQ s' (after_of e (by simp only [List.length_cons, List.length_nil]; omega) rd' wr' cs' f') ?_
  simp only [initK, arg_withRegions, h.a0] at post
  rw [← m₂]; exact post

/-! ## `update`, in a frame of its arguments -/

/-- What a framed call of `update` needs of the state before its push: the
state at `st` in `r`, the scratch space at `sc` in `ebp`, the `len` bytes of
data at `d` in `edx` and `ecx`, and the count, `0` in `eax` and `c` in
`lo`; the regions the callee may read and write; that they are disjoint as
it needs, and from the 48 bytes below `esp`; and that none of them wraps
around. -/
structure UpdArgs (s : State) (lo r : Reg) (st d sc c : BitVec 32) (len : Nat) : Prop where
  hst : s.gpr r = st
  hlo : s.gpr lo = c
  eax : s.gpr .eax = 0
  ecx : s.gpr .ecx = BitVec.ofNat 32 len
  edx : s.gpr .edx = d
  ebp : s.gpr .ebp = sc
  hr : r ≠ .esp
  hl : lo ≠ .esp
  hlen : len < 2 ^ 32
  sp48 : 48 ≤ (s.gpr .esp).toNat
  cd : Covers [⟨d.setWidth 64, len⟩] (s.rd ++ s.wr)
  cw : Covers [⟨st.setWidth 64, H.S⟩, ⟨sc.setWidth 64, hH.Wb⟩] s.wr
  st_sc : Region.Disjoint ⟨st.setWidth 64, H.S⟩ ⟨sc.setWidth 64, hH.Wb⟩
  d_st : Region.Disjoint ⟨d.setWidth 64, len⟩ ⟨st.setWidth 64, H.S⟩
  d_sc : Region.Disjoint ⟨d.setWidth 64, len⟩ ⟨sc.setWidth 64, hH.Wb⟩
  b_st : (stk s).Disjoint ⟨st.setWidth 64, H.S⟩
  b_d : (stk s).Disjoint ⟨d.setWidth 64, len⟩
  b_sc : (stk s).Disjoint ⟨sc.setWidth 64, hH.Wb⟩
  nst : st.toNat + H.S ≤ 2 ^ 32
  nd : d.toNat + len ≤ 2 ^ 32
  nsc : sc.toNat + hH.Wb ≤ 2 ^ 32

/-- The six words `update`'s frame pushes, last to first. -/
abbrev upd6 (lo r : Reg) : List Reg := [.ebp, .ecx, .edx, .eax, lo, r]

/-- The regions `update` is given: the data and its arguments, the state and the scratch space. -/
abbrev UpdArgs.rd (sp d : BitVec 32) (len : Nat) : List Region :=
  [⟨d.setWidth 64, len⟩, below sp 24]
abbrev UpdArgs.wr (st sc : BitVec 32) : List Region := [⟨st.setWidth 64, H.S⟩, ⟨sc.setWidth 64, hH.Wb⟩]

namespace UpdArgs
variable {hH} {s : State} {lo r : Reg} {st d sc c : BitVec 32} {len : Nat}
  (h : UpdArgs hH s lo r st d sc c len)
include h

theorem fit : 4 * (upd6 lo r).length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.sp48; simp only [List.length_cons, List.length_nil]; omega
theorem nesp : Reg.esp ∉ upd6 lo r := by simp [Ne.symm h.hr, Ne.symm h.hl]

theorem a0 : arg (pushed (upd6 lo r) s).callEntry 0 = st := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.hst
theorem a1 : arg (pushed (upd6 lo r) s).callEntry 1 = c := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.hlo
theorem a2 : arg (pushed (upd6 lo r) s).callEntry 2 = 0 := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.eax
theorem a3 : arg (pushed (upd6 lo r) s).callEntry 3 = d := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.edx
theorem a4 : arg (pushed (upd6 lo r) s).callEntry 4 = BitVec.ofNat 32 len := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.ecx
theorem a5 : arg (pushed (upd6 lo r) s).callEntry 5 = sc := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.ebp

theorem count_eq : count (pushed (upd6 lo r) s).callEntry = (0 : BitVec 32) ++ c := by
  rw [count, h.a1, h.a2]

theorem hlen' : (BitVec.ofNat 32 len).toNat = len := by rw [BitVec.toNat_ofNat]; have := h.hlen; omega

theorem callPre : CallPre (updK H.S hH.Wb hH.SH.Repr) (upd6 lo r) (UpdArgs.rd (s.gpr .esp) d len) (UpdArgs.wr hH st sc) s := by
  have e := h.sp48
  have fit := h.fit
  refine ⟨?_, ?_, ?_⟩
  · simp only [updK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
      argAddr_withRegions, h.a0, h.a3, h.a4, h.a5, h.hlen', callEntry_argAddr0, callEntry_esp', upd6,
      List.length_cons, List.length_nil]
    have sA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 6)).setWidth 64, 24⟩ (stk s) :=
      stk_sub e (by omega) (by omega)
    have sR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 6 + 4)).setWidth 64, 4⟩ (stk s) :=
      stk_sub e (by omega) (by omega)
    have sK : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 6 + 4)).setWidth 64 - 20, 20⟩ (stk s) :=
      stk_sub' (n := 20) e (by omega)
    refine ⟨trivial, trivial, h.st_sc, h.d_st, h.d_sc, h.b_st.sub_left sA, h.b_sc.sub_left sA,
      h.b_st.sub_left sR, h.b_sc.sub_left sR, h.b_st.sub_left sK, h.b_sc.sub_left sK, h.b_d.sub_left sK,
      h.nst, h.nd, h.nsc, ?_, ?_⟩
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := h.cd a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', hq', hc'⟩)
    · refine InRegions_append_cons.mpr (.inl ?_)
      simpa using hc
    · obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
  · intro a n hi
    obtain ⟨q', hq', hc'⟩ := h.cw a n hi
    exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

/-- The callee's memory on entry is ours outside `stk`. -/
theorem entry_frame : Frame [stk s] s.mem (pushed (upd6 lo r) s).callEntry.mem :=
  (callEntry_frame h.fit h.nesp).sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_singleton_self _, below_sub (by simp only [List.length_cons, List.length_nil]; omega) h.sp48⟩

end UpdArgs

theorem upd_frame {s : State} {lo r : Reg} {st d sc c : BitVec 32} {len : Nat}
    (h : UpdArgs hH s lo r st d sc c len) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st.setWidth 64, H.S⟩, ⟨sc.setWidth 64, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem (st.setWidth 64) m → (0 : BitVec 32) ++ c = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem (st.setWidth 64) (m ++ bytesAt s.mem (d.setWidth 64) len)) → Q s') :
    WP isa (.frame (.push (upd6 lo r)) (.call H.updN H.updC) (.pop .eax (upd6 lo r).length)) s Q := by
  have e := h.sp48
  have su := hH.updSU
  refine WP.callWith hH.upd.1 hH.updSp (by simp) h.nesp
    (by simp only [List.length_cons, List.length_nil]; omega) h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  refine hQ s' (after_of e (by simp only [List.length_cons, List.length_nil]; omega) rd' wr' cs' f') fun m hr hc => ?_
  simp only [updK, arg_withRegions, State.withRegions_mem, h.a0, h.a3, h.a4, h.hlen'] at post
  have fE := h.entry_frame
  have hs : ∀ q ∈ [stk s], (⟨st.setWidth 64, H.S⟩ : Region).Disjoint q := by
    simp only [List.mem_singleton]; rintro q rfl; exact h.b_st.symm
  have hr' : hH.SH.Repr (pushed (upd6 lo r) s).callEntry.mem (st.setWidth 64) m :=
    hH.repr _ _ _ _ _ (fun i hi => fE.bytes (R := ⟨st.setWidth 64, H.S⟩) hs
      (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega) hi) hr
  have hd : bytesAt (pushed (upd6 lo r) s).callEntry.mem (d.setWidth 64) len = bytesAt s.mem (d.setWidth 64) len := by
    simp only [bytesAt]
    apply List.map_congr_left
    intro i hi
    exact fE.bytes (R := ⟨d.setWidth 64, len⟩)
      (by simp only [List.mem_singleton]; rintro q rfl; exact h.b_d.symm) (by show len ≤ 2 ^ 64; have := h.hlen; omega)
      (List.mem_range.mp hi)
  rw [← m₂, ← hd]
  exact post m hr' (by rw [count_withRegions, h.count_eq]; exact hc)

/-! ## `finalize`, in a frame of its arguments -/

/-- What a framed call of `finalize` needs of the state before its push:
the state at `st` in `r`, the count `hi ++ lo` in `ecx` and `eax`, and `out`
at `o` and the scratch space at `sc` in `edx` and `ebp`, as for `update`. -/
structure FinArgs (s : State) (r : Reg) (st o sc lo hi : BitVec 32) : Prop where
  hst : s.gpr r = st
  eax : s.gpr .eax = lo
  ecx : s.gpr .ecx = hi
  edx : s.gpr .edx = o
  ebp : s.gpr .ebp = sc
  hr : r ≠ .esp
  sp48 : 48 ≤ (s.gpr .esp).toNat
  cw : Covers [⟨st.setWidth 64, H.S⟩, ⟨o.setWidth 64, H.F⟩, ⟨sc.setWidth 64, hH.Wb⟩] s.wr
  st_o : Region.Disjoint ⟨st.setWidth 64, H.S⟩ ⟨o.setWidth 64, H.F⟩
  st_sc : Region.Disjoint ⟨st.setWidth 64, H.S⟩ ⟨sc.setWidth 64, hH.Wb⟩
  o_sc : Region.Disjoint ⟨o.setWidth 64, H.F⟩ ⟨sc.setWidth 64, hH.Wb⟩
  b_st : (stk s).Disjoint ⟨st.setWidth 64, H.S⟩
  b_o : (stk s).Disjoint ⟨o.setWidth 64, H.F⟩
  b_sc : (stk s).Disjoint ⟨sc.setWidth 64, hH.Wb⟩
  nst : st.toNat + H.S ≤ 2 ^ 32
  no : o.toNat + H.F ≤ 2 ^ 32
  nsc : sc.toNat + hH.Wb ≤ 2 ^ 32

/-- The five words `finalize`'s frame pushes, last to first. -/
abbrev fin5 (r : Reg) : List Reg := [.ebp, .edx, .ecx, .eax, r]

/-- The regions `finalize` is given, all writable: the state, `out`, the
scratch space and its arguments. -/
abbrev FinArgs.wr (st o sc sp : BitVec 32) : List Region :=
  [⟨st.setWidth 64, H.S⟩, ⟨o.setWidth 64, H.F⟩, ⟨sc.setWidth 64, hH.Wb⟩, below sp 20]

namespace FinArgs
variable {hH} {s : State} {r : Reg} {st o sc lo hi : BitVec 32} (h : FinArgs hH s r st o sc lo hi)
include h

theorem fit : 4 * (fin5 r).length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.sp48; simp only [List.length_cons, List.length_nil]; omega
theorem nesp : Reg.esp ∉ fin5 r := by simp [Ne.symm h.hr]

theorem a0 : arg (pushed (fin5 r) s).callEntry 0 = st := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.hst
theorem a1 : arg (pushed (fin5 r) s).callEntry 1 = lo := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.eax
theorem a2 : arg (pushed (fin5 r) s).callEntry 2 = hi := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.ecx
theorem a3 : arg (pushed (fin5 r) s).callEntry 3 = o := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.edx
theorem a4 : arg (pushed (fin5 r) s).callEntry 4 = sc := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.ebp

theorem count_eq : count (pushed (fin5 r) s).callEntry = hi ++ lo := by
  rw [count, h.a1, h.a2]

theorem callPre : CallPre (finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash) (fin5 r) []
    (FinArgs.wr hH st o sc (s.gpr .esp)) s := by
  have e := h.sp48
  have fit := h.fit
  refine ⟨?_, ?_, ?_⟩
  · simp only [finK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
      argAddr_withRegions, h.a0, h.a3, h.a4, callEntry_argAddr0, callEntry_esp', fin5,
      List.length_cons, List.length_nil]
    have sA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 5)).setWidth 64, 20⟩ (stk s) :=
      stk_sub e (by omega) (by omega)
    have sR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 5 + 4)).setWidth 64, 4⟩ (stk s) :=
      stk_sub e (by omega) (by omega)
    have sK : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 5 + 4)).setWidth 64 - 20, 20⟩ (stk s) :=
      stk_sub' (n := 20) e (by omega)
    refine ⟨trivial, trivial, h.st_o, h.st_sc, h.o_sc, h.b_st.sub_left sA, h.b_o.sub_left sA,
      h.b_sc.sub_left sA, h.b_st.sub_left sR, h.b_o.sub_left sR, h.b_sc.sub_left sR,
      h.b_st.sub_left sK, h.b_o.sub_left sK, h.b_sc.sub_left sK, h.nst, h.no, h.nsc, ?_, ?_⟩
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · intro a n ⟨q, hq, hc⟩
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    rotate_left 3
    · refine InRegions_append_cons.mpr (.inl ?_)
      simpa using hc
    all_goals
      obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
  · intro a n ⟨q, hq, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    rotate_left 3
    · exact ⟨_, List.mem_cons_self, by simpa using hc⟩
    all_goals
      obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

theorem entry_frame : Frame [stk s] s.mem (pushed (fin5 r) s).callEntry.mem :=
  (callEntry_frame h.fit h.nesp).sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_singleton_self _, below_sub (by simp only [List.length_cons, List.length_nil]; omega) h.sp48⟩

end FinArgs

theorem fin_frame {s : State} {r : Reg} {st o sc lo hi : BitVec 32} (h : FinArgs hH s r st o sc lo hi)
    {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st.setWidth 64, H.S⟩, ⟨o.setWidth 64, H.F⟩, ⟨sc.setWidth 64, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem (st.setWidth 64) m → m.length < 2 ^ 64 → hi ++ lo = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (o.setWidth 64) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.frame (.push (fin5 r)) (.call H.finN H.finC) (.pop .eax (fin5 r).length)) s Q := by
  have e := h.sp48
  have su := hH.finSU
  refine WP.callWith hH.fin.1 hH.finSp (by simp) h.nesp
    (by simp only [List.length_cons, List.length_nil]; omega) h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  have n5 : (fin5 r).length = 5 := rfl
  rw [n5] at f'
  have f'' : Frame ([⟨st.setWidth 64, H.S⟩, ⟨o.setWidth 64, H.F⟩, ⟨sc.setWidth 64, hH.Wb⟩] ++
      [below (s.gpr .esp) (4 * 5 + stackUse H.finC + 4)]) s.mem s'.mem :=
    Frame.sub f' fun q hq => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
          below_sub (by omega) (by omega)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
          fun _ h => h⟩
  refine hQ s' (after_of e (by omega) rd' wr' cs' f'')
    fun m hr hl hc => ?_
  simp only [finK, arg_withRegions, State.withRegions_mem, h.a0, h.a3] at post
  have fE := h.entry_frame
  have hs : ∀ q ∈ [stk s], (⟨st.setWidth 64, H.S⟩ : Region).Disjoint q := by
    simp only [List.mem_singleton]; rintro q rfl; exact h.b_st.symm
  have hr' : hH.SH.Repr (pushed (fin5 r) s).callEntry.mem (st.setWidth 64) m :=
    hH.repr _ _ _ _ _ (fun i hi => fE.bytes (R := ⟨st.setWidth 64, H.S⟩) hs
      (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega) hi) hr
  rw [← m₂]
  exact post m hr' hl (by rw [count_withRegions, h.count_eq]; exact hc)

/-! ## The calls in two runs

A call in a frame of its arguments is constant time when the callee's
precondition holds in both runs, `esp` is the same in both, and so are the
registers pushed (`RelCT.callWith`). -/

include hH in
theorem init_rel {P : State → State → Prop} {sp : BitVec 32} {r : Reg} {st : BitVec 32}
    (h : ∀ s s', P s s' → InitArgs (H := H) s r st ∧ InitArgs (H := H) s' r st ∧ s.gpr .esp = sp ∧
      s'.gpr .esp = sp) :
    RelCT isa P (H.callInit r) fun _ _ => True := by
  refine RelCT.callWith hH.init.1 hH.init.2.1 (InitArgs.rd sp) (InitArgs.wr (H := H) st) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c := a.callPre hH
  have c' := a'.callPre hH
  rw [e] at c; rw [e'] at c'
  refine ⟨c, c', e.trans e'.symm, ?_, ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e, e']
  · simp only [arg_withRegions, a.a0, a'.a0]

theorem upd_rel {P : State → State → Prop} {sp : BitVec 32} {lo r : Reg} {st d sc c : BitVec 32} {len : Nat}
    (h : ∀ s s', P s s' → UpdArgs hH s lo r st d sc c len ∧ UpdArgs hH s' lo r st d sc c len ∧
      s.gpr .esp = sp ∧ s'.gpr .esp = sp) :
    RelCT isa P (.frame (.push (upd6 lo r)) (.call H.updN H.updC) (.pop .eax (upd6 lo r).length))
      fun _ _ => True := by
  refine RelCT.callWith hH.upd.1 hH.upd.2.1 (UpdArgs.rd sp d len) (UpdArgs.wr hH st sc) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c₁ := a.callPre
  have c₂ := a'.callPre
  rw [e] at c₁; rw [e'] at c₂
  refine ⟨c₁, c₂, e.trans e'.symm, ?_, fun i hi => ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e, e']
  · simp only [arg_withRegions]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a.a0, a'.a0]
    · rw [a.a1, a'.a1]
    · rw [a.a2, a'.a2]
    · rw [a.a3, a'.a3]
    · rw [a.a4, a'.a4]
    · rw [a.a5, a'.a5]

theorem fin_rel {P : State → State → Prop} {sp : BitVec 32} {r : Reg} {st o sc lo hi : BitVec 32}
    (h : ∀ s s', P s s' → FinArgs hH s r st o sc lo hi ∧ FinArgs hH s' r st o sc lo hi ∧
      s.gpr .esp = sp ∧ s'.gpr .esp = sp) :
    RelCT isa P (.frame (.push (fin5 r)) (.call H.finN H.finC) (.pop .eax (fin5 r).length))
      fun _ _ => True := by
  refine RelCT.callWith hH.fin.1 hH.fin.2.1 [] (FinArgs.wr hH st o sc sp) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c₁ := a.callPre
  have c₂ := a'.callPre
  rw [e] at c₁; rw [e'] at c₂
  refine ⟨c₁, c₂, e.trans e'.symm, ?_, fun i hi => ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e, e']
  · simp only [arg_withRegions]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [a.a0, a'.a0]
    · rw [a.a1, a'.a1]
    · rw [a.a2, a'.a2]
    · rw [a.a3, a'.a3]
    · rw [a.a4, a'.a4]

/-! ## The pieces between the calls

The taint analysis checks the code between the calls from the registers
that hold our variables, and the words of the stack arguments (`argTaint`),
which the pieces read again: they are public, and the same in both runs as
long as nothing has written them (`ArgsKept`). -/

/-- The taint in which `esp`, the registers `rs` and the `n - 4` bytes of
stack arguments are public. -/
def argTaint (rs : List Reg) (n : Nat) : VG.X86.Taint.T :=
  { regs := .ofList (.esp :: rs), flags := false, argLen := n }

/-- The `k` words of arguments of `s` are those of `s₀`. -/
def ArgsKept (s₀ : State) (k : Nat) (s : State) : Prop := ∀ i < k, arg s i = arg s₀ i

/-- The arguments lie outside the writable regions, and do not wrap around. -/
def ArgsOut (k : Nat) (s : State) : Prop :=
  (s.gpr .esp).toNat + (4 + 4 * k) ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4 + 4 * k⟩ r

theorem agree_argTaint {rs : List Reg} {k : Nat} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hsp : s₁.gpr .esp = s₂.gpr .esp) (hw₁ : ArgsOut k s₁) (hw₂ : ArgsOut k s₂)
    (hm : ∀ i < k, arg s₁ i = arg s₂ i) : VG.X86.Taint.Agree (argTaint rs (4 + 4 * k)) s₁ s₂ := by
  have wf : ∀ s : State, ArgsOut k s → VG.X86.Taint.Wf (argTaint rs (4 + 4 * k)) s := fun s hs =>
    VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
      fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hs.1, hs.2⟩, fun _ h => (List.not_mem_nil h).elim⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf s₁ hw₁, wf s₂ hw₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp,
    fun j h4 hj => ?_⟩
  · simp only [argTaint, RegSet.mem_ofList, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact hsp
    · exact h r hr
  · simp only [argTaint] at hj
    rw [show VG.X86.Taint.depth (argTaint rs (4 + 4 * k)).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hw₁.1 h4 hj, VG.X86.Taint.argByte_eq hw₂.1 h4 hj,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (hm _ (by omega))

/-- Code the taint analysis checks from `τ`, in two runs whose single-run
facts `F` and `F'` make them agree on it. -/
theorem rel_agree {F F' G G' : State → Prop} {c : Prog isa} (τ : VG.X86.Taint.T)
    (hag : ∀ s s', F s → F' s' → VG.X86.Taint.Agree τ s s')
    (hc : ∃ hc, (VG.Taint.check taint τ c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) τ (fun s s' h => hag s s' h.1 h.2) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A call, in two runs each described by `WP`. -/
theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => F s ∧ F' s') c fun _ _ => True)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Hmac.Generic.X86
