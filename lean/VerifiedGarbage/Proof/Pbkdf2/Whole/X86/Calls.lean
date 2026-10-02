import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the calls of HMAC's functions and of `iterate`

`pbkdf2` calls HMAC's `init` and `finalize` and PBKDF2's `iterate`, each
verified against its shared contract (`VG.Spec.Hmac.initContract`,
`VG.Spec.Hmac.finalizeContract`, `VG.Spec.Pbkdf2.iterateContract`) with 48
bytes of stack and some working space; what a caller uses of such a proof is
`Sound`. Each call is in a frame of its arguments (`WP.callWith`): `hi_frame`,
`hf_frame` and `it_frame` run one, from the state before its push, given the
registers pushed (`HiArgs`, `HfArgs`, `ItArgs`), which give the callee's
precondition (evaluated with `sig_pre`); `hi_rel`, `hf_rel` and `it_rel`
relate two runs of one (`RelCT.callWith`).

Our frames hold at most six words, so with the return address and the 48
bytes the callee uses, a call writes only the 76 bytes below `esp` (`stk`),
which `After` lets change.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- What a caller uses of a proof of `Verified X86.target c k`: that `c`
meets `k` and is constant time under it. -/
structure Sound (c : Prog isa) (k : Contract isa) : Prop where
  ok : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub c

theorem Sound.of_verified {c : Prog isa} {k : Contract isa} (h : Verified X86.target c k) : Sound c k :=
  ⟨h.1, h.2.1⟩

/-- `Sound` for a contract that asks no more and gives no less. -/
theorem Sound.weaken {c : Prog isa} {k k' : Contract isa} (h : Sound c k) (hpre : ∀ s, k'.pre s → k.pre s)
    (hpost : ∀ s s', k'.pre s → k.post s s' → k'.post s s')
    (hpub : ∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ → k.pub s₁ s₂) : Sound c k' :=
  ⟨fun s hs => (h.ok s (hpre s hs)).elim fun t ⟨s', he, ha, hp⟩ => ⟨t, s', he, ha, hpost s s' hs hp⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
      h.ct s₁ s₂ t₁ t₂ s₁' s₂' (hpre _ h₁) (hpre _ h₂) (hpub _ _ h₁ h₂ hp) e₁ e₂⟩

/-! ## The stack below `esp` -/

/-- The 76 bytes below `esp`, where our frames and calls go. -/
abbrev stk (s : State) : Region := below (s.gpr .esp) 76

/-- What a call leaves: the regions, the callee-saved registers (`esp`
among them), and memory outside what it may write and `stk`. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame (ws ++ [stk s]) s.mem s'.mem

theorem After.esp {s s' : State} {ws : List Region} (h : After s ws s') : s'.gpr .esp = s.gpr .esp :=
  h.cs .esp (by simp [calleeSaved])

/-- A call of a hash function's streaming function (`Proof/Pbkdf2/Stream/X86/Hash.lean`),
which writes only the 48 bytes below `esp`. -/
theorem After.of_hmac {s s' : State} {ws : List Region} (h76 : 76 ≤ (s.gpr .esp).toNat)
    (h : Pbkdf2.Stream.X86.After s ws s') : After s ws s' :=
  ⟨h.rd, h.wr, h.cs, Frame.below_mono h.frame (by decide) h76⟩

theorem below_eq {E : BitVec 32} {k : Nat} (h : k ≤ E.toNat) :
    below E k = ⟨E.setWidth 64 - BitVec.ofNat 64 k, k⟩ := by
  unfold below; rw [Taint.sub_setWidth h]

/-- Two ranges below `p` that do not overlap. -/
theorem bdisj (p : Addr) (c : Nat) {a n b k : Nat} (ha : a ≤ c) (hb : b ≤ c)
    (h : c - a + n ≤ c - b ∨ c - b + k ≤ c - a) (hn : c + n < 2 ^ 32) (hk : c + k < 2 ^ 32) :
    Region.Disjoint ⟨p - BitVec.ofNat 64 a, n⟩ ⟨p - BitVec.ofNat 64 b, k⟩ := by
  rw [Offset.sub_ofNat_eq p ha, Offset.sub_ofNat_eq p hb]
  exact Offset.disjoint _ h (by omega) (by omega)

section Frames
variable {E : BitVec 32} (hE : 76 ≤ E.toNat) {n : Nat} (hn : n ≤ 6)
include hE hn

/-- A frame of `n` words is in `stk`. -/
theorem args_sub : Region.Sub ⟨(E - BitVec.ofNat 32 (4 * n)).setWidth 64, 4 * n⟩ (below E 76) := by
  rw [below_eq hE, Taint.sub_setWidth (by omega)]
  exact Offset.sub_below _ (by omega) (by omega)

/-- So is the return address of the call in it. -/
theorem ret_sub : Region.Sub ⟨(E - BitVec.ofNat 32 (4 * n + 4)).setWidth 64, 4⟩ (below E 76) := by
  rw [below_eq hE, Taint.sub_setWidth (by omega)]
  exact Offset.sub_below _ (by omega) (by omega)

/-- And the 48 bytes below it, which the callee uses. -/
theorem cstk_sub :
    Region.Sub ⟨(E - BitVec.ofNat 32 (4 * n + 4)).setWidth 64 - BitVec.ofNat 64 48, 48⟩ (below E 76) := by
  rw [below_eq hE, Taint.sub_setWidth (by omega), Offset.sub_sub_ofNat]
  exact Offset.sub_below _ (by omega) (by omega)

theorem ret_args : Region.Disjoint ⟨(E - BitVec.ofNat 32 (4 * n + 4)).setWidth 64, 4⟩
    ⟨(E - BitVec.ofNat 32 (4 * n)).setWidth 64, 4 * n⟩ := by
  rw [Taint.sub_setWidth (by omega), Taint.sub_setWidth (by omega)]
  exact bdisj _ (4 * n + 4) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem cstk_args :
    Region.Disjoint ⟨(E - BitVec.ofNat 32 (4 * n + 4)).setWidth 64 - BitVec.ofNat 64 48, 48⟩
      ⟨(E - BitVec.ofNat 32 (4 * n)).setWidth 64, 4 * n⟩ := by
  rw [Taint.sub_setWidth (by omega), Taint.sub_setWidth (by omega), Offset.sub_sub_ofNat]
  exact bdisj _ (4 * n + 52) (by omega) (by omega) (by omega) (by omega) (by omega)

end Frames

theorem argVal32 (s : State) (i : Nat) : argVal s 32 i = (arg s i).setWidth 64 := rfl

theorem toNat_setWidth64 (a : BitVec 32) : (a.setWidth 64).toNat = a.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

theorem setWidth32_64 (a : BitVec 32) : (a.setWidth 64).setWidth 32 = a := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; have := a.isLt; omega

theorem toNat_ofNat32 {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The callee's memory on entry is ours outside `stk`. -/
theorem entry_frame {rs : List Reg} {s : State} (hrs : Reg.esp ∉ rs) (hn : rs.length ≤ 6)
    (h76 : 76 ≤ (s.gpr .esp).toNat) : Frame [stk s] s.mem (pushed rs s).callEntry.mem :=
  (callEntry_frame (by omega) hrs).sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_singleton_self _, below_sub (by omega) h76⟩

theorem entry_bytes {rs : List Reg} {s : State} (hrs : Reg.esp ∉ rs) (hn : rs.length ≤ 6)
    (h76 : 76 ≤ (s.gpr .esp).toNat) {p : Addr} {k : Nat} (hd : (stk s).Disjoint ⟨p, k⟩) (hk : k ≤ 2 ^ 64) :
    bytesAt (pushed rs s).callEntry.mem p k = bytesAt s.mem p k := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => (entry_frame hrs hn h76).bytes (R := ⟨p, k⟩)
    (by simp only [List.mem_singleton]; rintro q rfl; exact hd.symm) hk (List.mem_range.mp hi)

/-- From `WP.callWith`'s frame, our `After`. -/
theorem after_of {s s' : State} {ws : List Region} {n : Nat} (h76 : 76 ≤ (s.gpr .esp).toNat) (hn : n ≤ 76)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame (ws ++ [below (s.gpr .esp) n]) s.mem s'.mem) : After s ws s' :=
  ⟨hrd, hwr, hcs, Frame.below_mono hf hn h76⟩

/-! ## HMAC's `init`, in a frame of its arguments -/

/-- The five words of `init`'s frame, last to first. -/
abbrev hi5 : List Reg := [.ebp, .ecx, .edx, .esi, .edi]

/-- What a framed call of HMAC's `init` needs of the state before its push:
the states at `inn` and `out` in `edi` and `esi`, the `kl` bytes of key at
`k` in `edx` and `ecx`, and `8 Wi` bytes of scratch space at `sc` in `ebp`;
the regions the callee may read and write; that they are disjoint as it
needs, and from the 76 bytes below `esp`; and that none of them wraps
around. -/
structure HiArgs (S : StreamingHash) (Wi : Nat) (s : State) (inn out k sc : BitVec 32) (kl : Nat) : Prop where
  edi : s.gpr .edi = inn
  esi : s.gpr .esi = out
  edx : s.gpr .edx = k
  ecx : s.gpr .ecx = BitVec.ofNat 32 kl
  ebp : s.gpr .ebp = sc
  klB : kl ≤ S.H.blockSize
  kl32 : kl < 2 ^ 32
  sp : 76 ≤ (s.gpr .esp).toNat
  cr : Covers [⟨k.setWidth 64, kl⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn.setWidth 64, S.stateBytes⟩, ⟨out.setWidth 64, S.stateBytes⟩, ⟨sc.setWidth 64, Wi * 8⟩] s.wr
  i_o : Region.Disjoint ⟨inn.setWidth 64, S.stateBytes⟩ ⟨out.setWidth 64, S.stateBytes⟩
  i_k : Region.Disjoint ⟨inn.setWidth 64, S.stateBytes⟩ ⟨k.setWidth 64, kl⟩
  i_s : Region.Disjoint ⟨inn.setWidth 64, S.stateBytes⟩ ⟨sc.setWidth 64, Wi * 8⟩
  o_k : Region.Disjoint ⟨out.setWidth 64, S.stateBytes⟩ ⟨k.setWidth 64, kl⟩
  o_s : Region.Disjoint ⟨out.setWidth 64, S.stateBytes⟩ ⟨sc.setWidth 64, Wi * 8⟩
  k_s : Region.Disjoint ⟨k.setWidth 64, kl⟩ ⟨sc.setWidth 64, Wi * 8⟩
  b_i : (stk s).Disjoint ⟨inn.setWidth 64, S.stateBytes⟩
  b_o : (stk s).Disjoint ⟨out.setWidth 64, S.stateBytes⟩
  b_k : (stk s).Disjoint ⟨k.setWidth 64, kl⟩
  b_s : (stk s).Disjoint ⟨sc.setWidth 64, Wi * 8⟩
  ni : inn.toNat + S.stateBytes ≤ 2 ^ 32
  no : out.toNat + S.stateBytes ≤ 2 ^ 32
  nk : k.toNat + kl ≤ 2 ^ 32
  nsc : sc.toNat + Wi * 8 ≤ 2 ^ 32

/-- The regions `init` is given. -/
abbrev HiArgs.rd (k : BitVec 32) (kl : Nat) : List Region := [⟨k.setWidth 64, kl⟩]
abbrev HiArgs.wr (S : StreamingHash) (Wi : Nat) (sp inn out sc : BitVec 32) : List Region :=
  [⟨inn.setWidth 64, S.stateBytes⟩, ⟨out.setWidth 64, S.stateBytes⟩, ⟨sc.setWidth 64, Wi * 8⟩,
    ⟨(sp - BitVec.ofNat 32 20).setWidth 64, 20⟩]

/-- `init`'s precondition on its entry state `t`, after a frame of its five
arguments pushed from a state that `HiArgs` describes. -/
theorem HiArgs.pre_of {S : StreamingHash} {Wi : Nat} {s : State} {inn out k sc : BitVec 32} {kl : Nat}
    (h : HiArgs S Wi s inn out k sc kl) {t : State} (hsp : t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24)
    (a0 : arg t 0 = inn) (a1 : arg t 1 = out) (a2 : arg t 2 = k) (a3 : arg t 3 = BitVec.ofNat 32 kl)
    (a4 : arg t 4 = sc) (hA : argAddr t 0 = (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64)
    (hrd : t.rd = HiArgs.rd k kl) (hwr : t.wr = HiArgs.wr S Wi (s.gpr .esp) inn out sc) :
    (Spec.Hmac.initContract S Wi X86.abi 48).pre t := by
  have e := h.sp
  sig_pre [Spec.Hmac.initContract, Spec.Hmac.initSig, X86.abi]
  simp only [argVal32, a0, a1, a2, a3, a4, hA, hsp, hrd, hwr, toNat_setWidth64, toNat_ofNat32 h.kl32,
    setWidth32_64, show argBytes [32, 32, 32, 32, 32] = 20 from rfl]
  have sA := args_sub (E := s.gpr .esp) e (n := 5) (by decide)
  have sR := ret_sub (E := s.gpr .esp) e (n := 5) (by decide)
  have sK := cstk_sub (E := s.gpr .esp) e (n := 5) (by decide)
  have rA := ret_args (E := s.gpr .esp) e (n := 5) (by decide)
  have kA := cstk_args (E := s.gpr .esp) e (n := 5) (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at sA sR sK rA kA
  refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; omega, trivial, trivial,
    h.i_o, h.i_k, h.i_s, (h.b_i.sub_left sA).symm, h.o_k, h.o_s, (h.b_o.sub_left sA).symm, h.k_s,
    (h.b_k.sub_left sA).symm, (h.b_s.sub_left sA).symm,
    h.b_i.sub_left sR, h.b_o.sub_left sR, h.b_k.sub_left sR, h.b_s.sub_left sR, rA,
    h.b_i.sub_left sK, h.b_o.sub_left sK, h.b_k.sub_left sK, h.b_s.sub_left sK, kA,
    h.ni, h.no, h.nk, h.nsc, h.klB⟩

theorem init_pub {S : StreamingHash} {Wi : Nat} {t t' : State} (he : t.gpr .esp = t'.gpr .esp)
    (a0 : arg t 0 = arg t' 0) (a1 : arg t 1 = arg t' 1) (a2 : arg t 2 = arg t' 2) (a3 : arg t 3 = arg t' 3)
    (a4 : arg t 4 = arg t' 4) :
    (Spec.Hmac.initContract S Wi X86.abi 48).pub t t' := by
  sig_pub [Spec.Hmac.initContract, Spec.Hmac.initSig, X86.abi]
  simp only [argVal32, he, a0, a1, a2, a3, a4, and_self]

theorem init_post {S : StreamingHash} {Wi : Nat} {t t' : State} {inn out k : BitVec 32} {kl : Nat}
    (hkl : kl < 2 ^ 32) (a0 : arg t 0 = inn) (a1 : arg t 1 = out) (a2 : arg t 2 = k)
    (a3 : arg t 3 = BitVec.ofNat 32 kl) (h : (Spec.Hmac.initContract S Wi X86.abi 48).post t t') :
    S.Repr t'.mem (inn.setWidth 64) (xorPad (blockKey S.H (bytesAt t.mem (k.setWidth 64) kl)) ipad) ∧
      S.Repr t'.mem (out.setWidth 64) (xorPad (blockKey S.H (bytesAt t.mem (k.setWidth 64) kl)) opad) := by
  sig_post [Spec.Hmac.initContract, Spec.Hmac.initSig, X86.abi] at h
  simp only [argVal32, a0, a1, a2, a3, setWidth32_64, toNat_ofNat32 hkl] at h
  exact h

namespace HiArgs
variable {S : StreamingHash} {Wi : Nat} {s : State} {inn out k sc : BitVec 32} {kl : Nat}
  (h : HiArgs S Wi s inn out k sc kl)
include h

theorem fit : 4 * hi5.length + 4 ≤ (s.gpr .esp).toNat := by have := h.sp; simp only [List.length_cons, List.length_nil]; omega

omit h in
theorem nesp : Reg.esp ∉ hi5 := by decide

theorem a0 : arg (pushed hi5 s).callEntry 0 = inn := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.edi
theorem a1 : arg (pushed hi5 s).callEntry 1 = out := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.esi
theorem a2 : arg (pushed hi5 s).callEntry 2 = k := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.edx
theorem a3 : arg (pushed hi5 s).callEntry 3 = BitVec.ofNat 32 kl := by
  rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.ecx
theorem a4 : arg (pushed hi5 s).callEntry 4 = sc := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.ebp

theorem pre : (Spec.Hmac.initContract S Wi X86.abi 48).pre
    ((pushed hi5 s).callEntry.withRegions (HiArgs.rd k kl) (HiArgs.wr S Wi (s.gpr .esp) inn out sc)) :=
  h.pre_of (by rw [State.withRegions_gpr, callEntry_esp']; rfl) (by rw [arg_withRegions, h.a0])
    (by rw [arg_withRegions, h.a1]) (by rw [arg_withRegions, h.a2]) (by rw [arg_withRegions, h.a3])
    (by rw [arg_withRegions, h.a4]) (by rw [argAddr_withRegions, callEntry_argAddr0]; rfl) rfl rfl

theorem callPre : CallPre (Spec.Hmac.initContract S Wi X86.abi 48) hi5 (HiArgs.rd k kl)
    (HiArgs.wr S Wi (s.gpr .esp) inn out sc) s := by
  refine ⟨h.pre, ?_, ?_⟩
  · intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := h.cr a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', hq', hc'⟩)
    rotate_right
    · exact InRegions_append_cons.mpr (.inl (by simpa using hc))
    all_goals
      obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
  · intro a n ⟨q, hq, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    rotate_right
    · exact ⟨_, List.mem_cons_self, by simpa using hc⟩
    all_goals
      obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

end HiArgs

theorem hi_frame {S : StreamingHash} {Wi : Nat} {n : String} {c : Prog isa}
    (hv : Sound c (Spec.Hmac.initContract S Wi X86.abi 48)) (hsp : NoSp c) (hsu : stackUse c ≤ 48)
    {s : State} {inn out k sc : BitVec 32} {kl : Nat} (h : HiArgs S Wi s inn out k sc kl) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨inn.setWidth 64, S.stateBytes⟩, ⟨out.setWidth 64, S.stateBytes⟩,
        ⟨sc.setWidth 64, Wi * 8⟩] s' →
      S.Repr s'.mem (inn.setWidth 64) (xorPad (blockKey S.H (bytesAt s.mem (k.setWidth 64) kl)) ipad) →
      S.Repr s'.mem (out.setWidth 64) (xorPad (blockKey S.H (bytesAt s.mem (k.setWidth 64) kl)) opad) → Q s') :
    WP isa (.frame (.push hi5) (.call n c) (.pop .eax hi5.length)) s Q := by
  have e := h.sp
  refine WP.callWith hv.ok hsp (by simp) HiArgs.nesp (by simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  have f'' : Frame ([⟨inn.setWidth 64, S.stateBytes⟩, ⟨out.setWidth 64, S.stateBytes⟩, ⟨sc.setWidth 64, Wi * 8⟩] ++
      [below (s.gpr .esp) 76]) s.mem s'.mem := by
    refine Frame.sub f' fun q hq => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
    · exact ⟨_, by simp, args_sub e (n := 5) (by decide)⟩
    · exact ⟨_, by simp, below_sub (by simp only [List.length_cons, List.length_nil]; omega) e⟩
  have post' := init_post h.kl32 (t := (pushed hi5 s).callEntry.withRegions (HiArgs.rd k kl)
    (HiArgs.wr S Wi (s.gpr .esp) inn out sc)) (by rw [arg_withRegions, h.a0]) (by rw [arg_withRegions, h.a1])
    (by rw [arg_withRegions, h.a2]) (by rw [arg_withRegions, h.a3]) post
  have ek : bytesAt (pushed hi5 s).callEntry.mem (k.setWidth 64) kl = bytesAt s.mem (k.setWidth 64) kl :=
    entry_bytes HiArgs.nesp (by decide) e h.b_k (by have := h.kl32; omega)
  rw [State.withRegions_mem, ek, m₂] at post'
  exact hQ s' ⟨rd', wr', cs', f''⟩ post'.1 post'.2

theorem hi_rel {S : StreamingHash} {Wi : Nat} {n : String} {c : Prog isa}
    (hv : Sound c (Spec.Hmac.initContract S Wi X86.abi 48)) {P : State → State → Prop}
    {sp inn out k sc : BitVec 32} {kl : Nat}
    (h : ∀ s s', P s s' → HiArgs S Wi s inn out k sc kl ∧ HiArgs S Wi s' inn out k sc kl ∧
      s.gpr .esp = sp ∧ s'.gpr .esp = sp) :
    RelCT isa P (.frame (.push hi5) (.call n c) (.pop .eax hi5.length)) fun _ _ => True := by
  refine RelCT.callWith hv.ok hv.ct (HiArgs.rd k kl) (HiArgs.wr S Wi sp inn out sc) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c := a.callPre
  have c' := a'.callPre
  rw [e] at c; rw [e'] at c'
  refine ⟨c, c', e.trans e'.symm, init_pub ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e, e']
  all_goals simp only [arg_withRegions, a.a0, a'.a0, a.a1, a'.a1, a.a2, a'.a2, a.a3, a'.a3, a.a4, a'.a4]

/-- The representation of a streaming state depends only on its bytes. -/
def ReprOK (S : StreamingHash) : Prop :=
  ∀ (m m' : Mem) (p q : Addr) (msg : List Byte),
    (∀ i < S.stateBytes, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) → S.Repr m p msg → S.Repr m' q msg

/-- A state outside `stk` represents the same message on entry to a callee. -/
theorem entry_repr {S : StreamingHash} (hR : ReprOK S) (hS : S.stateBytes ≤ 2 ^ 64) {rs : List Reg} {s : State}
    (hrs : Reg.esp ∉ rs) (hn : rs.length ≤ 6) (h76 : 76 ≤ (s.gpr .esp).toNat) {p : Addr}
    (hd : (stk s).Disjoint ⟨p, S.stateBytes⟩) {msg : List Byte} (h : S.Repr s.mem p msg) :
    S.Repr (pushed rs s).callEntry.mem p msg :=
  hR _ _ _ _ _ (fun i hi => (entry_frame hrs hn h76).bytes (R := ⟨p, S.stateBytes⟩)
    (by simp only [List.mem_singleton]; rintro q rfl; exact hd.symm) hS hi) h

/-! ## HMAC's `finalize`, in a frame of its arguments -/

/-- The six words of `finalize`'s frame, last to first. -/
abbrev hf6 : List Reg := [.ebp, .edi, .ecx, .eax, .esi, .edx]

/-- What a framed call of HMAC's `finalize` needs of the state before its
push: the inner and outer states at `inn` and `ou` in `edx` and `esi`, the
count `hi ++ lo` in `ecx` and `eax`, `out` at `o` in `edi` and `8 Wf` bytes
of scratch space at `sc` in `ebp`, as for `init`. -/
structure HfArgs (S : StreamingHash) (Wf : Nat) (s : State) (inn ou lo hi o sc : BitVec 32) : Prop where
  edx : s.gpr .edx = inn
  esi : s.gpr .esi = ou
  eax : s.gpr .eax = lo
  ecx : s.gpr .ecx = hi
  edi : s.gpr .edi = o
  ebp : s.gpr .ebp = sc
  sp : 76 ≤ (s.gpr .esp).toNat
  cr : Covers [⟨ou.setWidth 64, S.stateBytes⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn.setWidth 64, S.stateBytes⟩, ⟨o.setWidth 64, S.digestBytes⟩, ⟨sc.setWidth 64, Wf * 8⟩] s.wr
  i_u : Region.Disjoint ⟨inn.setWidth 64, S.stateBytes⟩ ⟨ou.setWidth 64, S.stateBytes⟩
  i_o : Region.Disjoint ⟨inn.setWidth 64, S.stateBytes⟩ ⟨o.setWidth 64, S.digestBytes⟩
  i_s : Region.Disjoint ⟨inn.setWidth 64, S.stateBytes⟩ ⟨sc.setWidth 64, Wf * 8⟩
  u_o : Region.Disjoint ⟨ou.setWidth 64, S.stateBytes⟩ ⟨o.setWidth 64, S.digestBytes⟩
  u_s : Region.Disjoint ⟨ou.setWidth 64, S.stateBytes⟩ ⟨sc.setWidth 64, Wf * 8⟩
  o_s : Region.Disjoint ⟨o.setWidth 64, S.digestBytes⟩ ⟨sc.setWidth 64, Wf * 8⟩
  b_i : (stk s).Disjoint ⟨inn.setWidth 64, S.stateBytes⟩
  b_u : (stk s).Disjoint ⟨ou.setWidth 64, S.stateBytes⟩
  b_o : (stk s).Disjoint ⟨o.setWidth 64, S.digestBytes⟩
  b_s : (stk s).Disjoint ⟨sc.setWidth 64, Wf * 8⟩
  ni : inn.toNat + S.stateBytes ≤ 2 ^ 32
  nu : ou.toNat + S.stateBytes ≤ 2 ^ 32
  no : o.toNat + S.digestBytes ≤ 2 ^ 32
  nsc : sc.toNat + Wf * 8 ≤ 2 ^ 32

/-- The regions `finalize` is given. -/
abbrev HfArgs.rd (S : StreamingHash) (ou : BitVec 32) : List Region := [⟨ou.setWidth 64, S.stateBytes⟩]
abbrev HfArgs.wr (S : StreamingHash) (Wf : Nat) (sp inn o sc : BitVec 32) : List Region :=
  [⟨inn.setWidth 64, S.stateBytes⟩, ⟨o.setWidth 64, S.digestBytes⟩, ⟨sc.setWidth 64, Wf * 8⟩,
    ⟨(sp - BitVec.ofNat 32 24).setWidth 64, 24⟩]

theorem HfArgs.pre_of {S : StreamingHash} {Wf : Nat} {s : State} {inn ou lo hi o sc : BitVec 32}
    (h : HfArgs S Wf s inn ou lo hi o sc) {t : State} (hsp : t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 28)
    (a0 : arg t 0 = inn) (a1 : arg t 1 = ou) (a4 : arg t 4 = o) (a5 : arg t 5 = sc)
    (hA : argAddr t 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64)
    (hrd : t.rd = HfArgs.rd S ou) (hwr : t.wr = HfArgs.wr S Wf (s.gpr .esp) inn o sc) :
    (Spec.Hmac.finalizeContract S Wf X86.abi 48).pre t := by
  have e := h.sp
  sig_pre [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, X86.abi]
  simp only [argVal32, a0, a1, a4, a5, hA, hsp, hrd, hwr, toNat_setWidth64,
    show argBytes [32, 32, 64, 32, 32] = 24 from rfl]
  have sA := args_sub (E := s.gpr .esp) e (n := 6) (by decide)
  have sR := ret_sub (E := s.gpr .esp) e (n := 6) (by decide)
  have sK := cstk_sub (E := s.gpr .esp) e (n := 6) (by decide)
  have rA := ret_args (E := s.gpr .esp) e (n := 6) (by decide)
  have kA := cstk_args (E := s.gpr .esp) e (n := 6) (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at sA sR sK rA kA
  refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; omega, trivial, trivial,
    h.i_u, h.i_o, h.i_s, (h.b_i.sub_left sA).symm, h.u_o, h.u_s, (h.b_u.sub_left sA).symm, h.o_s,
    (h.b_o.sub_left sA).symm, (h.b_s.sub_left sA).symm,
    h.b_i.sub_left sR, h.b_u.sub_left sR, h.b_o.sub_left sR, h.b_s.sub_left sR, rA,
    h.b_i.sub_left sK, h.b_u.sub_left sK, h.b_o.sub_left sK, h.b_s.sub_left sK, kA,
    h.ni, h.nu, h.no, h.nsc⟩

theorem fin_pub {S : StreamingHash} {Wf : Nat} {t t' : State} (he : t.gpr .esp = t'.gpr .esp)
    (a0 : arg t 0 = arg t' 0) (a1 : arg t 1 = arg t' 1) (a2 : arg t 2 = arg t' 2) (a3 : arg t 3 = arg t' 3)
    (a4 : arg t 4 = arg t' 4) (a5 : arg t 5 = arg t' 5) :
    (Spec.Hmac.finalizeContract S Wf X86.abi 48).pub t t' := by
  sig_pub [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, X86.abi]
  simp only [argVal, Nat.reduceEqDiff, ↓reduceIte, he, a0, a1, a2, a3, a4, a5, and_self]

theorem fin_post {S : StreamingHash} {Wf : Nat} {t t' : State} {inn ou lo hi o : BitVec 32}
    (a0 : arg t 0 = inn) (a1 : arg t 1 = ou) (a2 : arg t 2 = lo) (a3 : arg t 3 = hi) (a4 : arg t 4 = o)
    (h : (Spec.Hmac.finalizeContract S Wf X86.abi 48).post t t') :
    ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
      S.Repr t.mem (inn.setWidth 64) (xorPad k0 ipad ++ text) →
      hi ++ lo = BitVec.ofNat 64 (S.H.blockSize + text.length) →
      S.Repr t.mem (ou.setWidth 64) (xorPad k0 opad) →
      bytesAt t'.mem (o.setWidth 64) S.digestBytes = hmacBlockKey S.H k0 text := by
  sig_post [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, X86.abi] at h
  simp only [argVal, a0, a1, a2, a3, a4, ite_true] at h
  exact h

namespace HfArgs
variable {S : StreamingHash} {Wf : Nat} {s : State} {inn ou lo hi o sc : BitVec 32}
  (h : HfArgs S Wf s inn ou lo hi o sc)
include h

theorem fit : 4 * hf6.length + 4 ≤ (s.gpr .esp).toNat := by have := h.sp; simp only [List.length_cons, List.length_nil]; omega

omit h in
theorem nesp : Reg.esp ∉ hf6 := by decide

theorem a0 : arg (pushed hf6 s).callEntry 0 = inn := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.edx
theorem a1 : arg (pushed hf6 s).callEntry 1 = ou := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.esi
theorem a2 : arg (pushed hf6 s).callEntry 2 = lo := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.eax
theorem a3 : arg (pushed hf6 s).callEntry 3 = hi := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.ecx
theorem a4 : arg (pushed hf6 s).callEntry 4 = o := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.edi
theorem a5 : arg (pushed hf6 s).callEntry 5 = sc := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.ebp

theorem pre : (Spec.Hmac.finalizeContract S Wf X86.abi 48).pre
    ((pushed hf6 s).callEntry.withRegions (HfArgs.rd S ou) (HfArgs.wr S Wf (s.gpr .esp) inn o sc)) :=
  h.pre_of (by rw [State.withRegions_gpr, callEntry_esp']; rfl) (by rw [arg_withRegions, h.a0])
    (by rw [arg_withRegions, h.a1]) (by rw [arg_withRegions, h.a4]) (by rw [arg_withRegions, h.a5])
    (by rw [argAddr_withRegions, callEntry_argAddr0]; rfl) rfl rfl

theorem callPre : CallPre (Spec.Hmac.finalizeContract S Wf X86.abi 48) hf6 (HfArgs.rd S ou)
    (HfArgs.wr S Wf (s.gpr .esp) inn o sc) s := by
  refine ⟨h.pre, ?_, ?_⟩
  · intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := h.cr a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', hq', hc'⟩)
    rotate_right
    · exact InRegions_append_cons.mpr (.inl (by simpa using hc))
    all_goals
      obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
  · intro a n ⟨q, hq, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    rotate_right
    · exact ⟨_, List.mem_cons_self, by simpa using hc⟩
    all_goals
      obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

end HfArgs

theorem hf_frame {S : StreamingHash} {Wf : Nat} {n : String} {c : Prog isa} (hR : ReprOK S)
    (hSn : S.stateBytes ≤ 2 ^ 64)
    (hv : Sound c (Spec.Hmac.finalizeContract S Wf X86.abi 48)) (hsp : NoSp c) (hsu : stackUse c ≤ 48)
    {s : State} {inn ou lo hi o sc : BitVec 32} (h : HfArgs S Wf s inn ou lo hi o sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨inn.setWidth 64, S.stateBytes⟩, ⟨o.setWidth 64, S.digestBytes⟩,
        ⟨sc.setWidth 64, Wf * 8⟩] s' →
      (∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
        S.Repr s.mem (inn.setWidth 64) (xorPad k0 ipad ++ text) →
        hi ++ lo = BitVec.ofNat 64 (S.H.blockSize + text.length) →
        S.Repr s.mem (ou.setWidth 64) (xorPad k0 opad) →
        bytesAt s'.mem (o.setWidth 64) S.digestBytes = hmacBlockKey S.H k0 text) → Q s') :
    WP isa (.frame (.push hf6) (.call n c) (.pop .eax hf6.length)) s Q := by
  have e := h.sp
  refine WP.callWith hv.ok hsp (by simp) HfArgs.nesp (by simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  have f'' : Frame ([⟨inn.setWidth 64, S.stateBytes⟩, ⟨o.setWidth 64, S.digestBytes⟩, ⟨sc.setWidth 64, Wf * 8⟩] ++
      [below (s.gpr .esp) 76]) s.mem s'.mem := by
    refine Frame.sub f' fun q hq => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
    · exact ⟨_, by simp, args_sub e (n := 6) (by decide)⟩
    · exact ⟨_, by simp, below_sub (by simp only [List.length_cons, List.length_nil]; omega) e⟩
  have post' := fin_post (t := (pushed hf6 s).callEntry.withRegions (HfArgs.rd S ou)
    (HfArgs.wr S Wf (s.gpr .esp) inn o sc)) (by rw [arg_withRegions, h.a0]) (by rw [arg_withRegions, h.a1])
    (by rw [arg_withRegions, h.a2]) (by rw [arg_withRegions, h.a3]) (by rw [arg_withRegions, h.a4]) post
  rw [State.withRegions_mem, m₂] at post'
  refine hQ s' ⟨rd', wr', cs', f''⟩ fun k0 text hk hl hi' hc ho => post' k0 text hk hl ?_ hc ?_
  · exact entry_repr hR hSn HfArgs.nesp (by decide) e h.b_i hi'
  · exact entry_repr hR hSn HfArgs.nesp (by decide) e h.b_u ho

theorem hf_rel {S : StreamingHash} {Wf : Nat} {n : String} {c : Prog isa}
    (hv : Sound c (Spec.Hmac.finalizeContract S Wf X86.abi 48)) {P : State → State → Prop}
    {sp inn ou lo hi o sc : BitVec 32}
    (h : ∀ s s', P s s' → HfArgs S Wf s inn ou lo hi o sc ∧ HfArgs S Wf s' inn ou lo hi o sc ∧
      s.gpr .esp = sp ∧ s'.gpr .esp = sp) :
    RelCT isa P (.frame (.push hf6) (.call n c) (.pop .eax hf6.length)) fun _ _ => True := by
  refine RelCT.callWith hv.ok hv.ct (HfArgs.rd S ou) (HfArgs.wr S Wf sp inn o sc) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c := a.callPre
  have c' := a'.callPre
  rw [e] at c; rw [e'] at c'
  refine ⟨c, c', e.trans e'.symm, fin_pub ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e, e']
  all_goals simp only [arg_withRegions, a.a0, a'.a0, a.a1, a'.a1, a.a2, a'.a2, a.a3, a'.a3, a.a4, a'.a4, a.a5, a'.a5]

/-! ## `iterate`, in a frame of its arguments -/

/-- The five words of `iterate`'s frame, last to first. -/
abbrev it5 : List Reg := [.ebp, .edx, .ecx, .eax, .esi]

/-- What a framed call of `iterate` needs of the state before its push: the
key's states at `key` in `esi`, `U` at `u` in `eax`, `n` in `ecx`, `T` at
`tt` in `edx` and `8 Wt` bytes of scratch space at `sc` in `ebp`, as for
`init`. -/
structure ItArgs (S : StreamingHash) (Wt : Nat) (s : State) (key u n tt sc : BitVec 32) : Prop where
  esi : s.gpr .esi = key
  eax : s.gpr .eax = u
  ecx : s.gpr .ecx = n
  edx : s.gpr .edx = tt
  ebp : s.gpr .ebp = sc
  sp : 76 ≤ (s.gpr .esp).toNat
  cr : Covers [⟨key.setWidth 64, 2 * S.stateBytes⟩, ⟨u.setWidth 64, S.digestBytes⟩] (s.rd ++ s.wr)
  cw : Covers [⟨tt.setWidth 64, S.digestBytes⟩, ⟨sc.setWidth 64, Wt * 8⟩] s.wr
  k_t : Region.Disjoint ⟨key.setWidth 64, 2 * S.stateBytes⟩ ⟨tt.setWidth 64, S.digestBytes⟩
  k_s : Region.Disjoint ⟨key.setWidth 64, 2 * S.stateBytes⟩ ⟨sc.setWidth 64, Wt * 8⟩
  u_t : Region.Disjoint ⟨u.setWidth 64, S.digestBytes⟩ ⟨tt.setWidth 64, S.digestBytes⟩
  u_s : Region.Disjoint ⟨u.setWidth 64, S.digestBytes⟩ ⟨sc.setWidth 64, Wt * 8⟩
  t_s : Region.Disjoint ⟨tt.setWidth 64, S.digestBytes⟩ ⟨sc.setWidth 64, Wt * 8⟩
  b_k : (stk s).Disjoint ⟨key.setWidth 64, 2 * S.stateBytes⟩
  b_u : (stk s).Disjoint ⟨u.setWidth 64, S.digestBytes⟩
  b_t : (stk s).Disjoint ⟨tt.setWidth 64, S.digestBytes⟩
  b_s : (stk s).Disjoint ⟨sc.setWidth 64, Wt * 8⟩
  nk : key.toNat + 2 * S.stateBytes ≤ 2 ^ 32
  nu : u.toNat + S.digestBytes ≤ 2 ^ 32
  nt : tt.toNat + S.digestBytes ≤ 2 ^ 32
  nsc : sc.toNat + Wt * 8 ≤ 2 ^ 32

/-- The regions `iterate` is given. -/
abbrev ItArgs.rd (S : StreamingHash) (key u : BitVec 32) : List Region :=
  [⟨key.setWidth 64, 2 * S.stateBytes⟩, ⟨u.setWidth 64, S.digestBytes⟩]
abbrev ItArgs.wr (S : StreamingHash) (Wt : Nat) (sp tt sc : BitVec 32) : List Region :=
  [⟨tt.setWidth 64, S.digestBytes⟩, ⟨sc.setWidth 64, Wt * 8⟩, ⟨(sp - BitVec.ofNat 32 20).setWidth 64, 20⟩]

theorem ItArgs.pre_of {S : StreamingHash} {Wt : Nat} {s : State} {key u n tt sc : BitVec 32}
    (h : ItArgs S Wt s key u n tt sc) {t : State} (hsp : t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24)
    (a0 : arg t 0 = key) (a1 : arg t 1 = u) (a3 : arg t 3 = tt) (a4 : arg t 4 = sc)
    (hA : argAddr t 0 = (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64)
    (hrd : t.rd = ItArgs.rd S key u) (hwr : t.wr = ItArgs.wr S Wt (s.gpr .esp) tt sc) :
    (Spec.Pbkdf2.iterateContract S Wt X86.abi 48).pre t := by
  have e := h.sp
  sig_pre [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, X86.abi]
  simp only [argVal32, a0, a1, a3, a4, hA, hsp, hrd, hwr, toNat_setWidth64,
    show argBytes [32, 32, 32, 32, 32] = 20 from rfl]
  have sA := args_sub (E := s.gpr .esp) e (n := 5) (by decide)
  have sR := ret_sub (E := s.gpr .esp) e (n := 5) (by decide)
  have sK := cstk_sub (E := s.gpr .esp) e (n := 5) (by decide)
  have rA := ret_args (E := s.gpr .esp) e (n := 5) (by decide)
  have kA := cstk_args (E := s.gpr .esp) e (n := 5) (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at sA sR sK rA kA
  refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; omega, trivial, trivial,
    h.k_t, h.k_s, (h.b_k.sub_left sA).symm, h.u_t, h.u_s, (h.b_u.sub_left sA).symm, h.t_s,
    (h.b_t.sub_left sA).symm, (h.b_s.sub_left sA).symm,
    h.b_k.sub_left sR, h.b_u.sub_left sR, h.b_t.sub_left sR, h.b_s.sub_left sR, rA,
    h.b_k.sub_left sK, h.b_u.sub_left sK, h.b_t.sub_left sK, h.b_s.sub_left sK, kA,
    h.nk, h.nu, h.nt, h.nsc⟩

theorem it_pub {S : StreamingHash} {Wt : Nat} {t t' : State} (he : t.gpr .esp = t'.gpr .esp)
    (a0 : arg t 0 = arg t' 0) (a1 : arg t 1 = arg t' 1) (a2 : arg t 2 = arg t' 2) (a3 : arg t 3 = arg t' 3)
    (a4 : arg t 4 = arg t' 4) :
    (Spec.Pbkdf2.iterateContract S Wt X86.abi 48).pub t t' := by
  sig_pub [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, X86.abi]
  simp only [argVal32, he, a0, a1, a2, a3, a4, and_self]

theorem it_post {S : StreamingHash} {Wt : Nat} {t t' : State} {key u n tt : BitVec 32}
    (a0 : arg t 0 = key) (a1 : arg t 1 = u) (a2 : arg t 2 = n) (a3 : arg t 3 = tt)
    (h : (Spec.Pbkdf2.iterateContract S Wt X86.abi 48).post t t') :
    ∀ k0, k0.length = S.H.blockSize → S.Repr t.mem (key.setWidth 64) (xorPad k0 ipad) →
      S.Repr t.mem (key.setWidth 64 + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
      bytesAt t'.mem (tt.setWidth 64) S.digestBytes =
        Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) n.toNat (bytesAt t.mem (u.setWidth 64) S.digestBytes)
          (bytesAt t.mem (tt.setWidth 64) S.digestBytes) := by
  sig_post [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, X86.abi] at h
  simp only [argVal32, a0, a1, a2, a3, setWidth32_64] at h
  exact h

namespace ItArgs
variable {S : StreamingHash} {Wt : Nat} {s : State} {key u n tt sc : BitVec 32}
  (h : ItArgs S Wt s key u n tt sc)
include h

theorem fit : 4 * it5.length + 4 ≤ (s.gpr .esp).toNat := by have := h.sp; simp only [List.length_cons, List.length_nil]; omega

omit h in
theorem nesp : Reg.esp ∉ it5 := by decide

theorem a0 : arg (pushed it5 s).callEntry 0 = key := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.esi
theorem a1 : arg (pushed it5 s).callEntry 1 = u := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.eax
theorem a2 : arg (pushed it5 s).callEntry 2 = n := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.ecx
theorem a3 : arg (pushed it5 s).callEntry 3 = tt := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.edx
theorem a4 : arg (pushed it5 s).callEntry 4 = sc := by rw [callEntry_arg h.fit nesp (by simp)]; simpa using h.ebp

theorem pre : (Spec.Pbkdf2.iterateContract S Wt X86.abi 48).pre
    ((pushed it5 s).callEntry.withRegions (ItArgs.rd S key u) (ItArgs.wr S Wt (s.gpr .esp) tt sc)) :=
  h.pre_of (by rw [State.withRegions_gpr, callEntry_esp']; rfl) (by rw [arg_withRegions, h.a0])
    (by rw [arg_withRegions, h.a1]) (by rw [arg_withRegions, h.a3]) (by rw [arg_withRegions, h.a4])
    (by rw [argAddr_withRegions, callEntry_argAddr0]; rfl) rfl rfl

theorem callPre : CallPre (Spec.Pbkdf2.iterateContract S Wt X86.abi 48) it5 (ItArgs.rd S key u)
    (ItArgs.wr S Wt (s.gpr .esp) tt sc) s := by
  refine ⟨h.pre, ?_, ?_⟩
  · intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := h.cr a n ⟨_, by simp, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', hq', hc'⟩)
    · obtain ⟨q', hq', hc'⟩ := h.cr a n ⟨_, by simp, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', hq', hc'⟩)
    rotate_right
    · exact InRegions_append_cons.mpr (.inl (by simpa using hc))
    all_goals
      obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
  · intro a n ⟨q, hq, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    rotate_right
    · exact ⟨_, List.mem_cons_self, by simpa using hc⟩
    all_goals
      obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

end ItArgs

theorem it_frame {S : StreamingHash} {Wt : Nat} {nm : String} {c : Prog isa} (hR : ReprOK S)
    (hSn : 2 * S.stateBytes ≤ 2 ^ 32) (hDn : S.digestBytes ≤ 2 ^ 32)
    (hv : Sound c (Spec.Pbkdf2.iterateContract S Wt X86.abi 48)) (hsp : NoSp c) (hsu : stackUse c ≤ 48)
    {s : State} {key u n tt sc : BitVec 32} (h : ItArgs S Wt s key u n tt sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨tt.setWidth 64, S.digestBytes⟩, ⟨sc.setWidth 64, Wt * 8⟩] s' →
      (∀ k0, k0.length = S.H.blockSize → S.Repr s.mem (key.setWidth 64) (xorPad k0 ipad) →
        S.Repr s.mem (key.setWidth 64 + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
        bytesAt s'.mem (tt.setWidth 64) S.digestBytes =
          Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) n.toNat (bytesAt s.mem (u.setWidth 64) S.digestBytes)
            (bytesAt s.mem (tt.setWidth 64) S.digestBytes)) → Q s') :
    WP isa (.frame (.push it5) (.call nm c) (.pop .eax it5.length)) s Q := by
  have e := h.sp
  refine WP.callWith hv.ok hsp (by simp) ItArgs.nesp (by simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  have f'' : Frame ([⟨tt.setWidth 64, S.digestBytes⟩, ⟨sc.setWidth 64, Wt * 8⟩] ++ [below (s.gpr .esp) 76])
      s.mem s'.mem := by
    refine Frame.sub f' fun q hq => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, by simp, args_sub e (n := 5) (by decide)⟩
    · exact ⟨_, by simp, below_sub (by simp only [List.length_cons, List.length_nil]; omega) e⟩
  have post' := it_post (t := (pushed it5 s).callEntry.withRegions (ItArgs.rd S key u)
    (ItArgs.wr S Wt (s.gpr .esp) tt sc)) (by rw [arg_withRegions, h.a0]) (by rw [arg_withRegions, h.a1])
    (by rw [arg_withRegions, h.a2]) (by rw [arg_withRegions, h.a3]) post
  rw [State.withRegions_mem, m₂, entry_bytes ItArgs.nesp (by decide) e h.b_u (by omega),
    entry_bytes ItArgs.nesp (by decide) e h.b_t (by omega)] at post'
  refine hQ s' ⟨rd', wr', cs', f''⟩ fun k0 hk hi ho => post' k0 hk ?_ ?_
  · exact entry_repr hR (by omega) ItArgs.nesp (by decide) e
      (h.b_k.sub_right (Region.sub_prefix (by omega))) hi
  · exact entry_repr hR (by omega) ItArgs.nesp (by decide) e
      (h.b_k.sub_right (Offset.sub_base _ (by omega))) ho

theorem it_rel {S : StreamingHash} {Wt : Nat} {nm : String} {c : Prog isa}
    (hv : Sound c (Spec.Pbkdf2.iterateContract S Wt X86.abi 48)) {P : State → State → Prop}
    {sp key u n tt sc : BitVec 32}
    (h : ∀ s s', P s s' → ItArgs S Wt s key u n tt sc ∧ ItArgs S Wt s' key u n tt sc ∧
      s.gpr .esp = sp ∧ s'.gpr .esp = sp) :
    RelCT isa P (.frame (.push it5) (.call nm c) (.pop .eax it5.length)) fun _ _ => True := by
  refine RelCT.callWith hv.ok hv.ct (ItArgs.rd S key u) (ItArgs.wr S Wt sp tt sc) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c := a.callPre
  have c' := a'.callPre
  rw [e] at c; rw [e'] at c'
  refine ⟨c, c', e.trans e'.symm, it_pub ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e, e']
  all_goals simp only [arg_withRegions, a.a0, a'.a0, a.a1, a'.a1, a.a2, a'.a2, a.a3, a'.a3, a.a4, a'.a4]

end VG.Proof.Pbkdf2.Whole.X86
