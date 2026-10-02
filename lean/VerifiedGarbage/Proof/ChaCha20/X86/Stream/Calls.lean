import VerifiedGarbage.Proof.ChaCha20.X86.Stream.Bytes
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# Streaming ChaCha20 on x86 (32-bit): the entry state and the calls

Untrusted: everything here is checked by Lean. The contract of `apply`, what
its precondition gives, and the calls of `vg_chacha20_block` and
`vg_chacha20_xor`, each in a frame of its arguments (`WP.callWith`), from
their proofs of correctness, as ChaCha20-Poly1305 makes them: what they need
of the state they are called from (`CallPre`), and what holds when they
return.
-/

namespace VG.Proof.ChaCha20

open VG.X86
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt)

/-- x86 (32-bit) contract for `vg_chacha20_apply(state, data, len) -> eax`,
whose arguments are on the stack (cdecl), with 32 bytes of stack below the
return address (the frames, return addresses and stack of the calls). -/
def applyX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 768⟩
    let data : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩
    s.rd = [] ∧ s.wr = [state, data, args] ∧ state.Disjoint data ∧
    args.Disjoint state ∧ args.Disjoint data ∧ ret.Disjoint state ∧ ret.Disjoint data ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧
    (arg s 0).toNat + 768 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
    32 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' :=
    keyAt s'.mem ((arg s 0).setWidth 64) = keyAt s.mem ((arg s 0).setWidth 64) ∧
      if (arg s 2).toNat ≤ leftAt s.mem ((arg s 0).setWidth 64) then
        s'.gpr .eax = 1 ∧
          bytesAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
            List.zipWith (· ^^^ ·) (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
              ((restAt s.mem ((arg s 0).setWidth 64)).take (arg s 2).toNat) ∧
          restAt s'.mem ((arg s 0).setWidth 64) = (restAt s.mem ((arg s 0).setWidth 64)).drop (arg s 2).toNat
      else
        s'.gpr .eax = 0 ∧
          bytesAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
            bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat ∧
          restAt s'.mem ((arg s 0).setWidth 64) = restAt s.mem ((arg s 0).setWidth 64)
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧
      [leftAt s₁.mem ((arg s₁ 0).setWidth 64)] = [leftAt s₂.mem ((arg s₂ 0).setWidth 64)]

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86.Stream

open VG VG.X86 VG.Impl.ChaCha20.X86.Stream
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off)
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt keystream serialize block)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev E : BitVec 32 := s₀.gpr .esp
abbrev DP : BitVec 32 := arg s₀ 1
abbrev LN : BitVec 32 := arg s₀ 2
abbrev L : Nat := (LN s₀).toNat
abbrev dp : Addr := (DP s₀).setWidth 64
/-- The number of bytes of keystream left, and those in the buffered block. -/
abbrev N : Nat := leftAt s₀.mem (st s₀)
abbrev O : Nat := N s₀ % 64
/-- The bytes from the buffered block, the whole blocks and the bytes of the
next block that `apply` uses. -/
abbrev H : Nat := headLen s₀.mem (st s₀) (L s₀)
abbrev NB : Nat := blocksOf s₀.mem (st s₀) (L s₀)
abbrev T : Nat := tailLen s₀.mem (st s₀) (L s₀)
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev stR : Region := ⟨st s₀, 768⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 12⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 32
/-- The keystream byte XORed into byte `k` of the data. -/
abbrev KS (k : Nat) : Byte :=
  if k < H s₀ then s₀.mem (st s₀ + BitVec.ofNat 64 (128 - O s₀ + k))
  else (serialize (block (ctr (S0 s₀) ((k - H s₀) / 64)))).getD ((k - H s₀) % 64) 0
/-- The data with its first `j` bytes XORed. -/
abbrev Done (j : Nat) (m : Mem) : Prop :=
  ∀ k < L s₀, m (dp s₀ + BitVec.ofNat 64 k) = if k < j then D0 s₀ k ^^^ KS s₀ k else D0 s₀ k
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 32 := (LN s₀).isLt
theorem N_lt (s₀ : State) : N s₀ < 2 ^ 64 := (s₀.mem.readW (st s₀ + 128) 64).isLt
theorem H_le (s₀ : State) : H s₀ ≤ L s₀ := Nat.min_le_right _ _
theorem H_le_O (s₀ : State) : H s₀ ≤ O s₀ := Nat.min_le_left _ _
theorem O_lt (s₀ : State) : O s₀ < 64 := Nat.mod_lt _ (by decide)
theorem T_eq (s₀ : State) : T s₀ = L s₀ - H s₀ - 64 * NB s₀ := by simp only [T, NB, tailLen, blocksOf, H]; omega
theorem HNB_le (s₀ : State) : H s₀ + 64 * NB s₀ ≤ L s₀ := by
  have := H_le s₀; simp only [NB, blocksOf, H] at *; omega

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀, aR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  a_st : (aR s₀).Disjoint (stR s₀)
  a_d : (aR s₀).Disjoint (dR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  st_fit : (ST s₀).toNat + 768 ≤ 2 ^ 32
  d_fit : (DP s₀).toNat + L s₀ ≤ 2 ^ 32
  sp_lo : 32 ≤ (E s₀).toNat
  sp_hi : (E s₀).toNat + 16 ≤ 2 ^ 32

theorem APre.of (s₀ : State) (h : Proof.ChaCha20.applyX86.pre s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have e : (s₀.gpr .esp).setWidth 64 - 32 = (E s₀ - BitVec.ofNat 32 32).setWidth 64 :=
    (VG.X86.Taint.sub_setWidth h12).symm
  rw [e] at h8 h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

namespace APre
variable {s₀ : State} (hp : APre s₀)
include hp

theorem eaS {d : Nat} (hd : d < 768) : (ST s₀ + BitVec.ofNat 32 d).setWidth 64 = st s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fit; omega)

theorem sNat {d : Nat} (hd : d < 768) : (ST s₀ + BitVec.ofNat 32 d).toNat = (ST s₀).toNat + d := by
  have := hp.st_fit
  rw [BitVec.toNat_add, Proof.ChaCha20.X86.Xor.toNat_ofNat_lt32 (by omega), Nat.mod_eq_of_lt (by omega)]

theorem eaD {d : Nat} (hd : d < L s₀) : (DP s₀ + BitVec.ofNat 32 d).setWidth 64 = dp s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.d_fit; omega)

theorem dNat {d : Nat} (hd : d < L s₀) : (DP s₀ + BitVec.ofNat 32 d).toNat = (DP s₀).toNat + d := by
  have := hp.d_fit
  have := L_lt s₀
  rw [BitVec.toNat_add, Proof.ChaCha20.X86.Xor.toNat_ofNat_lt32 (by omega), Nat.mod_eq_of_lt (by omega)]

theorem w_st {d n : Nat} (h : d + n ≤ 768) : InRegions s₀.wr (st s₀ + BitVec.ofNat 64 d) n :=
  ⟨stR s₀, by rw [hp.wr]; exact List.mem_cons_self .., contains_off h (by omega)⟩

theorem r_st {d n : Nat} (h : d + n ≤ 768) : InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.rd, List.nil_append]; exact hp.w_st h

theorem in_arg {i : Nat} (hi : i < 3) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨aR s₀, by rw [hp.rd, hp.wr]; simp, arg_in s₀ (n := 3) (by have := hp.sp_hi; omega) hi⟩

theorem E64 {n : Nat} (hn : n ≤ 32) :
    (E s₀ - BitVec.ofNat 32 n).setWidth 64 = (E s₀).setWidth 64 - BitVec.ofNat 64 n :=
  VG.X86.Taint.sub_setWidth (by have := hp.sp_lo; omega)

/-- Part of the stack below the return address. -/
theorem stk_part {a n : Nat} (h : n ≤ a) (ha : a ≤ 32) :
    Region.Sub ⟨(E s₀ - BitVec.ofNat 32 a).setWidth 64, n⟩ (stkR s₀) :=
  fun x hx => below_sub ha hp.sp_lo x (Region.sub_prefix h x hx)

end APre

theorem d_ne_st {s₀ : State} (hp : APre s₀) {j k : Nat} (hj : j < L s₀) (hk : k < 768) :
    dp s₀ + BitVec.ofNat 64 j ≠ st s₀ + BitVec.ofNat 64 k := by
  intro he
  have c₁ : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by have := L_lt s₀; omega)
  have c₂ : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  rw [he] at c₁
  exact hp.st_d _ c₂ c₁

theorem not_in_prefix (p : Addr) {k c : Nat} (hk : c ≤ k) (hk' : k < 2 ^ 64) :
    ¬ (⟨p, c⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p hk']
  omega

theorem prefix_sub (p : Addr) {c n : Nat} (h : c ≤ n) : Region.Sub ⟨p, c⟩ ⟨p, n⟩ := Region.sub_prefix h

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-! ## The state a call is made from -/

structure At (s₀ s : State) : Prop where
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {s₀ s : State} (hp : APre s₀) (h : At s₀ s) {rs : List Reg} (hk : rs.length ≤ 4)
include hp h hk

theorem At.fit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := by
  rw [h.esp]; have := hp.sp_lo; omega

omit hp hk in
theorem At.argAddr0 :
    argAddr (pushed rs s).callEntry 0 = (E s₀ - BitVec.ofNat 32 (4 * rs.length)).setWidth 64 := by
  rw [callEntry_argAddr0, h.esp]

omit hp hk in
theorem At.esp64 :
    ((pushed rs s).callEntry.gpr .esp).setWidth 64 =
      (E s₀ - BitVec.ofNat 32 (4 * rs.length + 4)).setWidth 64 := by
  rw [callEntry_esp', h.esp]

theorem At.espNat : ((pushed rs s).callEntry.gpr .esp).toNat = (E s₀).toNat - (4 * rs.length + 4) := by
  rw [callEntry_espNat (h.fit hp hk), h.esp]

/-- The call's frame and return address are on the stack below `esp`. -/
theorem At.entry_frame (hrs : Reg.esp ∉ rs) : Frame [stkR s₀] s.mem (pushed rs s).callEntry.mem :=
  (callEntry_frame (h.fit hp hk) hrs).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by rw [h.esp]; exact below_sub (by omega) hp.sp_lo⟩

end

/-- A region at offset `o` within one of `rs'`. -/
theorem within {r : Region} {rs' : List Region} (r' : Region) (hr' : r' ∈ rs') (o : Nat)
    (hb : r.base = r'.base + BitVec.ofNat 64 o) (hl : o + r.len ≤ r'.len) :
    ∃ r' ∈ rs', ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len :=
  ⟨r', hr', o, hb, hl⟩

theorem block_nosp : NoSp Impl.ChaCha20.X86.block := NoSp.of_all (by lit_decide)
theorem xor_nosp : NoSp Impl.ChaCha20.X86.Xor.xor := NoSp.of_all (by lit_decide)
theorem block_stack : stackUse Impl.ChaCha20.X86.block = 0 := by lit_decide
theorem xor_stack : stackUse Impl.ChaCha20.X86.Xor.xor = 12 := by lit_decide

/-! ## `vg_chacha20_block` -/

/-- The permissions it is called with. -/
abbrev rdBlk (s₀ : State) : List Region := [⟨st s₀, 64⟩, below (E s₀) 8]
abbrev wrBlk (s₀ : State) : List Region := [⟨st s₀ + BitVec.ofNat 64 64, 256⟩]

theorem block_pre {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (hebx : s.gpr .ebx = ST s₀)
    (heax : s.gpr .eax = ST s₀ + BitVec.ofNat 32 64) :
    CallPre Proof.ChaCha20.blockX86 [.eax, .ebx] (rdBlk s₀) (wrBlk s₀) s := by
  have hk : [Reg.eax, .ebx].length ≤ 4 := by decide
  have fit := h.fit hp hk
  have a0 : arg (pushed [.eax, .ebx] s).callEntry 0 = ST s₀ := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hebx
  have a1 : arg (pushed [.eax, .ebx] s).callEntry 1 = ST s₀ + BitVec.ofNat 32 64 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact heax
  have e := hp.sp_lo
  have e₂ := hp.sp_hi
  have e' := hp.st_fit
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.ChaCha20.blockX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.eaS (d := 64) (by decide), hp.sNat (d := 64) (by decide),
      List.length_cons, List.length_nil]
    refine ⟨trivial, trivial, Offset.disjoint_base _ (by omega) (by omega), ?_, ?_, by omega, by omega, by omega⟩
    · exact (hp.stk_st.sub_left (hp.stk_part (by decide) (by decide))).sub_right (Offset.sub_base _ (by omega))
    · exact (hp.stk_st.sub_left (hp.stk_part (by decide) (by decide))).sub_right (Offset.sub_base _ (by omega))
  · rw [h.esp, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact within (stR s₀) (by simp) 0 (by simp) (by show 0 + 64 ≤ 768; omega)
    · exact within (below (E s₀) 8) (by simp) 0 (by simp) (by simp)
    · exact within (stR s₀) (by simp) 64 rfl (by show 64 + 256 ≤ 768; omega)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact within (stR s₀) (by simp) 64 rfl (by show 64 + 256 ≤ 768; omega)

/-- A call returns in a state from which calls can be made, with the
callee-saved registers. -/
theorem At.ret {s₀ s s' : State} (h : At s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) : At s₀ s' :=
  ⟨by rw [cs .esp (by simp [calleeSaved]), h.esp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem block_call {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (hebx : s.gpr .ebx = ST s₀)
    (heax : s.gpr .eax = ST s₀ + BitVec.ofNat 32 64) {Q : State → Prop}
    (hQ : ∀ s', At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st s₀ + BitVec.ofNat 64 64, 256⟩, stkR s₀] s.mem s'.mem →
      stateAt s'.mem (st s₀ + BitVec.ofNat 64 64) = block (stateAt s.mem (st s₀)) → Q s') :
    WP isa (callBlock) s Q := by
  have hk : [Reg.eax, .ebx].length ≤ 4 := by decide
  have fit := h.fit hp hk
  have e := hp.sp_lo
  refine WP.callWith Proof.ChaCha20.X86.block_correct block_nosp (by simp) (by decide)
    (by rw [block_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (block_pre hp h hebx heax) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [block_stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) ?_
  · simp only [wrBlk, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, below_sub (by omega) hp.sp_lo⟩
  · have a0 : arg (pushed [.eax, .ebx] s).callEntry 0 = ST s₀ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hebx
    have a1 : arg (pushed [.eax, .ebx] s).callEntry 1 = ST s₀ + BitVec.ofNat 32 64 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact heax
    simp only [Proof.ChaCha20.blockX86, arg_withRegions, State.withRegions_mem, a0, a1,
      hp.eaS (d := 64) (by decide), m₂] at post
    rw [post, VG.Proof.ChaCha20.X86.Xor.stateAt_frame (h.entry_frame hp hk (by decide)) (by
      simp only [List.mem_singleton, forall_eq]
      exact (hp.stk_st.sub_right (prefix_sub _ (by decide))).symm)]

/-! ## `vg_chacha20_xor` -/

/-- The regions of the call of `vg_chacha20_xor`: the copy of the state,
the data, the working space and its frame. -/
abbrev cpR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 192, 64⟩
abbrev blR (s₀ : State) : Region := ⟨dp s₀ + BitVec.ofNat 64 (H s₀), 64 * NB s₀⟩
abbrev wkR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 256, 320⟩
abbrev wrXor (s₀ : State) : List Region := [cpR s₀, blR s₀, wkR s₀, below (E s₀) 16]

theorem cpR_sub (s₀ : State) : Region.Sub (cpR s₀) (stR s₀) := Offset.sub_base _ (by omega)
theorem wkR_sub (s₀ : State) : Region.Sub (wkR s₀) (stR s₀) := Offset.sub_base _ (by omega)
theorem blR_sub (s₀ : State) : Region.Sub (blR s₀) (dR s₀) := Offset.sub_base _ (HNB_le s₀)

theorem xor_pre {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (hnb : 0 < NB s₀)
    (hedx : s.gpr .edx = ST s₀ + BitVec.ofNat 32 192) (hesi : s.gpr .esi = DP s₀ + BitVec.ofNat 32 (H s₀))
    (hecx : s.gpr .ecx = BitVec.ofNat 32 (64 * NB s₀)) (heax : s.gpr .eax = ST s₀ + BitVec.ofNat 32 256) :
    CallPre Proof.ChaCha20.xorX86 [.eax, .ecx, .esi, .edx] [] (wrXor s₀) s := by
  have hk : [Reg.eax, .ecx, .esi, .edx].length ≤ 4 := by decide
  have fit := h.fit hp hk
  have hHNB := HNB_le s₀
  have hL := L_lt s₀
  have a0 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 0 = ST s₀ + BitVec.ofNat 32 192 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
  have a1 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 1 = DP s₀ + BitVec.ofNat 32 (H s₀) := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hesi
  have a2 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 2 = BitVec.ofNat 32 (64 * NB s₀) := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
  have a3 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 3 = ST s₀ + BitVec.ofNat 32 256 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact heax
  have e := hp.sp_lo
  have e₂ := hp.sp_hi
  have e' := hp.st_fit
  have ed := hp.d_fit
  have es : (E s₀ - BitVec.ofNat 32 20).setWidth 64 - 12 = (E s₀ - BitVec.ofNat 32 32).setWidth 64 := by
    rw [hp.E64 (by decide), hp.E64 (by decide), BitVec.sub_sub]; rfl
  have hn : (BitVec.ofNat 32 (64 * NB s₀)).toNat = 64 * NB s₀ := Proof.ChaCha20.X86.Xor.toNat_ofNat_lt32 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.ChaCha20.xorX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.eaS (d := 192) (by decide), hp.eaS (d := 256) (by decide),
      hp.sNat (d := 192) (by decide), hp.sNat (d := 256) (by decide), hp.eaD (d := H s₀) (by omega),
      hp.dNat (d := H s₀) (by omega), hn, List.length_cons, List.length_nil, es]
    have sk : ∀ R, Region.Sub R (stkR s₀) → ∀ R', Region.Sub R' (stR s₀) → R.Disjoint R' :=
      fun R hR R' hR' => (hp.stk_st.sub_left hR).sub_right hR'
    have dk : ∀ R, Region.Sub R (stkR s₀) → R.Disjoint (blR s₀) :=
      fun R hR => (hp.stk_d.sub_left hR).sub_right (blR_sub s₀)
    refine ⟨trivial, trivial, (hp.st_d.sub_left (cpR_sub s₀)).sub_right (blR_sub s₀),
      Offset.disjoint _ (by omega) (by omega) (by omega),
      (hp.st_d.sub_left (wkR_sub s₀)).symm.sub_left (blR_sub s₀),
      sk _ (hp.stk_part (by decide) (by decide)) _ (cpR_sub s₀), dk _ (hp.stk_part (by decide) (by decide)),
      sk _ (hp.stk_part (by decide) (by decide)) _ (wkR_sub s₀),
      sk _ (hp.stk_part (by decide) (by decide)) _ (cpR_sub s₀), dk _ (hp.stk_part (by decide) (by decide)),
      sk _ (hp.stk_part (by decide) (by decide)) _ (wkR_sub s₀),
      sk _ (hp.stk_part (by decide) (by decide)) _ (cpR_sub s₀), dk _ (hp.stk_part (by decide) (by decide)),
      sk _ (hp.stk_part (by decide) (by decide)) _ (wkR_sub s₀), by omega, by omega, by omega, by omega,
      by omega⟩
  · rw [h.esp, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact within (stR s₀) (by simp) 192 rfl (by show 192 + 64 ≤ 768; omega)
    · exact within (dR s₀) (by simp) (H s₀) rfl hHNB
    · exact within (stR s₀) (by simp) 256 rfl (by show 256 + 320 ≤ 768; omega)
    · exact within (below (E s₀) 16) (by simp) 0 (by simp) (by simp)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact within (stR s₀) (by simp) 192 rfl (by show 192 + 64 ≤ 768; omega)
    · exact within (dR s₀) (by simp) (H s₀) rfl hHNB
    · exact within (stR s₀) (by simp) 256 rfl (by show 256 + 320 ≤ 768; omega)
    · exact within (below (E s₀) 16) (by simp) 0 (by simp) (by simp)

theorem xor_call {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (hnb : 0 < NB s₀)
    (hedx : s.gpr .edx = ST s₀ + BitVec.ofNat 32 192) (hesi : s.gpr .esi = DP s₀ + BitVec.ofNat 32 (H s₀))
    (hecx : s.gpr .ecx = BitVec.ofNat 32 (64 * NB s₀)) (heax : s.gpr .eax = ST s₀ + BitVec.ofNat 32 256)
    {Q : State → Prop}
    (hQ : ∀ s', At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [cpR s₀, blR s₀, wkR s₀, stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (dp s₀ + BitVec.ofNat 64 (H s₀)) (64 * NB s₀) =
        List.zipWith (· ^^^ ·) (bytesAt s.mem (dp s₀ + BitVec.ofNat 64 (H s₀)) (64 * NB s₀))
          (keystream (stateAt s.mem (st s₀ + BitVec.ofNat 64 192)) (64 * NB s₀)) → Q s') :
    WP isa callXor s Q := by
  have hk : [Reg.eax, .ecx, .esi, .edx].length ≤ 4 := by decide
  have fit := h.fit hp hk
  have e := hp.sp_lo
  have hHNB := HNB_le s₀
  have hL := L_lt s₀
  refine WP.callWith Proof.ChaCha20.X86.Xor.xor_correct xor_nosp (by simp) (by decide)
    (by rw [xor_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (xor_pre hp h hnb hedx hesi hecx heax) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [xor_stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) ?_
  · simp only [wrXor, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, below_sub (by omega) hp.sp_lo⟩
    · exact ⟨stkR s₀, by simp, below_sub (by omega) hp.sp_lo⟩
  · have a0 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 0 = ST s₀ + BitVec.ofNat 32 192 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
    have a1 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 1 = DP s₀ + BitVec.ofNat 32 (H s₀) := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hesi
    have a2 : arg (pushed [.eax, .ecx, .esi, .edx] s).callEntry 2 = BitVec.ofNat 32 (64 * NB s₀) := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
    have hn : (BitVec.ofNat 32 (64 * NB s₀)).toNat = 64 * NB s₀ :=
      Proof.ChaCha20.X86.Xor.toNat_ofNat_lt32 (by omega)
    simp only [Proof.ChaCha20.xorX86, arg_withRegions, State.withRegions_mem, a0, a1, a2,
      hp.eaS (d := 192) (by decide), hp.eaD (d := H s₀) (by omega), hn, m₂] at post
    have ef := h.entry_frame hp hk (by decide)
    rw [post, bytesAt_frame ef (by
      simp only [List.mem_singleton, forall_eq]; exact (hp.stk_d.sub_right (blR_sub s₀)).symm) (by omega),
      VG.Proof.ChaCha20.X86.Xor.stateAt_frame ef (by
        simp only [List.mem_singleton, forall_eq]; exact (hp.stk_st.sub_right (cpR_sub s₀)).symm)]

end VG.Proof.ChaCha20.X86.Stream
