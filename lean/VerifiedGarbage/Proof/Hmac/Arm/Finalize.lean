import VerifiedGarbage.Proof.Hmac.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Spec.Hmac.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# HMAC-SHA-256 on ARMv7: `finalize`

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 and AArch64 proofs (`VG.Proof.Hmac.X86_64.Finalize`,
`VG.Proof.Hmac.AArch64.Finalize`). The two SHA-256 finalizations are the
inlined `vg_sha256_finalize` (which calls `vg_sha256_compress`), used as a
black box through its proof, together with the fact that it never writes
`r0` (`WP.inlineCalls`); their stack
arguments (`out`, `scratch`) are ours, which they never write.
-/

namespace VG.Proof.Hmac.Arm.Finalize

open VG VG.Arm VG.Impl.Hmac.Arm
open VG.Proof.Hmac.Arm
open VG.Proof.Hmac.Common (writeBytes_at writeBytes_other bytesAt_getD' bytesAt_length
  bytesAt_writeBytes_self bytesAt_writeBytes_sep stateAt_eq_of_bytes xorPad_length repr_outer)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Sha256.Arm (contains_offset)
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_ldr wp_str wp_ldrSp op2_imm frame_bytes sub_offset)
open VG.Spec.Sha256 (bytesAt stateAt Repr)
open VG.Proof.Sha256 (countArm)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : BitVec 32 := s₀.gpr .r0
abbrev ou : BitVec 32 := s₀.gpr .r1
abbrev out : BitVec 32 := stackArg s₀ 0
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev inA : Addr := State.addr (inn s₀)
abbrev ouA : Addr := State.addr (ou s₀)
abbrev outA : Addr := State.addr (out s₀)
abbrev scA : Addr := State.addr (scr s₀)
abbrev inR : Region := ⟨inA s₀, 96⟩
abbrev ouR : Region := ⟨ouA s₀, 96⟩
abbrev outR : Region := ⟨outA s₀, 32⟩
abbrev scR : Region := ⟨scA s₀, 240⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩
/-- Where the inlined finalizations may write. -/
abbrev finW : List Region := [inR s₀, outR s₀, ⟨scA s₀, 160⟩]

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [ouR s₀, argR s₀]
  wr : s₀.wr = [inR s₀, outR s₀, scR s₀]
  i_o : (inR s₀).Disjoint (outR s₀)
  i_s : (inR s₀).Disjoint (scR s₀)
  o_s : (outR s₀).Disjoint (scR s₀)
  u_i : (ouR s₀).Disjoint (inR s₀)
  u_o : (ouR s₀).Disjoint (outR s₀)
  u_s : (ouR s₀).Disjoint (scR s₀)
  a_i : (argR s₀).Disjoint (inR s₀)
  a_o : (argR s₀).Disjoint (outR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  in_fit : (inn s₀).toNat + 96 ≤ 2 ^ 32
  ou_fit : (ou s₀).toNat + 96 ≤ 2 ^ 32
  out_fit : (out s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 240 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Proof.Hmac.finalizeSha256Arm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-! ## The stack arguments -/

theorem argAddr_eq {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 2) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega)]
  simp

theorem arg_in {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 2) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨argR s₀, by simp [hp.rd], by rw [argAddr_eq hp hk]; exact contains_offset (by omega) (by omega)⟩

theorem arg_sub {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 2) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (argR s₀) := by
  rw [argAddr_eq hp hk]; exact sub_offset (by omega) (by omega)

/-- The stack arguments are never written. -/
theorem stackArg_eq {s₀ : State} (hp : Pre s₀) {s : State} (hsp : s.sp = s₀.sp)
    (hf : Frame s₀.wr s₀.mem s.mem) {k : Nat} (hk : k < 2) : stackArg s k = stackArg s₀ k := by
  have e : stackArgAddr s k = stackArgAddr s₀ k := by simp only [stackArgAddr, hsp]
  simp only [stackArg, e]
  refine hf.readW (r := ⟨stackArgAddr s₀ k, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_i.sub_left (arg_sub hp hk)
  · exact hp.a_o.sub_left (arg_sub hp hk)
  · exact hp.a_s.sub_left (arg_sub hp hk)

theorem sub160 (s₀ : State) : Region.Sub ⟨scA s₀, 160⟩ (scR s₀) := Region.sub_prefix (by omega)

theorem finW_sub (s₀ : State) : ∀ r ∈ finW s₀, ∃ r' ∈ [inR s₀, outR s₀, scR s₀], Region.Sub r r' := by
  intro r hr
  simp only [finW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨inR s₀, by simp, fun _ h => h⟩
  · exact ⟨outR s₀, by simp, fun _ h => h⟩
  · exact ⟨scR s₀, by simp, sub160 s₀⟩

/-! ## The inlined finalization -/

theorem fin_exec : ∀ s, Proof.Sha256.finalizeArm.pre s → ∃ t s',
    Exec isa Impl.Sha256.Arm.Stream.finalize s t s' ∧ abiPreserved s s' ∧
      Proof.Sha256.finalizeArm.post s s' := by
  exact Proof.Sha256.Arm.Stream.Finalize.finalize_verified.1

theorem r0_ok : ∀ i ∈ instrs Impl.Sha256.Arm.Stream.finalize, dstOf i ≠ some .r0 := by
  have : ((instrs Impl.Sha256.Arm.Stream.finalize).all fun i => dstOf i != some .r0) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- The inlined `vg_sha256_finalize` on the inner state, with our stack
arguments (`out`, and `scratch[0..160)` as its scratch space). -/
theorem fin_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.sp = s₀.sp) (h0 : s.gpr .r0 = inn s₀) (ha0 : stackArg s 0 = out s₀)
    (ha1 : stackArg s 1 = scr s₀) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → abiPreserved s s' → Frame (finW s₀) s.mem s'.mem →
      s'.gpr .r0 = inn s₀ →
      (∀ m, Repr s.mem (inA s₀) m → countArm s = BitVec.ofNat 64 m.length →
        bytesAt s'.mem (outA s₀) 32 = Spec.Sha256.hash m) → Q s') :
    WP isa Impl.Sha256.Arm.Stream.finalize s Q := by
  have e0 : stackArg (s.withRegions [argR s₀] (finW s₀)) 0 = out s₀ := ha0
  have e1 : stackArg (s.withRegions [argR s₀] (finW s₀)) 1 = scr s₀ := ha1
  have ea : stackArgAddr (s.withRegions [argR s₀] (finW s₀)) 0 = stackArgAddr s₀ 0 := by
    simp only [stackArgAddr, State.withRegions_sp, hsp]
  refine WP.inlineCalls (k := Proof.Sha256.finalizeArm) fin_exec (rd := [argR s₀]) (wr := finW s₀) ?_ ?_ ?_ ?_
  · simp only [Proof.Sha256.finalizeArm, e0, e1, ea, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, h0, hsp]
    have := hp.scr_fit
    exact ⟨by first | rfl | trivial, by first | rfl | trivial, hp.i_o, hp.i_s.sub_right (sub160 s₀), hp.o_s.sub_right (sub160 s₀), hp.a_i, hp.a_o,
      hp.a_s.sub_right (sub160 s₀), hp.in_fit, hp.out_fit, by omega, hp.sp_fit⟩
  · rw [hrd, hwr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [finW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨argR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨inR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨outR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [finW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨inR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨outR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · intro s' h₁ h₂ h₃ h₄ hg hpost
    simp only [Proof.Sha256.finalizeArm, State.withRegions_gpr, State.withRegions_mem, h0, e0] at hpost
    exact hQ s' h₁ h₂ h₃ h₄ (by rw [hg _ r0_ok (by decide), h0]) hpost

/-! ## Saving the outer hash value -/

/-- After the prologue: the outer hash value's bytes are in `scratch[160..192)`. -/
structure Saved (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  frame : Frame [scR s₀] s₀.mem s.mem
  outer : ∀ i < 32, s.mem (scA s₀ + BitVec.ofNat 64 160 + BitVec.ofNat 64 i) = s₀.mem (ouA s₀ + BitVec.ofNat 64 i)

theorem ofNat_zero_add (p : Addr) : p + BitVec.ofNat 64 0 = p := by simp

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block saveOuter) s₀ (Saved s₀) := by
  have hsc := hp.scr_fit; have hou := hp.ou_fit
  unfold saveOuter
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  have c192 : (scR s₀).Contains (scA s₀ + BitVec.ofNat 64 192) 4 := contains_offset (by omega) (by omega)
  refine wp_str (a := scA s₀ + BitVec.ofNat 64 192) (by decide) (by rw [h12, addr_add (by omega)])
    ⟨scR s₀, by simp [u₁.wr, hp.wr], c192⟩ fun s₂ u₂ => ?_
  have e1 : s₂.gpr .r1 = ou s₀ := by rw [u₂.gpr, u₁.other _ (by decide)]
  have e12 : s₂.gpr .r12 = scr s₀ := by rw [u₂.gpr, h12]
  have fr₂ : Frame [scR s₀] s₀.mem s₂.mem := by
    rw [u₂.mem, u₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c192
  refine copy_ok (t := .r2) (src := .r1) (dst := .r12) (by decide) (by decide) 0 160 8
    ⟨by omega, by omega⟩ _ s₂ _ (by rw [e1]; omega) (by rw [e12]; omega) (fun k hk => ?_) (fun k hk => ?_) ?_
    fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  · rw [e1, ofNat_zero_add, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
    exact ⟨ouR s₀, by simp [hp.rd], contains_offset (by omega) (by omega)⟩
  · rw [e12, u₂.wr, u₁.wr, ← add_off]
    exact ⟨scR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩
  · rw [e1, e12, ofNat_zero_add]
    exact hp.u_s.sep (by simp [Region.Contains]) (contains_offset (by omega) (by omega))
  rw [e1, e12, ofNat_zero_add] at m₃
  have h12₃ : s₃.gpr .r12 = scr s₀ := by rw [g₃ _ (by decide), e12]
  have c160 : (scR s₀).Contains (scA s₀ + BitVec.ofNat 64 160) 32 := contains_offset (by omega) (by omega)
  have fw : Frame [⟨scA s₀ + BitVec.ofNat 64 160, 32⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine wp_ldr (a := scA s₀ + BitVec.ofNat 64 192) (by decide) (by rw [h12₃, addr_add (by omega)])
    ⟨scR s₀, by simp [rd₃, wr₃, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hp.wr], c192⟩ fun s₄ u₄ => WP.block_nil ?_
  have hb : ∀ i < 32, s₂.mem (ouA s₀ + BitVec.ofNat 64 i) = s₀.mem (ouA s₀ + BitVec.ofNat 64 i) :=
    fun i hi => frame_bytes fr₂ (R := ouR s₀) (by simpa using hp.u_s) (by simp) (by show i < 96; omega)
  refine ⟨by rw [u₄.rd, rd₃, u₂.rd, u₁.rd], by rw [u₄.wr, wr₃, u₂.wr, u₁.wr],
    by rw [u₄.sp, sp₃, u₂.sp, u₁.sp], fun r hr => ?_, ?_, fun i hi => ?_⟩
  · by_cases h2 : r = .r2
    · subst h2
      rw [u₄.gpr, fw.readW (r := ⟨scA s₀ + BitVec.ofNat 64 192, 4⟩) (a := scA s₀ + BitVec.ofNat 64 192)
        (w := 32) (Region.contains_self _ _) ?_ (by decide), u₂.mem, u₁.other _ (by decide)]
      · exact Mem.readW_writeW_self32 _ _ _
      · simp only [List.mem_singleton]; rintro r rfl
        off_disj
    · rw [u₄.other r h2, g₃ r h2, u₂.gpr, u₁.other r hr]
  · rw [u₄.mem]
    exact fr₂.trans (fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, sub_offset (by omega) (by omega)⟩)
  · rw [u₄.mem, m₃, writeBytes_at _ _ _ (by rw [bytesAt_length]; omega) (by rw [bytesAt_length]; omega),
      bytesAt_getD' _ _ hi, hb i hi]

/-! ## Loading the outer hash value and the inner digest -/

/-- After the middle block, from `s`: the inner state holds the hash value from
`scratch[160..192)` and, in its buffer, the digest from `out`. -/
structure Loaded (s₀ s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  r0 : s'.gpr .r0 = inn s₀
  r2 : s'.gpr .r2 = 96
  r3 : s'.gpr .r3 = 0
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  state : stateAt s'.mem (inA s₀) = stateAt s.mem (scA s₀ + BitVec.ofNat 64 160)
  buf : bytesAt s'.mem (inA s₀ + 32) 32 = bytesAt s.mem (outA s₀) 32
  frame : Frame [inR s₀] s.mem s'.mem

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.sp = s₀.sp) (h0 : s.gpr .r0 = inn s₀) (ha0 : stackArg s 0 = out s₀)
    (ha1 : stackArg s 1 = scr s₀) : WP isa (.block loadOuter) s (Loaded s₀ s) := by
  have hsc := hp.scr_fit; have hin := hp.in_fit; have hot := hp.out_fit
  unfold loadOuter
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  have hi1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 4 := by
    rw [show stackArgAddr s 1 = stackArgAddr s₀ 1 by simp only [stackArgAddr, hsp], hrd, hwr]
    exact arg_in hp (by decide)
  have hi0 : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4 := by
    rw [show stackArgAddr s 0 = stackArgAddr s₀ 0 by simp only [stackArgAddr, hsp], hrd, hwr]
    exact arg_in hp (by decide)
  refine wp_ldrSp (a := stackArgAddr s 1) (by decide) rfl hi1 fun s₁ u₁ => ?_
  refine wp_ldrSp (a := stackArgAddr s 0) (by decide) (by rw [u₁.sp]; rfl) (by rw [u₁.rd, u₁.wr]; exact hi0)
    fun s₂ u₂ => ?_
  have e1 : s₂.gpr .r1 = scr s₀ := by rw [u₂.other _ (by decide), u₁.gpr]; exact ha1
  have e12 : s₂.gpr .r12 = out s₀ := by rw [u₂.gpr, u₁.mem]; exact ha0
  have e0 : s₂.gpr .r0 = inn s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h0]
  have rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd, hrd]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, hwr]
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have cin : ∀ k < 8, InRegions s₂.wr (inA s₀ + BitVec.ofNat 64 0 + BitVec.ofNat 64 (4 * k)) 4 :=
    fun k hk => ⟨inR s₀, by simp [wr₂, hp.wr], by rw [← add_off]; exact contains_offset (by omega) (by omega)⟩
  refine copy_ok (t := .r3) (src := .r1) (dst := .r0) (by decide) (by decide) 160 0 8
    ⟨by omega, by omega⟩ _ s₂ _ (by rw [e1]; omega) (by rw [e0]; omega) (fun k hk => ?_)
    (fun k hk => by rw [e0]; exact cin k hk) ?_ fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  · rw [e1, rd₂, wr₂, ← add_off]
    exact ⟨scR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩
  · rw [e1, e0, ofNat_zero_add]
    exact hp.i_s.symm.sep (contains_offset (by omega) (by omega)) (by simp [Region.Contains])
  rw [e1, e0, ofNat_zero_add, hm₂] at m₃
  have e12₃ : s₃.gpr .r12 = out s₀ := by rw [g₃ _ (by decide), e12]
  have e0₃ : s₃.gpr .r0 = inn s₀ := by rw [g₃ _ (by decide), e0]
  refine copy_ok (t := .r3) (src := .r12) (dst := .r0) (by decide) (by decide) 0 32 8
    ⟨by omega, by omega⟩ _ s₃ _ (by rw [e12₃]; omega) (by rw [e0₃]; omega) (fun k hk => ?_)
    (fun k hk => ?_) ?_ fun s₄ g₄ rd₄ wr₄ sp₄ m₄ => ?_
  · rw [e12₃, rd₃, wr₃, rd₂, wr₂, ofNat_zero_add]
    exact ⟨outR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩
  · rw [e0₃, wr₃, wr₂, ← add_off]
    exact ⟨inR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩
  · rw [e12₃, e0₃, ofNat_zero_add]
    exact hp.i_o.symm.sep (by simp [Region.Contains]) (contains_offset (by omega) (by omega))
  rw [e12₃, e0₃, ofNat_zero_add] at m₄
  refine wp_mov (op2_imm (by decide)) fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have c₀ : (inR s₀).Contains (inA s₀) 32 := by simp [Region.Contains]
  have hm : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have hbuf : bytesAt s₄.mem (inA s₀ + 32) 32 = bytesAt s.mem (outA s₀) 32 := by
    rw [m₄, show inA s₀ + 32 = inA s₀ + BitVec.ofNat 64 32 from rfl]
    have := bytesAt_writeBytes_self s₃.mem (inA s₀ + BitVec.ofNat 64 32)
      (bytesAt s₃.mem (outA s₀) (4 * 8)) (by simp [bytesAt])
    rw [bytesAt_length] at this
    rw [this, m₃, bytesAt_writeBytes_sep]
    · rw [bytesAt_length]
      exact hp.i_o.symm.sep (Region.contains_self _ _) c₀
    · omega
  have hst : stateAt s₄.mem (inA s₀) = stateAt s.mem (scA s₀ + BitVec.ofNat 64 160) := by
    refine stateAt_eq_of_bytes fun i hi => ?_
    have key : ∀ p : Addr, ¬ (p + BitVec.ofNat 64 i - (p + BitVec.ofNat 64 32)).toNat < 4 * 8 := by
      intro p; bv_omega
    rw [m₄, writeBytes_other _ _ _ (by rw [bytesAt_length]; exact key _), m₃,
      writeBytes_at _ _ _ (by rw [bytesAt_length]; omega) (by rw [bytesAt_length]; omega),
      bytesAt_getD' _ _ (by omega)]
  have hfr : Frame [inR s₀] s.mem s₄.mem := by
    rw [m₄, m₃]
    refine (writeBytes_frame (R := inR s₀) _ _ _ ?_).trans (writeBytes_frame (R := inR s₀) _ _ _ ?_)
    · rw [bytesAt_length]; exact c₀
    · rw [bytesAt_length]; exact contains_offset (by omega) (by omega)
  have k₄ : ∀ r, r ≠ .r1 → r ≠ .r12 → r ≠ .r3 → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [g₄ r c, g₃ r c, u₂.other r b, u₁.other r a]
  refine ⟨by rw [u₆.rd, u₅.rd, rd₄, rd₃, rd₂, hrd], by rw [u₆.wr, u₅.wr, wr₄, wr₃, wr₂, hwr],
    by rw [u₆.sp, u₅.sp, sp₄, sp₃, u₂.sp, u₁.sp], ?_, ?_, u₆.gpr, fun r hr => ?_,
    by rw [hm, hst], by rw [hm, hbuf], by rw [hm]; exact hfr⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), k₄ _ (by decide) (by decide) (by decide), h0]
  · rw [u₆.other _ (by decide), u₅.gpr]
  · have : r ≠ .r1 ∧ r ≠ .r12 ∧ r ≠ .r3 ∧ r ≠ .r2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₆.other _ this.2.2.1, u₅.other _ this.2.2.2, k₄ _ this.1 this.2.1 this.2.2.1]

/-! ## Correctness -/

/-- `scratch[160..192)` is not written by the inlined finalizations. -/
theorem not_finW {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) :
    ∀ r ∈ finW s₀, ¬ r.Contains (scA s₀ + BitVec.ofNat 64 160 + BitVec.ofNat 64 i) 1 := by
  have := hp.scr_fit
  have hs : (scR s₀).Contains (scA s₀ + BitVec.ofNat 64 160 + BitVec.ofNat 64 i) 1 := by
    rw [← add_off]; exact contains_offset (by omega) (by omega)
  intro r hr
  simp only [finW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact fun hc => hp.i_s _ hc hs
  · exact fun hc => hp.o_s _ hc hs
  · simp only [Region.Contains]
    have : (State.addr (scr s₀)).toNat = (scr s₀).toNat :=
      Proof.MdStream.Arm.addr_toNat _
    bv_omega

theorem countArm_96 {s : State} (h2 : s.gpr .r2 = 96) (h3 : s.gpr .r3 = 0) :
    countArm s = BitVec.ofNat 64 (64 + 32) := by
  simp only [countArm, h2, h3]; decide

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Hmac.finalizeSha256Arm.post s₀ s' := by
  unfold finalize
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have fW₁ : Frame s₀.wr s₀.mem s₁.mem := h₁.frame.mono (by simp [hp.wr])
  refine WP.seq (fin_ok hp h₁.rd h₁.wr h₁.sp (h₁.gpr _ (by decide)) (stackArg_eq hp h₁.sp fW₁ (by decide))
    (stackArg_eq hp h₁.sp fW₁ (by decide)) fun s₂ rd₂ wr₂ abi₂ fr₂ r0₂ post₂ => ?_)
  have sp₂ : s₂.sp = s₀.sp := abi₂.2.trans h₁.sp
  have fW₂ : Frame s₀.wr s₀.mem s₂.mem := fW₁.trans (by rw [hp.wr]; exact fr₂.sub (finW_sub s₀))
  refine WP.seq (WP.mono (load_ok hp (s := s₂) (rd₂.trans h₁.rd) (wr₂.trans h₁.wr) sp₂ r0₂
    (stackArg_eq hp sp₂ fW₂ (by decide)) (stackArg_eq hp sp₂ fW₂ (by decide))) fun s₃ h₃ => ?_)
  have sp₃ : s₃.sp = s₀.sp := h₃.sp.trans sp₂
  have fW₃ : Frame s₀.wr s₀.mem s₃.mem := fW₂.trans (h₃.frame.mono (by simp [hp.wr]))
  refine fin_ok hp (h₃.rd.trans (rd₂.trans h₁.rd)) (h₃.wr.trans (wr₂.trans h₁.wr)) sp₃ h₃.r0
    (stackArg_eq hp sp₃ fW₃ (by decide)) (stackArg_eq hp sp₃ fW₃ (by decide))
    fun s₄ rd₄ wr₄ abi₄ fr₄ _ post₄ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have : r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [abi₄.1 r hr, h₃.cs r hr, abi₂.1 r hr, h₁.gpr r this]
  · rw [abi₄.2, sp₃]
  · intro k0 text hk hin hcnt hout
    -- The inner digest.
    have hin₁ : Repr s₁.mem (inA s₀) (xorPad k0 ipad ++ text) :=
      Proof.Sha256.Stream.repr_congr (fun i hi => frame_bytes (R := inR s₀) h₁.frame
        (by simpa using hp.i_s) (by simp) hi) hin
    have hc₁ : countArm s₁ = BitVec.ofNat 64 (xorPad k0 ipad ++ text).length := by
      rw [List.length_append, xorPad_length, hk, ← hcnt]
      simp only [countArm, h₁.gpr _ (show Reg.r2 ≠ .r12 by decide), h₁.gpr _ (show Reg.r3 ≠ .r12 by decide)]
    have hd := post₂ _ hin₁ hc₁
    -- The outer state.
    have hst : stateAt s₃.mem (inA s₀) = Spec.Sha256.compressList Spec.Sha256.H0 (xorPad k0 opad) 1 := by
      rw [h₃.state]
      have e : stateAt s₂.mem (scA s₀ + BitVec.ofNat 64 160) = stateAt s₀.mem (ouA s₀) := by
        refine stateAt_eq_of_bytes fun i hi => ?_
        rw [fr₂ _ (not_finW hp hi), h₁.outer i hi]
      rw [e, hout.1, xorPad_length, hk]
    have hrepr := repr_outer hk (by rw [bytesAt_length]) hst h₃.buf
    have := post₄ _ hrepr (by rw [countArm_96 h₃.r2 h₃.r3, List.length_append, xorPad_length, hk,
      bytesAt_length])
    rw [hd] at this
    simpa [hmacBlockKey, sha256] using this

/-! ## `Verified` -/

/-- The initial taint: `r0`–`r3` (`inner`, `outer`, `count`) are public, `r0`
points at the inner state, and the 8 bytes of stack arguments are public,
the second one pointing at the scratch space. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [96, 32, 240], bases := [(.r0, 0)],
    argLen := 8, argBases := [(4, 2)] }

theorem wf₀ {s : State} (h : Proof.Hmac.finalizeSha256Arm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have hst := hp.in_fit; have ho := hp.out_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.i_o, hp.i_s⟩, hp.o_s, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [Proof.MdStream.Arm.addr_toNat] <;> omega
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'; simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 8⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.a_i
    · exact hp.a_o
    · exact hp.a_s
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Hmac.finalizeSha256Arm.pre s₁)
    (h₂ : Proof.Hmac.finalizeSha256Arm.pre s₂) (hpub : Proof.Hmac.finalizeSha256Arm.pub s₁ s₂) :
    VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0, a1⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [inR, outR, scR, inA, outA, scA, inn, out, scr, p0, a0, a1]
  · simp only [τ₀] at hk
    rw [Proof.MdStream.Arm.argByte_eq hp₁.sp_fit hk,
      Proof.MdStream.Arm.argByte_eq hp₂.sp_fit hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

/-- A state satisfying the precondition: `inner` at `0x1000`, `outer` at
`0x2000`, `out` at `0x3000` and the scratch space at `0x4000`, passed on the
stack at `0x5000`. -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x30 else if a = 0x5005 then 0x40 else 0
  rd := [⟨0x2000, 96⟩, ⟨0x5000, 8⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x3000, 32⟩, ⟨0x4000, 240⟩]

theorem finalize_correct (s : State) (hs : Proof.Hmac.finalizeSha256Arm.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ Proof.Hmac.finalizeSha256Arm.post s s' :=
      by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, h⟩

theorem finalize_ct : ConstantTime isa Proof.Hmac.finalizeSha256Arm.pre
    Proof.Hmac.finalizeSha256Arm.pub finalize := by
  exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by taint_decide)

/-- `finalizeSha256Arm` with the 688 bytes of scratch of the shared contract
(sized for the x86-64 AVX2 compression function), of which the code uses 240. -/
def finalizeWide : Contract isa :=
  { Proof.Hmac.finalizeSha256Arm with
    pre := fun s =>
      let inner : Region := ⟨State.addr (s.gpr .r0), 96⟩
      let outer : Region := ⟨State.addr (s.gpr .r1), 96⟩
      let out : Region := ⟨State.addr (stackArg s 0), 32⟩
      let scratch : Region := ⟨State.addr (stackArg s 1), 688⟩
      let args : Region := ⟨stackArgAddr s 0, 8⟩
      s.rd = [outer, args] ∧ s.wr = [inner, out, scratch] ∧
      inner.Disjoint out ∧ inner.Disjoint scratch ∧ out.Disjoint scratch ∧
      outer.Disjoint inner ∧ outer.Disjoint out ∧ outer.Disjoint scratch ∧
      args.Disjoint inner ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + 96 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 96 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 688 ≤ 2 ^ 32 ∧
      s.sp.toNat + 8 ≤ 2 ^ 32 }

/-- The regions `finalizeSha256Arm` lets the code write. -/
def narrowWr (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), 96⟩, ⟨State.addr (stackArg s 0), 32⟩, ⟨State.addr (stackArg s 1), 240⟩]

/-- Rewrites the contracts at a narrowed state (`stackArg` does not unfold
cheaply). -/
local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Hmac.finalizeSha256Arm, Proof.Sha256.countArm, VG.Proof.Hmac.Arm.Finalize.finalizeWide,
    VG.Proof.Hmac.Arm.Finalize.narrowWr, VG.Arm.stackArg_withRegions, VG.Arm.stackArgAddr_withRegions,
    VG.Arm.State.withRegions_gpr, VG.Arm.State.withRegions_sp, VG.Arm.State.withRegions_mem,
    VG.Arm.State.withRegions_rd, VG.Arm.State.withRegions_wr] $(loc)?)

theorem finalizeWide_pre (s : State) (h : finalizeWide.pre s) :
    Proof.Hmac.finalizeSha256Arm.pre (s.withRegions s.rd (narrowWr s)) := by
  obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆⟩ := h
  narrow
  exact ⟨h₁, trivial, h₃, h₄.sub_right (Region.sub_of_ble rfl), h₅.sub_right (Region.sub_of_ble rfl),
    h₆, h₇, h₈.sub_right (Region.sub_of_ble rfl), h₉, h₁₀, h₁₁.sub_right (Region.sub_of_ble rfl), h₁₂,
    h₁₃, h₁₄, Region.end_le_of_ble rfl h₁₅, h₁₆⟩

/-- A state satisfying `finalizeWide.pre`. -/
def wideSat : State := { sat with wr := [⟨0x1000, 96⟩, ⟨0x3000, 32⟩, ⟨0x4000, 688⟩] }

theorem finalizeWide_implies :
    finalizeWide.Implies (Spec.Hmac.finalizeSha256OutContract Arm.abi) := by
  sig_implies [Spec.Hmac.finalizeSha256OutContract, Spec.Hmac.finalizeSha256OutSig, finalizeWide,
    Proof.Hmac.finalizeSha256Arm, Proof.Sha256.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [wideSat, sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using wideSat

/-- The proof is written against `finalizeSha256Arm`, widened to the shared
contract's scratch. -/
theorem finalize_verified :
    Verified Arm.target Impl.Hmac.Arm.finalize (Spec.Hmac.finalizeSha256OutContract Arm.abi) :=
  have hsat := finalizeWide_implies.sat_left
  (Verified.widen (Verified.of_correct finalize_correct finalize_ct
    (.refl (hsat.elim fun s hs => ⟨_, finalizeWide_pre s hs⟩)))
    narrowWr finalizeWide_pre
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      exact .cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl)
        (.cons (Region.prefix_of_ble rfl) .nil)))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies finalizeWide_implies

end VG.Proof.Hmac.Arm.Finalize
