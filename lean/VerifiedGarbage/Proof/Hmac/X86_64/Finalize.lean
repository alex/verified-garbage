import VerifiedGarbage.Proof.Hmac.X86_64.Common
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.FinalizeCT
import VerifiedGarbage.Proof.Sha256.X86_64.Shared
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Hmac.Contract

/-!
# HMAC-SHA-256 on x86-64: `finalize`

Untrusted: everything here is checked by Lean. The two SHA-256
finalizations are calls of the streaming finalization over any compression
function `f` (`Callee.Ok`), used as a black box through its proof (with the
extra fact that it leaves `rdi` and `rcx` unchanged), so this is proven once
for every implementation.
-/

namespace VG.Proof.Hmac.X86_64.Finalize

open VG VG.X86_64 VG.Impl.Hmac.X86_64
open VG.Impl.Sha256.X86_64.Stream (Callee)
open VG.Proof.Hmac.X86_64
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame compressList_append)
open VG.Proof.Sha256.X86_64 (contains_offset toNat_ofNat_lt sub_offset)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov wp_mov32i wp_addi)
open VG.Spec.Sha256 (bytesAt stateAt Repr)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .rdi
abbrev out : Addr := s₀.gpr .rsi
abbrev scr : Addr := s₀.gpr .rcx
abbrev inR : Region := ⟨inn s₀, 96⟩
abbrev outR : Region := ⟨out s₀, 96⟩
abbrev scR : Region := ⟨scr s₀, 240⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- Where the called finalizations may write. -/
abbrev finW : List Region := [inR s₀, ⟨scr s₀ + 176, 32⟩, ⟨scr s₀, 160⟩]
/-- Where the calls store their return addresses: ours, and that of the call
of the compression function in the finalization. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 16

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [outR s₀]
  wr : s₀.wr = [inR s₀, scR s₀]
  i_o : (inR s₀).Disjoint (outR s₀)
  i_s : (inR s₀).Disjoint (scR s₀)
  o_s : (outR s₀).Disjoint (scR s₀)
  ret_i : (retR s₀).Disjoint (inR s₀)
  ret_o : (retR s₀).Disjoint (outR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  stk_i : (stkR s₀).Disjoint (inR s₀)
  stk_o : (stkR s₀).Disjoint (outR s₀)
  stk_s : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Hmac.finalizeSha256X86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- The return address and the 16 bytes below it. -/
theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

/-- Our call's return address. -/
theorem sub_stk₁ (s₀ : State) : Region.Sub ⟨s₀.gpr .rsp - 8, 8⟩ (stkR s₀) := by
  intro a h; simp only [Region.Contains] at h ⊢; bv_omega

/-- The return address of the finalization's call. -/
theorem sub_stk₂ (s₀ : State) : Region.Sub ⟨s₀.gpr .rsp - 8 - 8, 8⟩ (stkR s₀) := by
  intro a h; simp only [Region.Contains] at h ⊢; bv_omega

/-! ## The called finalization -/

/-- The finalization's contract, and `rdi` and `rcx` are unchanged. -/
def finK : Contract isa :=
  { Proof.Sha256.finalizeX86_64 with
    post := fun s s' => Proof.Sha256.finalizeX86_64.post s s' ∧ s'.gpr .rdi = s.gpr .rdi ∧
      s'.gpr .rcx = s.gpr .rcx }

section
variable {f : Callee} (hf : f.Ok)
  (hm : (Impl.Sha256.X86_64.Stream.finalize f).allInstrs (fun i => !loadsMxcsr i) = true)

include hf hm in
theorem finK_ok : ∀ s, finK.pre s → ∃ t s', Exec isa (Impl.Sha256.X86_64.Stream.finalize f) s t s' ∧
    abiPreserved s s' ∧ finK.post s s' := by
  intro s hs
  obtain ⟨t, s', he, h₁, h₂, h₃, h₄⟩ :=
    Proof.Sha256.X86_64.Stream.Finalize.correct hf (Proof.Sha256.X86_64.Stream.Finalize.pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec hm he h₁, h₂, h₃, h₄⟩

theorem sub176 (s₀ : State) : Region.Sub ⟨scr s₀ + 176, 32⟩ (scR s₀) :=
  sub_offset (off := 176) (by omega) (by omega)

theorem sub160 (s₀ : State) : Region.Sub ⟨scr s₀, 160⟩ (scR s₀) := Region.sub_prefix (by omega)

include hf in
theorem finalize_depth : (Impl.Sha256.X86_64.Stream.finalize f).depth = 1 := by
  simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.Sha256.X86_64.Stream.finalizeBody,
    Impl.Sha256.X86_64.Stream.compressAt, Code.depth, hf.depth]
  decide +kernel

include hf in
theorem finalize_nosp : NoSp (Impl.Sha256.X86_64.Stream.finalize f) := by
  have hc : (f.code.allInstrs fun i => !Taint.clobbers i .rsp) = true := by
    rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by simp [hf.nosp i hi]
  have : ((instrs (Impl.Sha256.X86_64.Stream.finalize f)).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]
    simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.Sha256.X86_64.Stream.finalizeBody,
      Impl.Sha256.X86_64.Stream.compressAt, Code.allInstrs, hc, Bool.true_and]
    decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- The call's precondition, narrowed to the regions it is given. -/
theorem fin_hyps {s₀ : State} (hp : Pre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hdi : s.gpr .rdi = inn s₀) (hcx : s.gpr .rcx = scr s₀) (hdx : s.gpr .rdx = scr s₀ + 176)
    (hsp : s.gpr .rsp = s₀.gpr .rsp) :
    finK.pre (s.callEntry.withRegions [] (finW s₀)) ∧ Covers ([] ++ finW s₀) (s.rd ++ s.wr) ∧
      Covers (finW s₀) s.wr := by
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, by simp [hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rcx ≠ .rsp),
      hne _ (by decide : Reg.rdx ≠ .rsp), hdi, hcx, hdx], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [State.withRegions_gpr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
        hne _ (by decide : Reg.rcx ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp), hdi, hcx, hdx, hsp]
    · exact hp.i_s.sub_right (sub176 s₀)
    · exact hp.i_s.sub_right (sub160 s₀)
    · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
    · exact (hp.stk_i.sub_left (sub_stk₁ s₀))
    · exact (hp.stk_s.sub_left (sub_stk₁ s₀)).sub_right (sub176 s₀)
    · exact (hp.stk_s.sub_left (sub_stk₁ s₀)).sub_right (sub160 s₀)
    · exact (hp.stk_i.sub_left (sub_stk₂ s₀))
    · exact (hp.stk_s.sub_left (sub_stk₂ s₀)).sub_right (sub176 s₀)
    · exact (hp.stk_s.sub_left (sub_stk₂ s₀)).sub_right (sub160 s₀)
  · rw [hrd, hwr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨inR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 176, rfl, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨inR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 176, rfl, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩

include hf hm in
/-- The called finalization (`name`) on the inner state, with its digest at
`scratch[176..208)` and `scratch[0..160)` as its scratch space. -/
theorem fin_ok (name : String) {s₀ : State} (hp : Pre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hdi : s.gpr .rdi = inn s₀) (hcx : s.gpr .rcx = scr s₀) (hdx : s.gpr .rdx = scr s₀ + 176)
    (hsp : s.gpr .rsp = s₀.gpr .rsp) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (finW s₀ ++ [stkR s₀]) s.mem s'.mem →
      s'.gpr .rdi = inn s₀ → s'.gpr .rcx = scr s₀ →
      (∀ m, Repr s.mem (inn s₀) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
        bytesAt s'.mem (scr s₀ + 176) 32 = Spec.Sha256.hash m) → Q s') :
    WP isa (sha256Finalize f name) s Q := by
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  obtain ⟨hpre, hc, hw⟩ := fin_hyps hp hrd hwr hdi hcx hdx hsp
  refine WP.call (k := finK) (finK_ok hf hm) (finalize_nosp hf) (by rw [finalize_depth hf]; decide)
    (rd := []) (wr := finW s₀) hpre hc hw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, hg, hpost, h₅, h₆⟩
  simp only [Proof.Sha256.finalizeX86_64, State.withRegions_gpr, State.withRegions_mem, hm,
    hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rcx ≠ .rsp),
    hne _ (by decide : Reg.rdx ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp), hdi, hdx, hcx] at hpost h₅ h₆
  rw [finalize_depth hf, hsp] at h₄
  refine hQ s' h₁ h₂ h₃ h₄ (by rw [← hg _ (by decide)]; exact h₅) (by rw [← hg _ (by decide)]; exact h₆)
    fun m hm hl => hpost m (Proof.Sha256.Stream.repr_congr (fun i hi => ?_) hm) hl
  refine Proof.Sha256.X86_64.Stream.callEntry_byte s (R := inR s₀) ?_ (by simp) hi
  rw [hsp]; exact hp.stk_i.sub_left (below_sub (by omega) (by omega))

end

/-! ## Saving the outer hash value -/

theorem sx176 : BitVec.signExtend 64 (176 : BitVec 32) = (176 : BitVec 64) := by decide

/-- After the prologue: the outer hash value's bytes are in `scratch[208..240)`. -/
structure Saved (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rdi : s.gpr .rdi = inn s₀
  rcx : s.gpr .rcx = scr s₀
  rsi : s.gpr .rsi = s₀.gpr .rdx
  rdx : s.gpr .rdx = scr s₀ + 176
  cs : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  mem : s.mem = writeBytes s₀.mem (scr s₀ + BitVec.ofNat 64 208) (bytesAt s₀.mem (out s₀) 32)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveOuter ++ ([.mov .rsi (.reg .rdx), .mov .rdx (.reg .rcx), .alu .add .rdx (.imm 176)] : List Instr)))
      s₀ (Saved s₀) := by
  unfold saveOuter
  have h0 : out s₀ + BitVec.ofNat 64 0 = out s₀ := by simp
  refine copy32_ok (by decide) (by decide) 0 208 8 _ s₀ _ (fun k hk => ?_) (fun k hk => ?_) ?_ (by omega)
    fun s₁ g₁ rd₁ wr₁ m₁ => wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_addi fun s₄ u₄ =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [h0]
    exact ⟨outR s₀, by simp [hp.rd], contains_offset (by omega) (by omega)⟩
  · refine ⟨scR s₀, by simp [hp.wr], ?_⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact contains_offset (by omega) (by omega)
  · rw [h0]
    exact hp.o_s.sep (a := out s₀) (n := 32) (by simp [Region.Contains]) (contains_offset (by omega) (by omega))
  · rw [u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide)]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide)]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁ _ (by decide)]
  · rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), g₁ _ (by decide), sx176]
  · have : r ≠ .rax ∧ r ≠ .rsi ∧ r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₄.other _ this.2.2, u₃.other _ this.2.2, u₂.other _ this.2.1, g₁ _ this.1]
  · rw [u₄.mem, u₃.mem, u₂.mem, m₁, h0]

/-! ## Loading the outer hash value and the inner digest -/

theorem sx96 : ((96 : BitVec 32).setWidth 64) = BitVec.ofNat 64 (64 + 32) := by decide

/-- After the middle block, from `s`: the inner state holds the hash value from
`scratch[208..240)` and, in its buffer, the digest from `scratch[176..208)`. -/
structure Loaded (s₀ s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  rdi : s'.gpr .rdi = inn s₀
  rcx : s'.gpr .rcx = scr s₀
  rsi : s'.gpr .rsi = BitVec.ofNat 64 (64 + 32)
  rdx : s'.gpr .rdx = scr s₀ + 176
  cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  state : stateAt s'.mem (inn s₀) = stateAt s.mem (scr s₀ + BitVec.ofNat 64 208)
  buf : bytesAt s'.mem (inn s₀ + 32) 32 = bytesAt s.mem (scr s₀ + 176) 32
  frame : Frame [inR s₀] s.mem s'.mem

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr)
    (hdi : s.gpr .rdi = inn s₀) (hcx : s.gpr .rcx = scr s₀) :
    WP isa (.block (loadOuter ++ ([.mov32 .rsi (.imm 96), .mov .rdx (.reg .rcx), .alu .add .rdx (.imm 176)] : List Instr)))
      s (Loaded s₀ s) := by
  unfold loadOuter
  rw [List.append_assoc]
  have hin : ∀ {o k : Nat}, o + k ≤ 240 → InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofNat 64 o) k :=
    fun h => ⟨scR s₀, by simp [hwr, hp.wr], contains_offset h (by omega)⟩
  have hout : ∀ {o k : Nat}, o + k ≤ 96 → InRegions s.wr (inn s₀ + BitVec.ofNat 64 o) k :=
    fun h => ⟨inR s₀, by simp [hwr, hp.wr], contains_offset h (by omega)⟩
  have add : ∀ (p : Addr) (a b : Nat), p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) :=
    fun p a b => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine copy32_ok (src := .rcx) (dst := .rdi) (by decide) (by decide) 208 0 8 _ s _ ?_ ?_ ?_
    (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  · intro k hk; rw [hcx, add]; exact hin (by omega)
  · intro k hk; rw [hdi, add]; exact hout (by omega)
  · rw [hcx, hdi]
    exact hp.i_s.symm.sep (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  have e₁ : s₁.gpr .rcx = scr s₀ := by rw [g₁ _ (by decide), hcx]
  have d₁ : s₁.gpr .rdi = inn s₀ := by rw [g₁ _ (by decide), hdi]
  refine copy64_ok (src := .rcx) (dst := .rdi) (by decide) (by decide) 176 32 4 _ s₁ _ ?_ ?_ ?_
    (by omega) fun s₂ g₂ rd₂ wr₂ m₂ => wp_mov32i fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ =>
      wp_addi fun s₅ u₅ => WP.block_nil ?_
  · intro k hk; rw [e₁, add, rd₁, wr₁]; exact hin (by omega)
  · intro k hk; rw [d₁, add, wr₁]; exact hout (by omega)
  · rw [e₁, d₁]
    exact hp.i_s.symm.sep (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  rw [hcx, hdi, show inn s₀ + BitVec.ofNat 64 0 = inn s₀ by simp] at m₁
  rw [e₁, d₁] at m₂
  have c₀ : (inR s₀).Contains (inn s₀) 32 := by simp [Region.Contains]
  have hm : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have k₂ : ∀ r, r ≠ .rax → s₂.gpr r = s.gpr r := fun r h => by rw [g₂ r h, g₁ r h]
  -- The bytes of the inner state.
  have hbuf : bytesAt s₂.mem (inn s₀ + 32) 32 = bytesAt s.mem (scr s₀ + 176) 32 := by
    rw [m₂, show inn s₀ + 32 = inn s₀ + BitVec.ofNat 64 32 from rfl]
    have := bytesAt_writeBytes_self s₁.mem (inn s₀ + BitVec.ofNat 64 32)
      (bytesAt s₁.mem (scr s₀ + BitVec.ofNat 64 176) (8 * 4)) (by simp [bytesAt])
    rw [bytesAt_length] at this
    rw [this, m₁, bytesAt_writeBytes_sep]
    · rfl
    · rw [bytesAt_length]
      exact hp.i_s.symm.sep (contains_offset (by omega) (by omega)) c₀
    · omega
  have hst : stateAt s₂.mem (inn s₀) = stateAt s.mem (scr s₀ + BitVec.ofNat 64 208) := by
    refine stateAt_eq_of_bytes fun i hi => ?_
    rw [m₂, writeBytes_other _ _ _ (by rw [bytesAt_length]; bv_omega), m₁,
      writeBytes_at _ _ _ (by rw [bytesAt_length]; omega) (by rw [bytesAt_length]; omega),
      bytesAt_getD' _ _ (by omega)]
  have hfr : Frame [inR s₀] s.mem s₂.mem := by
    rw [m₂, m₁]
    refine (writeBytes_frame (R := inR s₀) _ _ _ ?_).trans (writeBytes_frame (R := inR s₀) _ _ _ ?_)
    · rw [bytesAt_length]; exact c₀
    · rw [bytesAt_length]; exact contains_offset (by omega) (by omega)
  refine ⟨by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁], ?_, ?_, ?_, ?_,
    fun r hr => ?_, by rw [hm, hst], by rw [hm, hbuf], by rw [hm]; exact hfr⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), k₂ _ (by decide), hdi]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), k₂ _ (by decide), hcx]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, sx96]
  · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), k₂ _ (by decide), hcx, sx176]
  · have : r ≠ .rax ∧ r ≠ .rsi ∧ r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₅.other _ this.2.2, u₄.other _ this.2.2, u₃.other _ this.2.1, k₂ _ this.1]

/-! ## Correctness -/

theorem xorPad_length (k : List Byte) (p : Byte) : (xorPad k p).length = k.length := by
  simp [xorPad]

/-- A state holding the outer hash value and a 32-byte digest represents
`(K₀ ⊕ opad) ‖ digest`. -/
theorem repr_outer {k0 d : List Byte} (hk : k0.length = 64) (hd : d.length = 32) {m : Mem} {p : Addr}
    (hst : stateAt m p = Spec.Sha256.compressList Spec.Sha256.H0 (xorPad k0 opad) 1)
    (hb : bytesAt m (p + 32) 32 = d) : Repr m p (xorPad k0 opad ++ d) := by
  have hl : (xorPad k0 opad ++ d).length = 96 := by simp [xorPad_length, hk, hd]
  refine ⟨?_, ?_⟩
  · rw [hl, show 96 / 64 = 1 from rfl, compressList_append (by rw [xorPad_length, hk]), hst]
  · rw [hl, show 96 % 64 = 32 from rfl, show 64 * (96 / 64) = 64 from rfl,
      List.drop_left' (by rw [xorPad_length, hk]), hb]

/-- `scratch[208..240)` is not written by the called finalizations. -/
theorem not_finW {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) :
    ∀ r ∈ finW s₀ ++ [stkR s₀], ¬ r.Contains (scr s₀ + BitVec.ofNat 64 208 + BitVec.ofNat 64 i) 1 := by
  have hs : (scR s₀).Contains (scr s₀ + BitVec.ofNat 64 208 + BitVec.ofNat 64 i) 1 := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact contains_offset (by omega) (by omega)
  intro r hr
  simp only [finW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact fun hc => hp.i_s _ hc hs
  · simp only [Region.Contains]; bv_omega
  · simp only [Region.Contains]; bv_omega
  · exact fun hc => hp.stk_s _ hc hs

theorem correct {f : Callee} (hf : f.Ok)
    (hm : (Impl.Sha256.X86_64.Stream.finalize f).allInstrs (fun i => !loadsMxcsr i) = true) (name : String)
    {s₀ : State} (hp : Pre s₀) :
    WP isa (finalize f name) s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Hmac.finalizeSha256X86_64.post s₀ s' := by
  unfold finalize
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have sp₁ := h₁.cs .rsp (by decide)
  refine WP.seq (fin_ok hf hm name hp h₁.rd h₁.wr h₁.rdi h₁.rcx h₁.rdx sp₁
    fun s₂ rd₂ wr₂ abi₂ fr₂ di₂ cx₂ post₂ => ?_)
  have sp₂ : s₂.gpr .rsp = s₀.gpr .rsp := (abi₂ .rsp (by decide)).trans sp₁
  refine WP.seq (WP.mono (load_ok hp (s := s₂) (wr₂.trans h₁.wr) di₂ cx₂) fun s₃ h₃ => ?_)
  have sp₃ : s₃.gpr .rsp = s₀.gpr .rsp := (h₃.cs .rsp (by decide)).trans sp₂
  refine fin_ok hf hm name hp (h₃.rd.trans (rd₂.trans h₁.rd)) (h₃.wr.trans (wr₂.trans h₁.wr)) h₃.rdi h₃.rcx h₃.rdx sp₃
    fun s₄ rd₄ wr₄ abi₄ fr₄ _ _ post₄ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [abi₄ r hr, h₃.cs r hr, abi₂ r hr, h₁.cs r hr]
  · -- The return address.
    have fr₁ : Frame [scR s₀] s₀.mem s₁.mem := by
      rw [h₁.mem]; refine writeBytes_frame _ _ _ ?_
      rw [bytesAt_length]; exact contains_offset (by omega) (by omega)
    have ret : (retR s₀).Contains (s₀.gpr .rsp) (64 / 8) := Region.contains_self _ _
    have dW : ∀ r ∈ finW s₀ ++ [stkR s₀], (retR s₀).Disjoint r := by
      intro r hr
      simp only [finW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.ret_i
      · exact hp.ret_s.sub_right (sub176 s₀)
      · exact hp.ret_s.sub_right (sub160 s₀)
      · exact ret_stk s₀
    rw [fr₄.readW ret dW (by decide), h₃.frame.readW ret (by simpa using hp.ret_i) (by decide),
      fr₂.readW ret dW (by decide), fr₁.readW ret (by simpa using hp.ret_s) (by decide)]
  · intro k0 text hk hin hcnt hout
    -- The inner digest.
    have hin₁ : Repr s₁.mem (inn s₀) (xorPad k0 ipad ++ text) := by
      refine Proof.Sha256.Stream.repr_congr (fun i hi => ?_) hin
      rw [h₁.mem]
      refine Frame.bytes (R := inR s₀) (writeBytes_frame (R := scR s₀) _ _ _ ?_) ?_ (by simp) hi
      · rw [bytesAt_length]; exact contains_offset (by omega) (by omega)
      · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.i_s
    have hd := post₂ _ hin₁ (by rw [h₁.rsi, hcnt, List.length_append, xorPad_length, hk])
    -- The outer state.
    have hst : stateAt s₃.mem (inn s₀) = Spec.Sha256.compressList Spec.Sha256.H0 (xorPad k0 opad) 1 := by
      rw [h₃.state]
      have e : stateAt s₂.mem (scr s₀ + BitVec.ofNat 64 208) = stateAt s₀.mem (out s₀) := by
        refine stateAt_eq_of_bytes fun i hi => ?_
        rw [fr₂ _ (not_finW hp hi), h₁.mem,
          writeBytes_at _ _ _ (by rw [bytesAt_length]; omega) (by rw [bytesAt_length]; omega),
          bytesAt_getD' _ _ (by omega)]
      rw [e, hout.1, xorPad_length, hk]
    have hrepr := repr_outer hk (by rw [bytesAt_length]) hst h₃.buf
    have := post₄ _ hrepr (by rw [h₃.rsi, List.length_append, xorPad_length, hk, bytesAt_length])
    rw [hd] at this
    simpa [hmacBlockKey, sha256] using this

/-! ## Constant time

As for `init`, two runs are related (`RelCT`): correctness determines the
registers each piece between the calls uses from the public arguments, the
taint analysis proves each piece constant time, and the calls are constant
time by the finalization's own proof. -/

/-- The registers that hold public values across the calls. -/
structure Base (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rdi : s.gpr .rdi = inn s₀
  rcx : s.gpr .rcx = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp

/-- Before a call of the finalization, of `v` bytes. -/
def Args (s₀ : State) (v : BitVec 64) (s : State) : Prop :=
  Base s₀ s ∧ s.gpr .rdx = scr s₀ + 176 ∧ s.gpr .rsi = v

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

section
variable {f : Callee} (hf : f.Ok)
  (hm : (Impl.Sha256.X86_64.Stream.finalize f).allInstrs (fun i => !loadsMxcsr i) = true) (name : String)
  {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hf hm hp hp' hq

/-- A call of the finalization, the same in both runs. -/
theorem fin_rel {v : BitVec 64} :
    RelCT isa (fun s s' => Args s₀ v s ∧ Args s₀' v s') (sha256Finalize f name)
      fun s s' => Base s₀ s ∧ Base s₀' s' := by
  have ok : ∀ {σ : State}, Pre σ → ∀ {s : State}, Args σ v s → WP isa (sha256Finalize f name) s (Base σ) :=
    fun {σ} hp {s} h => fin_ok hf hm name hp h.1.rd h.1.wr h.1.rdi h.1.rcx h.2.1 h.1.rsp fun _ rd wr cs _ di cx _ =>
      ⟨rd.trans h.1.rd, wr.trans h.1.wr, di, cx, (cs _ (by decide)).trans h.1.rsp⟩
  refine ((RelCT.callEx (finK_ok hf hm)
    (Proof.Sha256.X86_64.Stream.Finalize.constantTime hf) fun s s' ⟨h, h'⟩ => ?_).wp
    fun _ _ h => ⟨ok hp h.1, ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨p, c, w⟩ := fin_hyps hp h.1.rd h.1.wr h.1.rdi h.1.rcx h.2.1 h.1.rsp
  obtain ⟨p', c', w'⟩ := fin_hyps hp' h'.1.rd h'.1.wr h'.1.rdi h'.1.rcx h'.2.1 h'.1.rsp
  refine ⟨_, _, _, _, p, p', ?_, c, w, c', w', by rw [h.1.rsp, h'.1.rsp]; exact hq.rsp⟩
  simp only [finK, Proof.Sha256.finalizeX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp)]
  exact ⟨by rw [h.1.rdi, h'.1.rdi]; exact hq.rdi, by rw [h.2.2, h'.2.2],
    by rw [h.2.1, h'.2.1, show scr s₀ = scr s₀' from hq.rcx],
    by rw [h.1.rcx, h'.1.rcx]; exact hq.rcx, by rw [h.1.rsp, h'.1.rsp, hq.rsp]⟩

theorem finalize_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (finalize f name) fun _ _ => True := by
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀')
      (.block (saveOuter ++ [.mov .rsi (.reg .rdx), .mov .rdx (.reg .rcx), .alu .add .rdx (.imm 176)]))
      fun s s' => Args s₀ (s₀.gpr .rdx) s ∧ Args s₀' (s₀.gpr .rdx) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.rsp) (by taint_decide)).wp (F₁ := Saved s₀) (F₂ := Saved s₀')
      fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h)
      fun _ _ h => ⟨⟨⟨h.2.1.rd, h.2.1.wr, h.2.1.rdi, h.2.1.rcx, h.2.1.cs _ (by decide)⟩, h.2.1.rdx, h.2.1.rsi⟩,
        ⟨⟨h.2.2.rd, h.2.2.wr, h.2.2.rdi, h.2.2.rcx, h.2.2.cs _ (by decide)⟩, h.2.2.rdx,
          by rw [h.2.2.rsi, hq.rdx]⟩⟩
  have ld : ∀ {σ : State}, Pre σ → ∀ {s : State}, Base σ s →
      WP isa (.block (loadOuter ++ [.mov32 .rsi (.imm 96), .mov .rdx (.reg .rcx), .alu .add .rdx (.imm 176)]))
        s (Args σ (BitVec.ofNat 64 (64 + 32))) :=
    fun {σ} hp {s} h => WP.mono (load_ok hp h.wr h.rdi h.rcx) fun _ l =>
      ⟨⟨l.rd.trans h.rd, l.wr.trans h.wr, l.rdi, l.rcx, (l.cs _ (by decide)).trans h.rsp⟩, l.rdx, l.rsi⟩
  have mid : RelCT isa (fun s s' => Base s₀ s ∧ Base s₀' s')
      (.block (loadOuter ++ [.mov32 .rsi (.imm 96), .mov .rdx (.reg .rcx), .alu .add .rdx (.imm 176)]))
      fun s s' => Args s₀ (BitVec.ofNat 64 (64 + 32)) s ∧ Args s₀' (BitVec.ofNat 64 (64 + 32)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rcx, .rsp])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.rdi, h'.rdi]; exact hq.rdi
        · rw [h.rcx, h'.rcx]; exact hq.rcx
        · rw [h.rsp, h'.rsp]; exact hq.rsp) (by taint_decide)).wp
      fun _ _ h => ⟨ld hp h.1, ld hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  exact pro.seq ((fin_rel hf hm name hp hp' hq).seq (mid.seq ((fin_rel hf hm name hp hp' hq).mono
    (fun _ _ h => h) fun _ _ _ => trivial)))

end

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 96⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x3000, 240⟩]

theorem finalize_ok {f : Callee} (hf : f.Ok)
    (hm : (Impl.Sha256.X86_64.Stream.finalize f).allInstrs (fun i => !loadsMxcsr i) = true)
    (name : String) (s : State) (hs : Proof.Hmac.finalizeSha256X86_64.pre s) :
    ∃ t s', Exec isa (finalize f name) s t s' ∧ abiPreserved s s' ∧
      Proof.Hmac.finalizeSha256X86_64.post s s' := by
  have hm' : (finalize f name).allInstrs (fun i => !loadsMxcsr i) = true := by
    simp only [finalize, sha256Finalize, Code.allInstrs, hm, Bool.and_true]
    decide +kernel
  obtain ⟨t, s', he, h⟩ := correct hf hm name (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec hm' he h.1, h.2⟩

theorem finalize_ct {f : Callee} (hf : f.Ok)
    (hm : (Impl.Sha256.X86_64.Stream.finalize f).allInstrs (fun i => !loadsMxcsr i) = true)
    (name : String) :
    ConstantTime isa Proof.Hmac.finalizeSha256X86_64.pre Proof.Hmac.finalizeSha256X86_64.pub
      (finalize f name) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpub
  exact (finalize_rel hf hm name (pre_of h₁) (pre_of h₂) ⟨p1, p2, p3, p4, p5⟩ _ _ _ _ _ _ ⟨rfl, rfl⟩
    e₁ e₂).1

/-- `finalize`, calling the SHA-256 finalization `name` made with any
compression function `f`. -/
theorem finalize_verified {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !loadsMxcsr i) = true) (name : String) :
    Verified X86_64.target (finalize f name) (Spec.Hmac.finalizeSha256Contract X86_64.abi 16) :=
  have hm' : (Impl.Sha256.X86_64.Stream.finalize f).allInstrs (fun i => !loadsMxcsr i) = true := by
    simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.Sha256.X86_64.Stream.finalizeBody,
      Impl.Sha256.X86_64.Stream.compressAt, Code.allInstrs, hm, Bool.true_and]
    decide +kernel
  Verified.of_correct (finalize_ok hf hm' name) (finalize_ct hf hm' name) (by
    sig_implies [Spec.Hmac.finalizeSha256Contract, Spec.Hmac.finalizeSha256Sig,
      Proof.Hmac.finalizeSha256X86_64, X86_64.abi, X86_64.argRegs] [sat] using sat)

theorem finalize_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true)
    (name : String) :
    (finalize f name).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finalize, sha256Finalize, Code.all,
    Proof.Sha256.X86_64.Shared.finalize_spSafe h, Bool.and_true]
  decide +kernel

end VG.Proof.Hmac.X86_64.Finalize
