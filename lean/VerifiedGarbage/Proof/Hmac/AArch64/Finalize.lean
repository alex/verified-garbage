import VerifiedGarbage.Proof.Hmac.AArch64.Common
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Spec.Hmac.Contract
import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC-SHA-256 on AArch64: `finalize`

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`VG.Proof.Hmac.X86_64.Finalize`). The two SHA-256
finalizations are calls of `vg_sha256_finalize`, used as a black box through
its proof (`WP.callF`), inside the frame saving `x30` (`WP.frameReg`).
-/

namespace VG.Proof.Hmac.AArch64.Finalize

open VG VG.AArch64 VG.Impl.Hmac.AArch64
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Proof.Hmac.AArch64
open VG.Proof.Hmac.Common (writeBytes_at writeBytes_other bytesAt_getD' bytesAt_length
  bytesAt_writeBytes_self bytesAt_writeBytes_sep stateAt_eq_of_bytes xorPad_length repr_outer)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Sha256.AArch64 (contains_offset sub_offset toNat_ofNat_lt)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_movz wp_addImm wp_str wp_ldr frame_bytes
  write_frame_bytes readW_writeW_save)
open VG.Spec.Sha256 (bytesAt stateAt Repr)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .x0
abbrev out : Addr := s₀.gpr .x1
abbrev scr : Addr := s₀.gpr .x3
abbrev inR : Region := ⟨inn s₀, 96⟩
abbrev outR : Region := ⟨out s₀, 96⟩
abbrev scR : Region := ⟨scr s₀, 240⟩
/-- Where the finalizations may write (besides their frames). -/
abbrev finW : List Region := [inR s₀, ⟨scr s₀ + 176, 32⟩, ⟨scr s₀, 160⟩]

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [outR s₀]
  wr : s₀.wr = [inR s₀, scR s₀]
  i_o : (inR s₀).Disjoint (outR s₀)
  i_s : (inR s₀).Disjoint (scR s₀)
  o_s : (outR s₀).Disjoint (scR s₀)

/-- The frame a call of `vg_sha256_finalize` pushes, below the stack pointer
`s` has, is disjoint from the buffers. -/
structure Stack (s : State) : Prop where
  sp16 : 16 ≤ s.sp.toNat
  i : (below s.sp 16).Disjoint (inR s)
  o : (below s.sp 16).Disjoint (outR s)
  s : (below s.sp 16).Disjoint (scR s)

/-- On entry: our frame and the callee's are in the 32 bytes below the stack
pointer, disjoint from the buffers. -/
structure Stack₀ (s₀ : State) : Prop where
  sp32 : 32 ≤ s₀.sp.toNat
  i : (below s₀.sp 32).Disjoint (inR s₀)
  o : (below s₀.sp 32).Disjoint (outR s₀)
  s : (below s₀.sp 32).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Hmac.finalizeSha256AArch64.pre s₀) : Pre s₀ ∧ Stack₀ s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩⟩

/-! ## The calls of `vg_sha256_finalize` -/

theorem fin_exec : ∀ s, Proof.Sha256.finalizeAArch64.pre s → ∃ t s',
    Exec isa Impl.Sha256.AArch64.Stream.finalize s t s' ∧ abiPreserved s s' ∧
      Proof.Sha256.finalizeAArch64.post s s' := by
  exact Proof.Sha256.AArch64.Stream.Finalize.finalize_verified.1

theorem fin_fdepth : Impl.Sha256.AArch64.Stream.finalize.fdepth = 1 := by lit_decide

theorem sub176 (s₀ : State) : Region.Sub ⟨scr s₀ + 176, 32⟩ (scR s₀) :=
  sub_offset (off := 176) (by omega_nat) (by omega_nat)

theorem sub160 (s₀ : State) : Region.Sub ⟨scr s₀, 160⟩ (scR s₀) := Region.sub_prefix (by omega_nat)

/-- A call of `vg_sha256_finalize` on the inner state, with its digest at
`scratch[176..208)` and `scratch[0..160)` as its scratch space. -/
theorem fin_ok {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {s : State} (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp)
    (h0 : s.gpr .x0 = inn s₀) (h3 : s.gpr .x3 = scr s₀) (h2 : s.gpr .x2 = scr s₀ + 176)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (finW s₀ ++ [below s₀.sp 16]) s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ m, Repr s.mem (inn s₀) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
        bytesAt s'.mem (scr s₀ + 176) 32 = Spec.Sha256.hash m) → Q s') :
    WP isa sha256Finalize s Q := by
  have c0 : s.callEntry.gpr .x0 = inn s₀ := (State.callEntry_gpr _ (by decide)).trans h0
  have c2 : s.callEntry.gpr .x2 = scr s₀ + 176 := (State.callEntry_gpr _ (by decide)).trans h2
  have c3 : s.callEntry.gpr .x3 = scr s₀ := (State.callEntry_gpr _ (by decide)).trans h3
  refine WP.callF (k := Proof.Sha256.finalizeAArch64) fin_exec (rd := []) (wr := finW s₀) ?_ ?_ ?_ ?_
    (by rw [fin_fdepth]; decide)
  · simp only [Proof.Sha256.finalizeAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c2, c3, hsp]
    refine ⟨trivial, trivial, ?_, ?_, ?_, hs.sp16, hs.i, ?_, ?_⟩
    · exact hp.i_s.sub_right (sub176 s₀)
    · exact hp.i_s.sub_right (sub160 s₀)
    · exact Offset.disjoint_base _ (d := 176) (by omega_nat) (by omega_nat)
    · exact hs.s.sub_right (sub176 s₀)
    · exact hs.s.sub_right (sub160 s₀)
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
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [Proof.Sha256.finalizeAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c2] at hpost
    rw [fin_fdepth, hsp] at h₄
    exact hQ s' h₁ h₂ h₃ h₄ hcs hpost

/-! ## Saving `x25`, `x26` and the outer hash value -/

/-- The memory after saving our caller's `x25` and `x26` in `scratch[160..176)`. -/
abbrev svMem (s₀ : State) : Mem :=
  (s₀.mem.writeW (scr s₀ + BitVec.ofNat 64 160) (s₀.gpr .x25)).writeW (scr s₀ + BitVec.ofNat 64 168)
    (s₀.gpr .x26)

/-- After the prologue: our caller's `x25` and `x26` are in `scratch[160..176)`,
and the outer hash value's bytes in `scratch[208..240)`. -/
structure Saved (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x0 : s.gpr .x0 = inn s₀
  x3 : s.gpr .x3 = scr s₀
  x25 : s.gpr .x25 = inn s₀
  x26 : s.gpr .x26 = scr s₀
  x1 : s.gpr .x1 = s₀.gpr .x2
  x2 : s.gpr .x2 = scr s₀ + 176
  cs : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes (svMem s₀) (scr s₀ + BitVec.ofNat 64 208) (bytesAt s₀.mem (out s₀) 32)

theorem not_pres {r : Reg} (hr : r ∈ preserved) :
    r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x9 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem svMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (svMem s₀) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_nat) (by omega_nat))).writeW
    (List.mem_singleton_self _) _ (contains_offset (by omega_nat) (by omega_nat))

theorem svMem_out {s₀ : State} (hp : Pre s₀) :
    bytesAt (svMem s₀) (out s₀) 32 = bytesAt s₀.mem (out s₀) 32 :=
  Proof.Sha256.Stream.bytesAt_congr fun i hi =>
    frame_bytes (svMem_frame s₀) (R := outR s₀) (by simpa using hp.o_s) (by simp) (show i < 96 by omega_nat)

/-- Everything the prologue writes is in the scratch space. -/
theorem Saved.frame {s₀ s : State} (h : Saved s₀ s) : Frame [scR s₀] s₀.mem s.mem := by
  rw [h.mem]
  refine (svMem_frame s₀).trans (writeBytes_frame _ _ _ ?_)
  rw [bytesAt_length]; exact contains_offset (by omega_nat) (by omega_nat)

theorem Saved.sv_eq {s₀ s : State} (h : Saved s₀ s) {o : Nat} (ho : 160 ≤ o ∧ o + 8 ≤ 176) :
    s.mem.readW (scr s₀ + BitVec.ofNat 64 o) 64 = (svMem s₀).readW (scr s₀ + BitVec.ofNat 64 o) 64 := by
  rw [h.mem]
  refine (writeBytes_frame (R := ⟨scr s₀ + BitVec.ofNat 64 208, 32⟩) _ _ _
    (by rw [bytesAt_length]; exact Region.contains_self _ _)).readW (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton]; rintro r rfl
  exact Offset.disjoint _ (Or.inl (by omega_nat)) (by omega_nat) (by omega_nat)

theorem Saved.sv25 {s₀ s : State} (h : Saved s₀ s) :
    s.mem.readW (scr s₀ + BitVec.ofNat 64 160) 64 = s₀.gpr .x25 := by
  rw [h.sv_eq (by omega_nat), svMem, readW_writeW_save _ _ _ (by omega_nat) (by omega_nat) (by omega_nat),
    Mem.readW_writeW_self64]

theorem Saved.sv26 {s₀ s : State} (h : Saved s₀ s) :
    s.mem.readW (scr s₀ + BitVec.ofNat 64 168) 64 = s₀.gpr .x26 := by
  rw [h.sv_eq (by omega_nat), svMem, Mem.readW_writeW_self64]

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (([.str .x .x25 .x3 160, .str .x .x26 .x3 168, mov .x25 .x0, mov .x26 .x3] : List Instr) ++ saveOuter ++
      [mov .x1 .x2, .addImm .x .x2 .x3 176])) s₀ (Saved s₀) := by
  unfold saveOuter
  have h0 : out s₀ + BitVec.ofNat 64 0 = out s₀ := by simp
  simp only [List.cons_append, List.nil_append]
  refine wp_str (a := scr s₀ + BitVec.ofNat 64 160) (by decide) rfl
    ⟨scR s₀, by simp [hp.wr], contains_offset (by omega_nat) (by omega_nat)⟩ fun sa ua => ?_
  refine wp_str (a := scr s₀ + BitVec.ofNat 64 168) (by decide) (by rw [ua.gpr])
    ⟨scR s₀, by simp [ua.wr, hp.wr], contains_offset (by omega_nat) (by omega_nat)⟩ fun sb ub => ?_
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => ?_
  have e1 : s₂.gpr .x1 = out s₀ := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), ub.gpr, ua.gpr]
  have e3 : s₂.gpr .x3 = scr s₀ := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), ub.gpr, ua.gpr]
  have rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd, ub.rd, ua.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, ub.wr, ua.wr]
  have m₂ : s₂.mem = svMem s₀ := by rw [u₂.mem, u₁.mem, ub.mem, ua.gpr, ua.mem]
  have k₂ : ∀ r, r ≠ .x25 → r ≠ .x26 → s₂.gpr r = s₀.gpr r := fun r a b => by
    rw [u₂.other _ b, u₁.other _ a, ub.gpr, ua.gpr]
  refine copy32_ok (by decide) (by decide) 0 208 8 ⟨rfl, rfl⟩ ⟨by omega_nat, by omega_nat⟩ _ s₂ _
    (fun k hk => ?_) (fun k hk => ?_) ?_
    fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => wp_mov fun s₄ u₄ => wp_addImm (imm := 176) (by omega_nat) fun s₅ u₅ =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr h25 h26 => ?_, ?_, ?_⟩
  · rw [e1, h0, rd₂, wr₂]
    exact ⟨outR s₀, by simp [hp.rd], contains_offset (by omega_nat) (by omega_nat)⟩
  · rw [e3, wr₂]
    refine ⟨scR s₀, by simp [hp.wr], ?_⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact contains_offset (by omega_nat) (by omega_nat)
  · rw [e1, e3, h0]
    exact hp.o_s.sep (a := out s₀) (n := 32) (by simp [Region.Contains]) (contains_offset (by omega_nat) (by omega_nat))
  · rw [u₅.rd, u₄.rd, rd₃, rd₂]
  · rw [u₅.wr, u₄.wr, wr₃, wr₂]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), k₂ _ (by decide) (by decide)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), e3]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide), u₁.gpr,
      ub.gpr, ua.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), u₂.gpr, u₁.other _ (by decide),
      ub.gpr, ua.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr, g₃ _ (by decide), k₂ _ (by decide) (by decide)]
  · rw [u₅.gpr, u₄.other _ (by decide), g₃ _ (by decide), e3]; rfl
  · have := not_pres hr
    rw [u₅.other _ this.2.2.1, u₄.other _ this.2.1, g₃ _ this.2.2.2.2, k₂ _ h25 h26]
  · rw [u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp, ub.sp, ua.sp]
  · rw [u₅.mem, u₄.mem, m₃, m₂, e1, e3, h0]
    exact congrArg _ (svMem_out hp)

/-! ## Loading the outer hash value and the inner digest -/

theorem sw96 : ((96 : BitVec 16).setWidth 64) = BitVec.ofNat 64 (64 + 32) := by decide

/-- After the middle block, from `s`: the inner state holds the hash value from
`scratch[208..240)` and, in its buffer, the digest from `scratch[176..208)`. -/
structure Loaded (s₀ s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  x0 : s'.gpr .x0 = inn s₀
  x3 : s'.gpr .x3 = scr s₀
  x1 : s'.gpr .x1 = BitVec.ofNat 64 (64 + 32)
  x2 : s'.gpr .x2 = scr s₀ + 176
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  state : stateAt s'.mem (inn s₀) = stateAt s.mem (scr s₀ + BitVec.ofNat 64 208)
  buf : bytesAt s'.mem (inn s₀ + 32) 32 = bytesAt s.mem (scr s₀ + 176) 32
  frame : Frame [inR s₀] s.mem s'.mem

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr)
    (h25 : s.gpr .x25 = inn s₀) (h26 : s.gpr .x26 = scr s₀) :
    WP isa (.block (loadOuter ++ [mov .x0 .x25, .movz .x .x1 96 0, .addImm .x .x2 .x26 176, mov .x3 .x26]))
      s (Loaded s₀ s) := by
  unfold loadOuter
  rw [List.append_assoc]
  have hin : ∀ {o k : Nat}, o + k ≤ 240 → InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofNat 64 o) k :=
    fun h => ⟨scR s₀, by simp [hwr, hp.wr], contains_offset h (by omega_nat)⟩
  have hout : ∀ {o k : Nat}, o + k ≤ 96 → InRegions s.wr (inn s₀ + BitVec.ofNat 64 o) k :=
    fun h => ⟨inR s₀, by simp [hwr, hp.wr], contains_offset h (by omega_nat)⟩
  have add : ∀ (p : Addr) (a b : Nat), p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) :=
    fun p a b => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine copy32_ok (src := .x26) (dst := .x25) (by decide) (by decide) 208 0 8 ⟨rfl, rfl⟩
    ⟨by omega_nat, by omega_nat⟩ _ s _ ?_ ?_ ?_ fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · intro k hk; rw [h26, add]; exact hin (by omega_nat)
  · intro k hk; rw [h25, add]; exact hout (by omega_nat)
  · rw [h26, h25]
    exact hp.i_s.symm.sep (contains_offset (by omega_nat) (by omega_nat)) (contains_offset (by omega_nat) (by omega_nat))
  have e₁ : s₁.gpr .x26 = scr s₀ := by rw [g₁ _ (by decide), h26]
  have d₁ : s₁.gpr .x25 = inn s₀ := by rw [g₁ _ (by decide), h25]
  refine copy64_ok (src := .x26) (dst := .x25) (by decide) (by decide) 176 32 4 ⟨rfl, rfl⟩
    ⟨by omega_nat, by omega_nat⟩ _ s₁ _ ?_ ?_ ?_ fun s₂ g₂ rd₂ wr₂ sp₂ m₂ =>
      wp_mov fun s₃ u₃ => wp_movz fun s₄ u₄ => wp_addImm (imm := 176) (by omega_nat) fun s₅ u₅ =>
        wp_mov fun s₆ u₆ => WP.block_nil ?_
  · intro k hk; rw [e₁, add, rd₁, wr₁]; exact hin (by omega_nat)
  · intro k hk; rw [d₁, add, wr₁]; exact hout (by omega_nat)
  · rw [e₁, d₁]
    exact hp.i_s.symm.sep (contains_offset (by omega_nat) (by omega_nat)) (contains_offset (by omega_nat) (by omega_nat))
  rw [h26, h25, show inn s₀ + BitVec.ofNat 64 0 = inn s₀ by simp] at m₁
  rw [e₁, d₁] at m₂
  have c₀ : (inR s₀).Contains (inn s₀) 32 := by simp [Region.Contains]
  have hm : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have k₂ : ∀ r, r ≠ .x9 → s₂.gpr r = s.gpr r := fun r h => by rw [g₂ r h, g₁ r h]
  have hbuf : bytesAt s₂.mem (inn s₀ + 32) 32 = bytesAt s.mem (scr s₀ + 176) 32 := by
    rw [m₂, show inn s₀ + 32 = inn s₀ + BitVec.ofNat 64 32 from rfl]
    have := bytesAt_writeBytes_self s₁.mem (inn s₀ + BitVec.ofNat 64 32)
      (bytesAt s₁.mem (scr s₀ + BitVec.ofNat 64 176) (8 * 4)) (by simp [bytesAt])
    rw [bytesAt_length] at this
    rw [this, m₁, bytesAt_writeBytes_sep]
    · rfl
    · rw [bytesAt_length]
      exact hp.i_s.symm.sep (contains_offset (by omega_nat) (by omega_nat)) c₀
    · omega_nat
  have hst : stateAt s₂.mem (inn s₀) = stateAt s.mem (scr s₀ + BitVec.ofNat 64 208) := by
    refine stateAt_eq_of_bytes fun i hi => ?_
    rw [m₂, writeBytes_other _ _ _ (by
        rw [bytesAt_length, Offset.lt_iff _ _ (by omega_nat), Mem.sub_ofNat_toNat _ (by omega_nat)]; omega_nat), m₁,
      writeBytes_at _ _ _ (by rw [bytesAt_length]; omega_nat) (by rw [bytesAt_length]; omega_nat),
      bytesAt_getD' _ _ (by omega_nat)]
  have hfr : Frame [inR s₀] s.mem s₂.mem := by
    rw [m₂, m₁]
    refine (writeBytes_frame (R := inR s₀) _ _ _ ?_).trans (writeBytes_frame (R := inR s₀) _ _ _ ?_)
    · rw [bytesAt_length]; exact c₀
    · rw [bytesAt_length]; exact contains_offset (by omega_nat) (by omega_nat)
  refine ⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁],
    ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, sp₁],
    by rw [hm, hst], by rw [hm, hbuf], by rw [hm]; exact hfr⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, k₂ _ (by decide), h25]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), k₂ _ (by decide), h26]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, sw96]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), k₂ _ (by decide), h26]
    rfl
  · have := not_pres hr
    rw [u₆.other _ this.2.2.2.1, u₅.other _ this.2.2.1, u₄.other _ this.2.1, u₃.other _ this.1,
      k₂ _ this.2.2.2.2]

/-! ## Correctness -/

/-- The calls of `vg_sha256_finalize` write outside `scratch[160..176)` and
`scratch[208..240)`. -/
theorem not_finW {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {o : Nat}
    (ho : (160 ≤ o ∧ o < 176) ∨ (208 ≤ o ∧ o < 240)) :
    ∀ r ∈ finW s₀ ++ [below s₀.sp 16], (⟨scr s₀ + BitVec.ofNat 64 o, 1⟩ : Region).Disjoint r := by
  have hsub : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, 1⟩ (scR s₀) := sub_offset (by omega_nat) (by omega_nat)
  have ht : (BitVec.ofNat 64 o).toNat = o := toNat_ofNat_lt (by omega_nat)
  intro r hr
  simp only [finW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.i_s.symm.sub_left hsub
  · exact Offset.disjoint _ (e := 176) (by omega_nat) (by omega_nat) (by omega_nat)
  · exact Offset.disjoint_base _ (by omega_nat) (by omega_nat)
  · exact hs.s.symm.sub_left hsub

/-- A byte of `scratch[160..176)` or `scratch[208..240)` survives a call. -/
theorem kept {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {m m' : Mem}
    (hf : Frame (finW s₀ ++ [below s₀.sp 16]) m m') {o : Nat}
    (ho : (160 ≤ o ∧ o < 176) ∨ (208 ≤ o ∧ o < 240)) :
    m' (scr s₀ + BitVec.ofNat 64 o) = m (scr s₀ + BitVec.ofNat 64 o) := by
  have := frame_bytes hf (not_finW hp hs ho) Nat.one_le_two_pow (i := 0) Nat.one_pos
  simpa using this

/-- A byte of `scratch[160..176)` or `scratch[208..240)` survives loading the
inner state. -/
theorem kept_load {s₀ : State} (hp : Pre s₀) {m m' : Mem} (hf : Frame [inR s₀] m m') {o : Nat}
    (ho : o < 240) : m' (scr s₀ + BitVec.ofNat 64 o) = m (scr s₀ + BitVec.ofNat 64 o) := by
  have hsub : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, 1⟩ (scR s₀) := sub_offset (by omega_nat) (by omega_nat)
  have := frame_bytes hf (R := ⟨scr s₀ + BitVec.ofNat 64 o, 1⟩)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.symm.sub_left hsub) Nat.one_le_two_pow
    (i := 0) Nat.one_pos
  simpa using this

/-- A saved register survives the calls and the load. -/
theorem sv_kept {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {m₁ m₂ m₃ m₄ : Mem}
    (f₂ : Frame (finW s₀ ++ [below s₀.sp 16]) m₁ m₂) (f₃ : Frame [inR s₀] m₂ m₃)
    (f₄ : Frame (finW s₀ ++ [below s₀.sp 16]) m₃ m₄) {o : Nat} (ho : o = 160 ∨ o = 168) :
    m₄.readW (scr s₀ + BitVec.ofNat 64 o) 64 = m₁.readW (scr s₀ + BitVec.ofNat 64 o) 64 := by
  simp only [Mem.readW]
  refine congrArg _ (Mem.read_congr fun i hi => ?_)
  have e : scr s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i = scr s₀ + BitVec.ofNat 64 (o + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hi' : i < 8 := hi
  rw [e, kept hp hs f₄ (by omega_nat), kept_load hp f₃ (by omega_nat), kept hp hs f₂ (by omega_nat)]

theorem sub16 (s : State) : Region.Sub ⟨s.sp - 16, 16⟩ (below s.sp 32) := below_frame s.sp 16 (by decide)

/-- `finalize` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) :
    WP isa finalizeMain s₀ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ Proof.Hmac.finalizeSha256AArch64.post s₀ s' := by
  unfold finalizeMain
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (fin_ok hp hs h₁.rd h₁.wr h₁.sp h₁.x0 h₁.x3 h₁.x2
    fun s₂ rd₂ wr₂ sp₂ fr₂ cs₂ post₂ => ?_)
  have x25₂ : s₂.gpr .x25 = inn s₀ := by rw [cs₂ _ (by decide) (by decide), h₁.x25]
  have x26₂ : s₂.gpr .x26 = scr s₀ := by rw [cs₂ _ (by decide) (by decide), h₁.x26]
  refine WP.seq (WP.mono (load_ok hp (s := s₂) (wr₂.trans h₁.wr) x25₂ x26₂) fun s₃ h₃ => ?_)
  refine WP.seq (fin_ok hp hs (h₃.rd.trans (rd₂.trans h₁.rd)) (h₃.wr.trans (wr₂.trans h₁.wr))
    (h₃.sp.trans (sp₂.trans h₁.sp)) h₃.x0 h₃.x3 h₃.x2
    fun s₄ rd₄ wr₄ sp₄ fr₄ cs₄ post₄ => ?_)
  -- Restoring `x25` and `x26`.
  have x26₄ : s₄.gpr .x26 = scr s₀ := by
    rw [cs₄ _ (by decide) (by decide), h₃.cs _ (by decide), x26₂]
  have hin : ∀ o, o + 8 ≤ 240 → InRegions (s₄.rd ++ s₄.wr) (scr s₀ + BitVec.ofNat 64 o) 8 := fun o h =>
    ⟨scR s₀, by simp [wr₄, h₃.wr, wr₂, h₁.wr, hp.wr], contains_offset h (by omega_nat)⟩
  have sv : ∀ o, o = 160 ∨ o = 168 → s₄.mem.readW (scr s₀ + BitVec.ofNat 64 o) 64 =
      s₁.mem.readW (scr s₀ + BitVec.ofNat 64 o) 64 :=
    fun o ho => sv_kept hp hs fr₂ h₃.frame fr₄ ho
  refine wp_ldr (a := scr s₀ + BitVec.ofNat 64 160) (by decide) (by rw [x26₄]) (hin 160 (by omega_nat))
    fun s₅ u₅ => ?_
  refine wp_ldr (a := scr s₀ + BitVec.ofNat 64 168) (by decide) (by rw [u₅.other _ (by decide), x26₄])
    (by rw [u₅.rd, u₅.wr]; exact hin 168 (by omega_nat)) fun s₆ u₆ => WP.block_nil ⟨fun r hr h30 => ?_,
      by rw [u₆.sp, u₅.sp, sp₄, h₃.sp, sp₂, h₁.sp], ?_⟩
  · by_cases h26 : r = .x26
    · subst h26; rw [u₆.gpr, u₅.mem, sv _ (.inr rfl), h₁.sv26]
    by_cases h25 : r = .x25
    · subst h25; rw [u₆.other _ (by decide), u₅.gpr, sv _ (.inl rfl), h₁.sv25]
    rw [u₆.other _ h26, u₅.other _ h25, cs₄ _ hr h30, h₃.cs _ hr, cs₂ _ hr h30, h₁.cs _ hr h25 h26]
  · intro k0 text hk hin hcnt hout
    -- The inner digest.
    have hin₁ : Repr s₁.mem (inn s₀) (xorPad k0 ipad ++ text) :=
      Proof.Sha256.Stream.repr_congr (fun i hi => frame_bytes h₁.frame (R := inR s₀)
        (by simpa using hp.i_s) (by simp) hi) hin
    have hd := post₂ _ hin₁ (by rw [h₁.x1, hcnt, List.length_append, xorPad_length, hk])
    -- The outer state.
    have hst : stateAt s₃.mem (inn s₀) = Spec.Sha256.compressList Spec.Sha256.H0 (xorPad k0 opad) 1 := by
      rw [h₃.state]
      have e : stateAt s₂.mem (scr s₀ + BitVec.ofNat 64 208) = stateAt s₀.mem (out s₀) := by
        refine stateAt_eq_of_bytes fun i hi => ?_
        rw [show scr s₀ + BitVec.ofNat 64 208 + BitVec.ofNat 64 i = scr s₀ + BitVec.ofNat 64 (208 + i) by
            rw [BitVec.add_assoc, ← BitVec.ofNat_add],
          kept hp hs fr₂ (by omega_nat), BitVec.ofNat_add,
          ← BitVec.add_assoc, h₁.mem,
          writeBytes_at _ _ _ (by rw [bytesAt_length]; omega_nat) (by rw [bytesAt_length]; omega_nat),
          bytesAt_getD' _ _ (by omega_nat)]
      rw [e, hout.1, xorPad_length, hk]
    have hrepr := repr_outer hk (by rw [bytesAt_length]) hst h₃.buf
    have := post₄ _ hrepr (by rw [h₃.x1, List.length_append, xorPad_length, hk, bytesAt_length])
    rw [hd] at this
    rw [u₆.mem, u₅.mem]
    simpa [hmacBlockKey, sha256] using this

/-- The state `finalizeMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct {s₀ : State} (hp : Pre s₀) (hs : Stack₀ s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Hmac.finalizeSha256AArch64.post s₀ s' := by
  have hsp := hs.sp32
  have hb : Region.Sub (below (s₀.sp - 16) 16) (below s₀.sp 32) := below_body s₀.sp 16
  have hsi : Stack (inner s₀) :=
    ⟨by show 16 ≤ (s₀.sp - BitVec.ofNat 64 16).toNat; rw [Offset.toNat_sub_ofNat]; omega_nat, hs.i.sub_left hb,
      hs.o.sub_left hb, hs.s.sub_left hb⟩
  refine WP.frameReg (by omega_nat) (fun R hR => ?_)
    (WP.mono (correctMain (s₀ := inner s₀) ⟨hp.rd, hp.wr, hp.i_o, hp.i_s, hp.o_s⟩ hsi)
      fun s' ⟨hk, _, hpost⟩ => ?_)
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.i.sub_left (sub16 s₀)
    · exact hs.s.sub_left (sub16 s₀)
  · refine ⟨⟨fun r hr => ?_, rfl⟩, fun k0 text hk hin hcnt hout => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have c : ∀ p : Addr, Region.Disjoint ⟨s₀.sp - 16, 16⟩ ⟨p, 96⟩ → ∀ l,
          Repr s₀.mem p l → Repr (inner s₀).mem p l := fun p hd l h =>
        Proof.Sha256.Stream.repr_congr (fun i hi => write_frame_bytes (R := ⟨p, 96⟩) hd (show 96 < 2 ^ 64 by omega_nat) hi) h
      have := hpost k0 text hk (c _ (hs.i.sub_left (sub16 s₀)) _ hin) hcnt
        (c _ (hs.o.sub_left (sub16 s₀)) _ hout)
      simpa [State.write] using this

/-! ## `Verified` -/

/-- The initial taint: only the arguments are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Hmac.finalizeSha256AArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 96⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x3000, 240⟩]

theorem finalize_correct (s : State) (hs : Proof.Hmac.finalizeSha256AArch64.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧
      Proof.Hmac.finalizeSha256AArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs).1 (pre_of hs).2
  exact ⟨t, s', he, h⟩

theorem finalize_ct : ConstantTime isa Proof.Hmac.finalizeSha256AArch64.pre
    Proof.Hmac.finalizeSha256AArch64.pub finalize := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => agree₀ hp)
    (by taint_decide)

/-- `finalizeSha256AArch64` with the 688 bytes of scratch of the shared
contract (sized for the x86-64 AVX2 compression function), of which the code
uses 240 (the MAC stays at byte 176). -/
def finalizeWide : Contract isa :=
  { Proof.Hmac.finalizeSha256AArch64 with
    pre := fun s =>
      let inner : Region := ⟨s.gpr .x0, 96⟩
      let outer : Region := ⟨s.gpr .x1, 96⟩
      let scratch : Region := ⟨s.gpr .x3, 688⟩
      let stack : Region := ⟨s.sp - 32, 32⟩
      s.rd = [outer] ∧ s.wr = [inner, scratch] ∧
      inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
      32 ≤ s.sp.toNat ∧ stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint scratch }

/-- The regions `finalizeSha256AArch64` lets the code write. -/
def narrowWr (s : State) : List Region := [⟨s.gpr .x0, 96⟩, ⟨s.gpr .x3, 240⟩]

theorem finalizeWide_pre (s : State) (h : finalizeWide.pre s) :
    Proof.Hmac.finalizeSha256AArch64.pre (s.withRegions s.rd (narrowWr s)) :=
  let ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := h
  ⟨h₁, rfl, h₃, h₄.sub_right (Region.sub_of_ble rfl), h₅.sub_right (Region.sub_of_ble rfl), h₆, h₇,
    h₈, h₉.sub_right (Region.sub_of_ble rfl)⟩

/-- A state satisfying `finalizeWide.pre`. -/
def wideSat : State := { sat with wr := [⟨0x1000, 96⟩, ⟨0x3000, 688⟩] }

theorem finalizeWide_implies :
    finalizeWide.Implies (Spec.Hmac.finalizeSha256Contract AArch64.abi 32) := by
  sig_implies [Spec.Hmac.finalizeSha256Contract, Spec.Hmac.finalizeSha256Sig, finalizeWide,
    Proof.Hmac.finalizeSha256AArch64, AArch64.abi, AArch64.argRegs] [wideSat, sat] using wideSat

/-- The proof is written against `finalizeSha256AArch64`, widened to the
shared contract's scratch. -/
theorem finalize_verified :
    Verified AArch64.target Impl.Hmac.AArch64.finalize (Spec.Hmac.finalizeSha256Contract AArch64.abi
      32) :=
  have hsat := finalizeWide_implies.sat_left
  (Verified.widen (Verified.of_correct finalize_correct finalize_ct
    (.refl (hsat.elim fun s hs => ⟨_, finalizeWide_pre s hs⟩)))
    narrowWr finalizeWide_pre
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat).of_implies finalizeWide_implies

end VG.Proof.Hmac.AArch64.Finalize
