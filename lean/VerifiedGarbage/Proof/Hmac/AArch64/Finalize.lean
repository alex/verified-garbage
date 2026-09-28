import VerifiedGarbage.Proof.Hmac.AArch64.Common
import VerifiedGarbage.Proof.Hmac.X86_64.Finalize
import VerifiedGarbage.Spec.Hmac.AArch64

/-!
# HMAC-SHA-256 on AArch64: `finalize`

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`VG.Proof.Hmac.X86_64.Finalize`). The two SHA-256
finalizations are the inlined `vg_sha256_finalize`, used as a black box
through its proof, together with the fact that it never writes `x16` or
`x17` (`WP.inline`).
-/

namespace VG.Proof.Hmac.AArch64.Finalize

open VG VG.AArch64 VG.Impl.Hmac.AArch64
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Proof.Hmac.AArch64
open VG.Proof.Hmac.X86_64 (writeBytes_at writeBytes_other bytesAt_getD' bytesAt_length
  bytesAt_writeBytes_self bytesAt_writeBytes_sep stateAt_eq_of_bytes)
open VG.Proof.Hmac.X86_64.Finalize (xorPad_length repr_outer)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Sha256.AArch64 (contains_offset sub_offset)
open VG.Proof.Sha256.AArch64.Stream (Upd wp_mov wp_movz wp_addImm frame_bytes)
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
/-- Where the inlined finalizations may write. -/
abbrev finW : List Region := [inR s₀, ⟨scr s₀ + 176, 32⟩, ⟨scr s₀, 160⟩]

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [outR s₀]
  wr : s₀.wr = [inR s₀, scR s₀]
  i_o : (inR s₀).Disjoint (outR s₀)
  i_s : (inR s₀).Disjoint (scR s₀)
  o_s : (outR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Spec.Hmac.finalizeSha256AArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-! ## The inlined finalization -/

theorem fin_exec : ∀ s, Spec.Sha256.finalizeAArch64.pre s → ∃ t s',
    Exec isa Impl.Sha256.AArch64.Stream.finalize s t s' ∧ abiPreserved s s' ∧
      Spec.Sha256.finalizeAArch64.post s s' := by
  intro s hs
  obtain ⟨t, s', he, h₁, h₂⟩ :=
    Proof.Sha256.AArch64.Stream.Finalize.correct (Proof.Sha256.AArch64.Stream.Finalize.pre_of hs)
  exact ⟨t, s', he, h₁, h₂⟩

theorem x16_ok : ∀ i ∈ instrs Impl.Sha256.AArch64.Stream.finalize,
    VG.AArch64.dstOf i ≠ some .x16 := by
  have : (Impl.Sha256.AArch64.Stream.finalize.allInstrs fun i => VG.AArch64.dstOf i != some .x16) =
      true := by decide +kernel
  rw [Code.allInstrs_eq] at this
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem x17_ok : ∀ i ∈ instrs Impl.Sha256.AArch64.Stream.finalize,
    VG.AArch64.dstOf i ≠ some .x17 := by
  have : (Impl.Sha256.AArch64.Stream.finalize.allInstrs fun i => VG.AArch64.dstOf i != some .x17) =
      true := by decide +kernel
  rw [Code.allInstrs_eq] at this
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem sub176 (s₀ : State) : Region.Sub ⟨scr s₀ + 176, 32⟩ (scR s₀) :=
  sub_offset (off := 176) (by omega) (by omega)

theorem sub160 (s₀ : State) : Region.Sub ⟨scr s₀, 160⟩ (scR s₀) := Region.sub_prefix (by omega)

/-- The inlined `vg_sha256_finalize` on the inner state, with its digest at
`scratch[176..208)` and `scratch[0..160)` as its scratch space. -/
theorem fin_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (h0 : s.gpr .x0 = inn s₀) (h3 : s.gpr .x3 = scr s₀) (h2 : s.gpr .x2 = scr s₀ + 176)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → abiPreserved s s' → Frame (finW s₀) s.mem s'.mem →
      s'.gpr .x16 = s.gpr .x16 → s'.gpr .x17 = s.gpr .x17 →
      (∀ m, Repr s.mem (inn s₀) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
        bytesAt s'.mem (scr s₀ + 176) 32 = Spec.Sha256.hash m) → Q s') :
    WP isa Impl.Sha256.AArch64.Stream.finalize s Q := by
  refine WP.inline (k := Spec.Sha256.finalizeAArch64) fin_exec (rd := []) (wr := finW s₀) ?_ ?_ ?_ ?_
  · refine ⟨rfl, by simp [h0, h3, h2], ?_, ?_, ?_⟩ <;>
      simp only [State.withRegions_gpr, h0, h3, h2]
    · exact hp.i_s.sub_right (sub176 s₀)
    · exact hp.i_s.sub_right (sub160 s₀)
    · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
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
  · intro s' h₁ h₂ h₃ h₄ hg hpost
    simp only [Spec.Sha256.finalizeAArch64, State.withRegions_gpr, State.withRegions_mem, h0, h2]
      at hpost
    exact hQ s' h₁ h₂ h₃ h₄ (hg _ x16_ok) (hg _ x17_ok) hpost

/-! ## Saving the outer hash value -/

/-- After the prologue: the outer hash value's bytes are in `scratch[208..240)`. -/
structure Saved (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x0 : s.gpr .x0 = inn s₀
  x3 : s.gpr .x3 = scr s₀
  x16 : s.gpr .x16 = inn s₀
  x17 : s.gpr .x17 = scr s₀
  x1 : s.gpr .x1 = s₀.gpr .x2
  x2 : s.gpr .x2 = scr s₀ + 176
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem (scr s₀ + BitVec.ofNat 64 208) (bytesAt s₀.mem (out s₀) 32)

theorem not_pres {r : Reg} (hr : r ∈ preserved) :
    r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x9 ∧ r ≠ .x16 ∧ r ≠ .x17 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block ([mov .x16 .x0, mov .x17 .x3] ++ saveOuter ++ [mov .x1 .x2, .addImm .x .x2 .x3 176]))
      s₀ (Saved s₀) := by
  unfold saveOuter
  have h0 : out s₀ + BitVec.ofNat 64 0 = out s₀ := by simp
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => ?_
  have e1 : s₂.gpr .x1 = out s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have e3 : s₂.gpr .x3 = scr s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr]
  have m₂ : s₂.mem = s₀.mem := by rw [u₂.mem, u₁.mem]
  refine copy32_ok (by decide) (by decide) 0 208 8 ⟨rfl, rfl⟩ ⟨by omega, by omega⟩ _ s₂ _
    (fun k hk => ?_) (fun k hk => ?_) ?_
    fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => wp_mov fun s₄ u₄ => wp_addImm (imm := 176) (by omega) fun s₅ u₅ =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [e1, h0, rd₂, wr₂]
    exact ⟨outR s₀, by simp [hp.rd], contains_offset (by omega) (by omega)⟩
  · rw [e3, wr₂]
    refine ⟨scR s₀, by simp [hp.wr], ?_⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact contains_offset (by omega) (by omega)
  · rw [e1, e3, h0]
    exact hp.o_s.sep (a := out s₀) (n := 32) (by simp [Region.Contains]) (contains_offset (by omega) (by omega))
  · rw [u₅.rd, u₄.rd, rd₃, rd₂]
  · rw [u₅.wr, u₄.wr, wr₃, wr₂]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), e3]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide),
      u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.gpr, g₃ _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₅.gpr, u₄.other _ (by decide), g₃ _ (by decide), e3]; rfl
  · have := not_pres hr
    rw [u₅.other _ this.2.2.1, u₄.other _ this.2.1, g₃ _ this.2.2.2.2.1, u₂.other _ this.2.2.2.2.2.2,
      u₁.other _ this.2.2.2.2.2.1]
  · rw [u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp]
  · rw [u₅.mem, u₄.mem, m₃, m₂, e1, e3, h0]

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
    (h16 : s.gpr .x16 = inn s₀) (h17 : s.gpr .x17 = scr s₀) :
    WP isa (.block (loadOuter ++ [mov .x0 .x16, .movz .x .x1 96 0, .addImm .x .x2 .x17 176, mov .x3 .x17]))
      s (Loaded s₀ s) := by
  unfold loadOuter
  rw [List.append_assoc]
  have hin : ∀ {o k : Nat}, o + k ≤ 240 → InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofNat 64 o) k :=
    fun h => ⟨scR s₀, by simp [hwr, hp.wr], contains_offset h (by omega)⟩
  have hout : ∀ {o k : Nat}, o + k ≤ 96 → InRegions s.wr (inn s₀ + BitVec.ofNat 64 o) k :=
    fun h => ⟨inR s₀, by simp [hwr, hp.wr], contains_offset h (by omega)⟩
  have add : ∀ (p : Addr) (a b : Nat), p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) :=
    fun p a b => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine copy32_ok (src := .x17) (dst := .x16) (by decide) (by decide) 208 0 8 ⟨rfl, rfl⟩
    ⟨by omega, by omega⟩ _ s _ ?_ ?_ ?_ fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · intro k hk; rw [h17, add]; exact hin (by omega)
  · intro k hk; rw [h16, add]; exact hout (by omega)
  · rw [h17, h16]
    exact hp.i_s.symm.sep (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  have e₁ : s₁.gpr .x17 = scr s₀ := by rw [g₁ _ (by decide), h17]
  have d₁ : s₁.gpr .x16 = inn s₀ := by rw [g₁ _ (by decide), h16]
  refine copy64_ok (src := .x17) (dst := .x16) (by decide) (by decide) 176 32 4 ⟨rfl, rfl⟩
    ⟨by omega, by omega⟩ _ s₁ _ ?_ ?_ ?_ fun s₂ g₂ rd₂ wr₂ sp₂ m₂ =>
      wp_mov fun s₃ u₃ => wp_movz fun s₄ u₄ => wp_addImm (imm := 176) (by omega) fun s₅ u₅ =>
        wp_mov fun s₆ u₆ => WP.block_nil ?_
  · intro k hk; rw [e₁, add, rd₁, wr₁]; exact hin (by omega)
  · intro k hk; rw [d₁, add, wr₁]; exact hout (by omega)
  · rw [e₁, d₁]
    exact hp.i_s.symm.sep (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  rw [h17, h16, show inn s₀ + BitVec.ofNat 64 0 = inn s₀ by simp] at m₁
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
  refine ⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁],
    ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, sp₁],
    by rw [hm, hst], by rw [hm, hbuf], by rw [hm]; exact hfr⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, k₂ _ (by decide), h16]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), k₂ _ (by decide), h17]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, sw96]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), k₂ _ (by decide), h17]
    rfl
  · have := not_pres hr
    rw [u₆.other _ this.2.2.2.1, u₅.other _ this.2.2.1, u₄.other _ this.2.1, u₃.other _ this.1,
      k₂ _ this.2.2.2.2.1]

/-! ## Correctness -/

/-- `scratch[208..240)` is not written by the inlined finalizations. -/
theorem not_finW {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) :
    ∀ r ∈ finW s₀, ¬ r.Contains (scr s₀ + BitVec.ofNat 64 208 + BitVec.ofNat 64 i) 1 := by
  have hs : (scR s₀).Contains (scr s₀ + BitVec.ofNat 64 208 + BitVec.ofNat 64 i) 1 := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact contains_offset (by omega) (by omega)
  intro r hr
  simp only [finW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact fun hc => hp.i_s _ hc hs
  · simp only [Region.Contains]; bv_omega
  · simp only [Region.Contains]; bv_omega

set_option maxHeartbeats 1000000 in
theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ Spec.Hmac.finalizeSha256AArch64.post s₀ s' := by
  unfold finalize
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (fin_ok hp h₁.rd h₁.wr h₁.x0 h₁.x3 h₁.x2
    fun s₂ rd₂ wr₂ abi₂ fr₂ x16₂ x17₂ post₂ => ?_)
  refine WP.seq (WP.mono (load_ok hp (s := s₂) (wr₂.trans h₁.wr) (x16₂.trans h₁.x16)
    (x17₂.trans h₁.x17)) fun s₃ h₃ => ?_)
  refine fin_ok hp (h₃.rd.trans (rd₂.trans h₁.rd)) (h₃.wr.trans (wr₂.trans h₁.wr)) h₃.x0 h₃.x3 h₃.x2
    fun s₄ rd₄ wr₄ abi₄ fr₄ _ _ post₄ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [abi₄.1 r hr, h₃.cs r hr, abi₂.1 r hr, h₁.cs r hr]
  · rw [abi₄.2, h₃.sp, abi₂.2, h₁.sp]
  · intro k0 text hk hin hcnt hout
    -- The inner digest.
    have hin₁ : Repr s₁.mem (inn s₀) (xorPad k0 ipad ++ text) := by
      refine Proof.Sha256.Stream.repr_congr (fun i hi => ?_) hin
      rw [h₁.mem]
      refine frame_bytes (R := inR s₀) (writeBytes_frame (R := scR s₀) _ _ _ ?_) ?_ (by simp) hi
      · rw [bytesAt_length]; exact contains_offset (by omega) (by omega)
      · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.i_s
    have hd := post₂ _ hin₁ (by rw [h₁.x1, hcnt, List.length_append, xorPad_length, hk])
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
    have := post₄ _ hrepr (by rw [h₃.x1, List.length_append, xorPad_length, hk, bytesAt_length])
    rw [hd] at this
    simpa [hmacBlockKey, sha256] using this

/-! ## `Verified` -/

/-- The initial taint: only the arguments are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : Spec.Hmac.finalizeSha256AArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4⟩ := hpub
  intro r hr
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 96⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x3000, 240⟩]

set_option maxHeartbeats 0 in
theorem finalize_verified : Verified AArch64.target finalize Spec.Hmac.finalizeSha256AArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) (fun _ _ _ _ hp => agree₀ hp)
      (by taint_decide)
  · refine ⟨sat, rfl, rfl, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat] at h₁ h₂
      bv_omega

end VG.Proof.Hmac.AArch64.Finalize
