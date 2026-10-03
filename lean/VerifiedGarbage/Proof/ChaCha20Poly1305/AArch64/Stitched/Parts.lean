import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Bulk
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Setup

/-!
# ChaCha20-Poly1305 on AArch64, stitched: the parts around the chunks

`polyIn` and `polyOut` (`Impl/ChaCha20Poly1305/AArch64/Stitched.lean`), and
`Inv0`: the invariant `Inv` without the registers `x22`–`x25`, which the
stitched code reuses.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_addImm wp_subImm wp_mov wp_movz wp_str wp_ldr)
open VG.Spec.Poly1305 (Repr bytesAt)

theorem write_write_x (s : State) (d : Reg) (a b : BitVec 64) :
    (s.write .x d a).write .x d b = s.write .x d b := by
  simp only [State.write]; congr 1; funext r; split <;> rfl

set_option simprocs false in
theorem const64_run (d : Reg) (c : BitVec 64) (s : State) :
    WP isa (.block (VG.Impl.Poly1305.AArch64.const64 d c)) s fun u => u = s.write .x d c := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Impl.Poly1305.AArch64.const64, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq, ite_true, Option.some.injEq,
    exists_eq_left', RegUpd.gpr_write_self, write_write_x, movz_movk64']

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_and {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .x d n m :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n &&& s.gpr m))
    (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_const64 {d : Reg} {c : BitVec 64}
    (k : ∀ s', Upd s s' d c → WP isa (.block is) s' Q) :
    WP isa (.block (VG.Impl.Poly1305.AArch64.const64 d c ++ is)) s Q :=
  WP.block_append ((const64_run d c s).mono fun u hu => by subst hu; exact k _ (Upd.write64 _ _ _))

end

/-- `Inv` without `x22`–`x25`. -/
structure Inv0 (s₀ : State) (s : State) : Prop where
  x21 : s.gpr .x21 = cx s₀
  un : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [workR s₀, dR s₀] s₀.mem s.mem

theorem Inv.inv0 {s₀ s : State} (h : Inv s₀ s) : Inv0 s₀ s :=
  ⟨h.x21, h.un, h.sp, h.rd, h.wr, h.saved, h.frame⟩

theorem Inv0.step {s₀ s s' : State} {rs : List Region} (h : Inv0 s₀ s) (hk : Kept rs s s')
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [workR s₀, dR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ 592 48).Disjoint r) : Inv0 s₀ s' where
  x21 := by rw [hk.cs _ (pres .x21) (pres30 .x21), h.x21]
  un r hr := by
    rw [hk.cs _ (untouched_preserved r hr).1 (untouched_preserved r hr).2, h.un r hr]
  sp := by rw [hk.sp, h.sp]
  rd := by rw [hk.rd, h.rd]
  wr := by rw [hk.wr, h.wr]
  saved := h.saved.frame hk.frame hsv
  frame := h.frame.trans (hk.frame.sub hsub)

theorem mac_inv0 {s₀ s s' : State} (h : Inv0 s₀ s) (hk : Kept (macR s₀) s s') : Inv0 s₀ s' :=
  h.step hk (fun r hr => by
      simp only [macR, List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩)
    (fun r hr => by
      simp only [macR, List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))

/-- The lengths block absorbed. -/
theorem absorbLengths_ok0 {s₀ : State} (hp : APre s₀) {s : State} (h : Inv0 s₀ s) :
    WP isa absorbLengths s fun s' => Inv0 s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (off (cx s₀) 656) 16) := by
  unfold absorbLengths
  refine WP.seq (WP.mono (ptrs3_ok (a := 448) (b := 656) (by lit_omega) (by lit_omega) 1 s)
    fun s₁ ⟨h0, h1, h2, k₁⟩ => ?_)
  rw [h.x21] at h0 h1
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, h.wr]
  have m₁ := k₁.mem_eq
  refine blocks_call (n := 1) h0 h1 h2 (by lit_omega)
    (sub_disj s₀ (b := 656) (m := 16 * 1) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by lit_omega)]; have := hp.wrap_c; omega)
    (covers2 hp wr₁ (a := 448) (n := 128) (b := 656) (m := 16 * 1) (by lit_omega) (by lit_omega))
    (covers1 hp wr₁ (a := 448) (n := 128) (by lit_omega)) fun s₂ k₂ repr₂ => ?_
  have hk : Kept (macR s₀) s s₂ :=
    (kept_mac0 k₁).trans (kept_mac (k := 448) (n := 128) (by lit_omega) (by lit_omega) k₂)
  exact ⟨mac_inv0 h hk, hk, fun key msg hr => by rw [← m₁]; exact repr₂ key msg (by rw [m₁]; exact hr)⟩

/-- The tag written to `ctx[out, out + 16)`. -/
theorem finalizeTo_ok0 {s₀ : State} (hp : APre s₀) {s : State} (h : Inv0 s₀ s) {out : Nat}
    (hout : out + 16 ≤ 448 ∨ (640 ≤ out ∧ out + 16 ≤ 656)) :
    WP isa (finalizeTo out) s fun s' => Kept [sub s₀ 448 128, sub s₀ out 16] s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        bytesAt s'.mem (off (cx s₀) out) 16 = Spec.Poly1305.mac key msg := by
  unfold finalizeTo
  refine WP.seq (WP.mono (fptrs_ok (out := out) (by lit_omega) s) fun s₁ ⟨h0, h1, h2, k₁⟩ => ?_)
  rw [h.x21] at h0 h2
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, h.wr]
  have m₁ := k₁.mem_eq
  have ho : out + 16 ≤ 1024 := by omega
  refine finalize_call h0 h1 h2 (sub_disj s₀ (by lit_omega) (by lit_omega) ho)
    (Covers.right (covers_sub hp wr₁ _ (by
      intro r hr; simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩
      · exact ⟨out, rfl, ho⟩)))
    (covers_sub hp wr₁ _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩
      · exact ⟨out, rfl, ho⟩))
    fun s₂ k₂ tag₂ => ?_
  exact ⟨(k₁.sub fun _ hr => absurd hr List.not_mem_nil).trans k₂,
    fun key msg hr => tag₂ key msg (by rw [m₁]; exact hr)⟩

/-- The clamping masks. -/
abbrev M0 : BitVec 64 := 0x0ffffffc0fffffff
abbrev M1 : BitVec 64 := 0x0ffffffc0ffffffc

/-- The memory `polyIn` leaves: `x27`, `x28` and the clamped key stored. -/
def memIn (m : Mem) (c : Addr) (a b : BitVec 64) : Mem :=
  (((m.writeW (off c 800) a).writeW (off c 808) b).writeW (off c 288)
    (m.readW (off c 472) 64 &&& M0)).writeW (off c 296) (m.readW (off c 480) 64 &&& M1)

theorem polyIn_core {s₀ : State} (hp : APre s₀) {s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block polyIn) s fun u =>
      u.gpr .x21 = s.mem.readW (off (cx s₀) 448) 64 ∧ u.gpr .x22 = s.mem.readW (off (cx s₀) 456) 64 ∧
      u.gpr .x23 = s.mem.readW (off (cx s₀) 464) 64 ∧
      u.mem = memIn s.mem (cx s₀) (s.gpr .x27) (s.gpr .x28) ∧
      (∀ r, r ∉ [Reg.x21, .x22, .x23, .x24, .x25] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr := by
  have o (d : Nat) (hd : d + 8 ≤ 1024) : InRegions s.wr (off (cx s₀) d) 8 := by
    rw [hwr]; exact hp.in_ctx hd
  have i (d : Nat) (hd : d + 8 ≤ 1024) : InRegions (s.rd ++ s.wr) (off (cx s₀) d) 8 := by
    rw [hrd, hwr]; exact hp.in_ctx' hd
  unfold polyIn
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_str (a := off (cx s₀) 800) (by decide) (by rw [hx21]) (o 800 (by lit_omega)) fun s₁ g₁ => ?_
  refine wp_str (a := off (cx s₀) 808) (by decide) (by rw [g₁.gpr, hx21])
    (by rw [g₁.wr]; exact o 808 (by lit_omega)) fun s₂ g₂ => ?_
  refine wp_const64 fun s₃ u₃ => ?_
  have x21₃ : s₃.gpr .x21 = cx s₀ := by rw [u₃.other _ (by decide), g₂.gpr, g₁.gpr, hx21]
  have rw₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [u₃.rd, u₃.wr, g₂.rd, g₂.wr, g₁.rd, g₁.wr]
  refine wp_ldr (a := off (cx s₀) 472) (by decide) (by rw [x21₃]) (by rw [rw₃]; exact i 472 (by lit_omega))
    fun s₄ u₄ => ?_
  refine wp_and fun s₅ u₅ => ?_
  refine wp_str (a := off (cx s₀) 288) (by decide) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), x21₃])
    (by rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, g₁.wr]; exact o 288 (by lit_omega)) fun s₆ g₆ => ?_
  refine wp_const64 fun s₇ u₇ => ?_
  have x21₇ : s₇.gpr .x21 = cx s₀ := by
    rw [u₇.other _ (by decide), g₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), x21₃]
  have rw₇ : s₇.rd ++ s₇.wr = s.rd ++ s.wr := by rw [u₇.rd, u₇.wr, g₆.rd, g₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]
  refine wp_ldr (a := off (cx s₀) 480) (by decide) (by rw [x21₇]) (by rw [rw₇]; exact i 480 (by lit_omega))
    fun s₈ u₈ => ?_
  refine wp_and fun s₉ u₉ => ?_
  refine wp_str (a := off (cx s₀) 296) (by decide) (by rw [u₉.other _ (by decide), u₈.other _ (by decide), x21₇])
    (by rw [u₉.wr, u₈.wr, u₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, g₁.wr]; exact o 296 (by lit_omega))
    fun s₁₀ g₁₀ => ?_
  have x21₁₀ : s₁₀.gpr .x21 = cx s₀ := by
    rw [g₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), x21₇]
  have rw₁₀ : s₁₀.rd ++ s₁₀.wr = s.rd ++ s.wr := by rw [g₁₀.rd, g₁₀.wr, u₉.rd, u₉.wr, u₈.rd, u₈.wr, rw₇]
  refine wp_ldr (a := off (cx s₀) 456) (by decide) (by rw [x21₁₀]) (by rw [rw₁₀]; exact i 456 (by lit_omega))
    fun s₁₁ u₁₁ => ?_
  refine wp_ldr (a := off (cx s₀) 464) (by decide) (by rw [u₁₁.other _ (by decide), x21₁₀])
    (by rw [u₁₁.rd, u₁₁.wr, rw₁₀]; exact i 464 (by lit_omega)) fun s₁₂ u₁₂ => ?_
  refine wp_ldr (a := off (cx s₀) 448) (by decide)
    (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), x21₁₀])
    (by rw [u₁₂.rd, u₁₂.wr, u₁₁.rd, u₁₁.wr, rw₁₀]; exact i 448 (by lit_omega)) fun s₁₃ u₁₃ => ?_
  have m₂ : s₂.mem = (s.mem.writeW (off (cx s₀) 800) (s.gpr .x27)).writeW (off (cx s₀) 808) (s.gpr .x28) := by
    rw [g₂.mem, g₁.mem, g₁.gpr]
  have r472 : s₃.mem.readW (off (cx s₀) 472) 64 = s.mem.readW (off (cx s₀) 472) 64 := by
    rw [u₃.mem, m₂, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
      readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega)]
  have m₆ : s₆.mem = s₂.mem.writeW (off (cx s₀) 288) (s.mem.readW (off (cx s₀) 472) 64 &&& M0) := by
    rw [g₆.mem, u₅.mem, u₄.mem, u₃.mem, u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.gpr, ← u₃.mem, r472]
  have r480 : s₇.mem.readW (off (cx s₀) 480) 64 = s.mem.readW (off (cx s₀) 480) 64 := by
    rw [u₇.mem, m₆, m₂, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
      readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
      readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega)]
  have m₁₀ : s₁₀.mem = memIn s.mem (cx s₀) (s.gpr .x27) (s.gpr .x28) := by
    rw [g₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₉.gpr, u₈.gpr, u₈.other _ (by decide), u₇.gpr, ← u₇.mem, r480,
      u₇.mem, m₆, m₂]
    rfl
  have rd (d : Nat) (hd : d = 448 ∨ d = 456 ∨ d = 464) :
      s₁₀.mem.readW (off (cx s₀) d) 64 = s.mem.readW (off (cx s₀) d) 64 := by
    rw [m₁₀, memIn]
    rcases hd with rfl | rfl | rfl <;>
      rw [readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega)]
  refine WP.block_nil ⟨?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₁₃.gpr, u₁₂.mem, u₁₁.mem, rd 448 (by decide)]
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, rd 456 (by decide)]
  · rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.mem, rd 464 (by decide)]
  · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₃.other _ hr.1, u₁₂.other _ hr.2.2.1, u₁₁.other _ hr.2.1, g₁₀.gpr, u₉.other _ hr.2.2.2.2,
      u₈.other _ hr.2.2.2.2, u₇.other _ hr.2.2.2.1, g₆.gpr, u₅.other _ hr.2.2.2.2,
      u₄.other _ hr.2.2.2.2, u₃.other _ hr.2.2.2.1, g₂.gpr, g₁.gpr]
  · rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, g₁₀.rd, u₉.rd, u₈.rd, u₇.rd, g₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, g₁.rd]
  · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, g₁₀.wr, u₉.wr, u₈.wr, u₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, g₁.wr]

theorem polyIn_ok {s₀ : State} (hp : APre s₀) {s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block polyIn) s fun u =>
      (u.gpr .x21 = s.mem.readW (off (cx s₀) 448) 64 ∧ u.gpr .x22 = s.mem.readW (off (cx s₀) 456) 64 ∧
      u.gpr .x23 = s.mem.readW (off (cx s₀) 464) 64 ∧
      u.mem = memIn s.mem (cx s₀) (s.gpr .x27) (s.gpr .x28) ∧
      (∀ r, r ∉ [Reg.x21, .x22, .x23, .x24, .x25] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr) ∧ u.v = s.v ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr :=
  VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide +kernel) (polyIn_core hp hx21 hrd hwr)

/-- The accumulator's value in `x21`–`x23`. -/
abbrev hacc (s : State) : Nat :=
  (s.gpr .x21).toNat + 2 ^ 64 * (s.gpr .x22).toNat + 2 ^ 128 * (s.gpr .x23).toNat

/-- The data not yet absorbed, after the chunks. -/
def restP (enc : Bool) (x1 x2 : BitVec 64) : BitVec 64 × BitVec 64 :=
  if enc then (x1 - 512#64, x2 + 512#64) else (x1, x2)

theorem polyOut_core {s₀ : State} (hp : APre s₀) (enc : Bool) {s : State}
    (hx0 : s.gpr .x0 = off (cx s₀) 64) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block (polyOut enc)) s fun u =>
      ((s.gpr .x23).toNat ≤ 4 →
        Poly1305.AArch64.Radix64.hval u = hacc s % Spec.Poly1305.P) ∧
      u.mem = Poly1305.AArch64.storeHm s.mem (off (cx s₀) 448) (u.gpr .x4) (u.gpr .x5) (u.gpr .x6) ∧
      u.gpr .x21 = cx s₀ ∧ u.gpr .x27 = s.mem.readW (off (cx s₀) 800) 64 ∧
      u.gpr .x28 = s.mem.readW (off (cx s₀) 808) 64 ∧
      u.gpr .x22 = (restP enc (s.gpr .x1) (s.gpr .x2)).1 ∧
      u.gpr .x23 = (restP enc (s.gpr .x1) (s.gpr .x2)).2 ∧
      (∀ r, r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23, .x27, .x28] →
        u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr := by
  have o (d : Nat) (hd : d + 8 ≤ 1024) : InRegions s₀.wr (off (cx s₀) d) 8 := hp.in_ctx hd
  have i (d : Nat) (hd : d + 8 ≤ 1024) : InRegions (s₀.rd ++ s₀.wr) (off (cx s₀) d) 8 := hp.in_ctx' hd
  have hc : off (cx s₀) 64 - BitVec.ofNat 64 64 = cx s₀ := BitVec.add_sub_cancel _ _
  unfold polyOut
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => ?_
  refine WP.block_append (WP.mono (Poly1305.AArch64.Radix64.reduce_ok s₃) fun s₄ ⟨e₄, k₄⟩ => ?_)
  have g₃ (r : Reg) (h4 : r ≠ .x4) (h5 : r ≠ .x5) (h6 : r ≠ .x6) : s₃.gpr r = s.gpr r := by
    rw [u₃.other _ h6, u₂.other _ h5, u₁.other _ h4]
  have m₄ : s₄.mem = s.mem := by rw [k₄.2.1, u₃.mem, u₂.mem, u₁.mem]
  have rw₄ : s₄.rd = s.rd ∧ s₄.wr = s.wr := ⟨by rw [k₄.2.2.1, u₃.rd, u₂.rd, u₁.rd],
    by rw [k₄.2.2.2, u₃.wr, u₂.wr, u₁.wr]⟩
  refine wp_subImm (by decide) fun s₅ u₅ => ?_
  have x21₅ : s₅.gpr .x21 = cx s₀ := by
    rw [u₅.gpr, k₄.gpr' (r := .x0), g₃ _ (by decide) (by decide) (by decide), hx0, hc]
  refine wp_str (a := off (cx s₀) 448) (by decide) (by rw [x21₅])
    (by rw [u₅.wr, rw₄.2, hwr]; exact o 448 (by lit_omega)) fun s₆ g₆ => ?_
  refine wp_str (a := off (cx s₀) 456) (by decide) (by rw [g₆.gpr, x21₅])
    (by rw [g₆.wr, u₅.wr, rw₄.2, hwr]; exact o 456 (by lit_omega)) fun s₇ g₇ => ?_
  refine wp_str (a := off (cx s₀) 464) (by decide) (by rw [g₇.gpr, g₆.gpr, x21₅])
    (by rw [g₇.wr, g₆.wr, u₅.wr, rw₄.2, hwr]; exact o 464 (by lit_omega)) fun s₈ g₈ => ?_
  have x21₈ : s₈.gpr .x21 = cx s₀ := by rw [g₈.gpr, g₇.gpr, g₆.gpr, x21₅]
  have rw₈ : s₈.rd ++ s₈.wr = s₀.rd ++ s₀.wr := by
    rw [g₈.rd, g₈.wr, g₇.rd, g₇.wr, g₆.rd, g₆.wr, u₅.rd, u₅.wr, rw₄.1, rw₄.2, hrd, hwr]
  have m₈ : s₈.mem = Poly1305.AArch64.storeHm s.mem (off (cx s₀) 448) (s₄.gpr .x4) (s₄.gpr .x5)
      (s₄.gpr .x6) := by
    rw [g₈.mem, g₇.mem, g₆.mem, u₅.mem, m₄, g₇.gpr, g₆.gpr, u₅.other _ (by decide),
      u₅.other _ (by decide), u₅.other _ (by decide)]
    simp only [Poly1305.AArch64.storeHm, Poly1305.AArch64.off, off, BitVec.add_assoc, ← BitVec.ofNat_add]
  have r8 (d : Nat) (hd : d = 800 ∨ d = 808) :
      s₈.mem.readW (off (cx s₀) d) 64 = s.mem.readW (off (cx s₀) d) 64 := by
    rw [m₈]
    simp only [Poly1305.AArch64.storeHm, Poly1305.AArch64.off, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    rcases hd with rfl | rfl <;>
      rw [readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega)]
  refine wp_ldr (a := off (cx s₀) 800) (by decide) (by rw [x21₈]) (by rw [rw₈]; exact i 800 (by lit_omega))
    fun s₉ u₉ => ?_
  refine wp_ldr (a := off (cx s₀) 808) (by decide) (by rw [u₉.other _ (by decide), x21₈])
    (by rw [u₉.rd, u₉.wr, rw₈]; exact i 808 (by lit_omega)) fun s₁₀ u₁₀ => ?_
  have g₁₀ (r : Reg) (h27 : r ≠ .x27) (h28 : r ≠ .x28) : s₁₀.gpr r = s₈.gpr r := by
    rw [u₁₀.other _ h28, u₉.other _ h27]
  have x12 : s₁₀.gpr .x1 = s.gpr .x1 ∧ s₁₀.gpr .x2 = s.gpr .x2 := by
    refine ⟨?_, ?_⟩ <;> rw [g₁₀ _ (by decide) (by decide), g₈.gpr, g₇.gpr, g₆.gpr,
      u₅.other _ (by decide), k₄.gpr', g₃ _ (by decide) (by decide) (by decide)]
  have common : ∀ u : State, (∀ r, r ≠ .x22 → r ≠ .x23 → u.gpr r = s₁₀.gpr r) → u.mem = s₁₀.mem →
      u.rd = s₁₀.rd → u.wr = s₁₀.wr →
      ((s.gpr .x23).toNat ≤ 4 → Poly1305.AArch64.Radix64.hval u = hacc s % Spec.Poly1305.P) ∧
      u.mem = Poly1305.AArch64.storeHm s.mem (off (cx s₀) 448) (u.gpr .x4) (u.gpr .x5) (u.gpr .x6) ∧
      u.gpr .x21 = cx s₀ ∧ u.gpr .x27 = s.mem.readW (off (cx s₀) 800) 64 ∧
      u.gpr .x28 = s.mem.readW (off (cx s₀) 808) 64 ∧
      (∀ r, r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23, .x27, .x28] →
        u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr := by
    intro u hu hm hr hw
    have h456 (r : Reg) (h : r = .x4 ∨ r = .x5 ∨ r = .x6) : u.gpr r = s₄.gpr r := by
      rcases h with rfl | rfl | rfl <;>
        rw [hu _ (by decide) (by decide), g₁₀ _ (by decide) (by decide), g₈.gpr, g₇.gpr, g₆.gpr,
          u₅.other _ (by decide)]
    refine ⟨fun h23 => ?_, ?_, ?_, ?_, ?_, fun r hr' => ?_, ?_, ?_⟩
    · have a4 : s₃.gpr .x4 = s.gpr .x21 := by
        rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      have a5 : s₃.gpr .x5 = s.gpr .x22 := by
        rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
      have a6 : s₃.gpr .x6 = s.gpr .x23 := by
        rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
      have e := e₄ (by rw [a6]; exact h23)
      simp only [Poly1305.AArch64.Radix64.hval, h456 .x4 (by decide), h456 .x5 (by decide),
        h456 .x6 (by decide), a4, a5, a6] at e ⊢
      exact e
    · rw [hm, u₁₀.mem, u₉.mem, m₈, h456 .x4 (by decide), h456 .x5 (by decide), h456 .x6 (by decide)]
    · rw [hu _ (by decide) (by decide), g₁₀ _ (by decide) (by decide), x21₈]
    · rw [hu _ (by decide) (by decide), u₁₀.other _ (by decide), u₉.gpr, r8 800 (by decide)]
    · rw [hu _ (by decide) (by decide), u₁₀.gpr, u₉.mem, r8 808 (by decide)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨h4, h5, h6, h9, h10, h11, h12, h13, h14, h21, h22, h23, h27, h28⟩ := hr'
      have hk : r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h4, h5, h6, h9, h10, h11, h12, h13, h14⟩
      rw [hu _ h22 h23, g₁₀ _ h27 h28, g₈.gpr, g₇.gpr, g₆.gpr, u₅.other _ h21, k₄.1 r hk, g₃ _ h4 h5 h6]
    · rw [hr, u₁₀.rd, u₉.rd, g₈.rd, g₇.rd, g₆.rd, u₅.rd, rw₄.1]
    · rw [hw, u₁₀.wr, u₉.wr, g₈.wr, g₇.wr, g₆.wr, u₅.wr, rw₄.2]
  cases enc
  · simp only [Bool.false_eq_true, ite_false, restP]
    refine wp_mov fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ => WP.block_nil ?_
    obtain ⟨a, b, c, d, e, f, g, h⟩ := common s₁₂ (fun r h22 h23 => by
      rw [u₁₂.other _ h23, u₁₁.other _ h22]) (by rw [u₁₂.mem, u₁₁.mem]) (by rw [u₁₂.rd, u₁₁.rd])
      (by rw [u₁₂.wr, u₁₁.wr])
    exact ⟨a, b, c, d, e, by rw [u₁₂.other _ (by decide), u₁₁.gpr, x12.1],
      by rw [u₁₂.gpr, u₁₁.other _ (by decide), x12.2], f, g, h⟩
  · simp only [ite_true, restP]
    refine wp_subImm (by decide) fun s₁₁ u₁₁ => wp_addImm (by decide) fun s₁₂ u₁₂ => WP.block_nil ?_
    obtain ⟨a, b, c, d, e, f, g, h⟩ := common s₁₂ (fun r h22 h23 => by
      rw [u₁₂.other _ h23, u₁₁.other _ h22]) (by rw [u₁₂.mem, u₁₁.mem]) (by rw [u₁₂.rd, u₁₁.rd])
      (by rw [u₁₂.wr, u₁₁.wr])
    exact ⟨a, b, c, d, e, by rw [u₁₂.other _ (by decide), u₁₁.gpr, x12.1],
      by rw [u₁₂.gpr, u₁₁.other _ (by decide), x12.2], f, g, h⟩

theorem polyOut_ok {s₀ : State} (hp : APre s₀) (enc : Bool) {s : State}
    (hx0 : s.gpr .x0 = off (cx s₀) 64) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block (polyOut enc)) s fun u =>
      (((s.gpr .x23).toNat ≤ 4 →
        Poly1305.AArch64.Radix64.hval u = hacc s % Spec.Poly1305.P) ∧
      u.mem = Poly1305.AArch64.storeHm s.mem (off (cx s₀) 448) (u.gpr .x4) (u.gpr .x5) (u.gpr .x6) ∧
      u.gpr .x21 = cx s₀ ∧ u.gpr .x27 = s.mem.readW (off (cx s₀) 800) 64 ∧
      u.gpr .x28 = s.mem.readW (off (cx s₀) 808) 64 ∧
      u.gpr .x22 = (restP enc (s.gpr .x1) (s.gpr .x2)).1 ∧
      u.gpr .x23 = (restP enc (s.gpr .x1) (s.gpr .x2)).2 ∧
      (∀ r, r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23, .x27, .x28] →
        u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr) ∧ u.v = s.v ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr :=
  VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by cases enc <;> decide +kernel)
    (polyOut_core hp enc hx0 hrd hwr)

end VG.Proof.ChaCha20Poly1305.AArch64
