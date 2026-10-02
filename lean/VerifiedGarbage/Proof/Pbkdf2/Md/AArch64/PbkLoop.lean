import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Pbkdf2
import VerifiedGarbage.Proof.MdStream.AArch64.Words

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`'s loop

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/PbkLoop.lean`): after `k` blocks of the
output (`Inv`), `out` holds the first `min (k D) out_len` bytes of `T₁ ‖ … ‖
T_k`; a step computes `T_{k+1}` (`U₁` by `update` with `INT (k + 1)` and
HMAC's `finalize`, then `iterate`) and copies as much of it as the output
still needs.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_addImm wp_subImm wp_movz wp_lsr wp_ldr wp_str32 wp_ldrb
  wp_strb wp_add wp_sub wp_rev32 eval_zero eval_nonzero sub_ofNat add_ofNat ofNat_succ ofNat_beq_zero writeW32
  setWidth32)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK pbkG)
open VG.Proof.Pbkdf2.AArch64 (copy32_ok iterK)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG After UpdArgs restore_ok savedRegs CopyInv clob nm count_loop
  movz_ofNat ofNat_ne_zero)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (untouched)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take bytesAt_snoc' writeBytes_snoc not_mem_of_disjoint
  bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

/-! ## The specification's pieces -/

/-- The pseudorandom function: HMAC keyed with the password. -/
abbrev prf (hH : HashOK H) (s₀ : State) : List Byte → List Byte := hmacBlockKey hH.SH.H (K0 hH s₀)

abbrev saltB (s₀ : State) : List Byte := bytesAt s₀.mem (salt s₀) (sl s₀)

/-- `T_i`. -/
abbrev Tb (hH : HashOK H) (s₀ : State) (i : Nat) : List Byte := Spec.Pbkdf2.F (prf hH s₀) (saltB s₀) (cc s₀) i

/-- `T₁ ‖ … ‖ T_k`. -/
def G (hH : HashOK H) (s₀ : State) (k : Nat) : List Byte := (List.range k).flatMap fun j => Tb hH s₀ (j + 1)

theorem G_succ (hH : HashOK H) (s₀ : State) (k : Nat) : G hH s₀ (k + 1) = G hH s₀ k ++ Tb hH s₀ (k + 1) := by
  simp only [G, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The number of blocks of the output. -/
abbrev nb (H : Hash) (s₀ : State) : Nat := (ol s₀ + H.D - 1) / H.D

/-- The bytes of the output after `k` blocks. -/
abbrev done (H : Hash) (s₀ : State) (k : Nat) : Nat := min (k * H.D) (ol s₀)

theorem lt_nb {s₀ : State} (hD : 0 < H.D) {k : Nat} : k < nb H s₀ ↔ k * H.D < ol s₀ := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hD, Nat.succ_mul]; omega

theorem ol_le {s₀ : State} (hD : 0 < H.D) : ol s₀ ≤ nb H s₀ * H.D := by
  have h1 : nb H s₀ * H.D + (ol s₀ + H.D - 1) % H.D = ol s₀ + H.D - 1 := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have h2 := Nat.mod_lt (ol s₀ + H.D - 1) hD
  omega

theorem nb_lt {s₀ : State} (hD : 0 < H.D) (h : ol s₀ ≤ (2 ^ 32 - 1) * H.D) : nb H s₀ < 2 ^ 32 := by
  rw [Nat.div_lt_iff_lt_mul hD]; omega

theorem nb_zero {s₀ : State} (hD : 0 < H.D) : nb H s₀ = 0 ↔ ol s₀ = 0 := by
  have := lt_nb (s₀ := s₀) hD (k := 0); simp only [Nat.zero_mul] at this; omega

/-! ## Facts about words, lengths and registers -/

theorem bytes32_int (i : Nat) : VG.Proof.MdStream.bytes32 true (BitVec.ofNat 32 i) = Spec.Pbkdf2.int i := by
  simp only [VG.Proof.MdStream.bytes32, ite_true, Spec.Pbkdf2.int, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] <;> omega

/-- Two disjoint regions that do not wrap around fit in the address space
together. -/
theorem len_add_le {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) (h₁ : r₁.base.toNat + r₁.len ≤ 2 ^ 64)
    (h₂ : r₂.base.toNat + r₂.len ≤ 2 ^ 64) : r₁.len + r₂.len ≤ 2 ^ 64 := by
  by_contra hc
  rcases Nat.le_total r₁.base.toNat r₂.base.toNat with hb | hb
  · refine hd r₂.base ?_ ?_ <;> simp only [Region.Contains]
    · rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hb)]; omega
    · simp only [BitVec.sub_self, BitVec.toNat_zero]; omega
  · refine hd r₁.base ?_ ?_ <;> simp only [Region.Contains]
    · simp only [BitVec.sub_self, BitVec.toNat_zero]; omega
    · rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hb)]; omega

theorem eregs_pres : ∀ r ∈ eregs, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem eregs_clob : ∀ r ∈ eregs, r ∉ clob := by decide

theorem kregs_clob : ∀ r ∈ kregs, r ∉ clob := by decide

/-- A do-while loop on `x21 ≠ 0` whose body runs `n > 0` times. -/
theorem nb_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s → WP isa body s fun s' => I (k + 1) s' ∧
      isa.eval (.nonzero .x .x21) s' = some (decide (k + 1 ≠ n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .x .x21)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [hz]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## The loop's invariant -/

/-- After `k` blocks of the output: `x19` is the next block's number, `x20`
`salt_len`, `x21` the bytes left and `x22` where they go. -/
structure Inv (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : KR (H := H) s₀ s
  st : States hH s₀ s.mem
  x19 : s.gpr .x19 = BitVec.ofNat 64 (k + 1)
  x20 : s.gpr .x20 = s₀.gpr .x3
  x21 : s.gpr .x21 = BitVec.ofNat 64 (ol s₀ - done H s₀ k)
  x22 : s.gpr .x22 = out s₀ + BitVec.ofNat 64 (done H s₀ k)
  glen : (G hH s₀ k).length = k * H.D
  outB : bytesAt s.mem (out s₀) (done H s₀ k) = (G hH s₀ k).take (done H s₀ k)

/-- In step `k`, before `T_{k+1}` is copied out. -/
structure Mid (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : KR (H := H) s₀ s
  st : States hH s₀ s.mem
  x19 : s.gpr .x19 = BitVec.ofNat 64 (k + 1)
  x20 : s.gpr .x20 = s₀.gpr .x3
  x21 : s.gpr .x21 = BitVec.ofNat 64 (ol s₀ - k * H.D)
  x22 : s.gpr .x22 = out s₀ + BitVec.ofNat 64 (k * H.D)
  outB : bytesAt s.mem (out s₀) (k * H.D) = G hH s₀ k

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

theorem loopRegs_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hS : States hH s₀ s.mem) :
    WP isa (.block H.loopRegs) s fun t =>
      Inv hH s₀ 0 t ∧ isa.eval (.zero .x .x21) t = some (decide (ol s₀ = 0)) := by
  have hl := layout (H := H); have he := end_le hz
  simp only [Hash.loopRegs]
  refine wp_mov fun s₁ u₁ => ?_
  have k₁ := h.kr.upd u₁ (by decide)
  refine wp_ldr (a := A s₀ H.outO) ⟨by omega, by omega⟩ (by rw [k₁.x23]) (in_rw hp hz k₁ (by omega))
    fun s₂ u₂ => ?_
  have k₂ := k₁.upd u₂ (by decide)
  refine wp_ldr (a := A s₀ H.olO) ⟨by omega, by omega⟩ (by rw [k₂.x23]) (in_rw hp hz k₂ (by omega))
    fun s₃ u₃ => ?_
  have k₃ := k₂.upd u₃ (by decide)
  refine wp_movz fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have x21 : s₄.gpr .x21 = BitVec.ofNat 64 (ol s₀) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, h.kr.olW, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨⟨k₃.upd u₄ (by decide), m₄ ▸ hS, by rw [u₄.gpr]; rfl, ?_, ?_, ?_, by simp [G], by simp [bytesAt]⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.x22]
  · rw [x21]; simp
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, h.kr.outW]; simp
  · change eval (.zero .x .x21) s₄ = _
    rw [eval_zero, x21, ofNat_beq_zero (s₀.gpr .x6).isLt]

/-- What writes leave: they are in the working space of the functions we
call, in `scratch` from the working state on, or the 16 bytes below the
stack pointer. -/
theorem Mid.keep (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : Mid hH s₀ k s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hg : ∀ r ∈ eregs, s'.gpr r = s.gpr r)
    {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hw : ∀ r ∈ rs, (∃ j, r = ⟨scr s₀, j⟩ ∧ j ≤ 8 * H.W) ∨
      (∃ o j, r = sR s₀ o j ∧ H.stWO ≤ o ∧ o + j ≤ (H.W + H.S) * 8) ∨ r = below s.sp 16) :
    Mid hH s₀ k s' := by
  have hl := layout (H := H); have he := end_le hz
  have ho : Region.Sub ⟨out s₀, k * H.D⟩ (outR s₀) := Region.sub_prefix hk
  have key : ∀ {X : Region}, (∀ o j, H.stWO ≤ o → o + j ≤ (H.W + H.S) * 8 → X.Disjoint (sR s₀ o j)) →
      X.Disjoint (lowR (H := H) s₀) → X.Disjoint (below s.sp 16) → ∀ r ∈ rs, X.Disjoint r := by
    intro X h1 h2 h3 r hr
    rcases hw r hr with ⟨j, rfl, hj⟩ | ⟨o, j, rfl, ho1, ho2⟩ | rfl
    · exact h2.sub_right (Region.sub_prefix hj)
    · exact h1 o j ho1 ho2
    · exact h3
  have hstk : ∀ {X : Region}, Region.Sub X (scR (H := H) s₀) → X.Disjoint (below s.sp 16) :=
    fun hX => (stk_sc hp h.kr hX).symm
  refine ⟨h.kr.keep hrd hwr hsp (fun r hr => hg r (kregs_eregs r hr)) hf
      (key (fun o j h1 h2 => part_disj hz (Or.inl (by omega)) (by omega) h2) (low_disj hz (by omega) (by omega))
        (hstk (part_sub (by omega)))) (fun r hr => ?_),
    h.st.keep hz hH hf (key (fun o j h1 h2 => part_disj hz (Or.inl (by omega)) (by omega) h2)
      (low_disj hz (by omega) (by omega)) (hstk (part_sub (by omega)))),
    by rw [hg _ (by simp), h.x19], by rw [hg _ (by simp), h.x20],
    by rw [hg _ (by simp), h.x21], by rw [hg _ (by simp), h.x22], ?_⟩
  · rcases hw r hr with ⟨j, rfl, hj⟩ | ⟨o, j, rfl, _, h2⟩ | rfl
    · exact ⟨scR (H := H) s₀, by simp, Region.sub_prefix (by show j ≤ (H.W + H.S) * 8; omega)⟩
    · exact ⟨_, by simp, part_sub h2⟩
    · rw [h.kr.sp]
      exact ⟨_, by simp, fun _ h => h⟩
  · rw [← h.outB]
    exact bytes_keep hf (key (fun o j _ h2 => (hp.o_s.sub_left ho).sub_right (part_sub h2))
      ((hp.o_s.sub_left ho).sub_right low_sub) (by rw [h.kr.sp]; exact (hp.stk_o.sub_right ho).symm))
      (by have := hp.onw; omega)

/-- What a call leaves. -/
theorem Mid.call (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : Mid hH s₀ k s)
    {ws : List Region} (a : After s ws s')
    (hw : ∀ r ∈ ws, (∃ j, r = ⟨scr s₀, j⟩ ∧ j ≤ 8 * H.W) ∨
      ∃ o j, r = sR s₀ o j ∧ H.stWO ≤ o ∧ o + j ≤ (H.W + H.S) * 8) : Mid hH s₀ k s' :=
  h.keep hp hz hH hk a.rd a.wr a.sp (fun r hr => a.cs r (eregs_pres r hr).1 (eregs_pres r hr).2) a.frame
    fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · rcases hw r hr with h1 | h2
        · exact .inl h1
        · exact .inr (.inl h2)
      · simp only [List.mem_singleton] at hr; exact .inr (.inr hr)

/-- A write into a part of `scratch` from the working state on. -/
theorem Mid.write (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : Mid hH s₀ k s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hg : ∀ r ∈ eregs, s'.gpr r = s.gpr r)
    {o n : Nat} (ho : H.stWO ≤ o) (hon : o + n ≤ (H.W + H.S) * 8) (hf : Frame [sR s₀ o n] s.mem s'.mem) :
    Mid hH s₀ k s' :=
  h.keep hp hz hH hk hrd hwr hsp hg hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl ⟨o, n, rfl, ho, hon⟩)

omit hp hz in
theorem Mid.upd {hH : HashOK H} {k : Nat} {s s' : State} (h : Mid hH s₀ k s) {d : Reg} {v : BitVec 64}
    (u : Upd s s' d v) (hd : d ∉ eregs) : Mid hH s₀ k s' := by
  have ne : ∀ r ∈ eregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u fun h' => hd (kregs_eregs d h'), u.mem ▸ h.st,
    by rw [u.other _ (ne _ (by simp)), h.x19], by rw [u.other _ (ne _ (by simp)), h.x20],
    by rw [u.other _ (ne _ (by simp)), h.x21], by rw [u.other _ (ne _ (by simp)), h.x22],
    by rw [u.mem, h.outB]⟩

end

/-! ## Copying `T` out -/

theorem outLoop_ok {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 63) (htO : H.tO < 4096) {s : State}
    (hc : s.gpr .x11 = BitVec.ofNat 64 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .x23 + BitVec.ofNat 64 H.tO + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr .x23 + BitVec.ofNat 64 H.tO, n⟩ ⟨s.gpr .x22, n⟩) :
    WP isa H.outLoop s fun t => CopyInv s (s.gpr .x23 + BitVec.ofNat 64 H.tO) (s.gpr .x22) n t := by
  have e23 : ∀ {A B : Addr} {k : Nat} {t : State}, CopyInv s A B k t → t.gpr .x23 = s.gpr .x23 :=
    fun h => h.other .x23 (by decide)
  have e22 : ∀ {A B : Addr} {k : Nat} {t : State}, CopyInv s A B k t → t.gpr .x22 = s.gpr .x22 :=
    fun h => h.other .x22 (by decide)
  generalize eA : s.gpr .x23 + BitVec.ofNat 64 H.tO = A at hin hsep ⊢
  generalize eB : s.gpr .x22 = B at hout hsep ⊢
  unfold Hash.outLoop
  refine WP.seq (wp_movz fun s₀ u₀ => WP.block_nil ?_)
  have i0 : CopyInv s A B 0 s₀ ∧ s₀.gpr .x11 = BitVec.ofNat 64 (n - 0) :=
    ⟨⟨u₀.rd, u₀.wr, u₀.sp, fun r hr => u₀.other r (nm hr .x24), by rw [u₀.gpr]; rfl,
      by rw [u₀.mem, bytesAt, List.range_zero, List.map_nil, writeBytes_nil]⟩,
      by rw [u₀.other _ (by decide), hc, Nat.sub_zero]⟩
  refine WP.mono (count_loop hn (by omega)
    (fun k t => CopyInv s A B k t ∧ t.gpr .x11 = BitVec.ofNat 64 (n - k)) (fun k hk t h => ?_) i0)
    fun t h => h.1
  obtain ⟨h, h11⟩ := h
  refine wp_add fun t₁ u₁ => ?_
  refine wp_ldrb (a := A + BitVec.ofNat 64 k) htO
    (by rw [u₁.gpr, e23 h, h.x24, ← eA]; ac_rfl)
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₂ u₂ => ?_
  refine wp_add fun t₃ u₃ => ?_
  refine wp_strb (a := B + BitVec.ofNat 64 k) (by decide)
    (by rw [u₃.gpr, u₂.other .x22 (by decide), u₁.other .x22 (by decide), e22 h, u₂.other .x24 (by decide),
      u₁.other .x24 (by decide), h.x24, eB]; simp)
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₄ m₄ => ?_
  refine wp_addImm (by decide) fun t₅ u₅ => wp_subImm (by decide) fun t₆ u₆ => WP.block_nil ?_
  have h24 : t₅.gpr .x24 = BitVec.ofNat 64 (k + 1) := by
    rw [u₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x24]
    exact (ofNat_succ k).symm
  have x11 : t₆.gpr .x11 = BitVec.ofNat 64 (n - (k + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h11, sub_ofNat (by omega), Nat.sub_sub]
  refine ⟨⟨⟨by rw [u₆.rd, u₅.rd, m₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, m₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₆.sp, u₅.sp, m₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr => by
      rw [u₆.other r (nm hr .x11), u₅.other r (nm hr .x24), m₄.gpr, u₃.other r (nm hr .x13),
        u₂.other r (nm hr .x9), u₁.other r (nm hr .x12), h.other r hr],
    by rw [u₆.other _ (by decide), h24], ?_⟩, x11⟩, x11⟩
  have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
  have v : (t₃.gpr .x9).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, h.mem]
    simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega), ↓reduceIte]
    ext i hi; simp
  have e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k)) (by rw [hl]; omega)
  rw [hl] at e'
  rw [u₆.mem, u₅.mem, m₄.mem, v, u₃.mem, u₂.mem, u₁.mem, h.mem, bytesAt_snoc', e']

/-! ## A step: `U₁` -/

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

/-- `U₁ = PRF (S ‖ INT (k + 1))`. -/
abbrev U1 (hH : HashOK H) (s₀ : State) (k : Nat) : List Byte :=
  hmacBlockKey hH.SH.H (K0 hH s₀) (saltB s₀ ++ Spec.Pbkdf2.int (k + 1))

omit hp hz in
/-- Before `update` with `INT (k + 1)`. -/
structure AtUpd (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : Mid hH s₀ k s
  args : UpdArgs hH.stream s (A s₀ H.stWO) (A s₀ H.intO) (scr s₀) 4
  x1 : s.gpr .x1 = BitVec.ofNat 64 (H.P.B + sl s₀)
  repr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀)
  int : bytesAt s.mem (A s₀ H.intO) 4 = Spec.Pbkdf2.int (k + 1)

omit hp hz in
/-- Before HMAC's `finalize`. -/
structure AtFin (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : Mid hH s₀ k s
  args : FinArgs (H := H) s (A s₀ H.stWO) (A s₀ H.st1O) (s₀.gpr .x3 + BitVec.ofNat 64 (H.P.B + 4))
    (A s₀ H.uO) (scr s₀)
  repr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1))

omit hp hz in
/-- Before `iterate`. -/
structure AtIter (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : Mid hH s₀ k s
  args : IterArgs (H := H) s (A s₀ H.st0O) (A s₀ H.uO) (BitVec.ofNat 64 (cc s₀ - 1)) (A s₀ H.tO) (scr s₀)
  u : bytesAt s.mem (A s₀ H.uO) H.D = U1 hH s₀ k
  t : bytesAt s.mem (A s₀ H.tO) H.D = U1 hH s₀ k

/-- A copy of the salted inner state, `INT (k + 1)`, and `update`'s arguments. -/
theorem pieceA_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s : State} (h : Mid hH s₀ k s) :
    WP isa (.block H.intArgs) s (AtUpd hH s₀ k) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hWb := hH.wb_le
  have hB := hz.B_le; have hN4 := hz.z.N4; have hD := hz.z.D0; have hD4 := hz.z.D4; have hDN := hz.z.DN
  have hN := hz.N
  have hB4 : H.P.B % 4 = 0 := by rcases hz.z.B with h | h <;> omega
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have eS : 4 * (H.S / 4) = H.S := by omega
  have hkD : k * H.D < ol s₀ := (lt_nb hD).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD hp.olD; omega
  -- The salted inner state, copied.
  simp only [Hash.intArgs, Hash.copy32]
  refine copy32_ok (src := .x23) (dst := .x23) (by decide) (by decide) H.stSO H.stWO (H.S / 4)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ _ s _
    (fun j hj => by rw [h.kr.x23, add_ofNat]; exact in_rw hp hz h.kr (by omega))
    (fun j hj => by rw [h.kr.x23, add_ofNat]; exact in_sc hp hz h.kr.wr (by omega))
    (by rw [h.kr.x23, eS]; exact (part_disj hz (Or.inl (by omega)) (by omega) (by omega)).sep
          (Region.contains_self _ _) (Region.contains_self _ _))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  rw [h.kr.x23, eS] at m₁
  have f₁ : Frame [sR s₀ H.stWO H.S] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have md₁ := h.write hp hz hH hk' rd₁ wr₁ sp₁ (fun r hr => g₁ r (by rintro rfl; revert hr; decide))
    (o := H.stWO) (n := H.S) (Nat.le_refl _) (by omega) f₁
  have rs₁ : hH.SH.Repr s₁.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀) := by
    rw [m₁]; exact repr_copy hH h.st.s
  -- `INT (k + 1)`.
  refine wp_rev32 fun s₂ u₂ => ?_
  have md₂ := md₁.upd u₂ (by decide)
  refine wp_str32 (a := A s₀ H.intO) ⟨by omega, by omega⟩ (by rw [md₂.kr.x23])
    (in_sc hp hz md₂.kr.wr (by omega)) fun s₃ g₃ => ?_
  have f₃ : Frame [sR s₀ H.intO 4] s₂.mem s₃.mem := by
    rw [g₃.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have md₃ := md₂.write hp hz hH hk' g₃.rd g₃.wr g₃.sp (fun r _ => by rw [g₃.gpr]) (o := H.intO) (n := 4)
    (by omega) (by omega) f₃
  have e₃ : s₃.mem = writeBytes s₂.mem (A s₀ H.intO) (Spec.Pbkdf2.int (k + 1)) := by
    rw [g₃.mem, u₂.gpr, setWidth32, md₁.x19,
      show (BitVec.ofNat 64 (k + 1)).setWidth 32 = BitVec.ofNat 32 (k + 1) from
        BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega),
      show rev32 (BitVec.ofNat 32 (k + 1)) = if true then rev32 (BitVec.ofNat 32 (k + 1)) else _ from rfl,
      writeW32, bytes32_int]
  -- `update`'s arguments.
  refine wp_addImm (by omega) fun s₄ u₄ => wp_addImm (by omega) fun s₅ u₅ => wp_addImm (by omega) fun s₆ u₆ =>
    wp_movz fun s₇ u₇ => wp_mov fun s₈ u₈ => WP.block_nil ?_
  have md₈ := ((((md₃.upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)).upd u₈
    (by decide)
  have e₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have ua : UpdArgs hH.stream s₈ (A s₀ H.stWO) (A s₀ H.intO) (scr s₀) 4 :=
    { x0 := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.gpr, md₃.kr.x23]
      x2 := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
          u₄.other _ (by decide), md₃.kr.x23]
      x3 := by rw [u₈.other _ (by decide), u₇.gpr]; rfl
      x4 := by rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), md₃.kr.x23]
      cd := Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨r', h', off, e, l⟩ := cov_part hp md₈.kr (o := H.intO) (n := 4) (by omega)
        exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp md₈.kr (by omega)
        · exact cov_low hp md₈.kr (by omega)
      st_sc := (low_disj hz (by omega) (by omega)).sub_right (Region.sub_prefix hWb)
      d_st := part_disj hz (Or.inr (by omega)) (by omega) (by omega)
      d_sc := (low_disj hz (by omega) (by omega)).sub_right (Region.sub_prefix hWb)
      sp16 := by rw [md₈.kr.sp]; exact hp.sp16
      stk_st := stk_sc hp md₈.kr (part_sub (by omega))
      stk_d := stk_sc hp md₈.kr (part_sub (by omega))
      stk_sc := stk_sc hp md₈.kr (Region.sub_prefix (by omega)) }
  refine ⟨md₈, ua, ?_, by
      rw [e₈]
      exact repr_keep hH f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)) (by rw [u₂.mem]; exact rs₁),
    by rw [e₈, e₃, bytesAt_writeBytes_self' (by rfl) (by omega)]⟩
  rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
    md₃.x20, Nat.add_comm, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `update` with `INT (k + 1)`. -/
theorem callA_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s : State} (h : AtUpd hH s₀ k s) :
    WP isa (.call H.updN H.updC) s fun t => Mid hH s₀ k t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (H := H); have he := end_le hz; have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hk' : k * H.D ≤ ol s₀ := Nat.le_of_lt ((lt_nb hz.z.D0).1 hk)
  refine VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_call hH.stream h.args fun s₁ a₁ r₁ => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' a₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr ⟨_, _, rfl, Nat.le_refl _, by omega⟩
      · exact .inl ⟨_, rfl, hWb⟩
  · have := r₁ _ h.repr (by
      rw [h.x1, List.length_append, xorPad_length, blockKey_length, bytesAt_length])
    rwa [h.int] at this

/-- HMAC's `finalize`'s arguments. -/
theorem finArgs_ok (hH : HashOK H) {k : Nat} {s : State} (h : Mid hH s₀ k s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.block H.finArgs) s (AtFin hH s₀ k) := by
  have hl := layout (H := H); have he := end_le hz; have hD := hz.z.DN; have hN := hz.N
  have hB := hz.B_le
  simp only [Hash.finArgs]
  refine wp_addImm (by omega) fun s₁ u₁ => wp_addImm (by omega) fun s₂ u₂ => wp_addImm (by omega) fun s₃ u₃ =>
    wp_addImm (by omega) fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
  have m₅ := ((((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)).upd u₅
    (by decide)
  have e₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have stk : ∀ {o n : Nat}, o + n ≤ (H.W + H.S) * 8 → (below s₅.sp 16).Disjoint (sR s₀ o n) :=
    fun h => stk_sc hp m₅.kr (part_sub h)
  have fa : FinArgs (H := H) s₅ (A s₀ H.stWO) (A s₀ H.st1O) (s₀.gpr .x3 + BitVec.ofNat 64 (H.P.B + 4))
      (A s₀ H.uO) (scr s₀) :=
    { x0 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x1 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
          u₁.other _ (by decide), h.kr.x23]
      x2 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), h.x20]
      x3 := by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.kr.x23]
      x4 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.kr.x23]
      cr := Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨r', h', off, e, l⟩ := cov_part hp m₅.kr (o := H.st1O) (n := H.S) (by omega)
        exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp m₅.kr (by omega)
        · exact cov_part hp m₅.kr (by omega)
        · exact cov_low hp m₅.kr (by omega)
      i_u := part_disj hz (Or.inr (by omega)) (by omega) (by omega)
      i_o := part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      i_s := low_disj hz (by omega) (by omega)
      u_o := part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      u_s := low_disj hz (by omega) (by omega)
      o_s := low_disj hz (by omega) (by omega)
      sp16 := by rw [m₅.kr.sp]; exact hp.sp16
      stk_i := stk (by omega)
      stk_u := stk (by omega)
      stk_o := stk (by omega)
      stk_s := stk_sc hp m₅.kr low_sub
      scnw := by have := hp.snw; omega }
  exact ⟨m₅, fa, by rw [e₅]; exact hr⟩

/-- HMAC's `finalize`: `U₁`. -/
theorem callB_ok (hH : HashOK H) (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W))
    (hFd : H.hmacFin.aarch64Depth ≤ 1) {k : Nat} (hk : k < nb H s₀) {s : State} (h : AtFin hH s₀ k s) :
    WP isa (.call H.hmacFinN H.hmacFin) s fun t => Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.uO) H.D = U1 hH s₀ k := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz
  have hkD : k * H.D < ol s₀ := (lt_nb hz.z.D0).1 hk
  have hk' := Nat.le_of_lt hkD
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  refine hfin_call hH hF hFd h.args fun s₁ a₁ hpost => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' a₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr ⟨_, _, rfl, Nat.le_refl _, by omega⟩
      · exact .inr ⟨_, _, rfl, by omega, by omega⟩
      · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  · have hK := blockKey_length hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
    exact hpost _ _ hK (by rw [hK, List.length_append, bytesAt_length]; simp [Spec.Pbkdf2.int]; omega)
      (by rw [← List.append_assoc]; exact h.repr)
      (by
        rw [List.length_append, bytesAt_length, show (Spec.Pbkdf2.int (k + 1)).length = 4 from rfl]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        have : sl s₀ = (s₀.gpr .x3).toNat := rfl
        omega)
      h.mid.st.o

/-- `U` copied to `T`, and `iterate`'s arguments. -/
theorem pieceC_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s₇ : State} (m₇ : Mid hH s₀ k s₇)
    (hU : bytesAt s₇.mem (A s₀ H.uO) H.D = U1 hH s₀ k) :
    WP isa (.block H.iterArgs) s₇ (AtIter hH s₀ k) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz
  have hD := hz.z.D0; have hD4 := hz.z.D4; have hDN := hz.z.DN; have hN := hz.N; have hBg := hz.B_ge
  have eD : 4 * (H.D / 4) = H.D := by omega
  have hkD : k * H.D < ol s₀ := (lt_nb hD).1 hk
  have hk' := Nat.le_of_lt hkD
  -- `U` copied to `T`.
  simp only [Hash.iterArgs, Hash.copy32]
  refine copy32_ok (src := .x23) (dst := .x23) (by decide) (by decide) H.uO H.tO (H.D / 4)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ _ s₇ _
    (fun j hj => by rw [m₇.kr.x23, add_ofNat]; exact in_rw hp hz m₇.kr (by omega))
    (fun j hj => by rw [m₇.kr.x23, add_ofNat]; exact in_sc hp hz m₇.kr.wr (by omega))
    (by rw [m₇.kr.x23, eD]; exact (part_disj hz (Or.inl (by omega)) (by omega) (by omega)).sep
          (Region.contains_self _ _) (Region.contains_self _ _))
    fun s₈ g₈ rd₈ wr₈ sp₈ c₈ => ?_
  rw [m₇.kr.x23, eD] at c₈
  have f₈ : Frame [sR s₀ H.tO H.D] s₇.mem s₈.mem := by
    rw [c₈]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have m₈ := m₇.write hp hz hH hk' rd₈ wr₈ sp₈ (fun r hr => g₈ r (by rintro rfl; revert hr; decide))
    (o := H.tO) (n := H.D) (by omega) (by omega) f₈
  have hU₈ : bytesAt s₈.mem (A s₀ H.uO) H.D = bytesAt s₇.mem (A s₀ H.uO) H.D :=
    bytes_keep f₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)) (by omega)
  have hT₈ : bytesAt s₈.mem (A s₀ H.tO) H.D = bytesAt s₇.mem (A s₀ H.uO) H.D := by
    rw [c₈]; exact bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega)
  -- `iterate`'s arguments.
  refine wp_addImm (by omega) fun s₉ u₉ => wp_addImm (by omega) fun s₁₀ u₁₀ => ?_
  have m₁₀ := (m₈.upd u₉ (by decide)).upd u₁₀ (by decide)
  refine wp_ldr (a := A s₀ H.cO) ⟨by omega, by omega⟩ (by rw [m₁₀.kr.x23]) (in_rw hp hz m₁₀.kr (by omega))
    fun s₁₁ u₁₁ => ?_
  have m₁₁ := m₁₀.upd u₁₁ (by decide)
  refine wp_addImm (by omega) fun s₁₂ u₁₂ => wp_mov fun s₁₃ u₁₃ => WP.block_nil ?_
  have m₁₃ := (m₁₁.upd u₁₂ (by decide)).upd u₁₃ (by decide)
  have e₁₃ : s₁₃.mem = s₈.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  have ia : IterArgs (H := H) s₁₃ (A s₀ H.st0O) (A s₀ H.uO) (BitVec.ofNat 64 (cc s₀ - 1)) (A s₀ H.tO)
      (scr s₀) :=
    { x0 := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
          u₁₀.other _ (by decide), u₉.gpr, m₈.kr.x23]
      x1 := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr,
          u₉.other _ (by decide), m₈.kr.x23]
      x2 := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.mem, u₉.mem, m₈.kr.cW]
      x3 := by rw [u₁₃.other _ (by decide), u₁₂.gpr, m₁₁.kr.x23]
      x4 := by rw [u₁₃.gpr, u₁₂.other _ (by decide), m₁₁.kr.x23]
      cr := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · obtain ⟨r', h', off, e, l⟩ := cov_part hp m₁₃.kr (o := H.st0O) (n := 2 * H.S) (by omega)
          exact ⟨r', List.mem_append_right _ h', off, e, l⟩
        · obtain ⟨r', h', off, e, l⟩ := cov_part hp m₁₃.kr (o := H.uO) (n := H.D) (by omega)
          exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp m₁₃.kr (by omega)
        · exact cov_low hp m₁₃.kr (by omega)
      k_t := part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      k_s := low_disj hz (by omega) (by omega)
      u_t := part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      u_s := low_disj hz (by omega) (by omega)
      t_s := low_disj hz (by omega) (by omega)
      knw := by
        have := hp.snw
        have e : (A s₀ H.st0O).toNat = (scr s₀).toNat + H.st0O := by
          simp only [A, BitVec.toNat_add, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (a := H.st0O) (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [e]; omega
      scnw := by have := hp.snw; omega }
  exact ⟨m₁₃, ia, by rw [e₁₃, hU₈, hU], by rw [e₁₃, hT₈, hU]⟩

/-- `iterate`: `T_{k+1}`. -/
theorem callC_ok (hH : HashOK H) (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W))
    (hId : H.iterate.aarch64Depth ≤ 1) {k : Nat} (hk : k < nb H s₀) {s : State} (h : AtIter hH s₀ k s) :
    WP isa (.call H.iterN H.iterate) s fun t => Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.tO) H.D = Tb hH s₀ (k + 1) := by
  have hl := layout (H := H); have he := end_le hz
  have hk' : k * H.D ≤ ol s₀ := Nat.le_of_lt ((lt_nb hz.z.D0).1 hk)
  refine iter_call hH hI hId h.args fun s₁ a₁ hpost => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' a₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr ⟨_, _, rfl, by omega, by omega⟩
      · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  have hK := blockKey_length hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  have hc : ((BitVec.ofNat 64 (cc s₀ - 1)).setWidth 32).toNat = cc s₀ - 1 := by
    have := ((s₀.gpr .x4).setWidth 32).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hO : A s₀ H.st0O + BitVec.ofNat 64 H.S = A s₀ H.st1O := by
    rw [add_ofNat, show H.st0O + H.S = H.st1O by omega]
  rw [hpost _ hK h.mid.st.i (hO ▸ h.mid.st.o), hc, h.u, h.t]
  rfl

/-! ## A step: copying `T` out -/

omit hp in
/-- The bytes of `T` the output still needs: `x21 - D` is negative (its top
bit set) exactly when fewer than `D` are left. -/
theorem outLen_ok {hH : HashOK H} {k : Nat} (hol : ol s₀ < 2 ^ 63) {s : State} (h : Mid hH s₀ k s) :
    WP isa H.outLen s fun t => Mid hH s₀ k t ∧
      t.gpr .x11 = BitVec.ofNat 64 (min (ol s₀ - k * H.D) H.D) ∧ t.mem = s.mem := by
  have hD := hz.z.D0; have hDN := hz.z.DN; have hN := hz.N
  unfold Hash.outLen
  refine WP.seq (wp_movz fun s₁ u₁ => wp_subImm (by omega) fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ =>
    WP.block_nil ?_)
  have m₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  have e₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have x11 : s₃.gpr .x11 = BitVec.ofNat 64 H.D := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, movz_ofNat (by omega)]
  have ev : isa.eval (.zero .x .x9) s₃ = some (decide (H.D ≤ ol s₀ - k * H.D)) := by
    change eval (.zero .x .x9) s₃ = _
    rw [eval_zero, u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.x21, shr_beq_zero]
    simp only [Option.some.injEq, decide_eq_decide]
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine WP.ite _ ev (fun hT => WP.block_nil ⟨m₃, ?_, e₃⟩) fun hF => wp_mov fun s₄ u₄ =>
    WP.block_nil ⟨m₃.upd u₄ (by decide), ?_, by rw [u₄.mem, e₃]⟩
  · rw [x11, Nat.min_eq_right (of_decide_eq_true hT)]
  · have := of_decide_eq_false hF
    rw [u₄.gpr, m₃.x21, Nat.min_eq_left (by omega)]

/-- Copying as much of `T_{k+1}` as the output needs, and on to the next block. -/
theorem tail_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) (hg : (G hH s₀ k).length = k * H.D) {s : State}
    (h : Mid hH s₀ k s) (ht : bytesAt s.mem (A s₀ H.tO) H.D = Tb hH s₀ (k + 1)) :
    WP isa (.seq H.outLen (.seq H.outLoop (.block Hash.advance))) s fun t =>
      Inv hH s₀ (k + 1) t ∧ isa.eval (.nonzero .x .x21) t = some (decide (k + 1 ≠ nb H s₀)) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz
  have hD := hz.z.D0; have hDN := hz.z.DN; have hN := hz.N
  have hol : ol s₀ < 2 ^ 63 := by have := hp.olD; omega
  have hkD : k * H.D < ol s₀ := (lt_nb hD).1 hk
  have hk1 := lt_nb (s₀ := s₀) hD (k := k + 1)
  rw [Nat.succ_mul] at hk1
  have hon := hp.onw
  generalize en : min (ol s₀ - k * H.D) H.D = n
  have hn : 0 < n ∧ n ≤ H.D ∧ k * H.D + n ≤ ol s₀ := by omega
  have hdn : done H s₀ (k + 1) = k * H.D + n := by
    show min ((k + 1) * H.D) (ol s₀) = _; rw [Nat.succ_mul]; omega
  have osub : Region.Sub ⟨out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ (outR s₀) := Offset.sub_base _ hn.2.2
  refine WP.seq (WP.mono (outLen_ok hz hol h) fun s₁ ⟨m₁, rc₁, e₁⟩ => ?_)
  rw [en] at rc₁
  refine WP.seq (WP.mono (outLoop_ok (n := n) hn.1 (by omega) (by omega) rc₁
    (fun j hj => by rw [m₁.kr.x23, add_ofNat]; exact in_rw hp hz m₁.kr (by omega))
    (fun j hj => by
      rw [m₁.x22, add_ofNat]
      exact ⟨outR s₀, by rw [m₁.kr.wr, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [m₁.kr.x23, m₁.x22]; exact ((hp.o_s.sub_left osub).sub_right (part_sub (by omega))).symm))
    fun s₂ c₂ => ?_)
  rw [m₁.kr.x23, m₁.x22] at c₂
  have f₂ : Frame [(⟨out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ : Region)] s₁.mem s₂.mem := by
    rw [c₂.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have od : ∀ {X : Region}, Region.Sub X (scR (H := H) s₀) →
      ∀ r ∈ [(⟨out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ : Region)], X.Disjoint r := fun hX r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hp.o_s.sub_left osub).sub_right hX).symm
  have k₂ : KR (H := H) s₀ s₂ := m₁.kr.keep c₂.rd c₂.wr c₂.sp (fun r hr => c₂.other r (kregs_clob r hr)) f₂
    (od (part_sub (by omega))) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, osub⟩
  have g₂ : ∀ r ∈ eregs, s₂.gpr r = s₁.gpr r := fun r hr => c₂.other r (eregs_clob r hr)
  refine wp_add fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => WP.block_nil ?_
  have e₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have x21 : s₅.gpr .x21 = BitVec.ofNat 64 (ol s₀ - done H s₀ (k + 1)) := by
    rw [u₅.gpr, u₄.other .x21 (by decide), u₄.other .x24 (by decide), u₃.other .x21 (by decide),
      u₃.other .x24 (by decide), g₂ _ (by decide), c₂.x24, m₁.x21, sub_ofNat (by omega), hdn, Nat.sub_sub]
  refine ⟨⟨((k₂.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide), ?_, ?_, ?_, x21, ?_, ?_, ?_⟩, ?_⟩
  · rw [e₅]; exact m₁.st.keep hz hH f₂ (od (part_sub (by omega)))
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂ _ (by decide), m₁.x19]
    exact (ofNat_succ _).symm
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), m₁.x20]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂ _ (by decide), c₂.x24, m₁.x22, add_ofNat,
      hdn]
  · rw [G_succ, List.length_append, hg, ← ht, bytesAt_length, Nat.succ_mul]
  · rw [e₅, hdn, bytesAt_add, bytes_keep f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (Nat.le_refl _) (by omega)).symm)
      (by omega),
      c₂.mem, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega),
      m₁.outB, G_succ, ← hg, List.take_length_add_append, ← ht, e₁, ← bytesAt_take _ _ hn.2.1]
  · change eval (.nonzero .x .x21) s₅ = _
    rw [eval_nonzero, x21, ofNat_ne_zero (by omega)]
    simp only [Option.some.injEq, decide_eq_decide]
    omega

/-! ## The loop and `pbkdf2` -/

/-- One block of the output. -/
theorem block_ok (hH : HashOK H) (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W))
    (hFd : H.hmacFin.aarch64Depth ≤ 1) (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W))
    (hId : H.iterate.aarch64Depth ≤ 1) {k : Nat} (hk : k < nb H s₀) {s : State} (h : Inv hH s₀ k s) :
    WP isa H.block s fun t =>
      Inv hH s₀ (k + 1) t ∧ isa.eval (.nonzero .x .x21) t = some (decide (k + 1 ≠ nb H s₀)) := by
  have hkD : k * H.D < ol s₀ := (lt_nb hz.z.D0).1 hk
  have hd : done H s₀ k = k * H.D := by show min _ _ = _; omega
  have hb := h.outB
  rw [hd, List.take_of_length_le (Nat.le_of_eq h.glen)] at hb
  have m : Mid hH s₀ k s := ⟨h.kr, h.st, h.x19, h.x20, by rw [h.x21, hd], by rw [h.x22, hd], hb⟩
  unfold Hash.block
  refine WP.seq (WP.mono (pieceA_ok hp hz hH hk m) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (callA_ok hp hz hH hk h₁) fun s₂ ⟨m₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (finArgs_ok hp hz hH m₂ r₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (callB_ok hp hz hH hF hFd hk h₃) fun s₄ ⟨m₄, u₄⟩ => ?_)
  refine WP.seq (WP.mono (pieceC_ok hp hz hH hk m₄ u₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (callC_ok hp hz hH hI hId hk h₅) fun s₆ ⟨m₆, t₆⟩ => ?_)
  exact tail_ok hp hz hH hk h.glen m₆ t₆

/-- The loop over the blocks of the output: none when `out_len = 0`. -/
theorem loop_ok (hH : HashOK H) (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W))
    (hFd : H.hmacFin.aarch64Depth ≤ 1) (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W))
    (hId : H.iterate.aarch64Depth ≤ 1) {s : State} (h : Inv hH s₀ 0 s)
    (hz0 : isa.eval (.zero .x .x21) s = some (decide (ol s₀ = 0))) :
    WP isa (.ite (.zero .x .x21) (.block []) (.loop H.block (.nonzero .x .x21))) s (Inv hH s₀ (nb H s₀)) := by
  have hD := hz.z.D0
  refine WP.ite (decide (ol s₀ = 0)) hz0 (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · rw [(nb_zero hD).2 (of_decide_eq_true h0)]; exact h
  · have : nb H s₀ ≠ 0 := fun e => by simp [(nb_zero hD).1 e] at h0
    exact nb_loop (Nat.pos_of_ne_zero this) (Inv hH s₀)
      (fun k hk t ht => block_ok hp hz hH hF hFd hI hId hk ht) h

theorem correct (hH : HashOK H) (hIn : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hInd : H.hmacInit.aarch64Depth ≤ 1) (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W))
    (hFd : H.hmacFin.aarch64Depth ≤ 1) (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W))
    (hId : H.iterate.aarch64Depth ≤ 1) :
    WP isa H.pbkdf2 s₀ fun s' => abiPreserved s₀ s' ∧ (pbkG hH.SH (H.W + H.S)).post s₀ s' := by
  apply WP.withPreservedV (hc := hH.pbkdf2_keepsV)
  have hD := hz.z.D0; have hW := hz.W
  unfold Hash.pbkdf2
  refine WP.seq (WP.mono (entry_ok hp hz) fun s₁ k₁ => ?_)
  refine WP.seq (WP.mono (key_ok hp hz hH k₁) fun s₂ ⟨k₂, x2₂, x3₂, ka⟩ => ?_)
  refine WP.seq (WP.mono (setup_ok hp hz hH hIn hInd k₂ x2₂ x3₂ ka) fun s₃ ⟨k₃, st₃⟩ => ?_)
  refine WP.seq (WP.mono (loopRegs_ok hp hz hH k₃ st₃) fun s₄ ⟨i₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hp hz hH hF hFd hI hId i₄ z₄) fun s₅ i₅ => ?_)
  have k₅ := i₅.kr
  unfold Hash.exit
  refine WP.mono (restore_ok H.hh k₅.x23 (by show H.W ≤ 1024; omega) k₅.saved (in_wr hp k₅)
    (by have : H.S = H.P.N + H.P.B := rfl; have := hz.B_ge; show 8 * H.W + 56 ≤ (H.W + H.S) * 8; omega))
    fun s' ⟨hm, _, _, hsp, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hsp, k₅.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hg _ (by decide)
      | exact (ho _ (by decide)).trans (k₅.cs _ (by decide))
  have hdone : done H s₀ (nb H s₀) = ol s₀ := by
    have := ol_le (s₀ := s₀) hD; show min _ _ = _; omega
  have hb := i₅.outB
  rw [hdone] at hb
  show Spec.Pbkdf2.pbkdf2Hmac hH.SH (bytesAt s₀.mem (pw s₀) (pwl s₀)) (saltB s₀) (cc s₀) (ol s₀) =
    some (bytesAt s'.mem (out s₀) (ol s₀))
  have hol := hp.olD
  rw [Spec.Pbkdf2.pbkdf2Hmac, hH.hD, Spec.Pbkdf2.pbkdf2, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hm,
    hb]
  rfl

end

end VG.Proof.Pbkdf2.Md.AArch64.Pbk
