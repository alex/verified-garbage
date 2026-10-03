import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Pbkdf2
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`'s loop

After `k` blocks of the output (`Inv`), `out` holds the first `min (k D)
out_len` bytes of `T₁ ‖ … ‖ T_k`; a step computes `T_{k+1}` (`U₁` by `update`
with `INT (k + 1)` and HMAC's `finalize`, then `iterate`) and copies as much
of it as the output still needs.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64 VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK ea_nat wp_mov32r zx32 contains_pre)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG After SavedRegs SavedRegs.frame)
open VG.Proof.Hmac.Generic.Common (bytes_keep readW_writeW_ne InRegions.right' sub_of_off sub_of_self bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep bytesAt_getD' writeBytes_at xorPad_length)
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

/-- After `k` blocks of the output. -/
structure Inv (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : KR (H := H) s₀ s
  st : States hH s₀ s.mem
  rbx : s.gpr .rbx = BitVec.ofNat 64 (k + 1)
  rbp : s.gpr .rbp = s₀.gpr .rcx
  r12 : s.gpr .r12 = BitVec.ofNat 64 (ol s₀ - done H s₀ k)
  r13 : s.gpr .r13 = out s₀ + BitVec.ofNat 64 (done H s₀ k)
  glen : (G hH s₀ k).length = k * H.D
  outB : bytesAt s.mem (out s₀) (done H s₀ k) = (G hH s₀ k).take (done H s₀ k)

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

theorem loopRegs_ok (hH : HashOK H) {s : State} (h : KR (H := H) s₀ s) (h13 : s.gpr .r13 = s₀.gpr .rcx)
    (hS : States hH s₀ s.mem) :
    WP isa (.block H.loopRegs) s fun t => Inv hH s₀ 0 t ∧ t.zf = some (decide (ol s₀ = 0)) := by
  unfold Hash.loopRegs
  refine wp_mov fun s₁ u₁ _ _ => ?_
  refine wp_movm (a := A s₀ H.outO) (by rw [ea_nat, u₁.other _ (by decide), h.r15])
    (by rw [u₁.rd, u₁.wr]; exact InRegions.right' (in_sc hp hz h.wr (by
      have := layout (H := H); have := end_le hz; omega))) fun s₂ u₂ => ?_
  refine wp_movm (a := s₀.gpr .rsp + BitVec.ofNat 64 8)
    (by rw [ea_nat, u₂.other _ (by decide), u₁.other _ (by decide), h.rsp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, hp.rd]
        exact ⟨argR s₀, by simp, contains_pre (by decide)⟩) fun s₃ u₃ => ?_
  refine wp_mov32i fun s₄ u₄ _ _ => wp_test fun s₅ g₅ m₅ rd₅ wr₅ z₅ => WP.block_nil ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r12 : s₅.gpr .r12 = BitVec.ofNat 64 (ol s₀) := by
    rw [g₅, u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, h.olW hp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have k₅ := (((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)
  refine ⟨⟨k₅.same rd₅ wr₅ (by rw [g₅]) (by rw [g₅]) m₅, ?_, ?_, ?_, ?_, ?_,
    by simp [G], by simp [bytesAt]⟩, ?_⟩
  · rw [m₅, m₄]; exact hS
  · rw [g₅, u₄.gpr]; rfl
  · rw [g₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h13]
  · rw [r12]; simp
  · rw [g₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, h.outW]; simp
  · rw [z₅, BitVec.and_self, ← g₅, r12, ofNat_beq_zero (stackArg s₀ 0).isLt]

end

/-! ## Facts about words and lengths -/

theorem bytes32_int (i : Nat) : VG.Proof.MdStream.bytes32 true (BitVec.ofNat 32 i) = Spec.Pbkdf2.int i := by
  simp only [VG.Proof.MdStream.bytes32, ite_true, Spec.Pbkdf2.int, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] <;> omega

theorem sw32 (y : BitVec 32) : (y.setWidth 64).setWidth 32 = y := by
  have := y.isLt
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; omega

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

/-! ## A step, before `T` is copied out -/

/-- The registers a step keeps until `T` is copied out. -/
abbrev mregs : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

theorem mregs_saved : ∀ r ∈ mregs, r ∈ calleeSaved := by decide

/-- In step `k`, before `T_{k+1}` is copied out: the key's states, the
registers, and the first `k` blocks in `out`. -/
structure Mid (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : KR (H := H) s₀ s
  st : States hH s₀ s.mem
  rbx : s.gpr .rbx = BitVec.ofNat 64 (k + 1)
  rbp : s.gpr .rbp = s₀.gpr .rcx
  r12 : s.gpr .r12 = BitVec.ofNat 64 (ol s₀ - k * H.D)
  r13 : s.gpr .r13 = out s₀ + BitVec.ofNat 64 (k * H.D)
  outB : bytesAt s.mem (out s₀) (k * H.D) = G hH s₀ k

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

/-- What a call (or a write) leaves, writing parts of `scratch` from the
working state on, or its working space, and the stack below `rsp`. -/
theorem Mid.call (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : Mid hH s₀ k s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ mregs, s'.gpr r = s.gpr r)
    {ws : List Region} {n : Nat} (hn : n ≤ 24) (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ j, r = ⟨scr s₀, j⟩ ∧ j ≤ 8 * H.W) ∨
      ∃ o j, r = sR s₀ o j ∧ H.stWO ≤ o ∧ o + j ≤ (H.W + H.S) * 8) : Mid hH s₀ k s' := by
  have hl := layout (H := H); have he := end_le hz
  have hst : H.sv + 64 = H.st0O := by simp [Hash.st0O]
  have ho : Region.Sub ⟨out s₀, k * H.D⟩ (outR s₀) := Region.sub_prefix hk
  have key : ∀ {X : Region}, (∀ o j, H.stWO ≤ o → o + j ≤ (H.W + H.S) * 8 → X.Disjoint (sR s₀ o j)) →
      X.Disjoint (lowR (H := H) s₀) → X.Disjoint (below (s.gpr .rsp) n) →
      ∀ r ∈ ws ++ [below (s.gpr .rsp) n], X.Disjoint r := by
    intro X h1 h2 h3 r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨j, rfl, hj⟩ | ⟨o, j, rfl, ho1, ho2⟩
      · exact h2.sub_right (Region.sub_prefix hj)
      · exact h1 o j ho1 ho2
    · simp only [List.mem_singleton] at hr; subst hr; exact h3
  have hstk : ∀ {X : Region}, Region.Sub X (scR (H := H) s₀) → X.Disjoint (below (s.gpr .rsp) n) :=
    fun hX => (stk_sc hp h.kr hn hX).symm
  refine ⟨h.kr.keep hrd hwr (hcs _ (by simp)) (hcs _ (by simp)) hf
      (key (fun o j h1 h2 => part_disj hz (Or.inl (by omega)) (by omega) h2) (low_disj hz (by omega) (by omega))
        (hstk (part_sub (by omega)))) (fun r hr => ?_),
    h.st.keep hz hH hf (key (fun o j h1 h2 => part_disj hz (Or.inl (by omega)) (by omega) h2)
      (low_disj hz (by omega) (by omega)) (hstk (part_sub (by omega)))),
    by rw [hcs _ (by simp), h.rbx], by rw [hcs _ (by simp), h.rbp],
    by rw [hcs _ (by simp), h.r12], by rw [hcs _ (by simp), h.r13], ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨j, rfl, hj⟩ | ⟨o, j, rfl, _, h2⟩
      · exact ⟨scR (H := H) s₀, by simp, Region.sub_prefix (by show j ≤ (H.W + H.S) * 8; omega)⟩
      · exact ⟨_, by simp, part_sub h2⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, stk_sub h.kr hn⟩
  · rw [← h.outB]
    exact bytes_keep hf (key (fun o j _ h2 => (hp.o_s.sub_left ho).sub_right (part_sub h2))
      ((hp.o_s.sub_left ho).sub_right low_sub) ((hp.stk_o.sub_left (stk_sub h.kr hn)).sub_right ho).symm)
      (by have := hp.onw; omega)

/-- A write into a part of `scratch` from the working state on. -/
theorem Mid.write (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : Mid hH s₀ k s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r ∈ mregs, s'.gpr r = s.gpr r) {o n : Nat}
    (ho : H.stWO ≤ o) (hon : o + n ≤ (H.W + H.S) * 8) (hf : Frame [sR s₀ o n] s.mem s'.mem) :
    Mid hH s₀ k s' :=
  h.call hp hz hH hk hrd hwr hg (n := 0) (Nat.zero_le _) (hf.mono fun _ hr => List.mem_append_left _ hr)
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨o, n, rfl, ho, hon⟩

omit hp hz in
theorem Mid.upd {hH : HashOK H} {k : Nat} {s s' : State} (h : Mid hH s₀ k s) {d : Reg} {v : BitVec 64}
    (u : Upd s s' d v) (hd : d ∉ mregs) : Mid hH s₀ k s' := by
  have ne : ∀ r ∈ mregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u ⟨(ne _ (by simp)).symm, (ne _ (by simp)).symm⟩, u.mem ▸ h.st,
    by rw [u.other _ (ne _ (by simp)), h.rbx], by rw [u.other _ (ne _ (by simp)), h.rbp],
    by rw [u.other _ (ne _ (by simp)), h.r12], by rw [u.other _ (ne _ (by simp)), h.r13],
    by rw [u.mem, h.outB]⟩

end

/-! ## Copying `T` out -/

theorem ea_r13 (s : State) (k : Nat) (h14 : s.gpr .r14 = BitVec.ofNat 64 k) :
    s.ea { base := .r13, index := some .r14 } = s.gpr .r13 + BitVec.ofNat 64 k := by
  simp only [State.ea, h14]
  rw [show BitVec.ofInt 64 0 = 0#64 from rfl, show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one, BitVec.add_zero]

theorem outLoop_ok {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 31) {s : State} (hc : s.gpr .rcx = BitVec.ofNat 64 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .r15 + BitVec.ofNat 64 H.tO + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (s.gpr .r13 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr .r15 + BitVec.ofNat 64 H.tO, n⟩ ⟨s.gpr .r13, n⟩) :
    WP isa H.outLoop s fun t => VG.Proof.Pbkdf2.Md.X86_64.Calls.Copied s (s.gpr .r13)
      (bytesAt s.mem (s.gpr .r15 + BitVec.ofNat 64 H.tO) n) t := by
  generalize eA : s.gpr .r15 + BitVec.ofNat 64 H.tO = A at hin hsep ⊢
  generalize eB : s.gpr .r13 = B at hout hsep ⊢
  refine WP.seq (wp_mov32i fun s₀ u₀ _ _ => WP.block_nil ?_)
  have i0 : VG.Proof.Pbkdf2.Md.X86_64.Calls.CopyInv s A B 0 s₀ :=
    ⟨u₀.rd, u₀.wr, fun r _ h => u₀.other r h, by rw [u₀.gpr]; rfl,
      by rw [u₀.mem, bytesAt, List.range_zero, List.map_nil, writeBytes_nil]⟩
  refine WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.count_loop hn _ (fun k hk t h => ?_) i0)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  refine wp_movzx8 (a := A + BitVec.ofNat 64 k)
    (by rw [VG.Proof.Pbkdf2.Md.X86_64.Calls.ea_byteAt _ _ _ _ h.r14, h.other _ (by decide) (by decide), eA])
    (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_store8 (a := B + BitVec.ofNat 64 k)
    (by rw [ea_r13 _ k (by rw [u₁.other _ (by decide), h.r14]), u₁.other _ (by decide),
      h.other _ (by decide) (by decide), eB]) (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_cmp fun t₄ g₄ m₄ rd₄ wr₄ _ z₄ => WP.block_nil ?_
  have h14 : t₃.gpr .r14 = BitVec.ofNat 64 (k + 1) := by
    rw [u₃.gpr, g₂, u₁.other _ (by decide), h.r14, VG.Proof.Pbkdf2.Md.X86_64.Calls.sx_one, ← ofNat_succ]
  have hcx : t₃.gpr .rcx = BitVec.ofNat 64 n := by
    rw [u₃.other _ (by decide), g₂, u₁.other _ (by decide), h.other _ (by decide) (by decide), hc]
  refine ⟨⟨by rw [rd₄, u₃.rd, rd₂, u₁.rd, h.rd], by rw [wr₄, u₃.wr, wr₂, u₁.wr, h.wr],
    fun r ha h14' => by rw [g₄, u₃.other r h14', g₂, u₁.other r ha, h.other r ha h14'],
    by rw [g₄, h14], ?_⟩, by rw [z₄, h14, hcx, sub_beq (by omega) (by omega)]⟩
  have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
  rw [m₄, u₃.mem, m₂, u₁.gpr, u₁.mem, h.mem, VG.Proof.Hmac.Generic.Common.bytesAt_snoc']
  have e : writeBytes s.mem B (bytesAt s.mem A k) (A + BitVec.ofNat 64 k) = s.mem (A + BitVec.ofNat 64 k) := by
    simp only [writeBytes, hl, VG.Proof.Hmac.Generic.Common.not_mem_of_disjoint hsep hk (Nat.le_of_lt hk)
      (by omega), ↓reduceIte]
  have e' := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem B (bytesAt s.mem A k)
    (s.mem (A + BitVec.ofNat 64 k)) (by rw [hl]; omega)
  rw [hl] at e'
  rw [e, show ((s.mem (A + BitVec.ofNat 64 k)).setWidth 64).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) by
    simp, e']

/-! ## A step: `U₁` -/

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

/-- `U₁ = PRF (S ‖ INT (k + 1))`. -/
abbrev U1 (hH : HashOK H) (s₀ : State) (k : Nat) : List Byte :=
  hmacBlockKey hH.SH.H (K0 hH s₀) (saltB s₀ ++ Spec.Pbkdf2.int (k + 1))

/-- Before `update` with `INT (k + 1)`. -/
structure AtUpd (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : Mid hH s₀ k s
  args : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream s (A s₀ H.stWO) (A s₀ H.intO) (scr s₀) 4
  rsi : s.gpr .rsi = s₀.gpr .rcx + (BitVec.ofNat 32 H.P.B).signExtend 64
  repr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀)
  int : bytesAt s.mem (A s₀ H.intO) 4 = Spec.Pbkdf2.int (k + 1)

/-- Before HMAC's `finalize`. -/
structure AtFin (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : Mid hH s₀ k s
  args : FinArgs (H := H) s (A s₀ H.stWO) (A s₀ H.st1O) (s₀.gpr .rcx + (BitVec.ofNat 32 (H.P.B + 4)).signExtend 64)
    (A s₀ H.uO) (scr s₀)
  repr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1))

/-- Before `iterate`. -/
structure AtIter (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : Mid hH s₀ k s
  args : IterArgs (H := H) s (A s₀ H.st0O) (A s₀ H.uO) (BitVec.ofNat 64 (cc s₀ - 1)) (A s₀ H.tO) (scr s₀)
  u : bytesAt s.mem (A s₀ H.uO) H.D = U1 hH s₀ k
  t : bytesAt s.mem (A s₀ H.tO) H.D = U1 hH s₀ k

/-- A copy of the salted inner state, `INT (k + 1)`, and `update`'s arguments. -/
theorem pieceA_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s : State} (h : Mid hH s₀ k s) :
    WP isa (.seq (VG.Impl.Pbkdf2.Md.X86_64.copy .r15 H.stSO .r15 H.stWO H.S) (.block H.intArgs)) s
      (AtUpd hH s₀ k) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  -- The working state, copied.
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.copy_ok (src := .r15) (dst := .r15) (by decide)
    (by decide) (so := H.stSO) (d := H.stWO) (n := H.S) (by omega) (by omega) (s := s)
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact InRegions.right' (in_sc hp hz h.kr.wr (by omega)))
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact in_sc hp hz h.kr.wr (by omega))
    (by rw [h.kr.r15]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega))) fun s₁ c₁ => ?_)
  rw [h.kr.r15] at c₁
  have m₁ := h.write hp hz hH (Nat.le_of_lt hkD) c₁.rd c₁.wr (fun r hr => c₁.other r (by rintro rfl; simp at hr)
    (by rintro rfl; simp at hr)) (o := H.stWO) (n := H.S) (Nat.le_refl _) (by omega) (by
      rw [c₁.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _))
  have rs₁ : hH.SH.Repr s₁.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀) := by
    rw [c₁.mem]; exact repr_copy hH h.st.s
  -- `INT (k + 1)`.
  simp only [Hash.intArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov32r fun s₂ u₂ => wp_bswap32 fun s₃ u₃ => ?_
  have m₃ := (m₁.upd u₂ (by decide)).upd u₃ (by decide)
  refine wp_store32 (a := A s₀ H.intO) (by rw [ea_nat, m₃.kr.r15]) (in_sc hp hz m₃.kr.wr (by omega))
    fun s₄ g₄ e₄ rd₄ wr₄ => ?_
  have f₄ : Frame [sR s₀ H.intO 4] s₃.mem s₄.mem := by
    rw [e₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have m₄ := m₃.write hp hz hH (Nat.le_of_lt hkD) rd₄ wr₄ (fun r _ => by rw [g₄]) (o := H.intO) (n := 4) (by omega)
    (by omega) f₄
  have e₄' : s₄.mem = writeBytes s₃.mem (A s₀ H.intO) (Spec.Pbkdf2.int (k + 1)) := by
    rw [e₄, u₃.gpr, u₂.gpr, m₁.rbx, sw32, sw32,
      show (BitVec.ofNat 64 (k + 1)).setWidth 32 = BitVec.ofNat 32 (k + 1) from
        BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega),
      show bswap32 (BitVec.ofNat 32 (k + 1)) = if true then bswap32 (BitVec.ofNat 32 (k + 1)) else _ from rfl,
      writeW32, bytes32_int]
  -- `update`'s arguments.
  refine scr_ok m₄.kr.r15 (by omega) fun s₅ u₅ => wp_mov fun s₆ u₆ _ _ => wp_addi fun s₇ u₇ => ?_
  have m₇ := ((m₄.upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)
  refine scr_ok m₇.kr.r15 (by omega) fun s₈ u₈ => wp_mov32i fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ =>
    WP.block_nil ?_
  have m₁₀ := ((m₇.upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀ (by decide)
  have e₁₀ : s₁₀.mem = s₄.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  have ua : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream s₁₀ (A s₀ H.stWO) (A s₀ H.intO) (scr s₀) 4 :=
    { rdi := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
          u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
      rdx := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]
      rcx := by rw [u₁₀.other _ (by decide), u₉.gpr]; rfl
      r8 := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), m₇.kr.r15]
      cd := Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨r', h', off, e, l⟩ := cov_part hp m₁₀.kr (o := H.intO) (n := 4) (by omega)
        exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp m₁₀.kr (by omega)
        · exact cov_low hp m₁₀.kr (by rw [hWb]; omega)
      st_sc := (low_disj hz (by omega) (by omega)).sub_right (Region.sub_prefix (by rw [hWb]; omega))
      d_st := part_disj hz (Or.inr (by omega)) (by omega) (by omega)
      d_sc := (low_disj hz (by omega) (by omega)).sub_right (Region.sub_prefix (by rw [hWb]; omega))
      stk_st := stk_sc hp m₁₀.kr (by omega) (part_sub (by omega))
      stk_d := stk_sc hp m₁₀.kr (by omega) (part_sub (by omega))
      stk_sc := stk_sc hp m₁₀.kr (by omega) (Region.sub_prefix (by rw [hWb]; omega)) }
  refine ⟨m₁₀, ua, ?_, by rw [e₁₀]; exact repr_keep hH f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)) (by rw [u₃.mem, u₂.mem]; exact rs₁),
    by rw [e₁₀, e₄', VG.Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (by rfl) (by omega)]⟩
  rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr,
    u₅.other _ (by decide), m₄.rbp]

/-- `update` with `INT (k + 1)`. -/
theorem callA_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s : State} (h : AtUpd hH s₀ k s) :
    WP isa (.call H.updN H.updC) s fun t => Mid hH s₀ k t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_call hH.stream h.args (by omega) fun s₁₁ a₁₁ r₁₁ => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' a₁₁.rd a₁₁.wr (fun r hr => a₁₁.cs r (mregs_saved r hr)) (by omega)
      a₁₁.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr ⟨_, _, rfl, Nat.le_refl _, by omega⟩
        · exact .inl ⟨_, rfl, by rw [hWb]; omega⟩
  · have := r₁₁ _ h.repr (by
      rw [h.rsi, sx_ofNat (by omega), List.length_append, xorPad_length,
        blockKey_length, bytesAt_length, Nat.add_comm, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    rwa [h.int] at this

/-- HMAC's `finalize`'s arguments. -/
theorem finArgs_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s : State} (h : Mid hH s₀ k s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (K0 hH s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.block H.finArgs) s (AtFin hH s₀ k) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  -- `finalize`'s arguments.
  simp only [Hash.finArgs, List.append_assoc]
  refine scr_ok h.kr.r15 (by omega) fun s₁ u₁ => ?_
  refine scr_ok ((u₁.other _ (by decide)).trans h.kr.r15) (by omega) fun s₂ u₂ => ?_
  simp only [List.cons_append]
  refine wp_mov fun s₃ u₃ _ _ => wp_addi fun s₄ u₄ => ?_
  have m₄ := (((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)
  refine scr_ok m₄.kr.r15 (by omega) fun s₅ u₅ => wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  have m₆ := (m₄.upd u₅ (by decide)).upd u₆ (by decide)
  have e₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have stk : ∀ {o n : Nat}, o + n ≤ (H.W + H.S) * 8 → (below (s₆.gpr .rsp) 24).Disjoint (sR s₀ o n) :=
    fun h => stk_sc hp m₆.kr (Nat.le_refl _) (part_sub h)
  have fa : FinArgs (H := H) s₆ (A s₀ H.stWO) (A s₀ H.st1O) (s₀.gpr .rcx + (BitVec.ofNat 32 (H.P.B + 4)).signExtend 64)
      (A s₀ H.uO) (scr s₀) :=
    { rdi := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      rsi := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.gpr]
      rdx := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), h.rbp]
      rcx := by rw [u₆.other _ (by decide), u₅.gpr]
      r8 := by rw [u₆.gpr, u₅.other _ (by decide), m₄.kr.r15]
      cr := Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨r', h', off, e, l⟩ := cov_part hp m₆.kr (o := H.st1O) (n := H.S) (by omega)
        exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp m₆.kr (by omega)
        · exact cov_part hp m₆.kr (by omega)
        · exact cov_low hp m₆.kr (by omega)
      i_u := part_disj hz (Or.inr (by omega)) (by omega) (by omega)
      i_o := part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      i_s := low_disj hz (by omega) (by omega)
      u_o := part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      u_s := low_disj hz (by omega) (by omega)
      o_s := low_disj hz (by omega) (by omega)
      stk_i := stk (by omega)
      stk_u := stk (by omega)
      stk_o := stk (by omega)
      stk_s := stk_sc hp m₆.kr (Nat.le_refl _) low_sub
      scnw := by have := hp.snw; omega }
  exact ⟨m₆, fa, by rw [e₆]; exact hr⟩

/-- HMAC's `finalize`: `U₁`. -/
theorem callB_ok (hH : HashOK H) (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W))
    (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2) {k : Nat} (hk : k < nb H s₀) {s : State}
    (h : AtFin hH s₀ k s) :
    WP isa (.call H.hmacFinN H.hmacFin) s fun t => Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.uO) H.D = U1 hH s₀ k := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  refine hfin_call hH hF hFsp hFd h.args fun s₇ rd₇ wr₇ cs₇ f₇ hpost => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' rd₇ wr₇ (fun r hr => cs₇ r (mregs_saved r hr)) (Nat.le_refl _) f₇
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inr ⟨_, _, rfl, Nat.le_refl _, by omega⟩
        · exact .inr ⟨_, _, rfl, by omega, by omega⟩
        · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  · have hK := blockKey_length hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
    exact hpost _ _ hK (by rw [hK, List.length_append, bytesAt_length]; simp [Spec.Pbkdf2.int]; omega)
      (by rw [← List.append_assoc]; exact h.repr)
      (by
        rw [sx_ofNat (by omega), List.length_append, bytesAt_length,
          show (Spec.Pbkdf2.int (k + 1)).length = 4 from rfl]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        have : sl s₀ = (s₀.gpr .rcx).toNat := rfl
        omega)
      h.mid.st.o

/-- `U` copied to `T`, and `iterate`'s arguments. -/
theorem pieceC_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) {s₇ : State} (m₇ : Mid hH s₀ k s₇)
    (hU : bytesAt s₇.mem (A s₀ H.uO) H.D = U1 hH s₀ k) :
    WP isa (.seq (VG.Impl.Pbkdf2.Md.X86_64.copy .r15 H.uO .r15 H.tO H.D) (.block H.iterArgs)) s₇
      (AtIter hH s₀ k) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  -- `U` copied to `T`.
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.copy_ok (src := .r15) (dst := .r15) (by decide)
    (by decide) (so := H.uO) (d := H.tO) (n := H.D) hD.1 (by omega) (s := s₇)
    (fun j hj => by rw [m₇.kr.r15, add_ofNat]; exact InRegions.right' (in_sc hp hz m₇.kr.wr (by omega)))
    (fun j hj => by rw [m₇.kr.r15, add_ofNat]; exact in_sc hp hz m₇.kr.wr (by omega))
    (by rw [m₇.kr.r15]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega))) fun s₈ c₈ => ?_)
  rw [m₇.kr.r15] at c₈
  have f₈ : Frame [sR s₀ H.tO H.D] s₇.mem s₈.mem := by
    rw [c₈.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have m₈ := m₇.write hp hz hH hk' c₈.rd c₈.wr (fun r hr => c₈.other r (by rintro rfl; simp at hr)
    (by rintro rfl; simp at hr)) (o := H.tO) (n := H.D) (by omega) (by omega) f₈
  have hU₈ : bytesAt s₈.mem (A s₀ H.uO) H.D = bytesAt s₇.mem (A s₀ H.uO) H.D :=
    bytes_keep f₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)) (by omega)
  have hT₈ : bytesAt s₈.mem (A s₀ H.tO) H.D = bytesAt s₇.mem (A s₀ H.uO) H.D := by
    rw [c₈.mem]; exact VG.Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega)
  -- `iterate`'s arguments.
  simp only [Hash.iterArgs, List.append_assoc]
  refine scr_ok m₈.kr.r15 (by omega) fun s₉ u₉ => ?_
  refine scr_ok ((u₉.other _ (by decide)).trans m₈.kr.r15) (by omega) fun s₁₀ u₁₀ => ?_
  have m₁₀ := (m₈.upd u₉ (by decide)).upd u₁₀ (by decide)
  simp only [List.cons_append, List.nil_append]
  refine wp_movm (a := A s₀ H.cO) (by rw [ea_nat, m₁₀.kr.r15])
    (InRegions.right' (in_sc hp hz m₁₀.kr.wr (by omega))) fun s₁₁ u₁₁ => ?_
  have m₁₁ := m₁₀.upd u₁₁ (by decide)
  refine scr_ok m₁₁.kr.r15 (by omega) fun s₁₂ u₁₂ => wp_mov fun s₁₃ u₁₃ _ _ => WP.block_nil ?_
  have m₁₃ := (m₁₁.upd u₁₂ (by decide)).upd u₁₃ (by decide)
  have e₁₃ : s₁₃.mem = s₈.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  have stk' : ∀ {o n : Nat}, o + n ≤ (H.W + H.S) * 8 → (below (s₁₃.gpr .rsp) 24).Disjoint (sR s₀ o n) :=
    fun h => stk_sc hp m₁₃.kr (Nat.le_refl _) (part_sub h)
  have ia : IterArgs (H := H) s₁₃ (A s₀ H.st0O) (A s₀ H.uO) (BitVec.ofNat 64 (cc s₀ - 1)) (A s₀ H.tO) (scr s₀) :=
    { rdi := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
          u₁₀.other _ (by decide), u₉.gpr]
      rsi := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr]
      rdx := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, m₁₀.kr.cW]
      rcx := by rw [u₁₃.other _ (by decide), u₁₂.gpr]
      r8 := by rw [u₁₃.gpr, u₁₂.other _ (by decide), m₁₁.kr.r15]
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
      stk_k := stk' (by omega)
      stk_u := stk' (by omega)
      stk_t := stk' (by omega)
      stk_s := stk_sc hp m₁₃.kr (Nat.le_refl _) low_sub
      knw := by
        have := hp.snw
        simp only [A, BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      scnw := by have := hp.snw; omega }
  exact ⟨m₁₃, ia, by rw [e₁₃, hU₈, hU], by rw [e₁₃, hT₈, hU]⟩

/-- `iterate`: `T_{k+1}`. -/
theorem callC_ok (hH : HashOK H) (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate)
    (hId : H.iterate.depth ≤ 2) {k : Nat} (hk : k < nb H s₀) {s : State} (h : AtIter hH s₀ k s) :
    WP isa (.call H.iterN H.iterate) s fun t => Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.tO) H.D = Tb hH s₀ (k + 1) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D; have hfit := hz.z.fits
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := len_add_le hp.sa_s hp.sanw hp.snw
  refine iter_call hH hI hIsp hId h.args fun s₁₄ rd₁₄ wr₁₄ cs₁₄ f₁₄ hpost' => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' rd₁₄ wr₁₄ (fun r hr => cs₁₄ r (mregs_saved r hr)) (Nat.le_refl _) f₁₄
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr ⟨_, _, rfl, by omega, by omega⟩
        · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  have hK := blockKey_length hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  have hc : ((BitVec.ofNat 64 (cc s₀ - 1)).setWidth 32).toNat = cc s₀ - 1 := by
    have := ((s₀.gpr .r8).setWidth 32).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hO : A s₀ H.st0O + BitVec.ofNat 64 H.S = A s₀ H.st1O := by
    rw [add_ofNat, show H.st0O + H.S = H.st1O by omega]
  rw [hpost' _ hK h.mid.st.i (hO ▸ h.mid.st.o), hc, h.u, h.t]
  rfl

/-! ## A step: copying `T` out -/

omit hp hz in
theorem Mid.same {hH : HashOK H} {k : Nat} {s s' : State} (h : Mid hH s₀ k s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) : Mid hH s₀ k s' :=
  ⟨h.kr.same hrd hwr (by rw [hg]) (by rw [hg]) hm, hm ▸ h.st, by rw [hg, h.rbx], by rw [hg, h.rbp],
    by rw [hg, h.r12], by rw [hg, h.r13], by rw [hm, h.outB]⟩

omit hp in
/-- The bytes of `T` the output still needs. -/
theorem outLen_ok {hH : HashOK H} {k : Nat} {s : State} (h : Mid hH s₀ k s) :
    WP isa H.outLen s fun t => Mid hH s₀ k t ∧ t.gpr .rcx = BitVec.ofNat 64 (min (ol s₀ - k * H.D) H.D) ∧
      t.mem = s.mem := by
  have hD := hz.z.D; have hN := hz.z.N
  have hol : ol s₀ < 2 ^ 64 := (stackArg s₀ 0).isLt
  unfold Hash.outLen
  refine WP.seq (wp_mov32i fun s₁ u₁ _ _ => wp_cmp fun s₂ g₂ m₂ rd₂ wr₂ c₂ _ => WP.block_nil ?_)
  have e₂ : s₂.mem = s.mem := by rw [m₂, u₁.mem]
  have m₂ := (h.upd u₁ (by decide)).same rd₂ wr₂ g₂ m₂
  have rcx : s₂.gpr .rcx = BitVec.ofNat 64 H.D := by rw [g₂, u₁.gpr, zx_ofNat (by omega)]
  have cf : s₂.cf = some (decide (ol s₀ - k * H.D < H.D)) := by
    rw [c₂, ← g₂, m₂.r12, rcx, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
  refine WP.ite (decide (ol s₀ - k * H.D < H.D)) (by simp [eval, cf]) (fun hT => ?_) fun hF => WP.block_nil ?_
  · refine wp_mov fun s₃ u₃ _ _ => WP.block_nil ⟨m₂.upd u₃ (by decide), ?_, by rw [u₃.mem, e₂]⟩
    have : ol s₀ - k * H.D < H.D := of_decide_eq_true hT
    rw [u₃.gpr, m₂.r12, Nat.min_eq_left (Nat.le_of_lt this)]
  · have : ¬ ol s₀ - k * H.D < H.D := of_decide_eq_false (by simpa using hF)
    exact ⟨m₂, by rw [rcx, Nat.min_eq_right (by omega)], e₂⟩

/-- Copying as much of `T_{k+1}` as the output needs, and on to the next block. -/
theorem tail_ok (hH : HashOK H) {k : Nat} (hk : k < nb H s₀) (hg : (G hH s₀ k).length = k * H.D) {s : State}
    (h : Mid hH s₀ k s) (ht : bytesAt s.mem (A s₀ H.tO) H.D = Tb hH s₀ (k + 1)) :
    WP isa (.seq H.outLen (.seq H.outLoop (.block Hash.advance))) s fun t =>
      Inv hH s₀ (k + 1) t ∧ t.zf = some (decide (k + 1 = nb H s₀)) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz
  have hD := hz.z.D; have hN := hz.z.N
  have hol : ol s₀ < 2 ^ 64 := (stackArg s₀ 0).isLt
  have hkD : k * H.D < ol s₀ := (lt_nb hD.1).1 hk
  have hk32 : k + 1 < 2 ^ 32 := by have := nb_lt hD.1 hp.olD; omega
  have hk1 := lt_nb (s₀ := s₀) hD.1 (k := k + 1)
  rw [Nat.succ_mul] at hk1
  have hon := hp.onw
  generalize en : min (ol s₀ - k * H.D) H.D = n
  have hn : 0 < n ∧ n ≤ H.D ∧ k * H.D + n ≤ ol s₀ := by omega
  have hdn : done H s₀ (k + 1) = k * H.D + n := by
    show min ((k + 1) * H.D) (ol s₀) = _; rw [Nat.succ_mul]; omega
  have osub : Region.Sub ⟨out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ (outR s₀) := Offset.sub_base _ hn.2.2
  refine WP.seq (WP.mono (outLen_ok hz h) fun s₁ ⟨m₁, rc₁, e₁⟩ => ?_)
  rw [en] at rc₁
  refine WP.seq (WP.mono (outLoop_ok (n := n) hn.1 (by omega) rc₁
    (fun j hj => by rw [m₁.kr.r15, add_ofNat]; exact InRegions.right' (in_sc hp hz m₁.kr.wr (by omega)))
    (fun j hj => by
      rw [m₁.r13, add_ofNat]
      exact ⟨outR s₀, by rw [m₁.kr.wr, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [m₁.kr.r15, m₁.r13]; exact ((hp.o_s.sub_left osub).sub_right (part_sub (by omega))).symm))
    fun s₂ c₂ => ?_)
  rw [m₁.kr.r15, m₁.r13] at c₂
  have f₂ : Frame [(⟨out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ : Region)] s₁.mem s₂.mem := by
    rw [c₂.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have od : ∀ {X : Region}, Region.Sub X (scR (H := H) s₀) →
      ∀ r ∈ [(⟨out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ : Region)], X.Disjoint r := fun hX r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hp.o_s.sub_left osub).sub_right hX).symm
  have k₂ : KR (H := H) s₀ s₂ := m₁.kr.keep c₂.rd c₂.wr (c₂.other _ (by decide) (by decide))
    (c₂.other _ (by decide) (by decide)) f₂ (od (part_sub (by omega))) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, osub⟩
  refine wp_add fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_
  have g₄ : ∀ r, r ≠ .rax → r ≠ .r14 → r ≠ .r13 → r ≠ .rbx → s₄.gpr r = s₁.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other r h4, u₃.other r h3, c₂.other r h1 h2]
  have e₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨((k₂.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [e₅]; exact m₁.st.keep hz hH f₂ (od (part_sub (by omega)))
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), c₂.other _ (by decide) (by decide), m₁.rbx,
      VG.Proof.Pbkdf2.Md.X86_64.Calls.sx_one, ← ofNat_succ]
  · rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide), m₁.rbp]
  · rw [u₅.gpr, g₄ _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide) (by decide)
      (by decide), m₁.r12, rc₁, sub_ofNat (by omega), hdn]
    congr 1; omega
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, c₂.other _ (by decide) (by decide),
      c₂.other _ (by decide) (by decide), m₁.r13, rc₁, add_ofNat, hdn]
  · rw [G_succ, List.length_append, hg, ← ht, bytesAt_length, Nat.succ_mul]
  · rw [e₅, hdn, bytesAt_add, bytes_keep f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (Nat.le_refl _) (by omega)).symm)
      (by omega),
      c₂.mem, VG.Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega),
      m₁.outB, G_succ, ← hg, List.take_length_add_append, ← ht, e₁, ← bytesAt_take _ _ hn.2.1]
  · rw [z₅, g₄ _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide) (by decide)
      (by decide), m₁.r12, rc₁, sub_beq (by omega) (by omega)]
    simp only [Option.some.injEq, decide_eq_decide]
    omega

/-! ## The loop and `pbkdf2` -/

/-- One block of the output. -/
theorem block_ok (hH : HashOK H) (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W))
    (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2)
    (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate) (hId : H.iterate.depth ≤ 2)
    {k : Nat} (hk : k < nb H s₀) {s : State} (h : Inv hH s₀ k s) :
    WP isa H.block s fun t => Inv hH s₀ (k + 1) t ∧ t.zf = some (decide (k + 1 = nb H s₀)) := by
  have hkD : k * H.D < ol s₀ := (lt_nb hz.z.D.1).1 hk
  have hd : done H s₀ k = k * H.D := by show min _ _ = _; omega
  have hb := h.outB
  rw [hd, List.take_of_length_le (Nat.le_of_eq h.glen)] at hb
  have m : Mid hH s₀ k s := ⟨h.kr, h.st, h.rbx, h.rbp, by rw [h.r12, hd], by rw [h.r13, hd], hb⟩
  unfold Hash.block
  refine WP.assoc (WP.seq (WP.mono (pieceA_ok hp hz hH hk m) fun s₁ h₁ => ?_))
  refine WP.seq (WP.mono (callA_ok hp hz hH hk h₁) fun s₂ ⟨m₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (finArgs_ok hp hz hH hk m₂ r₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (callB_ok hp hz hH hF hFsp hFd hk h₃) fun s₄ ⟨m₄, u₄⟩ => ?_)
  refine WP.assoc (WP.seq (WP.mono (pieceC_ok hp hz hH hk m₄ u₄) fun s₅ h₅ => ?_))
  refine WP.seq (WP.mono (callC_ok hp hz hH hI hIsp hId hk h₅) fun s₆ ⟨m₆, t₆⟩ => ?_)
  exact tail_ok hp hz hH hk h.glen m₆ t₆

/-- The loop over the blocks of the output: none when `out_len = 0`. -/
theorem loop_ok (hH : HashOK H) (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W))
    (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2)
    (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate) (hId : H.iterate.depth ≤ 2)
    {s : State} (h : Inv hH s₀ 0 s) (hz0 : s.zf = some (decide (ol s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop H.block .ne)) s (Inv hH s₀ (nb H s₀)) := by
  have hD := hz.z.D.1
  refine WP.ite (decide (ol s₀ = 0)) (by simp [eval, hz0]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · rw [(nb_zero hD).2 (of_decide_eq_true h0)]; exact h
  · have : nb H s₀ ≠ 0 := fun e => by simp [(nb_zero hD).1 e] at h0
    exact VG.Proof.Pbkdf2.Md.X86_64.Calls.count_loop (Nat.pos_of_ne_zero this) (Inv hH s₀)
      (fun k hk t ht => block_ok hp hz hH hF hFsp hFd hI hIsp hId hk ht) h

theorem correct (hH : HashOK H) (hIn : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hInsp : NoSp H.hmacInit) (hInd : H.hmacInit.depth ≤ 2)
    (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W))
    (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2)
    (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate) (hId : H.iterate.depth ≤ 2) :
    WP isa H.pbkdf2 s₀ fun s' => gprPreserved s₀ s' ∧ (pbkG hH.SH (H.W + H.S)).post s₀ s' := by
  have hD := hz.z.D.1; have hW := hz.W
  unfold Hash.pbkdf2
  refine WP.seq (WP.mono (loadScr_ok hp) fun s₀' l => ?_)
  refine WP.seq (WP.mono (entry_ok hp hz l) fun s₁ ⟨k₁, bx, bp, r12, r13, cf⟩ => ?_)
  refine WP.seq (WP.mono (key_ok hp hz hH ⟨k₁, bx, bp, r12, r13⟩ cf) fun s₂ ⟨k₂, dx₂, cx₂, ka⟩ => ?_)
  refine WP.seq (WP.mono (setup_ok hp hz hH hIn hInsp hInd k₂ dx₂ cx₂ ka) fun s₃ ⟨k₃, st₃⟩ => ?_)
  refine WP.seq (WP.mono (loopRegs_ok hp hz hH k₃.kr k₃.r13 st₃) fun s₄ ⟨i₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hp hz hH hF hFsp hFd hI hIsp hId i₄ z₄) fun s₅ i₅ => ?_)
  have k₅ := i₅.kr
  refine WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.restore_ok H.hh k₅.r15 hW k₅.saved (in_wr hp k₅)
    (by have : H.S = H.P.N + H.P.B := rfl; have := hz.z.B; show 8 * H.W + 48 ≤ (H.W + H.S) * 8; omega))
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm, k₅.ret hp]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₅.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  have hdone : done H s₀ (nb H s₀) = ol s₀ := by
    have := ol_le (s₀ := s₀) hD; show min _ _ = _; omega
  have hb := i₅.outB
  rw [hdone] at hb
  show Spec.Pbkdf2.pbkdf2 (Spec.Hmac.hmac hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))) hH.SH.digestBytes
    (saltB s₀) (cc s₀) (ol s₀) = some (bytesAt s'.mem (out s₀) (ol s₀))
  have hol := hp.olD
  rw [hH.hD, Spec.Pbkdf2.pbkdf2, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hm, hb]
  rfl

end

end VG.Proof.Pbkdf2.Md.X86_64.Pbk
