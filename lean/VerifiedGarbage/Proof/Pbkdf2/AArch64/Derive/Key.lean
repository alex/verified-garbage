import VerifiedGarbage.Proof.Pbkdf2.AArch64.Derive.Calls
import VerifiedGarbage.Proof.Hmac.AArch64.Common

/-!
# PBKDF2-HMAC-SHA-256 on AArch64: the key and the salt

Untrusted: everything here is checked by Lean. The prologue, the password's
hash when it is longer than a block, the key's streaming states, and the salt
absorbed into a copy of the inner one.
-/

namespace VG.Proof.Pbkdf2.AArch64Derive

open VG VG.AArch64 VG.Impl.Pbkdf2.AArch64
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey sha256)
open VG.Proof.Sha256.AArch64 (contains_offset toNat_ofNat_lt)
open VG.Proof.Sha256.AArch64.Stream (Upd Mupd wp_str eval_zero)
open VG.AArch64.RegBlock (upd wp_run wp_run')

/-! ## Memory -/

/-- Reading a word of the scratch space past a write elsewhere in it. -/
theorem readW_sc_sep (s₀ : State) {a b w w' : Nat} (h : a + w / 8 ≤ b ∨ b + w' / 8 ≤ a)
    (ha : a + w / 8 ≤ 2048) (hb : b + w' / 8 ≤ 2048) (m : Mem) (v : BitVec w') :
    (m.writeW (sc s₀ + BitVec.ofNat 64 b) v).readW (sc s₀ + BitVec.ofNat 64 a) w =
      m.readW (sc s₀ + BitVec.ofNat 64 a) w := by
  refine Mem.readW_writeW_sep (fun x h₁ h₂ => ?_) (by omega)
  have ta : (BitVec.ofNat 64 a).toNat = a := toNat_ofNat_lt (by omega)
  have tb : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_lt (by omega)
  bv_omega

/-- The memory after storing the registers `L` at their offsets from `b`. -/
def stores (g : Reg → BitVec 64) (b : Addr) (L : List (Reg × Nat)) (m : Mem) : Mem :=
  L.foldl (fun m p => m.writeW (b + BitVec.ofNat 64 p.2) (g p.1)) m

/-- Storing registers at offsets from a base register. -/
theorem strs_ok {b : Reg} : ∀ (L : List (Reg × Nat)) {s : State} {rest : List Instr} {Q : State → Prop},
    (∀ p ∈ L, p.2 % 8 = 0 ∧ p.2 < 4096 * 8) → (∀ p ∈ L, InRegions s.wr (s.gpr b + BitVec.ofNat 64 p.2) 8) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = stores s.gpr (s.gpr b) L s.mem → WP isa (.block rest) s' Q) →
    WP isa (.block (L.map (fun (r, d) => Instr.str .x r b d) ++ rest)) s Q
  | [], s, _, _, _, _, k => k s rfl rfl rfl rfl rfl
  | p :: L, s, rest, Q, ho, hin, k => by
    simp only [List.map_cons, List.cons_append]
    refine wp_str (ho p (by simp)) rfl (hin p (by simp)) fun s₁ u₁ => ?_
    refine strs_ok L (fun q hq => ho q (by simp [hq]))
      (fun q hq => by rw [u₁.wr, u₁.gpr]; exact hin q (by simp [hq])) fun s' g rd wr sp m => ?_
    refine k s' (g.trans u₁.gpr) (rd.trans u₁.rd) (wr.trans u₁.wr) (sp.trans u₁.sp) ?_
    rw [m, u₁.gpr, u₁.mem]; rfl

theorem stores_frame (g : Reg → BitVec 64) (b : Addr) {R : Region} :
    ∀ (L : List (Reg × Nat)) (m : Mem), (∀ p ∈ L, R.Contains (b + BitVec.ofNat 64 p.2) 8) →
      Frame [R] m (stores g b L m)
  | [], _, _ => Frame.refl _ _
  | p :: L, m, h =>
    ((Frame.refl _ m).writeW (List.mem_singleton_self R) _ (h p (by simp))).trans
      (stores_frame g b L _ fun q hq => h q (by simp [hq]))

/-! ## The prologue -/

/-- After the prologue. -/
structure AtP (s₀ s : State) : Prop where
  base : Base s₀ s
  x20 : s.gpr .x20 = pw s₀
  x21 : s.gpr .x21 = s₀.gpr .x1
  x22 : s.gpr .x22 = sa s₀
  x23 : s.gpr .x23 = s₀.gpr .x3
  x24 : s.gpr .x24 = op s₀

theorem ini_frame {s₀ : State} (hp : Pre s₀) : Frame [stkR s₀] s₀.mem (ini s₀).mem :=
  (Frame.refl _ _).write (List.mem_singleton_self _) _ (by
    have := hp.sp48
    simp only [Region.Contains]
    bv_omega)

set_option simprocs false in
theorem saved_stores (s₀ : State) (m : Mem) :
    Saved s₀ (stores s₀.gpr (sc s₀) dSaved m) := by
  intro p hp
  simp only [dSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  simp only [stores, dSaved, List.foldl]
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) (disch := omega) only [readW_sc_sep, Mem.readW_writeW_self64]

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block dPrologue) (ini s₀) (AtP s₀) := by
  unfold dPrologue
  refine strs_ok dSaved (by decide) (fun p hq => ?_) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · have := dSaved_off p hq
    exact hp.in_sc rfl (by omega)
  refine wp_run' rfl fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  have G : ∀ r, s₁.gpr r = s₀.gpr r := fun r => by rw [g₁]
  have hm : s₂.mem = stores s₀.gpr (sc s₀) dSaved (ini s₀).mem := by rw [m₂, m₁]
  refine ⟨⟨by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁], ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₂]; simp [upd, G]
  · rw [g₂]; simp [upd, G]
  · rw [g₂]; simp [upd, G]
  · rw [hm]; exact saved_stores s₀ _
  · rw [hm]
    refine (ini_frame hp).sub (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨stkR s₀, by simp, fun _ h => h⟩)
      |>.trans ((stores_frame s₀.gpr (sc s₀) (R := sR s₀ 424 64) dSaved _ fun p hq => ?_).sub fun r hr => ?_)
    · have := dSaved_off p hq
      exact contains_sR s₀ (o := 424) (n := 64) this.1 (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, sR_sub s₀ (by omega)⟩
  · rw [g₂]; simp [upd, G]
  · rw [g₂]; simp [upd, G]
  · rw [g₂]; simp [upd, G]
  · rw [g₂]; simp [upd, G]
  · rw [g₂]; simp [upd, G]

/-! ## The registers we keep -/

/-- `Base`, and the callee-saved registers we use. -/
structure Kp (s₀ s : State) (a b c d e : BitVec 64) : Prop where
  base : Base s₀ s
  x20 : s.gpr .x20 = a
  x21 : s.gpr .x21 = b
  x22 : s.gpr .x22 = c
  x23 : s.gpr .x23 = d
  x24 : s.gpr .x24 = e

theorem Kp.call {s₀ s s' : State} {a b c d e : BitVec 64} (hp : Pre s₀) (h : Kp s₀ s a b c d e)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp)
    (cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r)
    (hf : Frame (wk s₀) s.mem s'.mem) : Kp s₀ s' a b c d e :=
  ⟨h.base.call hp rd wr sp cs hf, (cs _ (by decide) (by decide)).trans h.x20,
    (cs _ (by decide) (by decide)).trans h.x21, (cs _ (by decide) (by decide)).trans h.x22,
    (cs _ (by decide) (by decide)).trans h.x23, (cs _ (by decide) (by decide)).trans h.x24⟩

theorem Kp.regs {s₀ s s' : State} {a b c d e : BitVec 64} (h : Kp s₀ s a b c d e)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) (hm : s'.mem = s.mem)
    (cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) : Kp s₀ s' a b c d e :=
  ⟨h.base.regs rd wr sp (cs _ (by decide) (by decide)) (cs _ (by decide) (by decide))
      (cs _ (by decide) (by decide)) hm,
    (cs _ (by decide) (by decide)).trans h.x20, (cs _ (by decide) (by decide)).trans h.x21,
    (cs _ (by decide) (by decide)).trans h.x22, (cs _ (by decide) (by decide)).trans h.x23,
    (cs _ (by decide) (by decide)).trans h.x24⟩

set_option hygiene false in
/-- A block that writes none of the callee-saved registers keeps them. -/
macro "cs_keep " hg:term : tactic => `(tactic| (
  intro r hr h30; rw [$hg:term]
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl h30 | simp [RegBlock.upd]))

/-- That two of the regions the code uses are disjoint: parts of the scratch
space at different offsets, the stack, the password, the salt and `out`. -/
macro "dj" : tactic => `(tactic| first
  | with_reducible exact sR_disj _ (by omega) (by omega) (by omega)
  | with_reducible exact Pre.stk_sR ‹Pre _› (by omega)
  | with_reducible exact Pre.sR_stk ‹Pre _› (by omega)
  | with_reducible exact Pre.p_sR ‹Pre _› (by omega)
  | with_reducible exact (Pre.p_sR ‹Pre _› (by omega)).symm
  | with_reducible exact Pre.a_sR ‹Pre _› (by omega)
  | with_reducible exact (Pre.a_sR ‹Pre _› (by omega)).symm
  | with_reducible exact Pre.o_sR ‹Pre _› (by omega)
  | with_reducible exact (Pre.o_sR ‹Pre _› (by omega)).symm
  | with_reducible exact Pre.stk_p' ‹Pre _›
  | with_reducible exact Pre.stk_a' ‹Pre _›
  | with_reducible exact Pre.stk_o' ‹Pre _›
  | with_reducible exact (Pre.stk_o' ‹Pre _›).symm)

set_option hygiene false in
/-- The regions a callee is given are among ours. -/
macro "cov" : tactic => `(tactic| (
  refine Covers.of_sub ?_
  simp only [List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  repeat' apply And.intro
  all_goals first
    | ((with_reducible refine cov_self ?_); simp; done)
    | ((with_reducible refine cov_sR ?_ ?_) <;> first | (simp; done) | omega)))

set_option hygiene false in
/-- A call's frame is where the code writes. -/
macro "fwk" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  repeat' apply And.intro
  all_goals first
    | with_reducible exact wk_stk _
    | with_reducible exact wk_lo _ (by omega)
    | with_reducible exact wk_hi _ (by omega) (by omega)))

/-! ## The password's hash -/

/-- The key's registers: the password or its hash, and its length. -/
def kp (s₀ : State) : Addr := if pl s₀ < 65 then pw s₀ else sc s₀ + BitVec.ofNat 64 496
def kn (s₀ : State) : BitVec 64 := if pl s₀ < 65 then s₀.gpr .x1 else 32

abbrev Kp0 (s₀ s : State) : Prop := Kp s₀ s (pw s₀) (s₀.gpr .x1) (sa s₀) (s₀.gpr .x3) (op s₀)

/-- With the key set up. -/
structure AtK (s₀ s : State) : Prop where
  regs : Kp s₀ s (kp s₀) (kn s₀) (sa s₀) (s₀.gpr .x3) (op s₀)
  key : blockKey sha256 (bytesAt s.mem (kp s₀) (kn s₀).toNat) = k0 s₀

def HK1 (s₀ s : State) : Prop := Kp0 s₀ s ∧ s.gpr .x0 = sc s₀ + BitVec.ofNat 64 288
def HK2 (s₀ s : State) : Prop := Kp0 s₀ s ∧ Repr s.mem (sc s₀ + BitVec.ofNat 64 288) []
def HK3 (s₀ s : State) : Prop := HK2 s₀ s ∧ s.gpr .x0 = sc s₀ + BitVec.ofNat 64 288 ∧ s.gpr .x1 = 0 ∧
  s.gpr .x2 = pw s₀ ∧ s.gpr .x3 = s₀.gpr .x1 ∧ s.gpr .x4 = sc s₀ + BitVec.ofNat 64 528
def HK4 (s₀ s : State) : Prop := Kp0 s₀ s ∧ Repr s.mem (sc s₀ + BitVec.ofNat 64 288) (P s₀)
def HK5 (s₀ s : State) : Prop := HK4 s₀ s ∧ s.gpr .x0 = sc s₀ + BitVec.ofNat 64 288 ∧
  s.gpr .x1 = s₀.gpr .x1 ∧ s.gpr .x2 = sc s₀ + BitVec.ofNat 64 496 ∧ s.gpr .x3 = sc s₀ + BitVec.ofNat 64 528
def HK6 (s₀ s : State) : Prop := Kp0 s₀ s ∧ bytesAt s.mem (sc s₀ + BitVec.ofNat 64 496) 32 = Spec.Sha256.hash (P s₀)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

omit hp in
theorem hk1_ok {s : State} (h : Kp0 s₀ s) : WP isa (.block [.addImm .x .x0 .x19 288]) s (HK1 s₀) := by
  refine wp_run' rfl fun s' hg hm rd wr sp => ⟨h.regs rd wr sp hm (by cs_keep hg), ?_⟩
  rw [hg]; simp [upd, h.base.x19]

theorem hk2_ok {nm : String} {s : State} (h : HK1 s₀ s) :
    WP isa (.call nm Impl.Sha256.AArch64.Stream.init) s (HK2 s₀) := by
  refine sinit_call h.1.base.sp h.2 (by rw [h.1.base.rd, h.1.base.wr, hp.rd, hp.wr]; cov)
    (by rw [h.1.base.wr, hp.wr]; cov) fun s' rd wr sp cs hf hr =>
      ⟨h.1.call hp rd wr sp cs (hf.sub (by fwk)), hr⟩

omit hp in
theorem hk3_ok {s : State} (h : HK2 s₀ s) :
    WP isa (.block [.addImm .x .x0 .x19 288, .movz .x .x1 0 0, mov .x2 .x20, mov .x3 .x21,
      .addImm .x .x4 .x19 528]) s (HK3 s₀) := by
  refine wp_run' rfl fun s' hg hm rd wr sp => ⟨⟨h.1.regs rd wr sp hm (by cs_keep hg), by rw [hm]; exact h.2⟩,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hg] <;> simp [upd, h.1.base.x19, h.1.x20, h.1.x21]

theorem hk4_ok {nm : String} {s : State} (h : HK3 s₀ s) :
    WP isa (.call nm Impl.Sha256.AArch64.Stream.update) s (HK4 s₀) := by
  obtain ⟨⟨k, hr⟩, h0, h1, h2, h3, h4⟩ := h
  have hsp := k.base.sp
  refine update_call hsp hp.sp16 h0 h2 (congrArg BitVec.toNat h3) h4 (by dj) (by dj) (by dj) (by dj)
    (by dj) (by dj) (by rw [k.base.rd, k.base.wr, hp.rd, hp.wr]; cov) (by rw [k.base.wr, hp.wr]; cov) hr
    (by rw [h1]; rfl) fun s' rd wr sp cs hf hr' => ⟨k.call hp rd wr sp cs (hf.sub (by fwk)), ?_⟩
  rwa [List.nil_append, k.base.pw_eq hp] at hr'

omit hp in
theorem hk5_ok {s : State} (h : HK4 s₀ s) :
    WP isa (.block [.addImm .x .x0 .x19 288, mov .x1 .x21, .addImm .x .x2 .x19 496,
      .addImm .x .x3 .x19 528]) s (HK5 s₀) := by
  refine wp_run' rfl fun s' hg hm rd wr sp => ⟨⟨h.1.regs rd wr sp hm (by cs_keep hg), by rw [hm]; exact h.2⟩,
    ?_, ?_, ?_, ?_⟩ <;> rw [hg] <;> simp [upd, h.1.base.x19, h.1.x21]

theorem hk6_ok {nm : String} {s : State} (h : HK5 s₀ s) :
    WP isa (.call nm Impl.Sha256.AArch64.Stream.finalize) s (HK6 s₀) := by
  obtain ⟨⟨k, hr⟩, h0, h1, h2, h3⟩ := h
  refine sfin_call k.base.sp hp.sp16 h0 h2 h3 (by dj) (by dj) (by dj) (by dj) (by dj) (by dj)
    (by rw [k.base.rd, k.base.wr, hp.rd, hp.wr]; cov) (by rw [k.base.wr, hp.wr]; cov) hr
    (by rw [h1, Proof.Hmac.X86_64.bytesAt_length]; simp)
    fun s' rd wr sp cs hf hd => ⟨k.call hp rd wr sp cs (hf.sub (by fwk)), hd⟩

end

theorem hash_length (m : List Byte) : (Spec.Sha256.hash m).length = 32 :=
  Proof.Pbkdf2.X86_64.Derive.hash_length m

theorem blockKey_length (p : List Byte) : (blockKey sha256 p).length = 64 :=
  Proof.Pbkdf2.X86_64.Derive.blockKey_length p

section
variable {s₀ : State} (hp : Pre s₀)
include hp

omit hp in
theorem hk7_ok (hl : ¬ pl s₀ < 65) {s : State} (h : HK6 s₀ s) :
    WP isa (.block [.addImm .x .x20 .x19 496, .movz .x .x21 32 0]) s (AtK s₀) := by
  have e1 : kp s₀ = sc s₀ + BitVec.ofNat 64 496 := by simp [kp, hl]
  have e2 : kn s₀ = 32 := by simp [kn, hl]
  refine wp_run' rfl fun s' hg hm rd wr sp => ⟨⟨h.1.base.regs rd wr sp (by rw [hg]; simp [upd])
    (by rw [hg]; simp [upd]) (by rw [hg]; simp [upd]) hm, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hg, e1]; simp [upd, h.1.base.x19]
  · rw [hg, e2]; simp [upd]
  · rw [hg]; simp [upd, h.1.x22]
  · rw [hg]; simp [upd, h.1.x23]
  · rw [hg]; simp [upd, h.1.x24]
  · rw [hm, e1, e2, show (32 : BitVec 64).toNat = 32 from rfl, h.2,
      Proof.Pbkdf2.X86_64.Derive.blockKey_hash]
    rw [Proof.Hmac.X86_64.bytesAt_length]; omega

omit hp in
/-- `(x - 1) / 64` is zero iff `x < 65`, for `x ≠ 0`. -/
theorem shr_zero {x : BitVec 64} (h : x.toNat ≠ 0) :
    ((x - BitVec.ofNat 64 1) >>> 6 == 0) = decide (x.toNat < 65) := by
  have e : ((x - BitVec.ofNat 64 1) >>> 6).toNat = (x.toNat - 1) / 64 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat]
    congr 1
    omega
  by_cases hl : x.toNat < 65
  · simp only [hl, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [e]; show _ = 0
    omega
  · simp only [hl, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h0
    have := congrArg BitVec.toNat h0
    rw [e] at this; change _ = 0 at this
    omega

theorem hashKey_ok (hl : ¬ pl s₀ < 65) {s : State} (h : Kp0 s₀ s) : WP isa hashKey s (AtK s₀) := by
  unfold hashKey
  exact WP.seq (WP.mono (hk1_ok h) fun _ h1 => WP.seq (WP.mono (hk2_ok hp h1) fun _ h2 =>
    WP.seq (WP.mono (hk3_ok h2) fun _ h3 => WP.seq (WP.mono (hk4_ok hp h3) fun _ h4 =>
    WP.seq (WP.mono (hk5_ok h4) fun _ h5 => WP.seq (WP.mono (hk6_ok hp h5) fun _ h6 => hk7_ok hl h6))))))

/-- The key with the password itself. -/
theorem key_pw (hl : pl s₀ < 65) {s : State} (h : Kp0 s₀ s) : AtK s₀ s := by
  have e1 : kp s₀ = pw s₀ := by simp [kp, hl]
  have e2 : kn s₀ = s₀.gpr .x1 := by simp [kn, hl]
  refine ⟨⟨h.base, by rw [h.x20, e1], by rw [h.x21, e2], h.x22, h.x23, h.x24⟩, ?_⟩
  rw [e1, e2, h.base.pw_eq hp]

/-- The test of the password's length. -/
def KT (s₀ s : State) : Prop := Kp0 s₀ s ∧ s.gpr .x9 = (s₀.gpr .x1 - BitVec.ofNat 64 1) >>> 6

omit hp in
theorem kt_ok {s : State} (h : Kp0 s₀ s) :
    WP isa (.block [.subImm .x .x9 .x21 1, .lsr .x .x9 .x9 6]) s (KT s₀) := by
  refine wp_run' rfl fun s' hg hm rd wr sp => ⟨h.regs rd wr sp hm (by cs_keep hg), ?_⟩
  rw [hg]; simp [upd, h.x21]

theorem key_ok {s : State} (h : AtP s₀ s) : WP isa keyPrep s (AtK s₀) := by
  have k : Kp0 s₀ s := ⟨h.base, h.x20, h.x21, h.x22, h.x23, h.x24⟩
  unfold keyPrep
  refine WP.ite (s.gpr .x21 == 0) (eval_zero s .x21) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have : pl s₀ = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hb); rw [h.x21] at this; simpa using this
    exact key_pw hp (by omega) k
  · have h0 : pl s₀ ≠ 0 := fun h0 => by
      rw [h.x21, show s₀.gpr .x1 = 0 from BitVec.eq_of_toNat_eq h0] at hb; simp at hb
    refine WP.seq (WP.mono (kt_ok k) fun s₁ h₁ => ?_)
    refine WP.ite _ (eval_zero s₁ .x9) (fun hb₁ => WP.block_nil ?_) (fun hb₁ => ?_)
    · rw [h₁.2, shr_zero h0] at hb₁
      exact key_pw hp (by simpa using hb₁) h₁.1
    · rw [h₁.2, shr_zero h0] at hb₁
      exact hashKey_ok hp (by simpa using hb₁) h₁.1

end

/-! ## The key's streaming states, and the salt -/

/-- The key's inner and outer streaming states. -/
def KeyR (s₀ : State) (m : Mem) : Prop :=
  Repr m (sc s₀ + BitVec.ofNat 64 0) (xorPad (k0 s₀) ipad) ∧ Repr m (sc s₀ + BitVec.ofNat 64 96) (xorPad (k0 s₀) opad)

abbrev KpK (s₀ s : State) : Prop := Kp s₀ s (kp s₀) (kn s₀) (sa s₀) (s₀.gpr .x3) (op s₀)

def KS1 (s₀ s : State) : Prop := AtK s₀ s ∧ s.gpr .x0 = sc s₀ + BitVec.ofNat 64 0 ∧
  s.gpr .x1 = sc s₀ + BitVec.ofNat 64 96 ∧ s.gpr .x2 = kp s₀ ∧ s.gpr .x3 = kn s₀ ∧
  s.gpr .x4 = sc s₀ + BitVec.ofNat 64 528
def KS2 (s₀ s : State) : Prop := KpK s₀ s ∧ KeyR s₀ s.mem
def KS3 (s₀ s : State) : Prop := KS2 s₀ s ∧ Repr s.mem (sc s₀ + BitVec.ofNat 64 192) (xorPad (k0 s₀) ipad) ∧
  s.gpr .x0 = sc s₀ + BitVec.ofNat 64 192 ∧ s.gpr .x1 = BitVec.ofNat 64 64 ∧ s.gpr .x2 = sa s₀ ∧
  s.gpr .x3 = s₀.gpr .x3 ∧ s.gpr .x4 = sc s₀ + BitVec.ofNat 64 528
def KS4 (s₀ s : State) : Prop := KS2 s₀ s ∧
  Repr s.mem (sc s₀ + BitVec.ofNat 64 192) (xorPad (k0 s₀) ipad ++ S s₀)

/-- The key is the password or its hash. -/
theorem key_reg (s₀ : State) : ((⟨kp s₀, (kn s₀).toNat⟩ : Region) = pwR s₀ ∧ pl s₀ < 65) ∨
    ((⟨kp s₀, (kn s₀).toNat⟩ : Region) = sR s₀ 496 32) := by
  by_cases hl : pl s₀ < 65
  · exact .inl ⟨by simp [kp, kn, hl], hl⟩
  · exact .inr (by simp [kp, kn, hl])

theorem kn_le (s₀ : State) : (kn s₀).toNat ≤ 64 := by
  unfold kn; split
  · exact Nat.le_of_lt_succ ‹_›
  · decide

section
variable {s₀ : State} (hp : Pre s₀)
include hp

omit hp in
theorem ks1_ok {s : State} (h : AtK s₀ s) :
    WP isa (.block [mov .x0 .x19, .addImm .x .x1 .x19 96, mov .x2 .x20, mov .x3 .x21,
      .addImm .x .x4 .x19 528]) s (KS1 s₀) := by
  refine wp_run' rfl fun s' hg hm rd wr sp => ⟨⟨h.1.regs rd wr sp hm (by cs_keep hg), by rw [hm]; exact h.2⟩,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hg] <;> simp [upd, h.1.base.x19, h.1.x20, h.1.x21]

theorem ks2_ok {nm : String} {s : State} (h : KS1 s₀ s) :
    WP isa (.call nm Impl.Hmac.AArch64.init) s (KS2 s₀) := by
  obtain ⟨⟨k, hk⟩, h0, h1, h2, h3, h4⟩ := h
  have cK : ∀ R : Region, R = sR s₀ 0 96 ∨ R = sR s₀ 96 96 ∨ R = sR s₀ 528 160 →
      Region.Disjoint ⟨kp s₀, (kn s₀).toNat⟩ R := by
    rintro R (rfl | rfl | rfl) <;> rcases key_reg s₀ with ⟨e, -⟩ | e <;> rw [e] <;> dj
  refine hinit_call k.base.sp hp.sp16 h0 h1 h2 (congrArg BitVec.toNat h3) h4 (kn_le s₀) (by dj) (by dj)
    (by dj) (cK _ (.inl rfl)) (cK _ (.inr (.inl rfl))) (cK _ (.inr (.inr rfl))) (by dj) (by dj)
    (by rcases key_reg s₀ with ⟨e, -⟩ | e <;> rw [e] <;> dj) (by dj) ?_
    (by rw [k.base.wr, hp.wr]; cov) fun s' rd wr sp cs hf hI hO =>
      ⟨k.call hp rd wr sp cs (hf.sub (by fwk)), ?_, ?_⟩
  · rw [k.base.rd, k.base.wr, hp.rd, hp.wr]
    rcases key_reg s₀ with ⟨e, -⟩ | e <;> rw [e] <;> cov
  · rw [hk] at hI; exact hI
  · rw [hk] at hO; exact hO

omit hp in
theorem sc_copy {s : State} (hp : Pre s₀) (h19 : s.gpr .x19 = sc s₀) (hwr : s.wr = s₀.wr) {o₁ o₂ n : Nat}
    (hs : o₁ + 8 * n ≤ o₂ ∨ o₂ + 8 * n ≤ o₁) (h₁ : o₁ + 8 * n ≤ 2048) (h₂ : o₂ + 8 * n ≤ 2048)
    (ho : o₁ % 8 = 0 ∧ o₂ % 8 = 0)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = Proof.Sha256.Stream.writeBytes s.mem (sc s₀ + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (sc s₀ + BitVec.ofNat 64 o₁) (8 * n)) → WP isa (.block rest) s' Q) :
    WP isa (.block ((List.range n).flatMap (Impl.Hmac.AArch64.cp64 .x19 .x19 o₁ o₂) ++ rest)) s Q := by
  refine Proof.Hmac.AArch64.copy64_ok (by decide) (by decide) o₁ o₂ n ho ⟨by omega, by omega⟩ rest s Q
    (fun j hj => by rw [h19, add_ofNat]; exact hp.in_sc' hwr (by omega))
    (fun j hj => by rw [h19, add_ofNat]; exact hp.in_sc hwr (by omega)) ?_
    fun s' g rd wr sp m => k s' g rd wr sp (by rw [m, h19])
  rw [h19]
  exact Region.Disjoint.sep (sR_disj s₀ (a := o₁) (m := 8 * n) (b := o₂) (n := 8 * n) hs h₁ h₂)
    (contains_sR s₀ le_rfl le_rfl h₁) (contains_sR s₀ le_rfl le_rfl h₂)

theorem ks3_ok {s : State} (h : KS2 s₀ s) :
    WP isa (.block ((List.range 12).flatMap (Impl.Hmac.AArch64.cp64 .x19 .x19 0 192) ++
      [.addImm .x .x0 .x19 192, .movz .x .x1 64 0, mov .x2 .x22, mov .x3 .x23, .addImm .x .x4 .x19 528]))
      s (KS3 s₀) := by
  obtain ⟨k, hK⟩ := h
  refine sc_copy hp k.base.x19 k.base.wr (o₁ := 0) (o₂ := 192) (n := 12) (by omega) (by omega) (by omega)
    (by decide) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  have f₁ : Frame [sR s₀ 192 96] s.mem s₁.mem := by
    rw [m₁]; exact Proof.Pbkdf2.X86_64.Derive.copy_frame _ _ _ _
  have k₁ : KpK s₀ s₁ := k.call hp rd₁ wr₁ sp₁ (fun r hr _ => g₁ r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    (f₁.sub (by fwk))
  have hK₁ : KeyR s₀ s₁.mem := by
    refine ⟨repr_frame f₁ ?_ hK.1, repr_frame f₁ ?_ hK.2⟩ <;>
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] <;> dj
  have hS : Repr s₁.mem (sc s₀ + BitVec.ofNat 64 192) (xorPad (k0 s₀) ipad) := by
    refine Proof.Pbkdf2.X86_64.Derive.repr_of_bytes ?_ hK.1
    rw [m₁, show 8 * 12 = 96 from rfl, Proof.Pbkdf2.X86_64.Derive.copy_bytes _ _ _ _ (by omega)]
  refine wp_run' rfl fun s' hg hm rd wr sp => ⟨⟨k₁.regs rd wr sp hm (by cs_keep hg), hm ▸ hK₁⟩, hm ▸ hS,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hg] <;> simp [upd, k₁.base.x19, k₁.x22, k₁.x23]

theorem ks4_ok {nm : String} {s : State} (h : KS3 s₀ s) :
    WP isa (.call nm Impl.Sha256.AArch64.Stream.update) s (KS4 s₀) := by
  obtain ⟨⟨k, hK⟩, hS, h0, h1, h2, h3, h4⟩ := h
  refine update_call k.base.sp hp.sp16 h0 h2 (congrArg BitVec.toNat h3) h4 (by dj) (by dj) (by dj) (by dj)
    (by dj) (by dj) (by rw [k.base.rd, k.base.wr, hp.rd, hp.wr]; cov)
    (by rw [k.base.wr, hp.wr]; cov) hS (by rw [h1]; simp [xorPad, k0, blockKey_length])
    fun s' rd wr sp cs hf hr' => ⟨⟨k.call hp rd wr sp cs (hf.sub (by fwk)), ?_, ?_⟩, ?_⟩
  · refine repr_frame hf ?_ hK.1
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨by dj, by dj, by dj⟩
  · refine repr_frame hf ?_ hK.2
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨by dj, by dj, by dj⟩
  · rwa [k.base.salt_eq hp] at hr'

theorem keySalt_ok {s : State} (h : AtK s₀ s) : WP isa keySalt s (KS4 s₀) := by
  unfold keySalt
  exact WP.seq (WP.mono (ks1_ok h) fun _ h1 => WP.seq (WP.mono (ks2_ok hp h1) fun _ h2 =>
    WP.seq (WP.mono (ks3_ok hp h2) fun _ h3 => ks4_ok hp h3)))

end

end VG.Proof.Pbkdf2.AArch64Derive
