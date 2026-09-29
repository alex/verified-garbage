import VerifiedGarbage.Proof.Pbkdf2.X86_64.Derive.Calls

/-!
# PBKDF2-HMAC-SHA-256 on x86-64: the key and the salt

Untrusted: everything here is checked by Lean. The prologue, the password's
hash when it is longer than a block, the key's streaming states, the salt
absorbed into a copy of the inner one, and the registers of the loop.
-/

namespace VG.Proof.Pbkdf2.X86_64.Derive

open VG VG.X86_64 VG.Impl.Pbkdf2.X86_64
open VG.Impl.Sha256.X86_64 (at_)
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey sha256)
open VG.Proof.Sha256.X86_64 (contains_offset toNat_ofNat_lt ea_at ofInt_natCast)
open VG.Proof.Sha256.X86_64.Stream (wp_movm wp_store wp_store32 wp_cmpi wp_test wp_mov32m)
open VG.X86_64.RegBlock (upd wp_run wp_run')
open VG.Impl.Sha256.X86_64.Stream (Callee)

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

theorem ea_sc {s : State} {r : Reg} {s₀ : State} (h : s.gpr r = sc s₀) (d : Nat) :
    s.ea (at_ r d) = sc s₀ + BitVec.ofNat 64 d := by
  rw [ea_at, h, ofInt_natCast]

/-! ## The prologue -/

/-- After the prologue. -/
structure AtP (s₀ s : State) : Prop where
  base : Base s₀ s
  r12 : s.gpr .r12 = pw s₀
  r13 : s.gpr .r13 = s₀.gpr .rsi
  r14 : s.gpr .r14 = sa s₀
  r15 : s.gpr .r15 = s₀.gpr .rcx
  rbp : s.gpr .rbp = op s₀
  cf : s.cf = some (decide (pl s₀ < 65))

theorem se65 : BitVec.signExtend 64 (65 : BitVec 32) = 65 := by decide

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block dPrologue) s₀ (AtP s₀) := by
  have io : ∀ {s : State}, s.wr = s₀.wr → ∀ d w : Nat, d + w ≤ 2048 → InRegions s.wr (sc s₀ + BitVec.ofNat 64 d) w :=
    fun hw _ _ h => hp.in_sc hw h
  simp only [dPrologue, dSaved, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine wp_movm (a := stackArgAddr s₀ 1) (by rw [ea_at, ofInt_natCast]; rfl) ?_ fun s₁ u₁ => ?_
  · refine ⟨argR s₀, by simp [hp.rd], ?_⟩
    simp only [Region.Contains, stackArgAddr]
    rw [show s₀.gpr .rsp + BitVec.ofNat 64 (8 * (1 + 1)) - (s₀.gpr .rsp + BitVec.ofNat 64 (8 * (0 + 1))) = 8 by
      bv_omega]
    decide
  have ax : s₁.gpr .rax = sc s₀ := u₁.gpr
  refine wp_store (a := sc s₀ + BitVec.ofNat 64 432) (ea_sc ax _) (io u₁.wr _ _ (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_store (a := sc s₀ + BitVec.ofNat 64 440) (ea_sc (by rw [g₂, ax]) _)
    (io (wr₂.trans u₁.wr) _ _ (by omega)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_store (a := sc s₀ + BitVec.ofNat 64 448) (ea_sc (by rw [g₃, g₂, ax]) _)
    (io (wr₃.trans (wr₂.trans u₁.wr)) _ _ (by omega)) fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_store (a := sc s₀ + BitVec.ofNat 64 456) (ea_sc (by rw [g₄, g₃, g₂, ax]) _)
    (io (wr₄.trans (wr₃.trans (wr₂.trans u₁.wr))) _ _ (by omega)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_store (a := sc s₀ + BitVec.ofNat 64 464) (ea_sc (by rw [g₅, g₄, g₃, g₂, ax]) _)
    (io (wr₅.trans (wr₄.trans (wr₃.trans (wr₂.trans u₁.wr)))) _ _ (by omega)) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  refine wp_store (a := sc s₀ + BitVec.ofNat 64 424) (ea_sc (by rw [g₆, g₅, g₄, g₃, g₂, ax]) _)
    (io (wr₆.trans (wr₅.trans (wr₄.trans (wr₃.trans (wr₂.trans u₁.wr))))) _ _ (by omega))
    fun s₇ g₇ m₇ rd₇ wr₇ => ?_
  have G : s₇.gpr = s₁.gpr := by rw [g₇, g₆, g₅, g₄, g₃, g₂]
  have W₇ : s₇.wr = s₀.wr := by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, u₁.wr]
  have R₇ : s₇.rd = s₀.rd := by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, u₁.rd]
  refine wp_run (is := [.mov .rbx (.reg .rax), .mov .r12 (.reg .rdi), .mov .r13 (.reg .rsi),
    .mov .r14 (.reg .rdx), .mov .r15 (.reg .rcx), .mov .rbp (.reg .r9)]) rfl fun s₈ g₈ m₈ rd₈ wr₈ => ?_
  have e : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  have rbx₈ : s₈.gpr .rbx = sc s₀ := by rw [g₈]; simp [upd, G, ax]
  refine wp_store32 (a := sc s₀ + BitVec.ofNat 64 472) (ea_sc rbx₈ _) (io (wr₈.trans W₇) _ _ (by omega))
    fun s₉ g₉ m₉ rd₉ wr₉ => wp_cmpi fun s₁₀ g₁₀ m₁₀ rd₁₀ wr₁₀ c₁₀ _ => WP.block_nil ?_
  have G' : ∀ r, s₁₀.gpr r = s₈.gpr r := fun r => by rw [g₁₀, g₉]
  have hm : s₁₀.mem = ((((((((s₀.mem.writeW (sc s₀ + BitVec.ofNat 64 432) (s₀.gpr .rbp)).writeW
      (sc s₀ + BitVec.ofNat 64 440) (s₀.gpr .r12)).writeW (sc s₀ + BitVec.ofNat 64 448) (s₀.gpr .r13)).writeW
      (sc s₀ + BitVec.ofNat 64 456) (s₀.gpr .r14)).writeW (sc s₀ + BitVec.ofNat 64 464) (s₀.gpr .r15)).writeW
      (sc s₀ + BitVec.ofNat 64 424) (s₀.gpr .rbx)).writeW (sc s₀ + BitVec.ofNat 64 472)
      ((s₀.gpr .r8).setWidth 32))) := by
    rw [m₁₀, m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, u₁.mem, g₈, g₆, g₅, g₄, g₃, g₂]
    simp only [upd, G, e _ (by decide : Reg.rbp ≠ .rax), e _ (by decide : Reg.r12 ≠ .rax),
      e _ (by decide : Reg.r13 ≠ .rax), e _ (by decide : Reg.r14 ≠ .rax), e _ (by decide : Reg.r15 ≠ .rax),
      e _ (by decide : Reg.rbx ≠ .rax), e _ (by decide : Reg.r8 ≠ .rax), reduceCtorEq, ite_false]
  have cS : ∀ d w, 424 ≤ d → d + w ≤ 476 → (sR s₀ 424 52).Contains (sc s₀ + BitVec.ofNat 64 d) w :=
    fun d w h₁ h₂ => contains_sR s₀ h₁ h₂ (by omega)
  have F : Frame [sR s₀ 424 52] s₀.mem s₁₀.mem := by
    rw [hm]
    have r := Frame.refl [sR s₀ 424 52] s₀.mem
    have m := List.mem_singleton_self (sR s₀ 424 52)
    exact ((((((r.writeW m _ (cS 432 8 (by omega) (by omega))).writeW m _ (cS 440 8 (by omega) (by omega))).writeW
      m _ (cS 448 8 (by omega) (by omega))).writeW m _ (cS 456 8 (by omega) (by omega))).writeW m _
      (cS 464 8 (by omega) (by omega))).writeW m _ (cS 424 8 (by omega) (by omega))).writeW m _
      (cS 472 4 (by omega) (by omega))
  refine ⟨⟨by rw [rd₁₀, rd₉, rd₈, R₇], by rw [wr₁₀, wr₉, wr₈, W₇], ?_, by rw [G', rbx₈], ?_,
    F.sub fun r hr => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [G', g₈]; simp [upd, G, e _ (by decide : Reg.rsp ≠ .rax)]
  · refine ⟨fun p hp' => ?_, ?_⟩
    · simp only [dSaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rw [hm]
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (disch := omega) only [readW_sc_sep, Mem.readW_writeW_self64]
    · rw [hm, Mem.readW_writeW_self32]
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scR s₀, by simp, sR_sub s₀ (by omega)⟩
  · rw [G', g₈]; simp [upd, G, e _ (by decide : Reg.rdi ≠ .rax)]
  · rw [G', g₈]; simp [upd, G, e _ (by decide : Reg.rsi ≠ .rax)]
  · rw [G', g₈]; simp [upd, G, e _ (by decide : Reg.rdx ≠ .rax)]
  · rw [G', g₈]; simp [upd, G, e _ (by decide : Reg.rcx ≠ .rax)]
  · rw [G', g₈]; simp [upd, G, e _ (by decide : Reg.r9 ≠ .rax)]
  · rw [c₁₀, se65, g₉, g₈]
    simp [upd, G, e _ (by decide : Reg.rsi ≠ .rax)]

/-! ## The registers we keep -/

/-- `Base`, and the callee-saved registers we use. -/
structure Kp (s₀ s : State) (a b c d e : BitVec 64) : Prop where
  base : Base s₀ s
  r12 : s.gpr .r12 = a
  r13 : s.gpr .r13 = b
  r14 : s.gpr .r14 = c
  r15 : s.gpr .r15 = d
  rbp : s.gpr .rbp = e

theorem Kp.call {s₀ s s' : State} {a b c d e : BitVec 64} (hp : Pre s₀) (h : Kp s₀ s a b c d e)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame (wk s₀) s.mem s'.mem) : Kp s₀ s' a b c d e :=
  ⟨h.base.call hp rd wr cs hf, (cs _ (by simp [calleeSaved])).trans h.r12,
    (cs _ (by simp [calleeSaved])).trans h.r13, (cs _ (by simp [calleeSaved])).trans h.r14,
    (cs _ (by simp [calleeSaved])).trans h.r15, (cs _ (by simp [calleeSaved])).trans h.rbp⟩

theorem Kp.regs {s₀ s s' : State} {a b c d e : BitVec 64} (h : Kp s₀ s a b c d e)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (hm : s'.mem = s.mem) (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    Kp s₀ s' a b c d e :=
  ⟨h.base.regs rd wr (cs _ (by simp [calleeSaved])) (cs _ (by simp [calleeSaved])) hm,
    (cs _ (by simp [calleeSaved])).trans h.r12, (cs _ (by simp [calleeSaved])).trans h.r13,
    (cs _ (by simp [calleeSaved])).trans h.r14, (cs _ (by simp [calleeSaved])).trans h.r15,
    (cs _ (by simp [calleeSaved])).trans h.rbp⟩

set_option hygiene false in
/-- A block that writes none of the callee-saved registers keeps them. -/
macro "cs_keep " hg:term : tactic => `(tactic| (
  intro r hr; rw [$hg:term]
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [RegBlock.upd]))

/-- That two of the regions the code uses are disjoint: parts of the scratch
space at different offsets, the stack below the return address, the password and the salt. -/
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

theorem cov_sR' {s₀ : State} {rs : List Region} (hin : scR s₀ ∈ rs) {o n : Nat} (h : o + n ≤ 2048) :
    ∃ r' ∈ rs, ∃ off, sc s₀ + BitVec.ofNat 64 o = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
  ⟨scR s₀, hin, o, rfl, h⟩

theorem cov_self' {rs : List Region} {p : Addr} {n : Nat} (hin : (⟨p, n⟩ : Region) ∈ rs) :
    ∃ r' ∈ rs, ∃ off, p = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
  ⟨⟨p, n⟩, hin, 0, by simp, by simp⟩

set_option hygiene false in
/-- The regions a callee is given are among ours. -/
macro "cov" : tactic => `(tactic| (
  refine Covers.of_sub ?_
  simp only [List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  repeat' apply And.intro
  all_goals first
    | ((with_reducible refine cov_self' ?_); simp; done)
    | ((with_reducible refine cov_self ?_); simp; done)
    | ((with_reducible refine cov_sR' ?_ ?_) <;> first | (simp; done) | omega)))

set_option hygiene false in
/-- A call's frame is where the code writes. -/
macro "fwk" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  repeat' apply And.intro
  all_goals first
    | with_reducible exact wk_stk _ (by assumption) (by omega)
    | with_reducible exact wk_lo _ (by omega)
    | with_reducible exact wk_hi _ (by omega) (by omega)))

/-! ## The password's hash -/

/-- The key's registers: the password or its hash, and its length. -/
def kp (s₀ : State) : Addr := if pl s₀ < 65 then pw s₀ else sc s₀ + BitVec.ofNat 64 480
def kn (s₀ : State) : BitVec 64 := if pl s₀ < 65 then s₀.gpr .rsi else 32

abbrev Kp0 (s₀ s : State) : Prop := Kp s₀ s (pw s₀) (s₀.gpr .rsi) (sa s₀) (s₀.gpr .rcx) (op s₀)

/-- With the key set up. -/
structure AtK (s₀ s : State) : Prop where
  regs : Kp s₀ s (kp s₀) (kn s₀) (sa s₀) (s₀.gpr .rcx) (op s₀)
  key : blockKey sha256 (bytesAt s.mem (kp s₀) (kn s₀).toNat) = k0 s₀

section
variable {s₀ : State} (hp : Pre s₀) {f : Callee} (hv : Vf f)
include hp

def HK1 (s₀ s : State) : Prop := Kp0 s₀ s ∧ s.gpr .rdi = sc s₀ + BitVec.ofNat 64 288
def HK2 (s₀ s : State) : Prop := Kp0 s₀ s ∧ Repr s.mem (sc s₀ + BitVec.ofNat 64 288) []
def HK3 (s₀ s : State) : Prop := HK2 s₀ s ∧ s.gpr .rdi = sc s₀ + BitVec.ofNat 64 288 ∧ s.gpr .rsi = 0 ∧
  s.gpr .rdx = pw s₀ ∧ s.gpr .rcx = s₀.gpr .rsi ∧ s.gpr .r8 = sc s₀ + BitVec.ofNat 64 512
def HK4 (s₀ s : State) : Prop := Kp0 s₀ s ∧ Repr s.mem (sc s₀ + BitVec.ofNat 64 288) (P s₀)
def HK5 (s₀ s : State) : Prop := HK4 s₀ s ∧ s.gpr .rdi = sc s₀ + BitVec.ofNat 64 288 ∧
  s.gpr .rsi = s₀.gpr .rsi ∧ s.gpr .rdx = sc s₀ + BitVec.ofNat 64 480 ∧ s.gpr .rcx = sc s₀ + BitVec.ofNat 64 512
def HK6 (s₀ s : State) : Prop := Kp0 s₀ s ∧ bytesAt s.mem (sc s₀ + BitVec.ofNat 64 480) 32 = Spec.Sha256.hash (P s₀)

omit hp in
theorem hk1_ok {s : State} (h : Kp0 s₀ s) : WP isa (.block (ptr .rdi .rbx 288)) s (HK1 s₀) := by
  refine wp_run' rfl fun s' hg hm rd wr => ⟨h.regs rd wr hm (by cs_keep hg), ?_⟩
  rw [hg]; simp [upd, h.base.rbx, se_ofNat]

theorem hk2_ok {s : State} (h : HK1 s₀ s) :
    WP isa (.call "vg_sha256_init" Impl.Sha256.X86_64.Stream.init) s (HK2 s₀) := by
  have hsp := h.1.base.rsp
  refine sinit_call h.2 (by rw [hsp]; dj) (by rw [h.1.base.rd, h.1.base.wr, hp.rd, hp.wr]; cov)
    (by rw [h.1.base.wr, hp.wr]; cov) fun s' rd wr cs hf hr => ⟨h.1.call hp rd wr cs (hf.sub (by fwk)), hr⟩

omit hp in
theorem hk3_ok {s : State} (h : HK2 s₀ s) :
    WP isa (.block (ptr .rdi .rbx 288 ++ [.mov32 .rsi (.imm 0), .mov .rdx (.reg .r12), .mov .rcx (.reg .r13)] ++
      ptr .r8 .rbx 512)) s (HK3 s₀) := by
  refine wp_run' rfl fun s' hg hm rd wr => ⟨⟨h.1.regs rd wr hm (by cs_keep hg), by rw [hm]; exact h.2⟩, ?_, ?_,
    ?_, ?_, ?_⟩ <;> rw [hg] <;> simp [upd, h.1.base.rbx, h.1.r12, h.1.r13, se_ofNat]

include hv in
theorem hk4_ok {nm : String} {s : State} (h : HK3 s₀ s) :
    WP isa (.call nm (Impl.Sha256.X86_64.Stream.update f)) s (HK4 s₀) := by
  obtain ⟨⟨k, hr⟩, h1, h2, h3, h4, h5⟩ := h
  have hsp := k.base.rsp
  refine update_call hv h1 h3 (congrArg BitVec.toNat h4) h5 (by dj) (by dj) (by dj) (by rw [hsp]; dj) (by rw [hsp]; dj)
    (by rw [hsp]; dj) (by rw [k.base.rd, k.base.wr, hp.rd, hp.wr]; cov) (by rw [k.base.wr, hp.wr]; cov) hr
    (by rw [h2]; rfl) fun s' rd wr cs hf hr' => ⟨k.call hp rd wr cs (hf.sub (by fwk)), ?_⟩
  rwa [List.nil_append, k.base.pw_eq hp] at hr'

omit hp in
theorem hk5_ok {s : State} (h : HK4 s₀ s) :
    WP isa (.block (ptr .rdi .rbx 288 ++ [.mov .rsi (.reg .r13)] ++ ptr .rdx .rbx 480 ++ ptr .rcx .rbx 512)) s
      (HK5 s₀) := by
  refine wp_run' rfl fun s' hg hm rd wr => ⟨⟨h.1.regs rd wr hm (by cs_keep hg), by rw [hm]; exact h.2⟩, ?_, ?_,
    ?_, ?_⟩ <;> rw [hg] <;> simp [upd, h.1.base.rbx, h.1.r13, se_ofNat]

include hv in
theorem hk6_ok {nm : String} {s : State} (h : HK5 s₀ s) :
    WP isa (.call nm (Impl.Sha256.X86_64.Stream.finalize f)) s (HK6 s₀) := by
  obtain ⟨⟨k, hr⟩, h1, h2, h3, h4⟩ := h
  have hsp := k.base.rsp
  refine sfin_call hv h1 h3 h4 (by dj) (by dj) (by dj) (by rw [hsp]; dj) (by rw [hsp]; dj) (by rw [hsp]; dj)
    (by rw [k.base.rd, k.base.wr, hp.rd, hp.wr]; cov) (by rw [k.base.wr, hp.wr]; cov) hr
    (by rw [h2, Proof.Hmac.X86_64.bytesAt_length]; simp)
    fun s' rd wr cs hf hd => ⟨k.call hp rd wr cs (hf.sub (by fwk)), hd⟩

end


theorem hash_length (m : List Byte) : (Spec.Sha256.hash m).length = 32 := by
  simp [Spec.Sha256.hash, Spec.Sha256.wordBytes, List.length_flatMap, Vector.length_toList]

/-- A key longer than a block and its hash give the same `K₀`. -/
theorem blockKey_hash {p : List Byte} (h : 64 < p.length) :
    blockKey sha256 (Spec.Sha256.hash p) = blockKey sha256 p := by
  simp only [blockKey, sha256, hash_length, h, ↓reduceIte, show ¬ (64 < 32) by decide]

theorem blockKey_length (p : List Byte) : (blockKey sha256 p).length = 64 := by
  unfold blockKey; split
  · simp [sha256, hash_length]
  · simp [sha256] at *; omega

section
variable {s₀ : State} (hp : Pre s₀) {f : Callee} (hv : Vf f)
include hp

omit hp in
theorem hk7_ok (hl : ¬ pl s₀ < 65) {s : State} (h : HK6 s₀ s) :
    WP isa (.block (ptr .r12 .rbx 480 ++ [.mov32 .r13 (.imm 32)])) s (AtK s₀) := by
  have e1 : kp s₀ = sc s₀ + BitVec.ofNat 64 480 := by simp [kp, hl]
  have e2 : kn s₀ = 32 := by simp [kn, hl]
  refine wp_run' rfl fun s' hg hm rd wr => ⟨⟨h.1.base.regs rd wr (by rw [hg]; simp [upd])
    (by rw [hg]; simp [upd]) hm, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hg, e1]; simp [upd, h.1.base.rbx, se_ofNat]
  · rw [hg, e2]; simp [upd]
  · rw [hg]; simp [upd, h.1.r14]
  · rw [hg]; simp [upd, h.1.r15]
  · rw [hg]; simp [upd, h.1.rbp]
  · rw [hm, e1, e2, show (32 : BitVec 64).toNat = 32 from rfl, h.2, blockKey_hash]
    rw [Proof.Hmac.X86_64.bytesAt_length]; omega

include hv in
theorem key_ok (sfx : String) {s : State} (h : AtP s₀ s) :
    WP isa (.ite .b (.block []) (hashKey f sfx)) s (AtK s₀) := by
  refine WP.ite (decide (pl s₀ < 65)) h.cf (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hl : pl s₀ < 65 := by simpa using hb
    have e1 : kp s₀ = pw s₀ := by simp [kp, hl]
    have e2 : kn s₀ = s₀.gpr .rsi := by simp [kn, hl]
    refine ⟨⟨h.base, by rw [h.r12, e1], by rw [h.r13, e2], h.r14, h.r15, h.rbp⟩, ?_⟩
    rw [e1, e2, h.base.pw_eq hp]
  · have hl : ¬ pl s₀ < 65 := by simpa using hb
    have k : Kp0 s₀ s := ⟨h.base, h.r12, h.r13, h.r14, h.r15, h.rbp⟩
    unfold hashKey
    exact WP.seq (WP.mono (hk1_ok k) fun _ h1 => WP.seq (WP.mono (hk2_ok hp h1) fun _ h2 =>
      WP.seq (WP.mono (hk3_ok h2) fun _ h3 => WP.seq (WP.mono (hk4_ok hp hv h3) fun _ h4 =>
      WP.seq (WP.mono (hk5_ok h4) fun _ h5 => WP.seq (WP.mono (hk6_ok hp hv h5) fun _ h6 => hk7_ok hl h6))))))

end

/-! ## The key's streaming states, and the salt -/

/-- The key's inner and outer streaming states. -/
def KeyR (s₀ : State) (m : Mem) : Prop :=
  Repr m (sc s₀ + BitVec.ofNat 64 0) (xorPad (k0 s₀) ipad) ∧ Repr m (sc s₀ + BitVec.ofNat 64 96) (xorPad (k0 s₀) opad)

abbrev KpK (s₀ s : State) : Prop := Kp s₀ s (kp s₀) (kn s₀) (sa s₀) (s₀.gpr .rcx) (op s₀)

def KS1 (s₀ s : State) : Prop := AtK s₀ s ∧ s.gpr .rdi = sc s₀ + BitVec.ofNat 64 0 ∧
  s.gpr .rsi = sc s₀ + BitVec.ofNat 64 96 ∧ s.gpr .rdx = kp s₀ ∧ s.gpr .rcx = kn s₀ ∧
  s.gpr .r8 = sc s₀ + BitVec.ofNat 64 512
def KS2 (s₀ s : State) : Prop := KpK s₀ s ∧ KeyR s₀ s.mem
def KS3 (s₀ s : State) : Prop := KS2 s₀ s ∧ Repr s.mem (sc s₀ + BitVec.ofNat 64 192) (xorPad (k0 s₀) ipad) ∧
  s.gpr .rdi = sc s₀ + BitVec.ofNat 64 192 ∧ s.gpr .rsi = BitVec.ofNat 64 64 ∧ s.gpr .rdx = sa s₀ ∧
  s.gpr .rcx = s₀.gpr .rcx ∧ s.gpr .r8 = sc s₀ + BitVec.ofNat 64 512
def KS4 (s₀ s : State) : Prop := KS2 s₀ s ∧
  Repr s.mem (sc s₀ + BitVec.ofNat 64 192) (xorPad (k0 s₀) ipad ++ S s₀)

/-- The key is the password or its hash. -/
theorem key_reg (s₀ : State) : ((⟨kp s₀, (kn s₀).toNat⟩ : Region) = pwR s₀ ∧ pl s₀ < 65) ∨
    ((⟨kp s₀, (kn s₀).toNat⟩ : Region) = sR s₀ 480 32) := by
  by_cases hl : pl s₀ < 65
  · exact .inl ⟨by simp [kp, kn, hl], hl⟩
  · exact .inr (by simp [kp, kn, hl])

section
variable {s₀ : State} (hp : Pre s₀) {f : Callee} (hv : Vf f)
include hp

omit hp in
theorem ks1_ok {s : State} (h : AtK s₀ s) :
    WP isa (.block ([.mov .rdi (.reg .rbx)] ++ ptr .rsi .rbx 96 ++ [.mov .rdx (.reg .r12), .mov .rcx (.reg .r13)] ++
      ptr .r8 .rbx 512)) s (KS1 s₀) := by
  refine wp_run' rfl fun s' hg hm rd wr => ⟨⟨h.1.regs rd wr hm (by cs_keep hg), by rw [hm]; exact h.2⟩, ?_, ?_,
    ?_, ?_, ?_⟩ <;> rw [hg] <;> simp [upd, h.1.base.rbx, h.1.r12, h.1.r13, se_ofNat]

include hv in
theorem ks2_ok {nm : String} {s : State} (h : KS1 s₀ s) :
    WP isa (.call nm (Impl.Hmac.X86_64.init f)) s (KS2 s₀) := by
  obtain ⟨⟨k, hk⟩, h1, h2, h3, h4, h5⟩ := h
  have hsp := k.base.rsp
  have hn : (kn s₀).toNat ≤ 64 := by
    unfold kn; split
    · exact Nat.le_of_lt_succ ‹_›
    · decide
  have cK : ∀ R : Region, R = sR s₀ 0 96 ∨ R = sR s₀ 96 96 ∨ R = sR s₀ 512 160 →
      Region.Disjoint ⟨kp s₀, (kn s₀).toNat⟩ R := by
    rintro R (rfl | rfl | rfl) <;> rcases key_reg s₀ with ⟨e, -⟩ | e <;> rw [e] <;> dj
  refine hinit_call hv h1 h2 h3 (congrArg BitVec.toNat h4) h5 hn (by dj) (by dj) (by dj)
    (cK _ (.inl rfl)) (cK _ (.inr (.inl rfl))) (cK _ (.inr (.inr rfl))) (by rw [hsp]; dj) (by rw [hsp]; dj)
    (by rw [hsp]; rcases key_reg s₀ with ⟨e, -⟩ | e <;> rw [e] <;> dj) (by rw [hsp]; dj) ?_
    (by rw [k.base.wr, hp.wr]; cov) fun s' rd wr cs hf hI hO => ⟨k.call hp rd wr cs (hf.sub (by fwk)), ?_, ?_⟩
  · rw [k.base.rd, k.base.wr, hp.rd, hp.wr]
    rcases key_reg s₀ with ⟨e, -⟩ | e <;> rw [e] <;> cov
  · rw [hk] at hI; exact hI
  · rw [hk] at hO; exact hO

omit hp in
theorem sc_copy {s : State} (hp : Pre s₀) (hrbx : s.gpr .rbx = sc s₀) (hwr : s.wr = s₀.wr) {o₁ o₂ n : Nat}
    (hs : o₁ + 8 * n ≤ o₂ ∨ o₂ + 8 * n ≤ o₁) (h₁ : o₁ + 8 * n ≤ 2048) (h₂ : o₂ + 8 * n ≤ 2048)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = Proof.Sha256.Stream.writeBytes s.mem (sc s₀ + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (sc s₀ + BitVec.ofNat 64 o₁) (8 * n)) → WP isa (.block rest) s' Q) :
    WP isa (.block ((List.range n).flatMap (Impl.Hmac.X86_64.cp64 .rbx .rbx o₁ o₂) ++ rest)) s Q := by
  refine Proof.Hmac.X86_64.copy64_ok (by decide) (by decide) o₁ o₂ n rest s Q
    (fun j hj => by rw [hrbx, add_ofNat]; exact hp.in_sc' hwr (by omega))
    (fun j hj => by rw [hrbx, add_ofNat]; exact hp.in_sc hwr (by omega)) ?_ (by omega)
    fun s' g rd wr m => k s' g rd wr (by rw [m, hrbx])
  rw [hrbx]
  exact Region.Disjoint.sep (sR_disj s₀ (a := o₁) (m := 8 * n) (b := o₂) (n := 8 * n) hs h₁ h₂)
    (contains_sR s₀ le_rfl le_rfl h₁) (contains_sR s₀ le_rfl le_rfl h₂)

omit hp in
/-- The bytes a copy leaves. -/
theorem copy_bytes (m : Mem) (p q : Addr) (n : Nat) (hn : n < 2 ^ 64) :
    bytesAt (Proof.Sha256.Stream.writeBytes m q (bytesAt m p n)) q n = bytesAt m p n := by
  have := Proof.Hmac.X86_64.bytesAt_writeBytes_self m q (bytesAt m p n)
    (by rw [Proof.Hmac.X86_64.bytesAt_length]; exact hn)
  rwa [Proof.Hmac.X86_64.bytesAt_length] at this

omit hp in
theorem copy_frame (m : Mem) (p q : Addr) (n : Nat) :
    Frame [⟨q, n⟩] m (Proof.Sha256.Stream.writeBytes m q (bytesAt m p n)) :=
  Proof.Sha256.Stream.writeBytes_frame _ _ _ (by
    rw [Proof.Hmac.X86_64.bytesAt_length]; exact Region.contains_self _ _)

theorem ks3_ok {s : State} (h : KS2 s₀ s) :
    WP isa (.block ((List.range 12).flatMap (Impl.Hmac.X86_64.cp64 .rbx .rbx 0 192) ++ ptr .rdi .rbx 192 ++
      [.mov32 .rsi (.imm 64), .mov .rdx (.reg .r14), .mov .rcx (.reg .r15)] ++ ptr .r8 .rbx 512)) s (KS3 s₀) := by
  obtain ⟨k, hK⟩ := h
  rw [List.append_assoc, List.append_assoc]
  refine sc_copy hp k.base.rbx k.base.wr (o₁ := 0) (o₂ := 192) (n := 12) (by omega) (by omega) (by omega)
    fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  have f₁ : Frame [sR s₀ 192 96] s.mem s₁.mem := by rw [m₁]; exact copy_frame _ _ _ _
  have k₁ : KpK s₀ s₁ := k.call hp rd₁ wr₁ (fun r hr => g₁ r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    (f₁.sub (by fwk))
  have hK₁ : KeyR s₀ s₁.mem := by
    refine ⟨repr_frame f₁ ?_ hK.1, repr_frame f₁ ?_ hK.2⟩ <;>
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] <;> dj
  have hS : Repr s₁.mem (sc s₀ + BitVec.ofNat 64 192) (xorPad (k0 s₀) ipad) := by
    refine repr_of_bytes ?_ hK.1
    rw [m₁, show 8 * 12 = 96 from rfl, copy_bytes _ _ _ _ (by omega)]
  refine wp_run' rfl fun s' hg hm rd wr => ⟨⟨k₁.regs rd wr hm (by cs_keep hg), hm ▸ hK₁⟩, hm ▸ hS, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hg] <;> simp [upd, k₁.base.rbx, k₁.r14, k₁.r15, se_ofNat]

include hv in
theorem ks4_ok {nm : String} {s : State} (h : KS3 s₀ s) :
    WP isa (.call nm (Impl.Sha256.X86_64.Stream.update f)) s (KS4 s₀) := by
  obtain ⟨⟨k, hK⟩, hS, h1, h2, h3, h4, h5⟩ := h
  have hsp := k.base.rsp
  refine update_call hv h1 h3 (congrArg BitVec.toNat h4) h5 (by dj) (by dj) (by dj) (by rw [hsp]; dj)
    (by rw [hsp]; dj) (by rw [hsp]; dj) (by rw [k.base.rd, k.base.wr, hp.rd, hp.wr]; cov)
    (by rw [k.base.wr, hp.wr]; cov) hS (by rw [h2]; simp [xorPad, k0, blockKey_length])
    fun s' rd wr cs hf hr' => ⟨⟨k.call hp rd wr cs (hf.sub (by fwk)), ?_, ?_⟩, ?_⟩
  · refine repr_frame hf ?_ hK.1
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    refine ⟨by dj, by dj, by rw [hsp]; dj⟩
  · refine repr_frame hf ?_ hK.2
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    refine ⟨by dj, by dj, by rw [hsp]; dj⟩
  · rwa [k.base.salt_eq hp] at hr'

end

end VG.Proof.Pbkdf2.X86_64.Derive
