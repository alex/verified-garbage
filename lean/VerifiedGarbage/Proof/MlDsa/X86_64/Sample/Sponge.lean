import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Common
import VerifiedGarbage.Proof.MlKem.X86_64.KCall
import VerifiedGarbage.Proof.MlKem.X86_64.Zero
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.MlDsa.Sample.Hash

/-!
# ML-DSA on x86-64: the sampling functions' SHAKE

What the sampling functions share (`Impl/MlDsa/X86_64/Sample/Common.lean`),
for any of them: a call is described by `Sp` (the message, its length, the
working space, the output polynomial and the parameter kept in `r12`), whose
regions are laid out as `SpOk` says. From the prologue on, `Env` holds: the
registers of the layout, the caller's callee-saved registers (in their
registers or saved in the working space), and the memory changed only in the
output, the working space and the stack below `rsp`. `sponge` then leaves
`outlen` bytes of SHAKE of the message at `scratch + 840` (`sponge_ok`),
leaking only the pointers and the length (`sponge_ct`).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Spec.Sha3 (bytesAt stateAt rates)
open VG.Proof.MlDsa.Sample (padded)

/-- A call of a sampling function. -/
structure Sp where
  /-- The message hashed. -/
  sd : Addr
  len : Nat
  /-- `scratch`. -/
  scr : Addr
  /-- The output polynomial. -/
  a : Addr
  /-- The parameter, in `r12`. -/
  prm : BitVec 64

namespace Sp
variable (P : Sp)
/-- `scratch + off`. -/
abbrev at' (off : Nat) : Addr := P.scr + BitVec.ofNat 64 off
abbrev scrR : Region := ⟨P.scr, 2048⟩
abbrev sdR : Region := ⟨P.sd, P.len⟩
end Sp

/-- The regions of a call from the entry state `σ`. -/
structure SpOk (P : Sp) (σ : State) : Prop where
  rd : σ.rd = [P.sdR]
  wr : σ.wr = [pR P.a, P.scrR]
  sd_a : P.sdR.Disjoint (pR P.a)
  sd_scr : P.sdR.Disjoint P.scrR
  a_scr : (pR P.a).Disjoint P.scrR
  ret_sd : (retR σ).Disjoint P.sdR
  ret_a : (retR σ).Disjoint (pR P.a)
  ret_scr : (retR σ).Disjoint P.scrR
  stk_sd : (below (σ.gpr .rsp) 16).Disjoint P.sdR
  stk_a : (below (σ.gpr .rsp) 16).Disjoint (pR P.a)
  stk_scr : (below (σ.gpr .rsp) 16).Disjoint P.scrR
  scr_end : P.scr.toNat + 2048 ≤ 2 ^ 64
  len_lt : P.len < 2 ^ 64

/-- What holds from the prologue on, relative to the entry state `σ`. -/
structure Env (P : Sp) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rbx : s.gpr .rbx = P.scr
  rbp : s.gpr .rbp = P.a
  r12 : s.gpr .r12 = P.prm
  rsp : s.gpr .rsp = σ.gpr .rsp
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], s.gpr r = σ.gpr r
  saved : s.mem.readW (P.at' 2024) 64 = σ.gpr .rbx ∧ s.mem.readW (P.at' 2032) 64 = σ.gpr .rbp ∧
    s.mem.readW (P.at' 2040) 64 = σ.gpr .r12
  frame : Frame [pR P.a, P.scrR, below (σ.gpr .rsp) 16] σ.mem s.mem

theorem r13_not {r : Reg} (hr : r ∈ [Reg.r13, .r14, .r15]) :
    r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> decide

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

omit hp in
theorem sub_scr {a n : Nat} (h : a + n ≤ 2048) : Region.Sub ⟨P.at' a, n⟩ P.scrR := Offset.sub_base _ h

omit hp in
theorem sub_scr0 {n : Nat} (h : n ≤ 2048) : Region.Sub ⟨P.scr, n⟩ P.scrR := Region.sub_prefix h

omit hp in
theorem disj_scr {a n b m : Nat} (h : a + n ≤ b) (hb : b + m ≤ 2048) :
    Region.Disjoint ⟨P.at' a, n⟩ ⟨P.at' b, m⟩ := Offset.disjoint _ (.inl h) (by omega) (by omega)

omit hp in
theorem disj_scr0 {n b m : Nat} (h : n ≤ b) (hb : b + m ≤ 2048) :
    Region.Disjoint ⟨P.scr, n⟩ ⟨P.at' b, m⟩ := Offset.base_disjoint _ h (by omega)

theorem sd_scr' {a n : Nat} (h : a + n ≤ 2048) : P.sdR.Disjoint ⟨P.at' a, n⟩ := hp.sd_scr.sub_right (sub_scr h)

theorem stk_scr' {a n : Nat} (h : a + n ≤ 2048) : (below (σ.gpr .rsp) 16).Disjoint ⟨P.at' a, n⟩ :=
  hp.stk_scr.sub_right (sub_scr h)

theorem a_scr' {a n : Nat} (h : a + n ≤ 2048) : (pR P.a).Disjoint ⟨P.at' a, n⟩ :=
  hp.a_scr.sub_right (sub_scr h)

theorem sd_scr0 {n : Nat} (h : n ≤ 2048) : P.sdR.Disjoint ⟨P.scr, n⟩ := hp.sd_scr.sub_right (sub_scr0 h)

theorem stk_scr0 {n : Nat} (h : n ≤ 2048) : (below (σ.gpr .rsp) 16).Disjoint ⟨P.scr, n⟩ :=
  hp.stk_scr.sub_right (sub_scr0 h)

omit hp in
theorem contains_scr {a n : Nat} (h : a + n ≤ 2048) : P.scrR.Contains (P.at' a) n :=
  Offset.contains_base _ h (by omega)

/-- The message is not written. -/
theorem sd_frame {s : State} (he : Env P σ s) : bytesAt s.mem P.sd P.len = bytesAt σ.mem P.sd P.len :=
  MlKem.bytesAt_frame he.frame (by simpa using ⟨hp.sd_a, hp.sd_scr, hp.stk_sd.symm⟩) (by have := hp.len_lt; omega)

/-- A word of the working space from byte 2024 on (a saved register) is apart
from the first 2024 bytes, the output polynomial and the stack. -/
theorem saved_apart {k : Nat} (hk : 2024 ≤ k) (hk' : k + 8 ≤ 2048) {sp : Addr} (hsp : sp = σ.gpr .rsp) :
    ∀ r ∈ [(⟨P.scr, 2024⟩ : Region), pR P.a, below sp 16], (⟨P.at' k, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (disj_scr0 (n := 2024) hk hk').symm
  · exact (a_scr' hp hk').symm
  · subst hsp; exact (stk_scr' hp hk').symm

/-- A call that writes within the first 2024 bytes of the working space and
the stack keeps `Env`. -/
theorem Env.call {s s' : State} (he : Env P σ s) {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨P.scr, 2024⟩)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame (rs ++ [below (s.gpr .rsp) 16]) s.mem s'.mem) : Env P σ s' := by
  have hsp : s'.gpr .rsp = s.gpr .rsp := hcs .rsp (by simp [calleeSaved])
  have hd : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 → ∀ r ∈ rs ++ [below (s.gpr .rsp) 16],
      (⟨P.at' k, 8⟩ : Region).Disjoint r := by
    intro k hk hk' r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (saved_apart hp hk hk' rfl _ (by simp)).sub_right (hrs r hr)
    · simp only [List.mem_singleton] at hr; subst hr
      exact saved_apart hp hk hk' he.rsp _ (by simp)
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hcs .rbx (by simp [calleeSaved]), he.rbx],
    by rw [hcs .rbp (by simp [calleeSaved]), he.rbp], by rw [hcs .r12 (by simp [calleeSaved]), he.r12],
    by rw [hsp, he.rsp], fun r hr => ?_, ?_, ?_⟩
  · have hr' : r ∈ calleeSaved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    rw [hcs r hr', he.cs r hr]
  · rw [hf.readW (Region.contains_self _ _) (hd 2024 (by omega) (by omega)) (by decide),
      hf.readW (Region.contains_self _ _) (hd 2032 (by omega) (by omega)) (by decide),
      hf.readW (Region.contains_self _ _) (hd 2040 (by omega) (by omega)) (by decide)]
    exact he.saved
  · refine he.frame.trans (hf.sub fun r hr => ?_)
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨P.scrR, by simp, fun x h => sub_scr0 (P := P) (n := 2024) (by omega) x (hrs r hr x h)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below (σ.gpr .rsp) 16, by simp, by rw [he.rsp]; exact fun _ h => h⟩

omit hp in
/-- `Env` after a block that writes only caller-saved registers and no memory. -/
theorem Env.keep {s s' : State} (he : Env P σ s) (hm : s'.mem = s.mem)
    (hk : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s') : Env P σ s' :=
  ⟨hk.2.1.trans he.rd, hk.2.2.trans he.wr, by rw [hk.gpr (by decide), he.rbx], by rw [hk.gpr (by decide), he.rbp],
    by rw [hk.gpr (by decide), he.r12], by rw [hk.gpr (by decide), he.rsp],
    fun r hr => by rw [hk.gpr (r13_not hr), he.cs r hr], by rw [hm]; exact he.saved, by rw [hm]; exact he.frame⟩

/-- The regions, from the prologue on. -/
theorem regions {s : State} (he : Env P σ s) : s.rd ++ s.wr = [P.sdR, pR P.a, P.scrR] := by
  rw [he.rd, he.wr, hp.rd, hp.wr]; rfl

theorem cov_all {s : State} (he : Env P σ s) {rs : List Region}
    (h : ∀ r ∈ rs, r = P.sdR ∨ ∃ off, r.base = P.scr + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) :
    Covers rs (s.rd ++ s.wr) :=
  Covers.of_sub fun r hr => by
    rw [regions hp he]
    rcases h r hr with rfl | ⟨off, hb, hl⟩
    · exact ⟨P.sdR, by simp, 0, (add_ofNat_zero _).symm, by simp⟩
    · exact ⟨P.scrR, by simp, off, hb, hl⟩

theorem cov_scr {s : State} (he : Env P σ s) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = P.scr + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) : Covers rs s.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨P.scrR, by rw [he.wr, hp.wr]; simp, off, hb, hl⟩

theorem inScr {s : State} (he : Env P σ s) {a n : Nat} (h : a + n ≤ 2048) : InRegions s.wr (P.at' a) n := by
  rw [he.wr, hp.wr]
  exact ⟨P.scrR, by simp, contains_scr h⟩

theorem inScrRd {s : State} (he : Env P σ s) {a n : Nat} (h : a + n ≤ 2048) :
    InRegions (s.rd ++ s.wr) (P.at' a) n := by
  rw [regions hp he]
  exact ⟨P.scrR, by simp, contains_scr h⟩

end

/-! ## The sponge -/

/-- The entry of `sponge`: the message in `rcx` and its length in `r8`. -/
structure J0 (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  rcx : s.gpr .rcx = P.sd
  r8 : s.gpr .r8 = BitVec.ofNat 64 P.len

/-- The message. -/
abbrev Sp.msg (P : Sp) (σ : State) : List Byte := bytesAt σ.mem P.sd P.len

/-- After zeroing the state: the arguments of `absorb`. -/
structure J1 (rate : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  zero : stateAt s.mem P.scr = Spec.Sha3.zero
  args : AbsorbArgs s P.scr P.sd (P.at' 200) rate 0 P.len

theorem sx200 : BitVec.signExtend 64 (200 : BitVec 32) = BitVec.ofNat 64 200 := by decide
theorem sx840 : BitVec.signExtend 64 (840 : BitVec 32) = BitVec.ofNat 64 840 := by decide

theorem sw64 (x : BitVec 32) : BitVec.setWidth 64 x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The rates of SHAKE256 and SHAKE128. -/
def spRate (rate : BitVec 32) : Prop := rate.toNat = 136 ∨ rate.toNat = 168

theorem spRate_mem {rate : BitVec 32} (h : spRate rate) : rate.toNat ∈ rates := by
  rcases h with h | h <;> rw [h] <;> decide

theorem spRate_pos {rate : BitVec 32} (h : spRate rate) : 0 < rate.toNat := by rcases h with h | h <;> omega

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem blk1_ok {rate : BitVec 32} (hr : spRate rate) {s : State} (h : J0 P σ s) :
    WP isa (.block (zeroSt ++ absArgs rate)) s (J1 rate.toNat P σ) := by
  unfold zeroSt
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rax = 0) (by xrun) (by decide))
    fun s1 ⟨⟨hm1, hax⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  have hb1 : s1.gpr .rbx = P.scr := by rw [k1.gpr (by decide), h.env.rbx]
  refine WP.mono (zeroSt_ok .rbx 0 s1 hax fun i hi => by
      rw [hb1, add_ofNat_zero, k1.2.2]; exact inScr hp h.env (by omega)) fun s2 ⟨hz, hf2, k2⟩ => ?_
  rw [hb1, add_ofNat_zero] at hz hf2
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .r9] (Q := fun s' => s'.mem = s2.mem ∧
      s'.gpr .rdi = P.scr ∧ s'.gpr .rsi = BitVec.ofNat 64 rate.toNat ∧ s'.gpr .rdx = BitVec.ofNat 64 0 ∧
      s'.gpr .r9 = P.at' 200)
    (by unfold absArgs; xrun [k2.gpr (r := .rbx) (by decide), hb1, sx200, sw64]) (by rfl))
    fun s3 ⟨⟨hm3, hdi, hsi, hdx, h9⟩, k3⟩ => ?_
  have e1 := h.env.keep hm1 (k1.mono (by decide))
  have k23 := (k2.trans k3)
  have hsp : s3.gpr .rsp = σ.gpr .rsp := by rw [k23.gpr (by decide), k1.gpr (by decide), h.env.rsp]
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 → s3.mem.readW (P.at' k) 64 = s1.mem.readW (P.at' k) 64 := by
    intro k hk hk'
    rw [hm3, hf2.readW (Region.contains_self _ _) (by
      simpa using (disj_scr0 (n := 200) (b := k) (m := 8) (by omega) hk').symm) (by decide)]
  refine ⟨⟨k23.2.1.trans e1.rd, k23.2.2.trans e1.wr, by rw [k23.gpr (by decide), e1.rbx],
    by rw [k23.gpr (by decide), e1.rbp], by rw [k23.gpr (by decide), e1.r12], hsp,
    fun r hr => by rw [k23.gpr (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide), e1.cs r hr],
    (by rw [hsv 2024 (by omega) (by omega), hsv 2032 (by omega) (by omega), hsv 2040 (by omega) (by omega)];
        exact e1.saved), ?_⟩, by rw [hm3]; exact hz, ?_⟩
  · rw [hm3]
    exact e1.frame.trans (hf2.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨P.scrR, by simp, sub_scr0 (by omega)⟩)
  · have hcx : s3.gpr .rcx = P.sd := by rw [k23.gpr (by decide), k1.gpr (by decide), h.rcx]
    have h8 : s3.gpr .r8 = BitVec.ofNat 64 P.len := by rw [k23.gpr (by decide), k1.gpr (by decide), h.r8]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, spRate_mem hr, spRate_pos hr, hp.len_lt,
      disj_scr0 (by omega) (by omega), (sd_scr0 hp (by omega)), sd_scr' hp (by omega),
      by rw [hsp]; exact stk_scr0 hp (by omega), by rw [hsp]; exact hp.stk_sd,
      by rw [hsp]; exact stk_scr' hp (by omega)⟩

/-- After absorbing the message. -/
structure J2 (rate : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  repr : Spec.Sha3.Repr s.mem P.scr rate (P.msg σ)
  rax : s.gpr .rax = BitVec.ofNat 64 (P.len % rate)

theorem covA {s : State} (he : Env P σ s) :
    Covers ([P.sdR] ++ [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩] s.wr := by
  refine ⟨cov_all hp he ?_, cov_scr hp he ?_⟩
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [.inl rfl, .inr ⟨0, (add_ofNat_zero _).symm, by simp⟩, .inr ⟨200, rfl, by simp⟩]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨200, rfl, by simp⟩]

omit hp in
theorem subA : ∀ r ∈ [(⟨P.scr, 200⟩ : Region), ⟨P.at' 200, 640⟩], Region.Sub r ⟨P.scr, 2024⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [Region.sub_prefix (by omega), Offset.sub_base _ (by omega)]

omit hp in
/-- The all-zero state represents the empty message. -/
theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Spec.Sha3.Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

theorem call1_ok {rate : Nat} {s : State} (h : J1 rate P σ s) :
    WP isa (.call "vg_keccak_absorb" Impl.Sha3.X86_64.Stream.absorb) s (J2 rate P σ) := by
  refine absorb_call h.args (covA hp h.env).1 (covA hp h.env).2 fun s' hrd hwr hcs hf hr hax =>
    ⟨Env.call hp h.env subA hrd hwr hcs hf, ?_, ?_⟩
  · have := hr [] (repr_nil h.zero) rfl
    rwa [List.nil_append, sd_frame hp h.env] at this
  · apply BitVec.eq_of_toNat_eq
    rw [hax, BitVec.toNat_ofNat, Nat.zero_add]
    exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ h.args.hpos) (rate_lt h.args.hrate))).symm

/-- The arguments of `pad`. -/
structure J3 (rate : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  repr : Spec.Sha3.Repr s.mem P.scr rate (P.msg σ)
  args : PadArgs s P.scr (P.at' 200) rate (P.len % rate)
  rcx : (s.gpr .rcx).setWidth 8 = Spec.Sha3.shakeSuffix

theorem blk2_ok {rate : BitVec 32} (hr : spRate rate) {s : State} (h : J2 rate.toNat P σ s) :
    WP isa (.block (padArgs rate)) s (J3 rate.toNat P σ) := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = P.scr ∧ s'.gpr .rsi = BitVec.ofNat 64 rate.toNat ∧
      s'.gpr .rdx = BitVec.ofNat 64 (P.len % rate.toNat) ∧
      s'.gpr .rcx = BitVec.setWidth 64 (0x1f : BitVec 32) ∧ s'.gpr .r8 = P.at' 200)
    (by unfold padArgs; xrun [h.env.rbx, h.rax, sx200, sw64]) (by rfl))
    fun s' ⟨⟨hm, hdi, hsi, hdx, hcx, h8⟩, k⟩ => ?_
  have he := h.env.keep hm (k.mono (by decide))
  exact ⟨he, by rw [hm]; exact h.repr, ⟨hdi, hsi, hdx, h8, spRate_mem hr, Nat.mod_lt _ (spRate_pos hr),
    disj_scr0 (by omega) (by omega), by rw [he.rsp]; exact stk_scr0 hp (by omega),
    by rw [he.rsp]; exact stk_scr' hp (by omega)⟩, by rw [hcx]; decide⟩

/-- After padding. -/
structure J4 (rate : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  st : stateAt s.mem P.scr = padded rate Spec.Sha3.shakeSuffix (P.msg σ)

theorem covP {s : State} (he : Env P σ s) :
    Covers ([] ++ [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩] s.wr :=
  ⟨fun a n h => (covA hp he).1 a n (by simp only [List.nil_append] at h; exact
    ⟨_, List.mem_append_right _ h.choose_spec.1, h.choose_spec.2⟩), (covA hp he).2⟩

theorem call2_ok {rate : Nat} {s : State} (h : J3 rate P σ s) :
    WP isa (.call "vg_keccak_pad" Impl.Sha3.X86_64.Stream.pad) s (J4 rate P σ) := by
  obtain ⟨he, hrep, hargs, hcx⟩ := h
  refine pad_call hargs (covP hp he).1 (covP hp he).2 fun s' hrd hwr hcs hf hst =>
    ⟨Env.call hp he subA hrd hwr hcs hf, ?_⟩
  rw [hst (P.msg σ) hrep (by rw [MlKem.bytesAt_length]), hcx]

omit hp in
/-- The arguments of `squeeze`. -/
def J5 (rate outlen : Nat) (P : Sp) (σ s : State) : Prop :=
  J4 rate P σ s ∧ SqueezeArgs s P.scr (P.at' 840) (P.at' 200) rate 0 outlen

theorem blk3_ok {rate outlen : BitVec 32} (hr : spRate rate) (ho : 840 + outlen.toNat ≤ 2024) {s : State}
    (h : J4 rate.toNat P σ s) : WP isa (.block (sqzArgs rate outlen)) s (J5 rate.toNat outlen.toNat P σ) := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = P.scr ∧ s'.gpr .rsi = BitVec.ofNat 64 rate.toNat ∧ s'.gpr .rdx = BitVec.ofNat 64 0 ∧
      s'.gpr .rcx = P.at' 840 ∧ s'.gpr .r8 = BitVec.ofNat 64 outlen.toNat ∧ s'.gpr .r9 = P.at' 200)
    (by unfold sqzArgs; xrun [h.env.rbx, sx200, sx840, sw64]) (by rfl))
    fun s' ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ?_
  have he := h.env.keep hm (k.mono (by decide))
  refine ⟨⟨he, by rw [hm]; exact h.st⟩, ⟨hdi, hsi, hdx, hcx, h8, h9, spRate_mem hr, Nat.zero_le _, by omega,
    disj_scr0 (by omega) (by omega), disj_scr0 (by omega) (by omega),
    (disj_scr (a := 200) (n := 640) (b := 840) (m := outlen.toNat) (by omega) (by omega)).symm,
    by rw [he.rsp]; exact stk_scr0 hp (by omega), by rw [he.rsp]; exact stk_scr' hp (by omega),
    by rw [he.rsp]; exact stk_scr' hp (by omega)⟩⟩

/-- After squeezing: the output. -/
structure J6 (rate outlen : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  out : bytesAt s.mem (P.at' 840) outlen = Spec.Sha3.squeezeFrom rate (padded rate Spec.Sha3.shakeSuffix (P.msg σ)) 0 outlen

theorem covS {outlen : Nat} (ho : 840 + outlen ≤ 2024) {s : State} (he : Env P σ s) :
    Covers ([] ++ [⟨P.scr, 200⟩, ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨P.scr, 200⟩, ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩] s.wr := by
  refine ⟨cov_all hp he ?_, cov_scr hp he ?_⟩
  · intro r hr
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [.inr ⟨0, (add_ofNat_zero _).symm, by simp⟩, .inr ⟨840, rfl, by simp; omega⟩,
      .inr ⟨200, rfl, by simp⟩]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨840, rfl, by simp; omega⟩, ⟨200, rfl, by simp⟩]

theorem call3_ok {rate outlen : Nat} (ho : 840 + outlen ≤ 2024) {s : State} (h : J5 rate outlen P σ s) :
    WP isa (.call "vg_keccak_squeeze" Impl.Sha3.X86_64.Stream.squeeze) s (J6 rate outlen P σ) := by
  obtain ⟨h, hargs⟩ := h
  have cov := covS hp ho h.env
  have sub : ∀ r ∈ [(⟨P.scr, 200⟩ : Region), ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩],
      Region.Sub r ⟨P.scr, 2024⟩ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [Region.sub_prefix (by omega), Offset.sub_base _ (by omega), Offset.sub_base _ (by omega)]
  refine squeeze_call hargs cov.1 cov.2 fun s' hrd hwr hcs hf ho' => ⟨Env.call hp h.env sub hrd hwr hcs hf, ?_⟩
  rw [ho', h.st]

/-- The sponge, from `J0`. -/
theorem sponge_ok {rate outlen : BitVec 32} (hr : spRate rate) (ho : 840 + outlen.toNat ≤ 2024) {s : State}
    (h : J0 P σ s) : WP isa (sponge rate outlen) s (J6 rate.toNat outlen.toNat P σ) :=
  WP.seq (WP.mono (blk1_ok hp hr h) fun _ h1 =>
    WP.seq (WP.mono (call1_ok hp h1) fun _ h2 => WP.seq (WP.mono (blk2_ok hp hr h2) fun _ h3 =>
      WP.seq (WP.mono (call2_ok hp h3) fun _ h4 => WP.seq (WP.mono (blk3_ok hp hr ho h4) fun _ h5 =>
        call3_ok hp ho h5)))))

end

/-! ## Constant time -/

/-- Two calls whose public data agree. -/
structure SpPub (P₁ P₂ : Sp) (σ₁ σ₂ : State) : Prop where
  sd : P₁.sd = P₂.sd
  len : P₁.len = P₂.len
  scr : P₁.scr = P₂.scr
  a : P₁.a = P₂.a
  prm : P₁.prm = P₂.prm
  rsp : σ₁.gpr .rsp = σ₂.gpr .rsp

/-- The registers of the layout agree. -/
theorem env_pub {P₁ P₂ : Sp} {σ₁ σ₂ s₁ s₂ : State} (hq : SpPub P₁ P₂ σ₁ σ₂) (e₁ : Env P₁ σ₁ s₁)
    (e₂ : Env P₂ σ₂ s₂) : s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rbp = s₂.gpr .rbp ∧ s₁.gpr .r12 = s₂.gpr .r12 ∧
      s₁.gpr .rsp = s₂.gpr .rsp := by
  rw [e₁.rbx, e₂.rbx, e₁.rbp, e₂.rbp, e₁.r12, e₂.r12, e₁.rsp, e₂.rsp, hq.scr, hq.a, hq.prm, hq.rsp]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem at_pub {P₁ P₂ : Sp} {σ₁ σ₂ : State} (hq : SpPub P₁ P₂ σ₁ σ₂) (k : Nat) : P₁.at' k = P₂.at' k := by
  simp only [Sp.at', hq.scr]

section
/-! The runs of a sampling function whose entry states satisfy `Pre` and
agree by `Pub`, each making the call `f σ` of its entry state `σ`. -/
variable {Pre : State → Prop} {Pub : State → State → Prop} {f : State → Sp}
  (hok : ∀ σ, Pre σ → SpOk (f σ) σ)
  (hpub : ∀ σ₁ σ₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → SpPub (f σ₁) (f σ₂) σ₁ σ₂)
include hok hpub

omit hpub in
/-- A piece that leaks the same from runs related by `J`, and takes each run
from `J` to `J'`. -/
theorem relSp {J J' : Sp → State → State → Prop} {c : Prog isa}
    (hw : ∀ P σ s, SpOk P σ → J P σ s → WP isa c s (J' P σ))
    (ht : RelCT isa (Rel2 Pre Pub fun σ => J (f σ) σ) c fun _ _ => True) :
    RelCT isa (Rel2 Pre Pub fun σ => J (f σ) σ) c (Rel2 Pre Pub fun σ => J' (f σ) σ) :=
  relInv (fun σ s hp h => hw _ σ s (hok σ hp) h) ht

omit hok in
/-- Code the taint analysis proves constant time from `rbx`, `rbp`, `r12`
and `rsp`, and the registers `rs`, which agree in runs related by `J`. -/
theorem taintSp {J : Sp → State → State → Prop} (hJ : ∀ σ s, J (f σ) σ s → Env (f σ) σ s) {c : Prog isa}
    (rs : List Reg) (hr : ∀ s₁ s₂, Rel2 Pre Pub (fun σ => J (f σ) σ) s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (X86_64.Taint.ofRegs (([.rbx, .rbp, .r12, .rsp] : List Reg) ++ rs)) c hc).isSome = true) :
    RelCT isa (Rel2 Pre Pub fun σ => J (f σ) σ) c fun _ _ => True :=
  taintRel _ (fun s₁ s₂ hs r hr' => by
    rcases List.mem_append.mp hr' with hr' | hr'
    · obtain ⟨σ₁, σ₂, p₁, p₂, hq, i₁, i₂⟩ := hs
      have := env_pub (hpub σ₁ σ₂ p₁ p₂ hq) (hJ _ _ i₁) (hJ _ _ i₂)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl
      exacts [this.1, this.2.1, this.2.2.1, this.2.2.2]
    · exact hr s₁ s₂ hs r hr') h

theorem sponge_ct {rate outlen : BitVec 32} (hr : spRate rate) (ho : 840 + outlen.toNat ≤ 2024)
    {h1 h2 h3 : VG.Taint.Hint X86_64.Taint.T}
    (c1 : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .rsp]) (.block (zeroSt ++ absArgs rate)) h1).isSome
      = true)
    (c2 : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .rsp, .rax]) (.block (padArgs rate)) h2).isSome = true)
    (c3 : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .rsp]) (.block (sqzArgs rate outlen)) h3).isSome
      = true) :
    RelCT isa (Rel2 Pre Pub fun σ => J0 (f σ) σ) (sponge rate outlen)
      (Rel2 Pre Pub fun σ => J6 rate.toNat outlen.toNat (f σ) σ) := by
  refine RelCT.seq (relSp hok (J' := J1 rate.toNat) (fun P σ s hp h => blk1_ok hp hr h)
    (taintSp hpub (fun _ _ h => h.env) [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by simpa using c1))) ?_
  refine RelCT.seq (relSp hok (J' := J2 rate.toNat) (fun P σ s hp h => call1_ok hp h)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Absorb.absorb_correct Proof.Sha3.X86_64.Stream.Absorb.absorb_ct
      fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq', h₁, h₂⟩ => ?_)) ?_
  · have hq := hpub σ₁ σ₂ p₁ p₂ hq'
    have o₁ := hok σ₁ p₁
    have o₂ := hok σ₂ p₂
    refine ⟨_, _, _, _, absorb_pre h₁.args, absorb_pre h₂.args, ?_, (covA o₁ h₁.env).1, (covA o₁ h₁.env).2,
      (covA o₂ h₂.env).1, (covA o₂ h₂.env).2, (env_pub hq h₁.env h₂.env).2.2.2⟩
    simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.callEntry_rsp,
      ce_gpr _ (by decide : Reg.rdi ≠ .rsp), ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
      ce_gpr _ (by decide : Reg.rdx ≠ .rsp), ce_gpr _ (by decide : Reg.rcx ≠ .rsp),
      ce_gpr _ (by decide : Reg.r8 ≠ .rsp), ce_gpr _ (by decide : Reg.r9 ≠ .rsp), h₁.args.rdi, h₂.args.rdi,
      h₁.args.rsi, h₂.args.rsi, h₁.args.rdx, h₂.args.rdx, h₁.args.rcx, h₂.args.rcx, h₁.args.r8, h₂.args.r8,
      h₁.args.r9, h₂.args.r9, hq.scr, hq.sd, hq.len, at_pub hq, (env_pub hq h₁.env h₂.env).2.2.2, and_self]
  refine RelCT.seq (relSp hok (J' := J3 rate.toNat) (fun P σ s hp h => blk2_ok hp hr h)
    (taintSp hpub (fun _ _ h => h.env) [.rax] (fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, i₁, i₂⟩ r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      rw [i₁.rax, i₂.rax, (hpub σ₁ σ₂ p₁ p₂ hq).len]) (by simpa using c2))) ?_
  refine RelCT.seq (relSp hok (J' := J4 rate.toNat) (fun P σ s hp h => call2_ok hp h)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
      fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq', h₁, h₂⟩ => ?_)) ?_
  · have hq := hpub σ₁ σ₂ p₁ p₂ hq'
    have o₁ := hok σ₁ p₁
    have o₂ := hok σ₂ p₂
    refine ⟨_, _, _, _, pad_pre h₁.args, pad_pre h₂.args, ?_, (covP o₁ h₁.env).1, (covP o₁ h₁.env).2,
      (covP o₂ h₂.env).1, (covP o₂ h₂.env).2, (env_pub hq h₁.env h₂.env).2.2.2⟩
    simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.callEntry_rsp,
      ce_gpr _ (by decide : Reg.rdi ≠ .rsp), ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
      ce_gpr _ (by decide : Reg.rdx ≠ .rsp), ce_gpr _ (by decide : Reg.r8 ≠ .rsp), h₁.args.rdi, h₂.args.rdi,
      h₁.args.rsi, h₂.args.rsi, h₁.args.rdx, h₂.args.rdx, h₁.args.r8, h₂.args.r8, hq.scr, hq.len, at_pub hq,
      (env_pub hq h₁.env h₂.env).2.2.2, and_self]
  refine RelCT.seq (relSp hok (J' := J5 rate.toNat outlen.toNat) (fun P σ s hp h => blk3_ok hp hr ho h)
    (taintSp hpub (fun _ _ h => h.env) [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by simpa using c3))) ?_
  refine relSp hok (fun P σ s hp h => call3_ok hp ho h)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct
      fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq', h₁, h₂⟩ => ?_)
  have hq := hpub σ₁ σ₂ p₁ p₂ hq'
  have o₁ := hok σ₁ p₁
  have o₂ := hok σ₂ p₂
  refine ⟨_, _, _, _, squeeze_pre h₁.2, squeeze_pre h₂.2, ?_, (covS o₁ ho h₁.1.env).1, (covS o₁ ho h₁.1.env).2,
    (covS o₂ ho h₂.1.env).1, (covS o₂ ho h₂.1.env).2, (env_pub hq h₁.1.env h₂.1.env).2.2.2⟩
  simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
      ce_gpr _ (by decide : Reg.rdi ≠ .rsp), ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
      ce_gpr _ (by decide : Reg.rdx ≠ .rsp), ce_gpr _ (by decide : Reg.rcx ≠ .rsp),
      ce_gpr _ (by decide : Reg.r8 ≠ .rsp), ce_gpr _ (by decide : Reg.r9 ≠ .rsp), h₁.2.rdi, h₂.2.rdi,
      h₁.2.rsi, h₂.2.rsi, h₁.2.rdx, h₂.2.rdx, h₁.2.rcx, h₂.2.rcx, h₁.2.r8, h₂.2.r8,
      h₁.2.r9, h₂.2.r9, hq.scr, at_pub hq, (env_pub hq h₁.1.env h₂.1.env).2.2.2, and_self]

end

end VG.Proof.MlDsa.X86_64.Sample
