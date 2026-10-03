import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode

/-!
# `vg_rsa_public_precompute` on x86-64: correctness

The entry (`pcEntry_ok`), an invalid modulus (`pcFail_ok`) and the whole
function (`pcCode_correct`), against `pcContract`, which states the shared
contract's precondition on the registers.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

/-! ## The contract on the registers -/

/-- `vg_rsa_public_precompute(pre = rdi, pre_len = rsi, n = rdx, n_len = rcx,
scratch = r8, scratch_len = r9)`. -/
def pcContract : Contract isa where
  pre s :=
    let pre : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scr : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [n] ∧ s.wr = [pre, scr] ∧ pre.Disjoint n ∧ pre.Disjoint scr ∧ n.Disjoint scr ∧
      ret.Disjoint pre ∧ ret.Disjoint n ∧ ret.Disjoint scr ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64 ∧ Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧
      (s.gpr .rsi).toNat = Spec.Rsa.precomputedWords (s.gpr .rcx).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (s.gpr .r9).toNat
  post s s' :=
    match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) with
    | some ws => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Rsa.wordsAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = ws
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
      Spec.Rsa.wordsAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = List.replicate (s.gpr .rsi).toNat 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat

/-! ## The entry -/

/-- Slot `i` of the header at `r8`. -/
def hdr8 (i : Nat) : MemOp := { base := .r8, disp := 8 * (i : Int) }

theorem pcEntry_eq : Precompute.entry = [.store (hdr8 0) .rbx, .store (hdr8 1) .rbp, .store (hdr8 2) .r12,
    .store (hdr8 3) .r13, .store (hdr8 4) .r14, .store (hdr8 5) .r15, .store (hdr8 sOut) .rdi,
    .store (hdr8 sN) .rdx, .store (hdr8 sK) .rcx, .mov .rdi (.reg .r8)] := rfl

/-- The header after the entry's stores. -/
def pcEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk : BitVec 64) : Mem :=
  ((((((((m.writeW (off B (8 * 0)) v0).writeW (off B (8 * 1)) v1).writeW (off B (8 * 2)) v2).writeW
    (off B (8 * 3)) v3).writeW (off B (8 * 4)) v4).writeW (off B (8 * 5)) v5).writeW (off B (8 * sOut)) vo).writeW
    (off B (8 * sN)) vn).writeW (off B (8 * sK)) vk

theorem pcEntryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk : BitVec 64) :
    let m' := pcEntryMem m B v0 v1 v2 v3 v4 v5 vo vn vk
    word m' B (8 * 0) = v0 ∧ word m' B (8 * 1) = v1 ∧ word m' B (8 * 2) = v2 ∧ word m' B (8 * 3) = v3 ∧
    word m' B (8 * 4) = v4 ∧ word m' B (8 * 5) = v5 ∧ word m' B (8 * sOut) = vo ∧ word m' B (8 * sN) = vn ∧
    word m' B (8 * sK) = vk ∧ Outside B 0 (8 * 22) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' pcEntryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- The entry: the saved registers and the arguments in the header at
`scratch` (`r8`), and its base in `rdi`. -/
theorem pcEntry_ok {s : State} {B : Addr} (hB : s.gpr .r8 = B)
    (hw : ∀ i < 22, InRegions s.wr (off B (8 * i)) 8) :
    WP isa (.block Precompute.entry) s fun t => t.gpr .rdi = B ∧
      word t.mem B (8 * 0) = s.gpr .rbx ∧ word t.mem B (8 * 1) = s.gpr .rbp ∧
      word t.mem B (8 * 2) = s.gpr .r12 ∧ word t.mem B (8 * 3) = s.gpr .r13 ∧
      word t.mem B (8 * 4) = s.gpr .r14 ∧ word t.mem B (8 * 5) = s.gpr .r15 ∧
      word t.mem B (8 * sOut) = s.gpr .rdi ∧ word t.mem B (8 * sN) = s.gpr .rdx ∧
      word t.mem B (8 * sK) = s.gpr .rcx ∧ Outside B 0 (8 * 22) s.mem t.mem ∧ Keep [.rdi] s t := by
  rw [pcEntry_eq]
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧
      t.mem = pcEntryMem s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx)) ?_ rfl) fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  · xrun [State.ea, hdr8, hB, hdrOff, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide),
      hw 4 (by decide), hw 5 (by decide), hw sOut (by decide), hw sN (by decide), hw sK (by decide)]
    rfl
  rw [hm]
  obtain ⟨h0, h1, h2, h3, h4, h5, hO, hN, hK, ho⟩ := pcEntryMem_facts s.mem B (s.gpr .rbx) (s.gpr .rbp)
    (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx)
  exact ⟨hdi, h0, h1, h2, h3, h4, h5, hO, hN, hK, ho, k⟩

/-! ## An invalid modulus -/

theorem readW_zero {m : Mem} {a : Addr} (h : ∀ i < 8, m (a + BitVec.ofNat 64 i) = 0) : m.readW a 64 = 0 :=
  (Mem.readW_congr (m' := fun _ => 0) fun i hi => h i (by omega)).trans (by simp [Mem.readW, Mem.read])

theorem sixteen_w (r : BitVec 64) {w : Nat} (h : r = BitVec.ofNat 64 w) :
    r + r + (r + r) + (r + r + (r + r)) + (r + r + (r + r) + (r + r + (r + r))) = BitVec.ofNat 64 (16 * w) := by
  subst h; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega

/-- `fail`: `16 w` zero bytes to `pre` (`2 w` words), 0 returned, and the
saved registers restored. -/
theorem pcFail_ok {s : State} {B : Addr} {Z k : Nat} {op : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : 8 * 32 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : word s.mem B (8 * sOut) = op) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hout : ∀ j < 16 * ((k + 7) / 8), InRegions s.wr (op + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < 16 * ((k + 7) / 8), Z ≤ ofs B (op + BitVec.ofNat 64 j)) :
    WP isa Precompute.fail s fun t =>
      PcPost s t B Z ((k + 7) / 8) op (List.replicate (2 * ((k + 7) / 8)) 0) false := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold Precompute.fail
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 (16 * ((k + 7) / 8)) ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl sOut (by decide), hl sK (by decide), hO, hK,
      shr3_w k (by omega), sixteen_w _ rfl]) rfl) fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := 16 * ((k + 7) / 8)) (by omega)
    (FailInv s₁ op (16 * ((k + 7) / 8))) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩) fun t₂ hI => ?_)
  · intro j _ hj t hI
    have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
      rw [hI.keep.2.2, k₁.2.2]; exact hout j hj
    have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' =>
        t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
        t'.gpr .rsi = op + BitVec.ofNat 64 (j + 1) ∧
        t'.gpr .rcx = BitVec.ofNat 64 (16 * ((k + 7) / 8) - (j + 1)) ∧
        t'.zf = some (decide (j + 1 = 16 * ((k + 7) / 8)))) (by
      xrun [State.ea, at0, hI.rsi, hI.rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
        ofNat64_pred (show 1 ≤ 16 * ((k + 7) / 8) - j by omega) (by omega), BitVec.add_assoc, ofNat_add_one,
        ofNat64_beq_zero (show 16 * ((k + 7) / 8) - j - 1 < 2 ^ 64 by omega)]
      exact ⟨by rw [show 16 * ((k + 7) / 8) - j - 1 = 16 * ((k + 7) / 8) - (j + 1) by omega],
        decide_eq_decide.mpr (by omega)⟩) rfl)
      fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
    · intro i hi
      rw [hm, writeW8_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact hI.bytes i (by omega)
    · intro x hx
      rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact hI.frame x fun i hi => hx i (by omega)
  -- The saved registers.
  have hw₂ : ∀ i < 32, word t₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    apply Mem.readW_congr
    intro b hb
    rw [hI.frame _ (fun j hj => scr_ne_out hsep (d := 8 * i) (i := b) (by omega) (by omega) j (by omega)), hm₁]
  have k12 := k₁.trans hI.keep
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k12.2.1, k12.2.2]; exact hl i hi
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hdi
  rw [exit_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide),
      hl₂ 3 (by decide), hl₂ 4 (by decide), hl₂ 5 (by decide), hw₂ 0 (by decide), hw₂ 1 (by decide),
      hw₂ 2 (by decide), hw₂ 3 (by decide), hw₂ 4 (by decide), hw₂ 5 (by decide)]) rfl)
    fun t ⟨⟨h0, h1, h2, h3, h4, h5, hm⟩, k₃⟩ => ⟨?_, ?_, ?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [Spec.Rsa.wordsAt, List.eq_replicate_iff]
    refine ⟨by simp, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    refine readW_zero fun b hb => ?_
    have hi := List.mem_range.mp hi
    rw [hm, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact hI.bytes _ (by omega)
  · rw [k₃.gpr (by decide), hI.keep.gpr (by decide), hax]; rfl
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro x _ hx
    rw [hm, hI.frame x fun j hj he => by
      rw [he, ofs, Mem.sub_ofNat_toNat op (by omega)] at hx; omega,
      hm₁]

/-! ## The whole function -/

/-- What `code` uses of its contract's precondition, for the working space
`B = scratch` (`r8`) of `Z` bytes, `m`'s length `k` and `pre`'s `2 w`
words. -/
structure PcCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .rcx).toNat
  hk2 : (s.gpr .rcx).toNat ≤ 1024
  hpl : (s.gpr .rsi).toNat = 2 * (((s.gpr .rcx).toNat + 7) / 8)
  hZ : 128 * (s.gpr .rcx).toNat ≤ (s.gpr .r9).toNat * 8
  hs : Scr s (s.gpr .r8) ((s.gpr .r9).toNat * 8)
  hnb : Src s (s.gpr .r8) ((s.gpr .r9).toNat * 8) (s.gpr .rdx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  hpw : ∀ i < 2 * (((s.gpr .rcx).toNat + 7) / 8), InRegions s.wr (off (s.gpr .rdi) (8 * i)) 8
  hpb : ∀ j < 16 * (((s.gpr .rcx).toNat + 7) / 8), InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1
  hps : ∀ j < 16 * (((s.gpr .rcx).toNat + 7) / 8),
    (s.gpr .r9).toNat * 8 ≤ ofs (s.gpr .r8) (s.gpr .rdi + BitVec.ofNat 64 j)
  hret : ∀ b < 8, (s.gpr .r9).toNat * 8 ≤ ofs (s.gpr .r8) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    16 * (((s.gpr .rcx).toNat + 7) / 8) ≤ ofs (s.gpr .rdi) (s.gpr .rsp + BitVec.ofNat 64 b)

theorem pcCtx_of {s : State} (h : pcContract.pre s) : PcCtx s := by
  simp only [pcContract] at h
  obtain ⟨hrd, hwr, dPn, dPs, dns, dRp, dRn, dRs, wP, wN, wS, hk, hpl, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords at hpl
  have hs : Scr s (s.gpr .r8) ((s.gpr .r9).toNat * 8) := ⟨by rw [hwr]; simp, wS⟩
  have hn := hs.nowrap
  have hp8 : (s.gpr .rsi).toNat * 8 = 16 * (((s.gpr .rcx).toNat + 7) / 8) := by omega
  have hpre : (⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  refine ⟨hk1, hk2, hpl, by omega, hs, src_of_region (by rw [hrd]; simp) (by omega) dns,
    fun i hi => ⟨_, hpre, Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj => ⟨_, hpre, contains_byte _ (by omega) (by omega)⟩,
    fun j hj => out_scr dPs (contains_byte _ (by omega) (by omega)), fun b hb => ?_⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨out_scr dRs hc, hp8 ▸ out_scr dRp hc⟩

theorem pcCode_correct (s : State) (h : pcContract.pre s) :
    ∃ t s', Exec isa Precompute.code s t s' ∧ abiPreserved s s' ∧ pcContract.post s s' := by
  have c := pcCtx_of h
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hn := c.hs.nowrap
  suffices hwp : WP isa Precompute.code s fun s' => gprPreserved s s' ∧ pcContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hg, hp⟩
  unfold Precompute.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (pcEntry_ok rfl fun i hi => c.hs.st (by omega))
    fun t₁ ⟨hdi, h0, h1, h2, h3, h4, h5, hO, hN, hK, ho₁, k₁⟩ => ?_
  have i₁ : InScr (s.gpr .r8) ((s.gpr .r9).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega)
  have hnb₁ := c.hnb.congrK i₁ k₁
  refine WP.mono (invalid_ok ((k₁.gpr (by decide)).trans rfl) (by rw [k₁.gpr (by decide), ofNat_toNat64]) hk1 hk2
    (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi))
    (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  have kk := k₁.trans k₂
  have i₂ : InScr (s.gpr .r8) ((s.gpr .r9).toNat * 8) s.mem t₂.mem := by rw [hm₂]; exact i₁
  have hs₂ := c.hs.congr kk.2.2
  have hdi₂ : t₂.gpr .rdi = s.gpr .r8 := (k₂.gpr (by decide)).trans hdi
  have hw : ∀ i < 2 * (((s.gpr .rcx).toNat + 7) / 8), InRegions t₂.wr (off (s.gpr .rdi) (8 * i)) 8 :=
    fun i hi => by rw [kk.2.2]; exact c.hpw i hi
  have hz : slot (((s.gpr .rcx).toNat + 7) / 8) 8 ≤ (s.gpr .r9).toNat * 8 := by unfold slot hdrBytes; omega
  -- What either branch leaves.
  have fin : ∀ t (ws : List (BitVec 64)) (cb : Bool),
      PcPost t₂ t (s.gpr .r8) ((s.gpr .r9).toNat * 8) (((s.gpr .rcx).toNat + 7) / 8) (s.gpr .rdi) ws cb →
      (Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) =
        if cb then some ws else none) →
      (cb = false → ws = List.replicate (2 * (((s.gpr .rcx).toNat + 7) / 8)) 0) →
      gprPreserved s t ∧ pcContract.post s t := by
    intro t ws cb hp hpc hws
    refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
      rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hp.saved 0 (by decide)).trans (by rw [hm₂]; exact h0)
      · exact (hp.saved 1 (by decide)).trans (by rw [hm₂]; exact h1)
      · exact (hp.keep.gpr (by decide)).trans (kk.gpr (by decide))
      · exact (hp.saved 2 (by decide)).trans (by rw [hm₂]; exact h2)
      · exact (hp.saved 3 (by decide)).trans (by rw [hm₂]; exact h3)
      · exact (hp.saved 4 (by decide)).trans (by rw [hm₂]; exact h4)
      · exact (hp.saved 5 (by decide)).trans (by rw [hm₂]; exact h5)
    · obtain ⟨hZx, hPx⟩ := c.hret b hb
      rw [hp.frame _ hZx hPx, i₂ _ hZx]
    · simp only [pcContract]
      rw [hpc, c.hpl]
      cases cb
      · simp only [Bool.false_eq_true, ite_false]
        exact ⟨by rw [hp.rax]; rfl, by rw [hp.words, hws rfl]⟩
      · simp only [ite_true]
        exact ⟨by rw [hp.rax]; rfl, hp.words⟩
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    refine WP.mono (pcFail_ok hs₂ hdi₂ (by omega) (by omega) (by omega) (by rw [hm₂]; exact hO)
      (by rw [hm₂, hK, ofNat_toNat64]) (fun j hj => by rw [kk.2.2]; exact c.hpb j hj) c.hps)
      fun t hp => fin t _ false hp ?_ fun _ => rfl
    simp only [Spec.Rsa.publicPrecompute, bytesAt_length, hv, Bool.false_eq_true, ite_false]
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    refine WP.mono (pcMain_ok hs₂ hdi₂ hz hk1 hk2 (by rw [hm₂]; exact hO) (by rw [hm₂, hK, ofNat_toNat64])
      (by rw [hm₂]; exact hN) (c.hnb.congrK i₂ kk) (bytesAt_length _ _ _) hv hw c.hps)
      fun t ⟨ws, hws, hp⟩ => fin t ws true hp (by rw [hws]; rfl) fun h => absurd h (by decide)

end VG.Proof.Bignum.X86_64
