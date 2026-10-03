import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.X86_64.Cmp

/-!
# `vg_rsa_public` on x86-64: the setup

From the header that `entry` leaves, `w = ⌈k / 8⌉`, the arrays' bases,
`m` and the input loaded, the mask of `input < m`, `-m⁻¹` and the number 1
(`setup_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-! ## Frames -/

/-- Memory that changes only in the working space. -/
def InScr (B : Addr) (Z : Nat) (m m' : Mem) : Prop := ∀ x, Z ≤ ofs B x → m' x = m x

theorem InScr.refl (B : Addr) (Z : Nat) (m : Mem) : InScr B Z m m := fun _ _ => rfl

theorem InScr.trans {B : Addr} {Z : Nat} {m₁ m₂ m₃ : Mem} (h₁ : InScr B Z m₁ m₂) (h₂ : InScr B Z m₂ m₃) :
    InScr B Z m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem InScr.of_outside {B : Addr} {Z o n : Nat} {m m' : Mem} (h : Outside B o n m m') (hZ : o + n ≤ Z) :
    InScr B Z m m' := fun x hx => h x (Or.inr (by omega))

theorem InScr.of_frm {B : Addr} {Z : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ Z) : InScr B Z m m' :=
  fun x hx => h x fun r hr => Or.inr (by have := hZ r hr; omega)

theorem InScr.of_arrays {B : Addr} {Z w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    (hZ : slot w 8 ≤ Z) (hjs : ∀ j ∈ js, j < 8) : InScr B Z m m' :=
  fun x hx => h x fun j hj => Or.inr (by have := slot_le (w := w) (hjs j hj); omega)

/-- The header slots read on exit and by the setup: the saved registers and
the arguments. -/
def Fixed (B : Addr) (m m' : Mem) : Prop :=
  ∀ i, i < 6 ∨ (16 ≤ i ∧ i < 22) → word m' B (8 * i) = word m B (8 * i)

theorem Fixed.refl (B : Addr) (m : Mem) : Fixed B m m := fun _ _ => rfl

theorem Fixed.trans {B : Addr} {m₁ m₂ m₃ : Mem} (h₁ : Fixed B m₁ m₂) (h₂ : Fixed B m₂ m₃) :
    Fixed B m₁ m₃ := fun i hi => (h₂ i hi).trans (h₁ i hi)

theorem Fixed.of_outside {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside B o n m m')
    (ho : 8 * 22 ≤ o ∨ (8 * 6 ≤ o ∧ o + n ≤ 8 * 16)) : Fixed B m m' :=
  fun _ hi => h.word (by omega) (by omega)

theorem Fixed.of_frm {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (ho : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16)) : Fixed B m m' :=
  fun _ hi => h.word_eq (fun r hr => by have := ho r hr; omega) (by omega)

theorem Fixed.of_arrays {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m') :
    Fixed B m m' :=
  fun i hi => h.word_eq (fun j _ => Or.inl (by have := hdr_lt_slot w j (show i < 32 by omega); omega))
    (by omega)

theorem Fixed.store (m : Mem) (B : Addr) {i : Nat} (v : BitVec 64) (hi : 6 ≤ i) (hi' : i < 32)
    (hi'' : i < 16 ∨ 22 ≤ i) : Fixed B m (m.writeW (off B (8 * i)) v) :=
  Fixed.of_outside (writeW_outside m B v (by omega)) (by omega)

/-! ## `w` -/

theorem shr3_w (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) := by
  rw [sx7, show (7 : BitVec 64) = BitVec.ofNat 64 7 from rfl, BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- The first block: `w`, the bases, and `m`'s base and pointer. -/
theorem setupHead_ok {s : State} {B : Addr} {Z k : Nat} {np : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk : k < 2 ^ 32)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = np) :
    WP isa (.block (([.mov .rcx (.mem (hdr sK)), .mov .r12 (.reg .rcx), .alu .add .r12 (.imm 7),
      .shift .shr .r12 3, .store (hdr sW) .r12] : List Instr) ++ setBases ++
      ([.mov .rsi (.mem (hdr sN)), .mov .rbx (.mem (hdr (sArr aN)))] : List Instr))) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rsi = np ∧
      t.gpr .rbx = off B (slot ((k + 7) / 8) aN) ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64)] s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .rbx, .rsi, .r12] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have eK : sK = 18 := rfl
  have eN : sN = 17 := rfl
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eAN : sArr aN = 8 := rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧
      t.mem = s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 ((k + 7) / 8))) ?_ rfl)
    fun t₁ ⟨⟨h12, hcx, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sK) (by unfold sK sFn; omega),
      hs.st (d := 8 * sW) (by unfold sW; omega), hK, shr3_w k hk]
  have hs₁ := hs.congr k₁.2.2
  refine WP.mono (setBases_ok hs₁ ((k₁.gpr (by decide)).trans hdi) h12 (by unfold sArr; omega))
    fun t₂ ⟨hb₂, ho₂, k₂⟩ => ?_
  have hs₂ := hs₁.congr k₂.2.2
  have hN₂ : word t₂.mem B (8 * sN) = np := by
    rw [ho₂.word (by unfold sN sFn sArr; omega) (by omega), hm₁,
      (writeW_outside _ B _ (by omega)).word (by unfold sN sW sFn; omega) (by omega)]; exact hN
  have hW₂ : word t₂.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ho₂.word (by unfold sW sArr; omega) (by omega), hm₁, word_writeW_self]
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  refine WP.mono (WP.keep [.rsi, .rbx] (Q := fun t => t.gpr .rsi = np ∧
      t.gpr .rbx = off B (slot ((k + 7) / 8) aN) ∧ t.mem = t₂.mem) ?_ rfl) fun t ⟨⟨hsi, hbx, hm⟩, k₃⟩ => ?_
  · xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sN) (by unfold sN sFn; omega),
      hs₂.ld (d := 8 * sArr aN) (by omega), hN₂, hb₂ aN (by decide)]
  refine ⟨(k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12),
    (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hcx), hsi, hbx, by rw [hm]; exact hW₂,
    fun j hj => by rw [hm]; exact hb₂ j hj, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [hm]
  exact (Frm.of_outside (by rw [hm₁] at *; exact writeW_outside s.mem B _ (by omega)) (by simp)).trans
    (Frm.of_outside ho₂ (by simp))

/-! ## Sequences -/

theorem wp_seqs_append {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s : State} {Q : State → Prop}
    (h : WP isa (seqs a) s fun t => WP isa (seqs b) t Q) : WP isa (seqs (a ++ b)) s Q := by
  induction a generalizing s with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact WP.seq h
    | cons d rest =>
      simp only [seqs, List.cons_append] at h ⊢
      exact WP.seq (WP.mono (WP.seq_iff.mp h) fun t ht => ih (by simp) ht)

/-! ## Byte strings outside the working space -/

/-- The bytes `bs` at `p`, readable, outside the working space. -/
structure Src (s : State) (B : Addr) (Z : Nat) (p : Addr) (bs : List Byte) : Prop where
  rd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1
  val : ∀ i (h : i < bs.length), s.mem (p + BitVec.ofNat 64 i) = bs[i]
  out : ∀ i < bs.length, Z ≤ ofs B (p + BitVec.ofNat 64 i)

theorem Src.congr {s t : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs)
    (hm : InScr B Z s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Src t B Z p bs :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi, fun i hi => by rw [hm _ (h.out i hi)]; exact h.val i hi, h.out⟩

theorem Src.congrK {s t : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} {rs : List Reg}
    (h : Src s B Z p bs) (hm : InScr B Z s.mem t.mem) (k : Keep rs s t) : Src t B Z p bs :=
  h.congr hm k.2.1 k.2.2

/-- `loadBE` of bytes outside the working space into array `j`. -/
theorem loadArr_ok {s : State} {B : Addr} {Z k : Nat} {p : Addr} {bs : List Byte} {j : Nat} (hs : Scr s B Z)
    (hj : j < 8) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hsrc : Src s B Z p bs) (hk : bs.length = k) (hk1 : 1 ≤ k)
    (hk' : k < 2 ^ 31) (hsi : s.gpr .rsi = p) (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = off B (slot ((k + 7) / 8) j)) :
    WP isa loadBE s fun t =>
      wv t.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) = Spec.Rsa.os2ip bs ∧
      Arrays B ((k + 7) / 8) [j] s.mem t.mem ∧ Keep [.rax, .rdx, .rbp, .r14] s t := by
  have := slot_le (w := (k + 7) / 8) hj
  refine WP.mono (loadBE_ok hs hsi hcx hbx hk hk1 hk' rfl (by omega) (fun i hi => hsrc.rd i (by omega))
    (fun i hi => hsrc.val i (by omega)) (fun i hi => Or.inr (by have := hsrc.out i (by omega); omega)))
    fun t ⟨h1, h2, h3⟩ => ⟨h1, Arrays.of_outside (List.mem_singleton_self j) h2 (Nat.le_refl _) (by omega), h3⟩

/-! ## The steps of the setup -/

/-- `w`, the bases, `m` and the input. -/
def loadSteps : List (Prog isa) := [.block ([.mov .rcx (.mem (hdr sK)), .mov .r12 (.reg .rcx), .alu .add .r12 (.imm 7),
      .shift .shr .r12 3, .store (hdr sW) .r12] ++ setBases ++
      [.mov .rsi (.mem (hdr sN)), .mov .rbx (.mem (hdr (sArr aN)))]),
      loadBE,
      .block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))],
      loadBE]

/-- The mask of `input < m`, `-m⁻¹` and the number 1. -/
def restSteps : List (Prog isa) := [.block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
        .mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)],
      wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
        cfToRbp],
      .block ([.store (hdr sMask) .rbp, .mov .rbx (.mem (at0 .r10))] ++ minv ++
        [.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]),
      setWord aOne .rcx]

/-- What the loads change. -/
def loadRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sW, 8), (8 * sArr 0, 64), (slot w aN, 8 * (w + 2)), (slot w aX, 8 * (w + 2))]

theorem Frm.of_arrays1 {B : Addr} {w j : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Arrays B w [j] m m')
    (hr : (slot w j, 8 * (w + 2)) ∈ rs) : Frm B rs m m' :=
  Frm.of_arrays h fun _ hj => (List.mem_singleton.mp hj) ▸ hr

/-- `w`, the bases, `m` into array `aN` and the input into `aX`. -/
theorem setupLoad_ok {s : State} {B : Addr} {Z k : Nat} {np ip : Addr} {nb xb : List Byte} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 1 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = np)
    (hIn : word s.mem B (8 * sIn) = ip) (hnb : Src s B Z np nb) (hxb : Src s B Z ip xb)
    (hnl : nb.length = k) (hxl : xb.length = k) :
    WP isa (seqs loadSteps) s fun t =>
      wv t.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb ∧
      wv t.mem B (slot ((k + 7) / 8) aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) ∧
      Frm B (loadRanges ((k + 7) / 8)) s.mem t.mem ∧
      Keep [.rax, .rcx, .rdx, .rbx, .rsi, .rbp, .r12, .r14] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have eK : sK = 18 := rfl
  have eW : sW = 6 := rfl
  have eIn : sIn = 21 := rfl
  have eA : sArr 0 = 8 := rfl
  have eAX : sArr aX = 9 := rfl
  unfold loadSteps
  have hsl : ∀ r ∈ loadRanges ((k + 7) / 8), r.1 + r.2 ≤ Z := by
    have := slot_le (w := (k + 7) / 8) (show aN < 8 by decide)
    have := slot_le (w := (k + 7) / 8) (show aX < 8 by decide)
    simp only [loadRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [eW, eA] <;> omega
  have hhd : ∀ i, 8 * i + 8 ≤ 8 * sW ∨ (16 ≤ i ∧ i < 32) →
      ∀ r ∈ loadRanges ((k + 7) / 8), 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
    intro i hi
    have := hdr_lt_slot ((k + 7) / 8) aN (i := i) (by omega)
    have := hdr_lt_slot ((k + 7) / 8) aX (i := i) (by omega)
    simp only [loadRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [eW, eA] at * <;> omega
  refine WP.seq (WP.mono (setupHead_ok hs hdi hZ (by omega) hK hN)
    fun t₁ ⟨h12, hcx, hsi, hbx, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hf₁' : Frm B (loadRanges ((k + 7) / 8)) s.mem t₁.mem := hf₁.mono (by simp [loadRanges])
  refine WP.seq (WP.mono (loadArr_ok hs₁ (by decide) hZ (hnb.congrK (InScr.of_frm hf₁' hsl) k₁) hnl (by omega)
    hk hsi hcx hbx) fun t₂ ⟨hv₂, ha₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hf₂ : Frm B (loadRanges ((k + 7) / 8)) s.mem t₂.mem :=
    hf₁'.trans (Frm.of_arrays1 ha₂ (by simp [loadRanges]))
  have hw₂ : ∀ i, 8 * i + 8 ≤ 8 * sW ∨ (16 ≤ i ∧ i < 32) → word t₂.mem B (8 * i) = word s.mem B (8 * i) :=
    fun i hi => hf₂.word_eq (hhd i hi) (by omega)
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  have hb₂ : ∀ j < 8, word t₂.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j) := fun j hj => by
    rw [ha₂.hslot (by unfold sArr; omega)]; exact hb₁ j hj
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = ip ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rbx = off B (slot ((k + 7) / 8) aX) ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sIn) (by omega), hs₂.ld (d := 8 * sK) (by omega),
      hs₂.ld (d := 8 * sArr aX) (by omega), hw₂ sIn (by omega), hw₂ sK (by omega), hIn, hK, hb₂ aX (by decide)])
    rfl) fun t₃ ⟨⟨hsi₃, hcx₃, hbx₃, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hs₂.congr k₃.2.2
  have hf₃ : Frm B (loadRanges ((k + 7) / 8)) s.mem t₃.mem := by rw [hm₃]; exact hf₂
  refine WP.mono (loadArr_ok hs₃ (by decide) hZ (hxb.congrK (InScr.of_frm hf₃ hsl) ((k₁.trans k₂).trans k₃))
    hxl (by omega) hk hsi₃ hcx₃ hbx₃) fun t ⟨hv, ha, k₄⟩ => ?_
  have hN' : wv t.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb := by
    rw [ha.wv_eq (fun j hj => by
      rw [List.mem_singleton.mp hj]; have := slot_sep (w := (k + 7) / 8) (show aN ≠ aX by decide); omega)
      (by have := slot_le (w := (k + 7) / 8) (show aN < 8 by decide); omega), hm₃]
    exact hv₂
  refine ⟨hN', hv, ?_, fun j hj => ?_, hf₃.trans (Frm.of_arrays1 ha (by simp [loadRanges])),
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · rw [ha.hslot (by decide), hm₃, ha₂.hslot (by decide)]; exact hW₁
  · rw [ha.hslot (by unfold sArr; omega), hm₃]; exact hb₂ j hj

theorem wv_mod64 (m : Mem) (p : Addr) (d : Nat) {n : Nat} (hn : 1 ≤ n) :
    wv m p d n % 2 ^ 64 = (word m p d).toNat := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp [wv, Nat.mod_eq_of_lt (word m p d).isLt]
    · rw [wv, Nat.add_mod, ih hn', show 64 * n = 64 + 64 * (n - 1) by omega, Nat.pow_add, Nat.mul_assoc,
        Nat.mul_mod_right, Nat.add_zero, Nat.mod_eq_of_lt (word m p d).isLt]

/-- After the setup: the modulus `N`, `-N⁻¹` in the header, the input `X`,
the number 1, and the mask of `X < N`. -/
structure SetupOut (t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X : Nat) : Prop where
  good : Good t B Z w minv
  n : wv t.mem B (slot w aN) w = N
  inv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  x : wv t.mem B (slot w aX) w = X
  one : wv t.mem B (slot w aOne) w = 1
  mask : word t.mem B (8 * sMask) = mask (decide (X < N))
  r12 : t.gpr .r12 = BitVec.ofNat 64 w
  r10 : t.gpr .r10 = off B (slot w aN)

/-- The mask of `X < N`, `-N⁻¹` and the number 1. -/
theorem setupRest_ok {s : State} {B : Addr} {Z w : Nat} {N X : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hW : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hb : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot w j))
    (hN : wv s.mem B (slot w aN) w = N) (hX : wv s.mem B (slot w aX) w = X) (hodd : N % 2 = 1) :
    WP isa (seqs restSteps) s fun t => ∃ minv, SetupOut t B Z w minv N X ∧
      Frm B [(8 * sMinv, 8), (8 * sMask, 8), (slot w aOne, 8 * (w + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h0 := slot_le (w := w) (show 0 < 8 by decide)
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eK : sMask = 22 := rfl
  have eAX : sArr aX = 9 := rfl
  have eAN : sArr aN = 8 := rfl
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold restSteps
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off B (slot w aX) ∧ t.gpr .r10 = off B (slot w aN) ∧ t.gpr .rbp = mask false ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl sW (by omega), hl (sArr aX) (by omega), hl (sArr aN) (by omega),
      hW, hb aX (by decide), hb aN (by decide)]) rfl) fun t₁ ⟨⟨h12, hbx, h10, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (cmpLoop_ok hs₁ hbx h10 h12 hbp (by omega) hw'
    (by have := slot_le (w := w) (show aX < 8 by decide); omega)
    (by have := slot_le (w := w) (show aN < 8 by decide); omega)) fun t₂ ⟨hbp₂, hm₂, k₂⟩ => ?_)
  rw [hm₁, hN, hX] at hbp₂
  have hs₂ := hs₁.congr k₂.2.2
  have hm₂' : t₂.mem = s.mem := hm₂.trans hm₁
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  have h10₂ : t₂.gpr .r10 = off B (slot w aN) := (k₂.gpr (by decide)).trans h10
  -- `-N⁻¹`.
  have hodd₀ : (word s.mem B (slot w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ (show 1 ≤ w by omega), Nat.mod_mod_of_dvd _ (by decide), hN, hodd]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  have hst : ∀ i < 32, InRegions t₂.wr (off B (8 * i)) 8 := fun i hi => hs₂.st (by omega)
  have hsN : (s.mem.writeW (off B (8 * sMask)) (mask (decide (X < N)))).readW (off B (slot w aN)) 64 =
      word s.mem B (slot w aN) :=
    (writeW_outside _ B _ (by omega)).word (by have := hdr_lt_slot w aN (show sMask < 32 by decide); omega)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega)
  refine WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = word s.mem B (slot w aN) ∧
      t.mem = s.mem.writeW (off B (8 * sMask)) (mask (decide (X < N)))) (by
    xrun [State.ea, hdr, at0, hdi₂, hdrOff, hst sMask (by omega), hbp₂, h10₂, hm₂', hsN,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.ld (d := slot w aN) (by have := slot_le (w := w) (show aN < 8 by decide); omega)]) rfl)
    fun t₃ ⟨⟨hbx₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (minv_ok t₃ (by rw [hbx₃]; exact hodd₀)) fun t₄ ⟨hinv, k₄, hm₄⟩ => ?_
  rw [hbx₃] at hinv
  have hs₄ := (hs₂.congr k₃.2.2).congr k₄.2.2
  have hdi₄ : t₄.gpr .rdi = B := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi₂)
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = 1 ∧ t.gpr .rcx = BitVec.ofNat 64 0 ∧
      t.mem = t₄.mem.writeW (off B (8 * sMinv)) (t₄.gpr .r15)) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.st (d := 8 * sMinv) (by omega)]) rfl)
    fun t₅ ⟨⟨hdx₅, hcx₅, hm₅⟩, k₅⟩ => ?_
  have hs₅ := hs₄.congr k₅.2.2
  have hdi₅ : t₅.gpr .rdi = B := (k₅.gpr (by decide)).trans hdi₄
  have hm₅' : t₅.mem = (s.mem.writeW (off B (8 * sMask)) (mask (decide (X < N)))).writeW (off B (8 * sMinv))
      (t₄.gpr .r15) := by rw [hm₅, hm₄, hm₃]
  have hwv : ∀ j < 8, wv t₅.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj => by
    have := slot_le (w := w) hj
    rw [hm₅', (writeW_outside _ B _ (by omega)).wv (by have := hdr_lt_slot w j (show sMinv < 32 by decide); omega)
      (by omega), (writeW_outside _ B _ (by omega)).wv
      (by have := hdr_lt_slot w j (show sMask < 32 by decide); omega) (by omega)]
  have hw0 : word t₅.mem B (slot w aN) = word s.mem B (slot w aN) := by
    have := slot_le (w := w) (show aN < 8 by decide)
    rw [hm₅', (writeW_outside _ B _ (by omega)).word
      (by have := hdr_lt_slot w aN (show sMinv < 32 by decide); omega) (by omega)]; exact hsN
  have hhd : ∀ i < 32, i ≠ sMask → i ≠ sMinv → word t₅.mem B (8 * i) = word s.mem B (8 * i) := fun i hi h1 h2 => by
    rw [hm₅', hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h1)]
  have hH : Hdr t₅.mem B w (t₄.gpr .r15) :=
    ⟨by rw [hhd sW (by decide) (by decide) (by decide)]; exact hW,
      by rw [hm₅', word_writeW_self],
      fun j hj => by rw [hhd (sArr j) (by unfold sArr; omega) (by unfold sArr sMask sFn; omega)
        (by unfold sArr sMinv; omega)]; exact hb j hj⟩
  have h12₅ : t₅.gpr .r12 = BitVec.ofNat 64 w :=
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans
      ((k₂.gpr (by decide)).trans h12)))
  have h10₅ : t₅.gpr .r10 = off B (slot w aN) :=
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h10₂))
  refine WP.mono (setWord_ok hs₅ hdi₅ hH hZ h12₅ (by omega) hw' (o := aOne) (by decide) (ri := .rcx) (by decide)
    (i := 0) (by omega) hcx₅) fun t ⟨hone, ho, k₆⟩ => ⟨t₄.gpr .r15, ?_, ?_, ?_⟩
  · have ha : Arrays B w [aOne] t₅.mem t.mem := Arrays.of_outside (List.mem_singleton_self _) ho
      (Nat.le_refl _) (Nat.le_refl _)
    have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
    refine ⟨⟨hs₅.congr k₆.2.2, (k₆.gpr (by decide)).trans hdi₅, ha.hdr hH⟩, ?_, ?_, ?_, ?_, ?_,
      (k₆.gpr (by decide)).trans h12₅, (k₆.gpr (by decide)).trans h10₅⟩
    · rw [ha.wv_of_not_mem (by decide) (by decide) hn', hwv aN (by decide), hN]
    · rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega), hw0]; exact hinv
    · rw [ha.wv_of_not_mem (by decide) (by decide) hn', hwv aX (by decide), hX]
    · rw [hone, hdx₅]; rfl
    · rw [ha.hslot (by decide), hm₅', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm₅'] at ho
    exact ((Frm.of_outside (writeW_outside _ B _ (by omega)) (by simp)).trans
      (Frm.of_outside (writeW_outside _ B _ (by omega)) (by simp))).trans (Frm.of_outside ho (by simp))
  · exact (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)

/-- What the setup changes. -/
def setupRanges (w : Nat) : List (Nat × Nat) :=
  loadRanges w ++ [(8 * sMinv, 8), (8 * sMask, 8), (slot w aOne, 8 * (w + 2))]

/-- The setup, for a valid modulus. -/
theorem setup_ok {s : State} {B : Addr} {Z k : Nat} {np ip : Addr} {nb xb : List Byte} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = np)
    (hIn : word s.mem B (8 * sIn) = ip) (hnb : Src s B Z np nb) (hxb : Src s B Z ip xb)
    (hnl : nb.length = k) (hxl : xb.length = k) (hodd : Spec.Rsa.os2ip nb % 2 = 1) :
    WP isa (seqs (loadSteps ++ restSteps)) s fun t => ∃ minv,
      SetupOut t B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) ∧
      Frm B (setupRanges ((k + 7) / 8)) s.mem t.mem ∧ Keep mmRegs s t := by
  refine wp_seqs_append (by simp [loadSteps]) (by simp [restSteps])
    (WP.mono (setupLoad_ok hs hdi hZ (by omega) hk hK hN hIn hnb hxb hnl hxl)
      fun t₁ ⟨hN₁, hX₁, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  refine WP.mono (setupRest_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hZ (by omega) (by omega)
    hW₁ hb₁ hN₁ hX₁ hodd) fun t ⟨minv, ho, hf, k₂⟩ => ⟨minv, ho, ?_, (k₁.trans k₂).mono (by decide)⟩
  exact (hf₁.mono fun r hr => List.mem_append_left _ hr).trans
    (hf.mono fun r hr => List.mem_append_right _ hr)

end VG.Proof.Bignum.X86_64
