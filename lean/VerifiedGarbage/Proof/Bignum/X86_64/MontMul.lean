import VerifiedGarbage.Proof.Bignum.X86_64.Csub

/-!
# Multiword arithmetic on x86-64: Montgomery multiplication

The working space at `B` (`rdi`) holds the header and, after it, eight
arrays of `w + 2` words (`slot w j`). The header (`Hdr`) gives `w`,
`-m⁻¹ mod 2⁶⁴` and the arrays' bases. `montMul mo acc tmp o a b` leaves
`[o] < m` with `[o] R ≡ [a] [b] (mod m)` for `R = 2^(64 w)` and `m = [mo]`
(`montMul_ok`), changing only the arrays `acc`, `tmp` and `o`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The offset of array `j`. -/
def slot (w j : Nat) : Nat := hdrBytes + j * (8 * (w + 2))

theorem slot_sep {w j k : Nat} (h : j ≠ k) :
    slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j := by
  unfold slot
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ k by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · right
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show k + 1 ≤ j by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

theorem slot_le {w j : Nat} (h : j < 8) : slot w j + 8 * (w + 2) ≤ slot w 8 := by
  unfold slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ 8 by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem hdr_lt_slot (w j : Nat) {i : Nat} (hi : i < 32) : 8 * i + 8 ≤ slot w j := by
  unfold slot hdrBytes; omega

/-- The header: `w`, `-m⁻¹` and the arrays' bases. -/
structure Hdr (m : Mem) (B : Addr) (w : Nat) (minv : BitVec 64) : Prop where
  hw : word m B (8 * sW) = BitVec.ofNat 64 w
  hminv : word m B (8 * sMinv) = minv
  harr : ∀ j < 8, word m B (8 * sArr j) = off B (slot w j)

/-- Memory that changes only in the arrays `js`. -/
def Arrays (B : Addr) (w : Nat) (js : List Nat) (m m' : Mem) : Prop :=
  ∀ x, (∀ j ∈ js, ofs B x < slot w j ∨ slot w j + 8 * (w + 2) ≤ ofs B x) → m' x = m x

theorem Arrays.of_outside {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} {j : Nat} (hj : j ∈ js)
    {o n : Nat} (h : Outside B o n m m') (ho : slot w j ≤ o) (hn : o + n ≤ slot w j + 8 * (w + 2)) :
    Arrays B w js m m' := fun x hx => h x (by have := hx j hj; omega)

theorem Arrays.trans {B : Addr} {w : Nat} {js : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Arrays B w js m₁ m₂) (h₂ : Arrays B w js m₂ m₃) : Arrays B w js m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Arrays.mono {B : Addr} {w : Nat} {js js' : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    (hs : ∀ j ∈ js, j ∈ js') : Arrays B w js' m m' := fun x hx => h x fun j hj => hx j (hs j hj)

theorem Arrays.word_eq {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    {d : Nat} (hd : ∀ j ∈ js, d + 8 ≤ slot w j ∨ slot w j + 8 * (w + 2) ≤ d) (hd' : d + 8 ≤ 2 ^ 64) :
    word m' B d = word m B d :=
  (Mem.readW_congr fun i hi => (h _ fun j hj => by
    have := hd j hj; rw [ofs_off B (by omega)]; omega).symm).symm

theorem Arrays.wv_eq {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    {d k : Nat} (hd : ∀ j ∈ js, d + 8 * k ≤ slot w j ∨ slot w j + 8 * (w + 2) ≤ d)
    (hd' : d + 8 * k ≤ 2 ^ 64) : VG.Proof.Bignum.X86_64.wv m' B d k = VG.Proof.Bignum.X86_64.wv m B d k :=
  wv_congr fun i hi => h.word_eq (fun j hj => by have := hd j hj; omega) (by omega)

theorem Arrays.hdr {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    {minv : BitVec 64} (hH : Hdr m B w minv) : Hdr m' B w minv := by
  have hh : ∀ i < 32, word m' B (8 * i) = word m B (8 * i) := fun i hi =>
    h.word_eq (fun j _ => Or.inl (hdr_lt_slot w j hi)) (by omega)
  exact ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun j hj => (hh _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩

/-- Memory that changes only in the byte ranges `rs` (offsets and lengths
from `B`). -/
def Frm (B : Addr) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ x, (∀ r ∈ rs, ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x) → m' x = m x

theorem Frm.refl (B : Addr) (rs : List (Nat × Nat)) (m : Mem) : Frm B rs m m := fun _ _ => rfl

theorem Frm.trans {B : Addr} {rs : List (Nat × Nat)} {m₁ m₂ m₃ : Mem} (h₁ : Frm B rs m₁ m₂)
    (h₂ : Frm B rs m₂ m₃) : Frm B rs m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Frm.mono {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hs : ∀ r ∈ rs, r ∈ rs') : Frm B rs' m m' := fun x hx => h x fun r hr => hx r (hs r hr)

theorem Frm.of_outside {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} {o n : Nat} (h : Outside B o n m m')
    (hr : (o, n) ∈ rs) : Frm B rs m m' := fun x hx => h x (hx _ hr)

theorem Frm.of_arrays {B : Addr} {w : Nat} {js : List Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (h : Arrays B w js m m') (hr : ∀ j ∈ js, (slot w j, 8 * (w + 2)) ∈ rs) : Frm B rs m m' :=
  fun x hx => h x fun j hj => hx _ (hr j hj)

theorem Frm.word_eq {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 ≤ 2 ^ 64) : word m' B d = word m B d :=
  (Mem.readW_congr fun i hi => (h _ fun r hr => by
    have := hd r hr; rw [ofs_off B (by omega)]; omega).symm).symm

theorem Frm.wv_eq {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m') {d k : Nat}
    (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    VG.Proof.Bignum.X86_64.wv m' B d k = VG.Proof.Bignum.X86_64.wv m B d k :=
  wv_congr fun i hi => h.word_eq (fun r hr => by have := hd r hr; omega) (by omega)

/-- The header, after a store to a slot of the functions' own (`sFn`). -/
theorem Hdr.store {m : Mem} {B : Addr} {w : Nat} {minv : BitVec 64} (hH : Hdr m B w minv) {i : Nat}
    (hi : 16 ≤ i) (hi' : i < 32) (v : BitVec 64) : Hdr (m.writeW (off B (8 * i)) v) B w minv := by
  have hh : ∀ k < 16, word (m.writeW (off B (8 * i)) v) B (8 * k) = word m B (8 * k) := fun k hk =>
    (writeW_outside m B v (by omega)).word (by omega) (by omega)
  exact ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun j hj => (hh _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩

/-- A header slot's address, as `xrun` leaves it. -/
theorem hdrOff (B : Addr) (i : Nat) : B + BitVec.ofInt 64 (8 * (i : Int)) = off B (8 * i) := by
  rw [show (8 * (i : Int)) = ((8 * i : Nat) : Int) by omega, BitVec.ofInt_natCast]

/-- `bases o a b mo acc tmp`: the bases from the header, and `w` and `-m⁻¹`. -/
theorem bases_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b mo acc tmp : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) :
    WP isa (.block (bases o a b mo acc tmp)) s fun t =>
      t.gpr .rbx = off B (slot w o) ∧ t.gpr .r11 = off B (slot w a) ∧ t.gpr .r9 = off B (slot w b) ∧
      t.gpr .r10 = off B (slot w mo) ∧ t.gpr .r8 = off B (slot w acc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = off B (slot w tmp) ∧ t.mem = s.mem ∧
      Keep [.rbx, .r11, .r9, .r10, .r8, .r12, .r15, .rsi] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rbx, .r11, .r9, .r10, .r8, .r12, .r15, .rsi] (c := .block (bases o a b mo acc tmp))
    (Q := fun t => t.gpr .rbx = off B (slot w o) ∧ t.gpr .r11 = off B (slot w a) ∧
      t.gpr .r9 = off B (slot w b) ∧ t.gpr .r10 = off B (slot w mo) ∧ t.gpr .r8 = off B (slot w acc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = off B (slot w tmp) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2, k⟩
  unfold bases
  xrun [State.ea, hdr, hdi, hdrOff, hl (sArr o) (by unfold sArr; omega), hl (sArr a) (by unfold sArr; omega),
    hl (sArr b) (by unfold sArr; omega), hl (sArr mo) (by unfold sArr; omega),
    hl (sArr acc) (by unfold sArr; omega), hl (sArr tmp) (by unfold sArr; omega), hl sW (by decide),
    hl sMinv (by decide), hH.harr o ho, hH.harr a ha, hH.harr b hb, hH.harr mo hmo, hH.harr acc hacc,
    hH.harr tmp htmp, hH.hw, hH.hminv]

/-- The registers `montMul` may change: all but `rdi` and `rsp`. -/
def mmRegs : List Reg :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- A number of `w + 2` words: its low `w` words and the two above. -/
theorem wv_top2 (m : Mem) (B : Addr) (d w : Nat) :
    wv m B d (w + 2) = wv m B d w + 2 ^ (64 * w) *
      ((word m B (d + 8 * w)).toNat + 2 ^ 64 * (word m B (d + 8 * w + 8)).toNat) := by
  rw [show w + 2 = w + 1 + 1 from rfl, wv, wv, pow64_succ, show d + 8 * (w + 1) = d + 8 * w + 8 by omega]
  ring

/-- Montgomery multiplication: `[o] = [a] [b] R⁻¹ mod m` for `m = [mo]`, if
`[b] < m` and `-m⁻¹` is right. -/
theorem montMul_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {mo acc tmp o a b : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8) (ha : a < 8)
    (hb : b < 8) (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d4 : acc ≠ a) (d5 : acc ≠ b)
    (d6 : tmp ≠ mo) (d7 : tmp ≠ o)
    (hinv : ((word s.mem B (slot w mo)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w mo) w) :
    WP isa (montMul mo acc tmp o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w mo) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w mo) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w mo) w ∧
      Arrays B w [acc, tmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => (slot_le hj).trans hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have hN0 : 0 < wv s.mem B (slot w mo) w := by omega
  unfold montMul
  -- The bases.
  refine WP.seq (WP.mono (bases_ok hs hdi hH hZ ho ha hb hmo hacc htmp)
    fun s₁ ⟨hbx, h11, h9, h10, h8, h12, h15, hsi₁, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  -- The accumulator := 0.
  refine WP.seq (WP.mono (zeroAccLoop_ok hs₁ h8 h12 (by omega) hw' (sl acc hacc))
    fun s₂ ⟨hz₂, ho₂, k₂⟩ => ?_)
  rw [hm₁] at ho₂
  have hs₂ := hs₁.congr k₂.2.2
  have k12 := k₁.trans k₂
  have fr₂ : ∀ {j}, j < 8 → j ≠ acc → wv s₂.mem B (slot w j) w = wv s.mem B (slot w j) w :=
    fun hj hne => ho₂.wv (by have := sp hne; omega) (by have := sl _ hj; omega)
  have fw₂ : word s₂.mem B (slot w mo) = word s.mem B (slot w mo) :=
    ho₂.word (by have := sp (Ne.symm d1); have := sl _ hmo; omega) (by have := sl _ hmo; omega)
  -- The rounds.
  refine WP.seq (WP.mono (rounds_ok hs₂ ((k₂.gpr (by decide)).trans h8) ((k₂.gpr (by decide)).trans h9)
    ((k₂.gpr (by decide)).trans h10) ((k₂.gpr (by decide)).trans h11) ((k₂.gpr (by decide)).trans h12)
    hw hw' (sl acc hacc) (by have := sl b hb; omega) (by have := sl mo hmo; omega)
    (by have := sl a ha; omega) (by have := sp (Ne.symm d5); omega) (by have := sp (Ne.symm d1); omega)
    (by have := sp (Ne.symm d4); omega)
    (by rw [fw₂, (k₂.gpr (by decide) : s₂.gpr .r15 = s₁.gpr .r15), h15]; exact hinv) hz₂
    (by rw [fr₂ hb (Ne.symm d5), fr₂ hmo (Ne.symm d1)]; exact hB)) fun s₃ hR => ?_)
  have hTlt := hR.lt
  have hTc := hR.cong
  rw [fr₂ hmo (Ne.symm d1)] at hTlt hTc
  rw [fr₂ ha (Ne.symm d4), fr₂ hb (Ne.symm d5)] at hTc
  have k123 := k12.trans hR.keep
  have hs₃ := hR.scr
  have fr₃ : ∀ {j}, j < 8 → j ≠ acc → wv s₃.mem B (slot w j) w = wv s.mem B (slot w j) w := fun hj hne =>
    (hR.out.wv (by have := sp hne; omega) (by have := sl _ hj; omega)).trans (fr₂ hj hne)
  have k14 := k₂.trans hR.keep
  have hsi : s₃.gpr .rsi = off B (slot w tmp) := (k14.gpr (by decide)).trans hsi₁
  -- `T - m`.
  refine WP.seq (WP.mono (subMod_ok hs₃ ((k14.gpr (by decide)).trans h8) ((k14.gpr (by decide)).trans h10)
    hsi ((k14.gpr (by decide)).trans h12) (by omega) hw' (by have := sl acc hacc; omega)
    (by have := sl mo hmo; omega) (by have := sl tmp htmp; omega) (by have := sp d2; omega)
    (by have := sp d6; omega)) fun s₅ ⟨c, lt, hbp, hlt, hD, ho₅, k₅⟩ => ?_)
  have k5 := k123.trans k₅
  have k15 := k14.trans k₅
  -- The selection.
  have hs₅ := hs₃.congr k₅.2.2
  refine WP.mono (selectAcc_ok hs₅ ((k15.gpr (by decide)).trans h8) ((k₅.gpr (by decide)).trans hsi)
    ((k15.gpr (by decide)).trans hbx) ((k15.gpr (by decide)).trans h12) hbp (by omega) hw'
    (by have := sl acc hacc; omega) (by have := sl tmp htmp; omega) (by have := sl o ho; omega)
    (by have := sp (Ne.symm d3); omega) (by have := sp (Ne.symm d7); omega)) fun t ⟨hv, hot, k₆⟩ => ?_
  -- The words of `T` in `s₅`, as after the rounds.
  have hacc₅ : wv s₅.mem B (slot w acc) w = wv s₃.mem B (slot w acc) w :=
    ho₅.wv (by have := sp d2; omega) (by have := sl acc hacc; omega)
  have hD' : wv s₅.mem B (slot w tmp) w + wv s.mem B (slot w mo) w = wv s₃.mem B (slot w acc) w +
      2 ^ (64 * w) * c.toNat := by
    rw [← fr₃ hmo (Ne.symm d1)]; exact hD
  have hres : wv t.mem B (slot w o) w = wv s₃.mem B (slot w acc) (w + 2) % wv s.mem B (slot w mo) w := by
    rw [hv, hacc₅, hlt, wv_top2]
    have := VG.Proof.Bignum.csub_result (Tl := wv s₃.mem B (slot w acc) w)
      (Tw := (word s₃.mem B (slot w acc + 8 * w)).toNat)
      (Tw1 := (word s₃.mem B (slot w acc + 8 * w + 8)).toNat) (D := wv s₅.mem B (slot w tmp) w)
      (m := wv s.mem B (slot w mo) w) (R := 2 ^ (64 * w)) (c := c.toNat)
      (by have := wv_lt s.mem B (slot w mo) w; omega) (wv_lt _ _ _ _) (Bool.toNat_le c) (wv_lt _ _ _ _)
      (by rw [← wv_top2]; exact hTlt) hD'
    rw [← this]
    by_cases h : (word s₃.mem B (slot w acc + 8 * w)).toNat < c.toNat <;> simp [h]
  refine ⟨?_, ?_, ?_, (k5.trans k₆).mono (by decide)⟩
  · rw [hres]; exact Nat.mod_lt _ hN0
  · rw [hres, Nat.mod_mul_mod, Nat.mul_comm, hTc]
  · have a3 : Arrays B w [acc, tmp, o] s.mem s₃.mem :=
      Arrays.of_outside (j := acc) (by simp) (ho₂.trans hR.out) (Nat.le_refl _) (Nat.le_refl _)
    have a5 : Arrays B w [acc, tmp, o] s₃.mem s₅.mem :=
      Arrays.of_outside (j := tmp) (by simp) ho₅ (Nat.le_refl _) (by omega)
    have a6 : Arrays B w [acc, tmp, o] s₅.mem t.mem :=
      Arrays.of_outside (j := o) (by simp) hot (Nat.le_refl _) (by omega)
    exact (a3.trans a5).trans a6

end VG.Proof.Bignum.X86_64
