import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Calls
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Contract

/-!
# ChaCha20-Poly1305 on AArch64: the entry state, regions and invariant

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-! ## One instruction at a time (beyond those of `vg_chacha20_xor`'s proof) -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n <<< sh)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_add {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add .x d n m :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n + s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_eor {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_orr {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .orr .x d n m :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n ||| s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_movz32 {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d ((imm.setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .w d imm 0 :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .w d (imm.setWidth 32)) exec_movz_w (k _ (Upd.write _ _ _ _))

theorem wp_movk32 {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (((s.gpr d).setWidth 32 &&& (0xFFFF : BitVec 32) ||| imm.setWidth 32 <<< 16 :
      BitVec 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movk .w d imm 1 :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons exec_movk_w (k _ (Upd.write _ _ _ _))

end

/-- A block that writes no callee-saved register keeps them, and the stack
pointer. -/
theorem WP.kept {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q)
    (hc : (is.all fun i => preserved.all fun r => dstOf i != some r) = true) :
    WP isa (.block is) s fun s' => Q s' ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he (.inl rfl), Exec.sp he⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  simpa using this

/-- Code keeps the stack pointer. -/
theorem WP.withSp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.sp he⟩

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev cx : Addr := s₀.gpr .x0
abbrev ad : Addr := s₀.gpr .x1
abbrev AL : Nat := (s₀.gpr .x2).toNat
abbrev dp : Addr := s₀.gpr .x3
abbrev L : Nat := (s₀.gpr .x4).toNat
/-- The key, the nonce, the additional data, the data and the tag on entry. -/
abbrev K : List Byte := bytesAt s₀.mem (cx s₀) 32
abbrev N : List Byte := bytesAt s₀.mem (cx s₀ + 32) 12
abbrev A : List Byte := bytesAt s₀.mem (ad s₀) (AL s₀)
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (L s₀)
abbrev T0 : List Byte := bytesAt s₀.mem (cx s₀ + 48) 16
/-- The one-time Poly1305 key. -/
abbrev otk : List Byte := Spec.ChaCha20Poly1305.polyKeyGen (K s₀) (N s₀)
abbrev ctxR : Region := ⟨cx s₀, 1024⟩
abbrev aR : Region := ⟨ad s₀, AL s₀⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨off (cx s₀) k, n⟩
end

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [aR s₀]
  wr : s₀.wr = [ctxR s₀, dR s₀]
  c_a : (ctxR s₀).Disjoint (aR s₀)
  c_d : (ctxR s₀).Disjoint (dR s₀)
  a_d : (aR s₀).Disjoint (dR s₀)
  wrap_c : (cx s₀).toNat + 1024 ≤ 2 ^ 64
  wrap_a : (ad s₀).toNat + AL s₀ ≤ 2 ^ 64
  wrap_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : preAArch64 s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## Regions -/

theorem sub_ctx (s₀ : State) {k n : Nat} (h : k + n ≤ 1024) : Region.Sub (sub s₀ k n) (ctxR s₀) :=
  sub_off _ h

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 1024)
    (hb : b + m ≤ 1024) : (sub s₀ a n).Disjoint (sub s₀ b m) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 1024) :
    (sub s₀ k n).Contains (off (cx s₀) a) w := by
  simp only [Region.Contains]
  rw [show cx s₀ + BitVec.ofNat 64 a - (cx s₀ + BitVec.ofNat 64 k) = BitVec.ofNat 64 (a - k) by
    rw [show a = k + (a - k) by omega, BitVec.ofNat_add]; bv_omega, toNat_ofNat_lt (by omega)]
  omega

theorem contains_ctx (s₀ : State) {a w : Nat} (h : a + w ≤ 1024) : (ctxR s₀).Contains (off (cx s₀) a) w := by
  simp only [Region.Contains]
  rw [show cx s₀ + BitVec.ofNat 64 a - cx s₀ = BitVec.ofNat 64 a by bv_omega, toNat_ofNat_lt (by omega)]
  omega

theorem APre.in_ctx {s₀ : State} (hp : APre s₀) {a w : Nat} (h : a + w ≤ 1024) :
    InRegions s₀.wr (off (cx s₀) a) w := ⟨ctxR s₀, by simp [hp.wr], contains_ctx s₀ h⟩

theorem APre.in_ctx' {s₀ : State} (hp : APre s₀) {a w : Nat} (h : a + w ≤ 1024) :
    InRegions (s₀.rd ++ s₀.wr) (off (cx s₀) a) w := ⟨ctxR s₀, by simp [hp.wr], contains_ctx s₀ h⟩

theorem APre.off_toNat {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < 1024) :
    (off (cx s₀) k).toNat = (cx s₀).toNat + k := by
  have := hp.wrap_c
  rw [BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  show p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Words of the context at different offsets are at separate addresses. -/
theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  VG.Proof.ChaCha20.AArch64.Xor.readW64_off m p v hd he h

theorem readW32_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 32 = m.readW (off p d) 32 :=
  Mem.readW_writeW_sep (fun _ _ _ => by bv_omega) (by decide)

/-! ## Covering the callees' regions -/

theorem covers_sub {s₀ s : State} (hp : APre s₀) (hwr : s.wr = s₀.wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r = sub s₀ k r.len ∧ k + r.len ≤ 1024) : Covers rs s.wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hrk, hk⟩ := h r hr
  exact ⟨ctxR s₀, by simp [hwr, hp.wr], k, by rw [hrk], hk⟩

theorem covers_left {rs wr : List Region} (rd : List Region) (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := h a n hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_nil_append {rs rs' : List Region} (h : Covers rs rs') : Covers ([] ++ rs) rs' := by
  simpa using h

/-- A callee's state (at `ctx + a`, `n` bytes) and argument (at `ctx + b`,
`m` bytes) in the context. -/
theorem covers2 {s₀ s : State} (hp : APre s₀) (hwr : s.wr = s₀.wr) {a n b m : Nat}
    (ha : a + n ≤ 1024) (hb : b + m ≤ 1024) :
    Covers ([sub s₀ b m] ++ [sub s₀ a n]) (s.rd ++ s.wr) :=
  covers_left _ (covers_sub hp hwr _ fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨b, rfl, hb⟩
    · exact ⟨a, rfl, ha⟩)

theorem covers1 {s₀ s : State} (hp : APre s₀) (hwr : s.wr = s₀.wr) {a n : Nat} (ha : a + n ≤ 1024) :
    Covers [sub s₀ a n] s.wr :=
  covers_sub hp hwr _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨a, rfl, ha⟩

/-! ## The saved registers and the invariant -/

/-- Our caller's `x21`–`x25` and our return address, saved in `ctx[592, 640)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (off (cx s₀) 592) 64 = s₀.gpr .x21 ∧ m.readW (off (cx s₀) 600) 64 = s₀.gpr .x22 ∧
  m.readW (off (cx s₀) 608) 64 = s₀.gpr .x23 ∧ m.readW (off (cx s₀) 616) 64 = s₀.gpr .x24 ∧
  m.readW (off (cx s₀) 624) 64 = s₀.gpr .x25 ∧ m.readW (off (cx s₀) 632) 64 = s₀.gpr .x30

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sub s₀ 592 48).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 592 ≤ d → d + 8 ≤ 640 → (sub s₀ 592 48).Contains (off (cx s₀) d) (64 / 8) :=
    fun d h₁ h₂ => contains_sub s₀ h₁ h₂ (by omega)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨by rw [hf.readW (c 592 (Nat.le_refl _) (by omega)) hd (by decide), h1],
    by rw [hf.readW (c 600 (by omega) (by omega)) hd (by decide), h2],
    by rw [hf.readW (c 608 (by omega) (by omega)) hd (by decide), h3],
    by rw [hf.readW (c 616 (by omega) (by omega)) hd (by decide), h4],
    by rw [hf.readW (c 624 (by omega) (by omega)) hd (by decide), h5],
    by rw [hf.readW (c 632 (by omega) (by omega)) hd (by decide), h6]⟩

/-- The working space: `ctx[64, 1024)`. -/
abbrev workR (s₀ : State) : Region := sub s₀ 64 960

/-- The callee-saved registers the code never writes (the functions it
calls restore `x19` and `x20`). -/
def untouched : List Reg := [.x19, .x20, .x26, .x27, .x28, .x29]

theorem untouched_preserved : ∀ r ∈ untouched, r ∈ preserved ∧ r ≠ .x30 := by decide

/-- What holds between the parts of the code. -/
structure Inv (s₀ : State) (s : State) : Prop where
  x21 : s.gpr .x21 = cx s₀
  x22 : s.gpr .x22 = dp s₀
  x23 : s.gpr .x23 = s₀.gpr .x4
  x24 : s.gpr .x24 = ad s₀
  x25 : s.gpr .x25 = s₀.gpr .x2
  un : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [workR s₀, dR s₀] s₀.mem s.mem

theorem pres (r : Reg) (h : r ∈ preserved ∧ r ≠ .x30 := by decide) : r ∈ preserved := h.1
theorem pres30 (r : Reg) (h : r ∈ preserved ∧ r ≠ .x30 := by decide) : r ≠ .x30 := h.2

/-- The invariant survives a part that keeps the callee-saved registers and
writes only the working space and the data. -/
theorem Inv.step {s₀ s s' : State} {rs : List Region} (h : Inv s₀ s) (hk : Kept rs s s')
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [workR s₀, dR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ 592 48).Disjoint r) : Inv s₀ s' where
  x21 := by rw [hk.cs _ (pres .x21) (pres30 .x21), h.x21]
  x22 := by rw [hk.cs _ (pres .x22) (pres30 .x22), h.x22]
  x23 := by rw [hk.cs _ (pres .x23) (pres30 .x23), h.x23]
  x24 := by rw [hk.cs _ (pres .x24) (pres30 .x24), h.x24]
  x25 := by rw [hk.cs _ (pres .x25) (pres30 .x25), h.x25]
  un r hr := by
    rw [hk.cs _ (untouched_preserved r hr).1 (untouched_preserved r hr).2, h.un r hr]
  sp := by rw [hk.sp, h.sp]
  rd := by rw [hk.rd, h.rd]
  wr := by rw [hk.wr, h.wr]
  saved := h.saved.frame hk.frame hsv
  frame := h.frame.trans (hk.frame.sub hsub)

/-- Kept, from a block's facts. -/
theorem Kept.of {rs : List Region} {s s' : State} (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    Kept rs s s' :=
  ⟨fun r hr _ => hg r hr, hsp, hrd, hwr, hf⟩

end VG.Proof.ChaCha20Poly1305.AArch64
