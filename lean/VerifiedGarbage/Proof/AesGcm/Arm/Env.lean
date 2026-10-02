import VerifiedGarbage.Proof.AesGcm.Arm.Callee
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM on ARMv7: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes at
`c`), the streaming state (80 bytes at `st`), the working space (2560 bytes at
`w`) and the 8 bytes below the stack pointer `sp` used by the frames (`Lay`),
all 32-bit pointers: the state is disjoint from the parts of `W` other than
`[16, 96)` (where `seal` and `open` keep it), and the context from both.
`Perm` says the state may read the context and write the state and `W`;
`Env` adds the registers that hold the three pointers throughout, and the
stack pointer.

Memory is addressed with 64-bit addresses at offsets of `State.addr p`; the
code's 32-bit sums do not wrap (`Lay.cA`, `Lay.stA`, `Lay.wA`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)

/-- The part of a region at an offset is covered when the region is. -/
theorem covers_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine h a m ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem in_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 d) n :=
  covers_off h hd hk _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem in_left {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_left {rd wr rs : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => in_left (h a n hi)

theorem covers_cons {r : Region} {rs ts : List Region} (h₁ : Covers [r] ts) (h₂ : Covers rs ts) :
    Covers (r :: rs) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁ a n ⟨x, List.mem_singleton_self _, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem covers_nil {ts : List Region} : Covers [] ts := fun _ _ ⟨_, h, _⟩ => by cases h

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

theorem add_ofNat_zero {w : Nat} (x : BitVec w) : x + BitVec.ofNat w 0 = x := BitVec.add_zero x

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem add32_ofNat_assoc (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The regions: the context, the state and the parts of `W`, and the stack
below `sp` (8 bytes, for the frames of the calls). -/
structure Lay (c st w sp : BitVec 32) : Prop where
  cw : c.toNat + 256 ≤ 2 ^ 32
  sw : st.toNat + 80 ≤ 2 ^ 32
  ww : w.toNat + 2560 ≤ 2 ^ 32
  sp8 : 8 ≤ sp.toNat
  cs : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr st, 80⟩
  cw' : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr w, 2560⟩
  sa : (⟨State.addr st, 80⟩ : Region).Disjoint ⟨State.addr w, 16⟩
  sb : (⟨State.addr st, 80⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 96, 2464⟩
  kc : (below sp).Disjoint ⟨State.addr c, 256⟩
  ks : (below sp).Disjoint ⟨State.addr st, 80⟩
  kw : (below sp).Disjoint ⟨State.addr w, 2560⟩

/-- What a state may access. -/
structure Perm (c st w : BitVec 32) (s : State) : Prop where
  ctx : Covers [⟨State.addr c, 256⟩] (s.rd ++ s.wr)
  st : Covers [⟨State.addr st, 80⟩] s.wr
  w : Covers [⟨State.addr w, 2560⟩] s.wr

/-- The registers holding the context, the state and `W`, the stack pointer,
what the state may access, and the values `k7`, `k8` of `r7` and `r8`, which
the pieces keep (the number of rounds, or a length). -/
structure Env (c st w sp k7 k8 : BitVec 32) (s : State) : Prop where
  r7 : s.gpr .r7 = k7
  r8 : s.gpr .r8 = k8
  r9 : s.gpr .r9 = c
  r10 : s.gpr .r10 = st
  r11 : s.gpr .r11 = w
  sp : s.sp = sp
  perm : Perm c st w s

theorem Perm.of_eq {c st w : BitVec 32} {s s' : State} (h : Perm c st w s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Perm c st w s' := by
  obtain ⟨a, b, d⟩ := h; exact ⟨by rw [hrd, hwr]; exact a, by rw [hwr]; exact b, by rw [hwr]; exact d⟩

/-- An environment, after code that keeps `r7`–`r11`, `sp` and the permissions. -/
theorem Env.keep {c st w sp k7 k8 : BitVec 32} {s s' : State} (h : Env c st w sp k7 k8 s)
    (hg : ∀ r ∈ [Reg.r7, .r8, .r9, .r10, .r11], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env c st w sp k7 k8 s' :=
  ⟨by rw [hg _ (by simp), h.r7], by rw [hg _ (by simp), h.r8], by rw [hg _ (by simp), h.r9],
    by rw [hg _ (by simp), h.r10], by rw [hg _ (by simp), h.r11], by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after a call. -/
theorem Env.of_saved {c st w sp k7 k8 : BitVec 32} {s s' : State} (h : Env c st w sp k7 k8 s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env c st w sp k7 k8 s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

/-- An environment with a new value of `r7`. -/
theorem Env.set7 {c st w sp k7 k8 k7' : BitVec 32} {s s' : State} (h : Env c st w sp k7 k8 s)
    (h7 : s'.gpr .r7 = k7') (hg : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env c st w sp k7' k8 s' :=
  ⟨h7, by rw [hg _ (by simp), h.r8], by rw [hg _ (by simp), h.r9],
    by rw [hg _ (by simp), h.r10], by rw [hg _ (by simp), h.r11], by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

namespace Lay

/-! ### Sub-regions -/

theorem ctxSub {C : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ ⟨C, 256⟩ :=
  Offset.sub_base _ h

theorem stSub {S : Addr} {d n : Nat} (h : d + n ≤ 80) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 80⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

theorem bSub {W : Addr} {d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W + BitVec.ofNat 64 96, 2464⟩ :=
  Offset.sub _ h₁ (by omega)

theorem aSub {W : Addr} {d n : Nat} (h : d + n ≤ 16) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 16⟩ :=
  Offset.sub_base _ h

variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

/-! ### The code's sums do not wrap -/

theorem cA {d : Nat} (hd : d < 256) : State.addr (c + BitVec.ofNat 32 d) = State.addr c + BitVec.ofNat 64 d :=
  addr_add (by have := L.cw; omega)

theorem stA {d : Nat} (hd : d < 80) : State.addr (st + BitVec.ofNat 32 d) = State.addr st + BitVec.ofNat 64 d :=
  addr_add (by have := L.sw; omega)

theorem wA {d : Nat} (hd : d < 2560) : State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
  addr_add (by have := L.ww; omega)

/-- Parts of the state and of `W` outside `[16, 96)` are disjoint. -/
theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 2560)) :
    (⟨State.addr st + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, k⟩ := by
  rcases hd with hd | ⟨h₁, h₂⟩
  · exact (L.sa.sub_left (stSub ha)).sub_right (aSub hd)
  · exact (L.sb.sub_left (stSub ha)).sub_right (bSub h₁ h₂)

theorem ctx_st {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 80) :
    (⟨State.addr c + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr st + BitVec.ofNat 64 d, k⟩ :=
  (L.cs.sub_left (ctxSub ha)).sub_right (stSub hd)

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨State.addr c + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, k⟩ :=
  (L.cw'.sub_left (ctxSub ha)).sub_right (wSub hd)

theorem stk_ctx {a n : Nat} (ha : a + n ≤ 256) :
    (below sp).Disjoint ⟨State.addr c + BitVec.ofNat 64 a, n⟩ := L.kc.sub_right (ctxSub ha)

theorem stk_st {a n : Nat} (ha : a + n ≤ 80) :
    (below sp).Disjoint ⟨State.addr st + BitVec.ofNat 64 a, n⟩ := L.ks.sub_right (stSub ha)

theorem stk_w {a n : Nat} (ha : a + n ≤ 2560) :
    (below sp).Disjoint ⟨State.addr w + BitVec.ofNat 64 a, n⟩ := L.kw.sub_right (wSub ha)

omit L in
/-- Parts of the state are disjoint. -/
theorem st_st {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 80) (hd : d + k ≤ 80) :
    (⟨State.addr st + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr st + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

omit L in
/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨State.addr w + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

omit L in
theorem ctx_ctx {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 256) (hd : d + k ≤ 256) :
    (⟨State.addr c + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr c + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

/-- The 32-bit sums of the pointers, as numbers. -/
theorem cN {d : Nat} (hd : d < 256) : (c + BitVec.ofNat 32 d).toNat = c.toNat + d := by
  have := L.cw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem stN {d : Nat} (hd : d < 80) : (st + BitVec.ofNat 32 d).toNat = st.toNat + d := by
  have := L.sw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem wN {d : Nat} (hd : d < 2560) : (w + BitVec.ofNat 32 d).toNat = w.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

end Lay

namespace Perm

variable {c st w : BitVec 32} {s : State} (P : Perm c st w s)
include P

theorem ctxR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (State.addr c + BitVec.ofNat 64 d) n :=
  in_off P.ctx h (by decide)

theorem stW {d n : Nat} (h : d + n ≤ 80) : InRegions s.wr (State.addr st + BitVec.ofNat 64 d) n :=
  in_off P.st h (by decide)

theorem stR {d n : Nat} (h : d + n ≤ 80) : InRegions (s.rd ++ s.wr) (State.addr st + BitVec.ofNat 64 d) n :=
  in_left (P.stW h)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (State.addr w + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (State.addr w + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem ctxC {d n : Nat} (h : d + n ≤ 256) : Covers [⟨State.addr c + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.ctx h (by decide)

theorem stC {d n : Nat} (h : d + n ≤ 80) : Covers [⟨State.addr st + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.st h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨State.addr w + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

end VG.Proof.AesGcm.Arm
