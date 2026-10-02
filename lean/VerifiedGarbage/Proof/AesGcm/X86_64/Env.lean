import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM on x86-64: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes at
`Ctx`), the streaming state (80 bytes at `St`), the working space (2560 bytes
at `W`) and the stack below `SP` used by the calls (`Lay`): the state is
disjoint from the parts of `W` other than `[16, 96)` (where `seal` and
`open` keep it), and the context from both. `Perm` says the state may read
the context and write the state and `W`; `Env` adds the registers that hold
the three addresses throughout.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (i : Int) = BitVec.ofNat 64 i := rfl

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

theorem covers_append {xs ys ts : List Region} (h₁ : Covers xs ts) (h₂ : Covers ys ts) :
    Covers (xs ++ ys) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ a n ⟨x, hx, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

/-- The regions: the context, the state and the parts of `W`, and the stack
below `SP` (8 bytes, for the return addresses of the calls). -/
structure Lay (Ctx St W SP : Addr) : Prop where
  cw : Ctx.toNat + 256 ≤ 2 ^ 64
  sw : St.toNat + 80 ≤ 2 ^ 64
  ww : W.toNat + 2560 ≤ 2 ^ 64
  cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨St, 80⟩
  cw' : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩
  sa : (⟨St, 80⟩ : Region).Disjoint ⟨W, 16⟩
  sb : (⟨St, 80⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 96, 2464⟩
  kc : (below SP 8).Disjoint ⟨Ctx, 256⟩
  ks : (below SP 8).Disjoint ⟨St, 80⟩
  kw : (below SP 8).Disjoint ⟨W, 2560⟩

/-- What a state may access. -/
structure Perm (Ctx St W : Addr) (s : State) : Prop where
  ctx : Covers [⟨Ctx, 256⟩] (s.rd ++ s.wr)
  st : Covers [⟨St, 80⟩] s.wr
  w : Covers [⟨W, 2560⟩] s.wr

/-- The registers holding the context, the state, `W` and the stack pointer,
and what the state may access. -/
structure Env (Ctx St W SP : Addr) (s : State) : Prop where
  r13 : s.gpr .r13 = Ctx
  r14 : s.gpr .r14 = St
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = SP
  perm : Perm Ctx St W s

theorem Perm.of_eq {Ctx St W : Addr} {s s' : State} (h : Perm Ctx St W s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Perm Ctx St W s' := by
  obtain ⟨a, b, c⟩ := h; exact ⟨by rw [hrd, hwr]; exact a, by rw [hwr]; exact b, by rw [hwr]; exact c⟩

/-- An environment, after code that keeps `r13`–`r15`, `rsp` and the permissions. -/
theorem Env.keep {Ctx St W SP : Addr} {s s' : State} (h : Env Ctx St W SP s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env Ctx St W SP s' :=
  ⟨by rw [hg _ (by simp), h.r13], by rw [hg _ (by simp), h.r14], by rw [hg _ (by simp), h.r15],
    by rw [hg _ (by simp), h.rsp], h.perm.of_eq hrd hwr⟩

theorem Env.of_saved {Ctx St W SP : Addr} {s s' : State} (h : Env Ctx St W SP s)
    (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Env Ctx St W SP s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)) hrd hwr

namespace Lay

/-! ### Sub-regions -/

theorem ctxSub {Ctx : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨Ctx + BitVec.ofNat 64 d, n⟩ ⟨Ctx, 256⟩ :=
  Offset.sub_base _ h

theorem stSub {St : Addr} {d n : Nat} (h : d + n ≤ 80) : Region.Sub ⟨St + BitVec.ofNat 64 d, n⟩ ⟨St, 80⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

theorem bSub {W : Addr} {d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W + BitVec.ofNat 64 96, 2464⟩ :=
  Offset.sub _ h₁ (by omega)

theorem aSub {W : Addr} {d n : Nat} (h : d + n ≤ 16) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 16⟩ :=
  Offset.sub_base _ h

variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- Parts of the state and of `W` outside `[16, 96)` are disjoint. -/
theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 2560)) :
    (⟨St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ := by
  rcases hd with hd | ⟨h₁, h₂⟩
  · exact (L.sa.sub_left (stSub ha)).sub_right (aSub hd)
  · exact (L.sb.sub_left (stSub ha)).sub_right (bSub h₁ h₂)

theorem ctx_st {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 80) :
    (⟨Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 d, k⟩ :=
  (L.cs.sub_left (ctxSub ha)).sub_right (stSub hd)

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  (L.cw'.sub_left (ctxSub ha)).sub_right (wSub hd)

theorem stk_ctx {a n : Nat} (ha : a + n ≤ 256) :
    (below SP 8).Disjoint ⟨Ctx + BitVec.ofNat 64 a, n⟩ := L.kc.sub_right (ctxSub ha)

theorem stk_st {a n : Nat} (ha : a + n ≤ 80) :
    (below SP 8).Disjoint ⟨St + BitVec.ofNat 64 a, n⟩ := L.ks.sub_right (stSub ha)

theorem stk_w {a n : Nat} (ha : a + n ≤ 2560) :
    (below SP 8).Disjoint ⟨W + BitVec.ofNat 64 a, n⟩ := L.kw.sub_right (wSub ha)

/-- Parts of the state are disjoint. -/
theorem st_st {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 80) (hd : d + k ≤ 80) :
    (⟨St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.sw; omega) (by have := L.sw; omega)

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

end Lay

namespace Perm

variable {Ctx St W : Addr} {s : State} (P : Perm Ctx St W s)
include P

theorem ctxR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 d) n :=
  in_off P.ctx h (by decide)

theorem stW {d n : Nat} (h : d + n ≤ 80) : InRegions s.wr (St + BitVec.ofNat 64 d) n :=
  in_off P.st h (by decide)

theorem stR {d n : Nat} (h : d + n ≤ 80) : InRegions (s.rd ++ s.wr) (St + BitVec.ofNat 64 d) n :=
  in_left (P.stW h)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem ctxC {d n : Nat} (h : d + n ≤ 256) : Covers [⟨Ctx + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.ctx h (by decide)

theorem stC {d n : Nat} (h : d + n ≤ 80) : Covers [⟨St + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.st h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

end VG.Proof.AesGcm.X86_64
