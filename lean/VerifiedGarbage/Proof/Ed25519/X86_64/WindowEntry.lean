import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyWindow
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseAccumulate
import VerifiedGarbage.Proof.Ed25519.X86_64.PointTableAddr

/-!
# Adding a table entry

Untrusted. An addition `add` adds `q` to the accumulator when slots 4–7 hold
`f q` (`AddSpec`): `pointAdd` with `f = id`, `pointAddCached` with
`f = cache`. `pointFromTableQ` copies a table entry to slots 4–7.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off F fe_st4 st4_outside Outside Keeps clob)
open VG.Impl.X25519.X86_64 (stores)

variable {fld : Arith} [EdArith fld]

/-- `add` adds `q` to the accumulator in slots 0–3 when slots 4–7 hold `f q`. -/
def AddSpec (add : List Instr) (f : Spec.Ed25519.Point → Spec.Ed25519.Point) : Prop :=
  ∀ (s : State) (base : Addr) (q : Spec.Ed25519.Point), Scratch s base →
    env s.mem base 16 = Spec.Ed25519.d → point (env s.mem base) 4 5 6 7 = f q →
    WP isa (.block add) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i

theorem pointAdd_spec : AddSpec (pointAdd fld) id := fun _ _ _ hs hd hq =>
  WP.mono (pointAddWide_ok hs hd) fun _ ⟨k, v, h⟩ => ⟨k, v.trans (by rw [hq]; rfl), h⟩

theorem pointAddCached_spec : AddSpec (pointAddCached fld) cache := fun _ _ q hs _ hq =>
  pointAddCachedWide_ok hs q hq

theorem fromTableQuarterQ_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11)) s fun t =>
      env t.mem base ⟨4 + j, by omega⟩ = F s.mem base (o + 32 * j) ∧
      TableKeep base (192 + 32 * j) 32 s t := by
  rw [WP.block_append_iff]
  refine WP.mono (fromTableWords_ok hs hp (32 * j) (by omega)) fun t ⟨hv, hk⟩ => ?_
  have ht := hs.of_keeps hk (by decide)
  refine WP.mono (stores8192_ok ht.rdi ht.wr (by omega : 192 + 32 * j + 32 ≤ 8192)
    .r8 .r9 .r10 .r11) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.1 r hr), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩⟩
  · change F u.mem base (64 + 32 * (4 + j)) = _
    rw [show 64 + 32 * (4 + j) = 192 + 32 * j by omega, F, hm, fe_st4 _ _ (by omega), hv]
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega) _ _ _ _

theorem fromTablePrefixQ_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192)
    (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11)) s fun t =>
      (∀ j (hj : j < n), env t.mem base ⟨4 + j, by omega⟩ = F s.mem base (o + 32 * j)) ∧
      TableKeep base 192 (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (fromTableQuarterQ_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega) ho) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans
      (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · have he : env u.mem base ⟨4 + j, by omega⟩ = env t.mem base ⟨4 + j, by omega⟩ :=
        Outside_F ku.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
      rw [he, hv j h]
    · have he : j = n := by omega
      subst j
      rw [hu, Outside_F hk.mem (by omega) (Or.inr (by omega))]

theorem pointFromTableQ_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTableQ) s fun t =>
      point (env t.mem base) 4 5 6 7 = tablePoint s.mem base o ∧ TableKeep base 192 128 s t := by
  refine WP.mono (fromTablePrefixQ_ok hs hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  change env t.mem base 4 = _ at h0
  change env t.mem base 5 = _ at h1
  change env t.mem base 6 = _ at h2
  change env t.mem base 7 = _ at h3
  simp only [tablePoint, point, h0, h1, h2, h3]

theorem Keep.of_tableQ {base : Addr} {s t : State}
    (h : TableKeep base 192 128 s t) : Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ clob by decide) r hm

end VG.Proof.Ed25519.X86_64
