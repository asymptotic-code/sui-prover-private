/-
# Combinatorics

Generic, core-Lean (no Mathlib/Batteries) combinatorics lemmas shared across the
verification suite. Promoted out of per-module proof files so future proofs reuse
them instead of re-deriving. Everything here is stated over abstract `List α` and a
generic value map `f : α → Nat` wherever possible.
-/

namespace Combinatorics

/-- A `Nat`-valued list sum is monotone under `Sublist`. -/
theorem nat_sublist_sum_le {l₁ l₂ : List Nat} (h : List.Sublist l₁ l₂) :
    l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => simp
  | cons a _ ih => simp only [List.sum_cons]; omega
  | cons_cons a _ ih => simp only [List.sum_cons]; omega

/-- Nodup-keyed select-sum monotonicity: a `Nodup` list of keys all drawn from
`keys` selects values whose `f`-sum is bounded by the full `f`-sum over `keys`.
Proven by induction on `keys`, erasing each selected key once (Nodup ⟹ no double
count). -/
theorem nodup_subset_map_sum_le {α} [BEq α] [LawfulBEq α] (f : α → Nat) :
    ∀ (sel keys : List α), sel.Nodup → (∀ x ∈ sel, x ∈ keys) →
      (sel.map f).sum ≤ (keys.map f).sum := by
  intro sel keys
  induction keys generalizing sel with
  | nil =>
    intro _ hsub
    have hnil : sel = [] := by
      rcases sel with _ | ⟨x, xs⟩
      · rfl
      · exact absurd (hsub x (List.mem_cons_self)) (by simp)
    simp [hnil]
  | cons a rest ih =>
    intro hnd hsub
    by_cases ha : a ∈ sel
    · have hperm : sel.Perm (a :: sel.erase a) := List.perm_cons_erase ha
      have hsum : (sel.map f).sum = f a + ((sel.erase a).map f).sum := by
        rw [List.Perm.sum_nat (hperm.map f)]; simp only [List.map_cons, List.sum_cons]
      have hnd' : (sel.erase a).Nodup := hnd.erase a
      have hane : a ∉ sel.erase a := hnd.not_mem_erase
      have hsub' : ∀ x ∈ sel.erase a, x ∈ rest := by
        intro x hx
        have hxs : x ∈ sel := List.mem_of_mem_erase hx
        have hxa : x ≠ a := fun h => hane (h ▸ hx)
        rcases List.mem_cons.mp (hsub x hxs) with h | h
        · exact absurd h hxa
        · exact h
      have hrec := ih (sel.erase a) hnd' hsub'
      simp only [List.map_cons, List.sum_cons]; omega
    · have hsub' : ∀ x ∈ sel, x ∈ rest := by
        intro x hx
        rcases List.mem_cons.mp (hsub x hx) with h | h
        · exact absurd (h ▸ hx) ha
        · exact h
      have hrec := ih sel hnd hsub'
      simp only [List.map_cons, List.sum_cons]; omega

/-- `(l.map (const 1)).sum = l.length`. -/
theorem map_const_one_sum {α} (l : List α) :
    (l.map (fun _ => (1 : Nat))).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

/-- A `Nodup` list whose entries all lie in `keys` is no longer than `keys`. Reuses
the combinatorial core with `f := const 1`. -/
theorem nodup_length_le_of_subset {α} [BEq α] [LawfulBEq α] {sel keys : List α}
    (hnd : sel.Nodup) (hsub : ∀ x ∈ sel, x ∈ keys) : sel.length ≤ keys.length := by
  have h := nodup_subset_map_sum_le (fun _ : α => (1 : Nat)) sel keys hnd hsub
  rw [map_const_one_sum, map_const_one_sum] at h
  exact h

/-- `getD` at an in-bounds index is `getElem`. -/
theorem getD_eq {α} [Inhabited α] (l : List α) (k : Nat) (h : k < l.length) :
    l.getD k default = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- Swapping two in-bounds positions of a list yields a permutation of it.
The pure-`List` core behind the `MoveVector.swap` permutation lemmas. -/
theorem set_set_perm {α} (l : List α) {a b : Nat} (ha : a < l.length) (hb : b < l.length) :
    ((l.set a (l[b]'hb)).set b (l[a]'ha)).Perm l :=
  List.set_set_perm ha hb

/-- Find-under-Nodup: when the key projection of a list is `Nodup`, searching for the
key of the element at position `k` returns exactly `some k`. Generalizes the
`voting_power_at_self`-style "the address-keyed find selects its own slot". -/
theorem nodup_findIdx?_eq {α β} [BEq β] [LawfulBEq β] {key : α → β} {l : List α}
    (hnd : (l.map key).Nodup) {k : Nat} (hk : k < l.length) :
    l.findIdx? (fun w => key w == key l[k]) = some k := by
  rcases hfi : l.findIdx? (fun w => key w == key l[k]) with _ | idx
  · rw [List.findIdx?_eq_none_iff] at hfi
    exact absurd (hfi l[k] (List.getElem_mem hk)) (by simp)
  · obtain ⟨hil, hpi, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
    have hkey : key l[idx] = key l[k] := by simpa using hpi
    have hidxk : idx = k := by
      have hmap : (l.map key)[idx]'(by simpa using hil)
          = (l.map key)[k]'(by simpa using hk) := by
        simp only [List.getElem_map]; exact hkey
      exact (List.getElem_inj hnd).mp hmap
    rw [hidxk]

/-- `iterate step n s` applies `step` to `s` exactly `n` times. Local definition so
this file stays core-Lean (no `Function.iterate`/`Nat.iterate` dependency). -/
def iterate {S} (step : S → S) : Nat → S → S
  | 0,     s => s
  | n + 1, s => iterate step n (step s)

/-- Generic "push at most one per iteration" length bound: a loop expressed as
`iterate step n` whose body grows the measure by at most one bounds the final
measure by the initial measure plus the iteration count. Captures the
`cra_while_0_adj_len` / `gvi_while_0_len` fuel-induction shape abstractly. -/
theorem iterate_count_le {S} (count : S → Nat) (step : S → S)
    (hstep : ∀ s, count (step s) ≤ count s + 1) :
    ∀ (n : Nat) (s : S), count (iterate step n s) ≤ count s + n := by
  intro n
  induction n with
  | zero => intro s; exact Nat.le_refl _
  | succ n ih =>
    intro s
    show count (iterate step n (step s)) ≤ count s + (n + 1)
    have h1 := hstep s
    have h2 := ih (step s)
    omega


/-- Setting index `k` of a `Nat` list replaces its contribution: the new sum plus
the old element equals the old sum plus the new element. -/
theorem nat_set_sum (L : List Nat) (k y : Nat) (h : k < L.length) :
    (L.set k y).sum + L.getD k 0 = L.sum + y := by
  induction L generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero => simp only [List.set_cons_zero, List.sum_cons, List.getD_cons_zero]; omega
    | succ k =>
      have hk : k < t.length := by simpa using h
      simp only [List.set_cons_succ, List.sum_cons, List.getD_cons_succ]
      have := ih k hk; omega

/-- Swapping two in-range elements of a `Nat` list preserves its sum. -/
theorem nat_swap_sum (L : List Nat) (a b : Nat) (ha : a < L.length) (hb : b < L.length) :
    ((L.set a (L.getD b 0)).set b (L.getD a 0)).sum = L.sum := by
  by_cases hab : a = b
  · subst hab
    rw [List.set_set]
    have h := nat_set_sum L a (L.getD a 0) ha; omega
  · have h2 := nat_set_sum L a (L.getD b 0) ha
    have h1 := nat_set_sum (L.set a (L.getD b 0)) b (L.getD a 0)
      (by rw [List.length_set]; exact hb)
    have hbne : (L.set a (L.getD b 0)).getD b 0 = L.getD b 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
        ← List.getD_eq_getElem?_getD]
    rw [hbne] at h1; omega

/-- `getD` through `List.map`, for any default-preserving projection. -/
theorem map_getD {α : Type _} [Inhabited α] (f : α → Nat) (hf : f default = 0)
    (l : List α) (k : Nat) : (l.map f).getD k 0 = f (l.getD k default) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? with
  | none => simpa using hf.symm
  | some x => rfl

end Combinatorics
